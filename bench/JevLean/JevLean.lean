/-
Vendored from https://github.com/jesyspa/jev-lean at commit
54df393cab1c5da1e35dd842f0830e610054b820 (Apache License 2.0; see LICENSE and
NOTICE in this directory).

Modified for this benchmark:
* ported to Lean v4.34.0-rc2 without Mathlib: core `TryThis`, an inlined
  simp-declaration lookup, the `Std.Async` rename, and `theorem` for `lemma`;
* `JEV_MAX_WALL_MS` overrides the search's wall-clock budget, so a slower
  local ranker is not cut off by the default 10 s;
* converted to a Lean module (`public meta` imports and section), so that
  sf-in-lean chapters written as modules can import it, and the small
  synthetic test fixtures at the end of the file (`tally`, `Tree`, ...) are
  removed.
The search, action catalogue, and broker protocol are otherwise unchanged.
-/
/-
# Jev-first proof-search experiment

The executable experiment lives in `jevlean/`. This module pins and checks the
Lean/Mathlib environment used to verify candidate actions.
-/

module

public meta import Aesop
public meta import Lean.Meta.Tactic.TryThis
public meta import Std.Async.TCP
public meta import Std.Async.Timer

public meta section


namespace JevLean

namespace Search

open Lean Elab Tactic Meta

/-- A concrete Lean command generated locally from the current proof state. -/
structure Action where
  /-- Replayable Lean tactic syntax. -/
  tacticSyntax : TSyntax `tactic
  /-- Ranking description, which may include non-Lean provider rationale. -/
  text : String
  /-- Optional source when the ranking description is not itself replayable Lean. -/
  replayText? : Option String := none
  cost : Nat := 1
  /-- Generator family, used only for deterministic search telemetry. -/
  family : String := "ordinary"
  unfoldedConstants : List Name := []

/-- A restorable search node. Goals retain Lean's active-goal order. -/
structure Node where
  state : Lean.Elab.Tactic.SavedState
  goals : List MVarId
  path : List Action
  depth : Nat
  cost : Nat
  /-- Stable rendering of the ordered successor goals. -/
  fingerprint : String

/-- Deterministic theorem-wide limits for a single search invocation.
`maxHeartbeats` counts attempted catalogue transitions. -/
structure Config where
  maxDepth : Nat := 6
  maxCost : Nat := 6
  maxNodes : Nat := 64
  /-- Bounded number of canonical states retained for duplicate suppression. -/
  maxTranspositions : Nat := 128
  maxHeartbeats : Nat := 256
  maxJevCalls : Nat := 16
  maxWallMs : Nat := 10_000
  maxRetrievedNames : Nat := 24
  maxRewriteCandidates : Nat := 12
  maxRewriteSimpLemmas : Nat := 4
  maxRewriteSimpNames : Nat := 256
  maxRewriteMs : Nat := 100
  maxUnfoldCandidates : Nat := 4
  maxDataCases : Nat := 2
  maxPropCases : Nat := 2
  maxInductions : Nat := 2
  maxGeneralizingInductions : Nat := 1
  maxWitnesses : Nat := 2
  maxDestructures : Nat := 2
  maxLocalApplications : Nat := 16
  maxLocalApplicationTerms : Nat := 4
  maxLocalApplicationArity : Nat := 2
  /-- Enable the bounded helper-state meta-action. It is disabled by default. -/
  enableLlmHelpers : Bool := false
  /-- A deterministic state estimate must reach this percentage before generation. -/
  helperProbabilityThreshold : Nat := 85
  /-- One meta-action request returns no more than this many raw propositions. -/
  maxHelperProposals : Nat := 4
  /-- At most this many Lean-checked helper cuts enter the frontier. -/
  maxAdmittedHelpers : Nat := 2
  /-- Helper requests share the invocation wall budget and have this independent cap. -/
  maxHelperMs : Nat := 2_000

/-- The concrete state supplied to a ranker without exposing mutable tactic state. -/
structure RankContext where
  focusedGoal : String
  pendingGoals : List String
  path : List String
  remainingWallMs : Nat := 0

/-- A seam used by tests and alternative bounded action generators. -/
abbrev ActionSource := Config → TacticM (List Action)

/-- A seam used to replace the external ranker while retaining the same scheduler. -/
abbrev ActionRanker := RankContext → List Action → TacticM (List Action)

private partial def freshIntroName (used : List Name) (index : Nat := 0) : Name :=
  let candidate := Name.mkSimple <| if index == 0 then "jev_h" else s!"jev_h{index}"
  if used.contains candidate then freshIntroName used (index + 1) else candidate

/-- Locals introduced by replayed tactics have fresh macro scopes and cannot be named in later syntax. -/
private def hasReplayableUserName (decl : LocalDecl) : Bool :=
  !decl.isImplementationDetail && !decl.userName.isAnonymous && !decl.userName.hasMacroScopes

private def closingActions : TacticM (List Action) := do
  pure [
    { tacticSyntax := ← `(tactic| rfl), text := "rfl", family := "closing" },
    { tacticSyntax := ← `(tactic| assumption), text := "assumption", family := "closing" },
    { tacticSyntax := ← `(tactic| simp), text := "simp", family := "closing" },
    { tacticSyntax := ← `(tactic| omega), text := "omega", family := "closing" },
    { tacticSyntax := ← `(tactic| aesop (config := { terminal := true, maxRuleApplications := 32 })),
      text := "aesop (config := { terminal := true, maxRuleApplications := 32 })", family := "closing" }
  ]

private def candidateWorks (action : Action) : TacticM Bool := do
  let goals ← getGoals
  let state ← saveState
  try
    withMainContext do
      Term.withoutErrToSorry <| withoutRecover do evalTactic action.tacticSyntax
    return true
  catch _ => return false
  finally
    state.restore
    setGoals goals

private partial def headConstant? : Expr → Option Name
  | .const name _ => some name
  | .app function _ => headConstant? function
  | .mdata _ body => headConstant? body
  | .proj _ _ body => headConstant? body
  | _ => none

private def inductiveType (type : Expr) : MetaM Bool := do
  match headConstant? (← whnf type) with
  | some name => isInductive name
  | none => return false

private def destructurableType (type : Expr) : MetaM Bool := do
  let type ← whnf type
  return type.isAppOfArity ``And 2 || type.isAppOfArity ``Exists 2

private def existentialTarget : TacticM Bool := do
  let target ← (← getMainGoal).getType
  return (← whnf target).isAppOfArity ``Exists 2

private def occursIn (fvar : FVarId) (expression : Expr) : Bool :=
  (expression.find? fun expression => expression.fvarId? == some fvar).isSome

/-- Generate a small checked structural catalogue. Data elimination is limited to inductive
locals, while induction generalizes at most one preceding non-propositional local. -/
private def structuralActions (config : Config) : TacticM (List Action) := do
  let lctx ← getLCtx
  let declarations := lctx.foldl (init := []) fun result decl => result.concat decl
  let target ← (← getMainGoal).getType
  let used := declarations.map (·.userName)
  let introName := freshIntroName used
  let intro := mkIdent introName
  let mut actions := [
    { tacticSyntax := ← `(tactic| intro $intro:ident), text := s!"intro {introName}" },
    { tacticSyntax := ← `(tactic| constructor), text := "constructor" },
    { tacticSyntax := ← `(tactic| left), text := "left" },
    { tacticSyntax := ← `(tactic| right), text := "right" }
  ]
  let mut propCases := 0
  let mut dataCases := 0
  let mut inductions := 0
  let mut generalized := 0
  let mut destructures := 0
  for (decl, index) in declarations.zipIdx do
    if hasReplayableUserName decl then
      let type ← inferType decl.toExpr
      let ident := mkIdent decl.userName
      if ← isProp type then
        if propCases < config.maxPropCases then
          let action : Action := { tacticSyntax := ← `(tactic| cases $ident:ident), text := s!"cases {decl.userName}" }
          if ← candidateWorks action then
            actions := actions.concat action
            propCases := propCases + 1
        if destructures < config.maxDestructures && (← destructurableType type) then
          let left := freshIntroName (used ++ [decl.userName]) destructures
          let right := freshIntroName (used ++ [decl.userName, left]) (destructures + 1)
          let action : Action := {
            tacticSyntax := ← `(tactic| rcases $ident:ident with ⟨$(mkIdent left):ident, $(mkIdent right):ident⟩)
            text := s!"rcases {decl.userName} with ⟨{left}, {right}⟩"
          }
          if ← candidateWorks action then
            actions := actions.concat action
            destructures := destructures + 1
      else if ← inductiveType type then
        if dataCases < config.maxDataCases then
          let action : Action := { tacticSyntax := ← `(tactic| cases $ident:ident), text := s!"cases {decl.userName}" }
          if ← candidateWorks action then
            actions := actions.concat action
            dataCases := dataCases + 1
        if inductions < config.maxInductions then
          let action : Action := { tacticSyntax := ← `(tactic| induction $ident:ident), text := s!"induction {decl.userName}" }
          if ← candidateWorks action then
            actions := actions.concat action
            inductions := inductions + 1
        if generalized < config.maxGeneralizingInductions then
          for prior in declarations.take index do
            if generalized < config.maxGeneralizingInductions && hasReplayableUserName prior &&
                occursIn prior.fvarId target && !(← isProp (← inferType prior.toExpr)) then
              let generalize := mkIdent prior.userName
              let action : Action := {
                tacticSyntax := ← `(tactic| induction $ident:ident generalizing $generalize:ident),
                text := s!"induction {decl.userName} generalizing {prior.userName}"
              }
              if ← candidateWorks action then
                actions := actions.concat action
                generalized := generalized + 1
  if (← existentialTarget) then
    let mut witnesses := 0
    for decl in declarations do
      if witnesses < config.maxWitnesses && hasReplayableUserName decl then
        let ident := mkIdent decl.userName
        let action : Action := {
          tacticSyntax := ← `(tactic| refine ⟨$ident:ident, ?_⟩), text := s!"refine ⟨{decl.userName}, ?_⟩"
        }
        if ← candidateWorks action then
          actions := actions.concat action
          witnesses := witnesses + 1
  return actions

private def applicationTerm (function : TSyntax `term) (arguments : List (TSyntax `term)) :
    TacticM (TSyntax `term) := do
  match arguments with
  | [] => pure function
  | argument :: arguments =>
    let function ← applicationTerm function arguments
    `(term| $function $argument)

private def argumentLists {α : Type} (terms : List α) (arity : Nat) : List (List α) :=
  match arity with
  | 0 => [[]]
  | arity + 1 =>
    (argumentLists terms arity).flatMap fun arguments =>
      terms.map fun term => arguments ++ [term]

private def localApplicationActions (config : Config) : TacticM (List Action) := do
  if config.maxLocalApplications == 0 || config.maxLocalApplicationTerms == 0 ||
      config.maxLocalApplicationArity == 0 then
    return []
  let lctx ← getLCtx
  let terms : List ((TSyntax `term) × String) := lctx.foldl (init := []) fun terms decl =>
    if hasReplayableUserName decl then terms.concat (mkIdent decl.userName, decl.userName.toString) else terms
  let terms := terms.take config.maxLocalApplicationTerms
  let mut actions := []
  for decl in lctx do
    unless actions.length >= config.maxLocalApplications do
      if hasReplayableUserName decl && (← whnf decl.type).isForall then
        let function := mkIdent decl.userName
        for arity in [:config.maxLocalApplicationArity] do
          unless actions.length >= config.maxLocalApplications do
            for arguments in argumentLists terms (arity + 1) do
              unless actions.length >= config.maxLocalApplications do
                let term ← applicationTerm function (arguments.map (·.1))
                let application := s!"{decl.userName} {String.intercalate " " <| arguments.map (·.2)}"
                let variants ← #[
                  (term, application),
                  (← `(term| ($term).symm), s!"({application}).symm"),
                  (← `(term| ($term).1), s!"({application}).1"),
                  (← `(term| ($term).2), s!"({application}).2"),
                  (← `(term| ($term).mp), s!"({application}).mp"),
                  (← `(term| ($term).mpr), s!"({application}).mpr")
                ].toList.mapM fun (term, text) => do
                  let exact : Action := {
                    tacticSyntax := ← `(tactic| exact $term), text := s!"exact {text}"
                  }
                  let apply : Action := {
                    tacticSyntax := ← `(tactic| apply $term), text := s!"apply {text}"
                  }
                  pure [exact, apply]
                for variant in variants.flatten do
                  unless actions.length >= config.maxLocalApplications do
                    if ← candidateWorks variant then actions := actions.concat variant
  return actions

private def localActions (config : Config) : TacticM (List Action) := do
  let lctx ← getLCtx
  let basic ← lctx.foldlM (init := []) fun actions decl => do
    if hasReplayableUserName decl then
      let ident := mkIdent decl.userName
      pure (actions ++ [
        { tacticSyntax := ← `(tactic| exact $ident), text := s!"exact {decl.userName}" },
        { tacticSyntax := ← `(tactic| apply $ident), text := s!"apply {decl.userName}" }
      ])
    else
      pure actions
  return basic ++ (← localApplicationActions config)

private partial def constantsIn (expr : Expr) (constants : List Name := []) : List Name :=
  match expr with
  | .const name _ => if constants.contains name then constants else name :: constants
  | .app function argument => constantsIn argument (constantsIn function constants)
  | .lam _ type body _ | .forallE _ type body _ => constantsIn body (constantsIn type constants)
  | .letE _ type value body _ => constantsIn body (constantsIn value (constantsIn type constants))
  | .mdata _ body | .proj _ _ body => constantsIn body constants
  | _ => constants

private partial def forallBody : Expr → Expr
  | .forallE _ _ body _ => forallBody body
  | expr => expr

private def retrievalScore (query : List Name) (type : Expr) : Nat :=
  (constantsIn (forallBody type)).countP query.contains

/-- Retrieve globally named declarations related to the focused goal, then retain only candidates
that Lean can elaborate and execute in the current tactic state. -/
def globalActions (maxNames : Nat) : TacticM (List Action) := do
  let goal ← getMainGoal
  let target ← goal.getType
  let lctx ← getLCtx
  let query := lctx.foldl (init := constantsIn target) fun names decl =>
    constantsIn decl.type names
  let names ← (← getEnv).constants.map₂.foldlM (init := []) fun names name _ => do
    let some info := (← getEnv).find? name | return names
    let score := retrievalScore query info.type
    if score == 0 then return names
    return (score, name) :: names
  let names := names.mergeSort fun left right =>
    left.1 > right.1 || left.1 == right.1 && left.2.toString < right.2.toString
  let mut actions := []
  for (_, name) in names.take maxNames do
    let ident := mkIdent name
    let exactAction : Action := {
      tacticSyntax := ← `(tactic| exact $ident), text := s!"exact {name}"
    }
    if ← candidateWorks exactAction then actions := actions.concat exactAction
    let applyAction : Action := {
      tacticSyntax := ← `(tactic| apply $ident), text := s!"apply {name}"
    }
    if ← candidateWorks applyAction then actions := actions.concat applyAction
  return actions

private def isEquality (type : Expr) : MetaM Bool := do
  let type ← whnf type
  return type.isAppOfArity ``Eq 3 || type.isAppOfArity ``Iff 2

private partial def scoredSimpNames (names query : List Name) (deadline remaining : Nat) :
    TacticM (List (Nat × Name)) := do
  if remaining == 0 || (← IO.monoMsNow) >= deadline then
    return []
  match names with
  | [] => return []
  | name :: names =>
    let score? := (← getEnv).find? name |>.map fun info =>
      let textualMatch := query.any fun constant =>
        let text := constant.toString
        text.length > 1 && name.toString.contains (text.drop 1)
      retrievalScore query info.type + if textualMatch then 100 else 0
    let rest ← scoredSimpNames names query deadline (remaining - 1)
    return match score? with
      | some score => if score == 0 then rest else (score, name) :: rest
      | none => rest

/-- All declarations carrying a simp attribute (inlined from Mathlib's `getAllSimpDecls`). -/
private def allSimpDecls (simpAttr : Name) : CoreM (List Name) := do
  let some simpDecl ← Lean.Meta.getSimpExtension? simpAttr | return []
  let thms ← simpDecl.getTheorems
  return thms.toUnfold.toList ++ thms.lemmaNames.toList.filterMap fun
    | .decl decl _ => some decl
    | _ => none

def rewriteActions (config : Config) : TacticM (List Action) := do
  let deadline ← IO.monoMsNow.map (· + config.maxRewriteMs)
  let timedOut : TacticM Bool := return (← IO.monoMsNow) >= deadline
  let mut actions := []
  let lctx ← getLCtx
  for decl in lctx do
    if hasReplayableUserName decl && (← isEquality decl.type) then
      let ident := mkIdent decl.userName
      let forward : Action := {
        tacticSyntax := ← `(tactic| rw [$ident:ident]), text := s!"rw [{decl.userName}]"
      }
      unless actions.length >= config.maxRewriteCandidates || (← timedOut) do
        if ← candidateWorks forward then actions := actions.concat forward
      let backward : Action := {
        tacticSyntax := ← `(tactic| rw [← $ident:ident]), text := s!"rw [← {decl.userName}]"
      }
      unless actions.length >= config.maxRewriteCandidates || (← timedOut) do
        if ← candidateWorks backward then actions := actions.concat backward
  unless actions.length >= config.maxRewriteCandidates || (← timedOut) do
    let goal ← getMainGoal
    let target ← goal.getType
    let query := (constantsIn target).filter fun name =>
      name != ``Eq && name != ``Iff && name != ``True && name != ``Nat
    let simpNames ← allSimpDecls `simp
    let scored ← scoredSimpNames simpNames.reverse query deadline config.maxRewriteSimpNames
    let scored := scored.mergeSort fun left right =>
      left.1 > right.1 || left.1 == right.1 && left.2.toString < right.2.toString
    for (_, name) in scored.take config.maxRewriteSimpLemmas do
      unless actions.length >= config.maxRewriteCandidates || (← timedOut) do
        let ident := mkIdent name
        let witness : Action := {
          tacticSyntax := ← `(tactic| rw [$ident:ident]), text := s!"rw [{name}]"
        }
        if ← candidateWorks witness then
          let action : Action := {
            tacticSyntax := ← `(tactic| simp only [$ident:ident]), text := s!"simp only [{name}]"
          }
          unless actions.length >= config.maxRewriteCandidates || (← timedOut) do
            if ← candidateWorks action then actions := actions.concat action
  return actions

private def unfoldableDefinition (name : Name) : TacticM Bool := do
  match (← getEnv).find? name with
  | some (.defnInfo _) => return true
  | _ => return false

private def headDefinitions : TacticM (List (Option Name × Name)) := do
  let goal ← getMainGoal
  let target ← goal.getType
  let lctx ← getLCtx
  let candidates := match headConstant? (forallBody target) with
    | some name => [(none, name)]
    | none => []
  lctx.foldlM (init := candidates) fun candidates decl => do
    match headConstant? (forallBody decl.type) with
    | some name => return candidates.concat (some decl.userName, name)
    | none => return candidates

/-- Generate checked `unfold` actions only for definition heads of the goal and local hypotheses.
This avoids cataloguing unrelated reducible internals. -/
def unfoldActions (config : Config) : TacticM (List Action) := do
  let mut actions := []
  for (location, name) in ← headDefinitions do
    unless actions.length >= config.maxUnfoldCandidates do
      if ← unfoldableDefinition name then
        let ident := mkIdent name
        let action ← match location with
          | none => pure {
              tacticSyntax := ← `(tactic| unfold $ident:ident), text := s!"unfold {name}",
              unfoldedConstants := [name]
            }
          | some hypothesis =>
            if hypothesis.isAnonymous || hypothesis.hasMacroScopes then continue
            let hypothesis := mkIdent hypothesis
            pure {
              tacticSyntax := ← `(tactic| unfold $ident:ident at $hypothesis:ident),
              text := s!"unfold {name} at {hypothesis.getId}", unfoldedConstants := [name]
            }
        if ← candidateWorks action then actions := actions.concat action
  return actions

/-- Build the finite, syntax-safe action catalogue for the current active goal. -/
def catalogue (config : Config) : TacticM (List Action) := do
  return (← structuralActions config) ++ (← localActions config) ++ (← rewriteActions config) ++
    (← globalActions config.maxRetrievedNames) ++ (← unfoldActions config) ++ (← closingActions)

private initialize rankCache : IO.Ref (Std.HashMap String (List Nat)) ← IO.mkRef {}
private initialize helperCache : IO.Ref (Std.HashMap String (List (String × String))) ← IO.mkRef {}

/-- A provider supplies proposition text and a rationale; Lean remains the checker. -/
abbrev HelperSource := RankContext → Nat → Nat → TacticM (List (String × String))

/-- Cheap deterministic gate for the optional meta-action. Complex quantified or inductive-shaped
states are more likely to benefit from a cut than atomic closing goals. -/
def helperNeedProbability (context : RankContext) : Nat :=
  min 100 <| 20 + 20 * context.pendingGoals.length +
    (if context.focusedGoal.contains "∀" || context.focusedGoal.contains "∃" then 55 else 0) +
    (if context.focusedGoal.contains "→" then 20 else 0)

/-- Canonical identity deliberately excludes the path: equivalent revisits share a provider result. -/
def canonicalStateIdentity (context : RankContext) : String :=
  context.focusedGoal ++ "\n-- siblings --\n" ++ String.intercalate "\n" context.pendingGoals

private def applyRanking? (actions : List Action) (indices : List Nat) : Option (List Action) := do
  if indices.length != actions.length || indices.eraseDups.length != actions.length ||
      indices.any fun index => index == 0 || index > actions.length then
    none
  let ranked := indices.filterMap fun index => actions[index - 1]?
  if ranked.length == actions.length then some ranked else none

private def brokerAddress : IO Std.Net.SocketAddress := do
  let modelPort ← IO.getEnv "JEV_MODEL_BROKER_PORT"
  let rankPort ← IO.getEnv "JEV_RANK_BROKER_PORT"
  let port := match (modelPort.orElse fun _ => rankPort).bind String.toNat? with
    | some port => port
    | none => 8765
  if port == 0 || port > 65535 then
    throw <| IO.Error.userError "JEV_MODEL_BROKER_PORT must be between 1 and 65535"
  return .v4 { addr := Std.Net.IPv4Addr.ofParts 127 0 0 1, port := port.toUInt16 }

private def beforeDeadline (operation : Std.Async.Async α) (deadline : Nat) : IO α := do
  let now ← IO.monoMsNow
  if now >= deadline then
    throw <| IO.Error.userError "rank broker request deadline exceeded"
  let delay := Std.Time.Millisecond.Offset.ofNat (deadline - now)
  let result ← Std.Async.Async.race (some <$> operation)
    (Std.Async.sleep delay *> pure none) |>.block
  let some result := result | throw <| IO.Error.userError "rank broker request deadline exceeded"
  return result

private partial def receiveBrokerFrame (socket : Std.Async.TCP.Socket.Client)
    (deadline : Nat) (received : ByteArray := ByteArray.empty) : IO String := do
  if received.size > 1_000_000 then
    throw <| IO.Error.userError "rank broker response exceeds 1000000 bytes"
  let some chunk ← beforeDeadline (socket.recv? 65536) deadline |
    throw <| IO.Error.userError "rank broker closed the response"
  let received := received ++ chunk
  if received.size > 1_000_000 then
    throw <| IO.Error.userError "rank broker response exceeds 1000000 bytes"
  if received.toList.contains '\n'.toUInt8 then
    let some text := String.fromUTF8? received | throw <| IO.Error.userError "rank broker response is not UTF-8"
    return (text.takeWhile (· != '\n')).toString
  receiveBrokerFrame socket deadline received

private def brokerRanking (request : Json) (deadline : Nat) : IO (List Nat) := do
  let socket ← Std.Async.TCP.Socket.Client.mk
  beforeDeadline (socket.connect (← brokerAddress)) deadline
  beforeDeadline (socket.send ((Json.mkObj [
    ("operation", Json.str "rank"), ("request", request), ("deadline_ms", Json.num (deadline - (← IO.monoMsNow)))
  ]).compress.toUTF8 ++ "\n".toUTF8)) deadline
  let response ← receiveBrokerFrame socket deadline
  let json ← match Json.parse response with
    | .ok json => pure json
    | .error error => throw <| IO.Error.userError s!"rank broker response is invalid JSON: {error}"
  let object ← match json.getObj? with
    | .ok object => pure object
    | .error error => throw <| IO.Error.userError s!"rank broker response is not an object: {error}"
  let some okJson := object.get? "ok" | throw <| IO.Error.userError "rank broker response has no ok field"
  let ok ← match okJson.getBool? with
    | .ok ok => pure ok
    | .error error => throw <| IO.Error.userError s!"rank broker response has invalid ok field: {error}"
  unless ok do
    let error := ((object.get? "error").bind fun value => value.getStr?.toOption).getD "unknown error"
    throw <| IO.Error.userError s!"rank broker rejected request: {error}"
  let some rankingJson := object.get? "ranking" | throw <| IO.Error.userError "rank broker response has no ranking field"
  let ranking ← match rankingJson.getArr? with
    | .ok ranking => pure ranking
    | .error error => throw <| IO.Error.userError s!"rank broker response has invalid ranking field: {error}"
  ranking.toList.mapM fun identifier => do
    let identifier ← match identifier.getStr? with
      | .ok identifier => pure identifier
      | .error error => throw <| IO.Error.userError s!"rank broker returned non-string identifier: {error}"
    let some index := if identifier.startsWith "A" then (identifier.drop 1).toNat? else none |
      throw <| IO.Error.userError "rank broker returned invalid action identifier"
    return index

private def providerHelpers (context : RankContext) (maximum timeout : Nat) : TacticM (List (String × String)) := do
  let key := canonicalStateIdentity context
  if let some cached := (← helperCache.get).get? key then return cached
  let deadline ← IO.monoMsNow.map (· + timeout)
  let request := Json.mkObj [("operation", Json.str "helpers"), ("state", Json.mkObj [("focused_goal", Json.str context.focusedGoal), ("canonical_state", Json.str key)]), ("max_proposals", Json.num maximum), ("deadline_ms", Json.num timeout)]
  let result ← try
    let socket ← Std.Async.TCP.Socket.Client.mk
    beforeDeadline (socket.connect (← brokerAddress)) deadline
    beforeDeadline (socket.send (request.compress.toUTF8 ++ "\n".toUTF8)) deadline
    let text ← receiveBrokerFrame socket deadline
    let json ← match Json.parse text with | .ok json => pure json | .error error => throwError "invalid helper response: {error}"
    let object ← match json.getObj? with | .ok object => pure object | .error _ => throwError "helper response is not an object"
    let ok := match object.get? "ok" with | some value => value.getBool?.toOption.getD false | none => false
    unless ok do throwError "helper provider rejected request"
    let proposals ← match object.get? "proposals" with
      | some value => match value.getArr? with | .ok values => pure values.toList | .error _ => throwError "helper response has no proposals"
      | none => throwError "helper response has no proposals"
    proposals.take maximum |>.filterMapM fun proposal => do
      let proposalObject := proposal.getObj?.toOption
      let proposition := proposalObject.bind fun o => (o.get? "proposition").bind fun x => x.getStr?.toOption
      let rationale := proposalObject.bind fun o => (o.get? "rationale").bind fun x => x.getStr?.toOption
      return match proposition, rationale with | some p, some r => some (p, r) | _, _ => none
  catch _ => pure []
  helperCache.modify fun cache => (if cache.size >= 1024 then {} else cache).insert key result
  return result

/-- Elaborate provider text into checked cut actions; malformed and unavailable propositions vanish. -/
def helperCutActions (proposals : List (String × String)) : TacticM (List Action) := do
  let target ← (← getMainGoal).getType
  let mut actions := []
  for (text, rationale) in proposals do
    if text.length <= 2000 && !text.contains "sorry" && !text.contains "admit" then
      match Lean.Parser.runParserCategory (← getEnv) `term text with
      | .error _ => pure ()
      | .ok rawTermSyntax => try
        let termSyntax : TSyntax `term := ⟨rawTermSyntax⟩
        let proposition ← Lean.Elab.Term.elabTerm termSyntax none
        if (← isProp proposition) && !(← isDefEq proposition target) then
          let freshName := freshIntroName ((← getLCtx).foldl (init := []) fun ns d => d.userName :: ns)
          let name := mkIdent freshName
          let action : Action := {
            tacticSyntax := ← `(tactic| refine (let $name:ident : $termSyntax:term := ?_; ?_))
            text := s!"helper cut ({text}): {rationale}"
            replayText? := some s!"refine (let {freshName} : {text} := ?_; ?_)"
          }
          if ← candidateWorks action then actions := actions.concat action
      catch _ => pure ()
  return actions

private def helperActions (config : Config) (context : RankContext) : TacticM (List Action) := do
  if config.maxHelperProposals == 0 || config.maxAdmittedHelpers == 0 then return []
  let proposals ← providerHelpers context config.maxHelperProposals config.maxHelperMs
  return (← helperCutActions proposals).take config.maxAdmittedHelpers

/-- Ask the persistent localhost rank broker to order fixed catalogue entries.
Successful rankings are cached for the lifetime of the Lean process so incremental re-elaboration
of an unchanged proof state does not repeat the external call. -/
def rank (context : RankContext) (actions : List Action) : TacticM (List Action) := do
  let entries := actions.zipIdx.map fun (action, index) =>
    Json.mkObj [("id", Json.str s!"A{index + 1}"), ("tactic", Json.str action.text)]
  let request := Json.mkObj [
    ("focused_goal", Json.str context.focusedGoal),
    ("pending_sibling_goals", Json.arr (context.pendingGoals.map Json.str).toArray),
    ("path", Json.arr (context.path.map Json.str).toArray),
    ("actions", Json.arr entries.toArray)
  ]
  let requestText := request.compress
  if let some indices := (← rankCache.get).get? requestText then
    if let some ranked := applyRanking? actions indices then
      return ranked
  let deadline ← IO.monoMsNow.map (· + context.remainingWallMs)
  let indices ← try brokerRanking request deadline catch error =>
    throwError "jev? rank broker is unavailable or failed: {error.toMessageData}"
  let some ranked := applyRanking? actions indices |
    throwError "jev? rank broker returned an invalid action ordering"
  rankCache.modify fun cache =>
    let cache := if cache.size >= 1024 then {} else cache
    cache.insert requestText indices
  return ranked

/-- Capture the current tactic state as the root of a search. -/
def canonicalStateFingerprint (goals : List MVarId) : MetaM String := do
  if goals.isEmpty then return "no goals"
  return String.intercalate "\n-- next goal --\n" (← goals.mapM fun goal =>
    return (← ppGoal goal).pretty)

/-- Capture the current tactic state as the root of a search. -/
def initialNode : TacticM Node := do
  let goals ← getUnsolvedGoals
  let state ← saveState
  let fingerprint ← canonicalStateFingerprint goals
  return { state, goals, path := [], depth := 0, cost := 0, fingerprint }

/-- Restore both Lean's metavariable state and the node's ordered active goals. -/
def Node.restore (node : Node) : TacticM Unit := do
  node.state.restore
  setGoals node.goals

private def expandUpTo (node : Node) (actions : List Action) (maxAttempts : Nat)
    (deadline? : Option Nat := none) : TacticM (List Node × Nat) := do
  let originalGoals ← getGoals
  let original ← saveState
  let mut successors : List Node := []
  let mut attempts := 0
  try
    for action in actions.take maxAttempts do
      let now ← IO.monoMsNow
      if deadline?.any fun deadline => now >= deadline then
        pure ()
      else
        attempts := attempts + 1
        node.restore
        match node.goals with
        | [] => pure ()
        | goal :: siblings =>
          setGoals [goal]
          try
            withMainContext do
              Term.withoutErrToSorry <| withoutRecover do evalTactic action.tacticSyntax
            let descendants ← getUnsolvedGoals
            setGoals (descendants ++ siblings)
            let goals ← getUnsolvedGoals
            let state ← saveState
            let fingerprint ← canonicalStateFingerprint goals
            successors := successors.concat {
              state, goals, path := node.path.concat action, depth := node.depth + 1
              cost := node.cost + action.cost, fingerprint
            }
          catch _ => pure ()
    return (successors, attempts)
  finally
    original.restore
    setGoals originalGoals

/-- Try every action on only the first active goal, then reattach untouched siblings. -/
def expand (node : Node) (actions : List Action) : TacticM (List Node) := do
  return (← expandUpTo node actions actions.length).1

/-- Render a node's focused goal, ordered siblings, and preceding actions for ranking. -/
def rankContext (node : Node) : TacticM RankContext := do
  match node.goals with
  | [] => return { focusedGoal := "no goals", pendingGoals := [], path := node.path.map (·.text) }
  | goal :: siblings =>
    return {
      focusedGoal := (← ppGoal goal).pretty
      pendingGoals := ← siblings.mapM fun sibling => return (← ppGoal sibling).pretty
      path := node.path.map (·.text)
    }

/-- Remove actions which would unfold a definition already unfolded on this search path. -/
def withoutRepeatedUnfolds (path actions : List Action) : List Action :=
  actions.filter fun action =>
    action.unfoldedConstants.all fun name =>
      !path.any fun previous => previous.unfoldedConstants.contains name

/-- Search accounting, including duplicate outcomes suppressed after tactic execution. -/
structure SearchMetrics where
  expandedNodes : Nat := 0
  /-- Number of ranker invocations, including deterministic benchmark rankers. -/
  jevCalls : Nat := 0
  /-- Number of helper-provider requests admitted by the deterministic gate. -/
  helperRequests : Nat := 0
  /-- Number of checked helper-cut actions offered to the scheduler. -/
  helperActions : Nat := 0
  attemptedTransitions : Nat := 0
  admittedSuccessors : Nat := 0
  duplicateSuccessors : Nat := 0
  /-- Repeated generated action families observed before successor execution. -/
  repeatedActionFamilies : Nat := 0
  transpositionEntries : Nat := 0
  elapsedMs : Nat := 0
  deriving Repr

private def familyRepeats (actions : List Action) : Nat :=
  actions.foldl (fun (seen, repeats) action =>
    if seen.contains action.family then (seen, repeats + 1) else (action.family :: seen, repeats)) ([], 0) |>.2

private def bestCost? (table : List (String × Nat)) (fingerprint : String) : Option Nat :=
  (table.find? fun entry => entry.1 == fingerprint).map (·.2)

private def rememberState (limit : Nat) (table : List (String × Nat)) (node : Node) :
    List (String × Nat) :=
  if limit == 0 then [] else
    let table := table.filter fun entry => entry.1 != node.fingerprint
    (node.fingerprint, node.cost) :: table.take (limit - 1)

/-- Deterministic rank-guided depth-first search with bounded canonical-state suppression. -/
def searchWithMetrics (config : Config) (source : ActionSource) (ranker : ActionRanker) :
    TacticM (Option Node × SearchMetrics) := do
  let originalGoals ← getGoals
  let original ← saveState
  let root ← initialNode
  let start ← IO.monoMsNow
  let rec visit (frontier : List Node) (table : List (String × Nat))
      (nodeFuel attempts calls : Nat) (metrics : SearchMetrics) : TacticM (Option Node × SearchMetrics) := do
    match nodeFuel, frontier with
    | _, [] | 0, _ => return (none, metrics)
    | nodeFuel + 1, node :: rest =>
      if (bestCost? table node.fingerprint).any fun cost => cost < node.cost then
        visit rest table nodeFuel attempts calls metrics
      else
        let elapsed ← IO.monoMsNow
        if elapsed >= start + config.maxWallMs then return (none, { metrics with elapsedMs := elapsed - start })
        if node.goals.isEmpty then return (some node, { metrics with elapsedMs := elapsed - start })
        if node.depth >= config.maxDepth || node.cost >= config.maxCost then
          visit rest table nodeFuel attempts calls metrics
        else if attempts >= config.maxHeartbeats then
          return (none, { metrics with elapsedMs := elapsed - start })
        else
          node.restore
          let actions ← withMainContext do
            return withoutRepeatedUnfolds node.path (← source config)
          let deadline := start + config.maxWallMs
          -- Close the entire state locally before paying for a ranking request.
          let closers := (actions.filter (·.family == "closing")).mergeSort
            (fun a b => a.cost <= b.cost)
          let mut directAttempts := 0
          let mut directClosed : Option Node := none
          for action in closers do
            if directClosed.isNone && attempts + directAttempts < config.maxHeartbeats then
              let (successors, used) ← expandUpTo node [action] 1 (some deadline)
              directAttempts := directAttempts + used
              directClosed := successors.find? fun successor =>
                successor.goals.isEmpty && successor.depth <= config.maxDepth &&
                  successor.cost <= config.maxCost
          if let some closed := directClosed then
            let now ← IO.monoMsNow
            return (some closed, { metrics with
              expandedNodes := metrics.expandedNodes + 1
              attemptedTransitions := metrics.attemptedTransitions + directAttempts
              elapsedMs := now - start })
          let now ← IO.monoMsNow
          if attempts + directAttempts >= config.maxHeartbeats || now >= deadline then
            return (none, { metrics with
              attemptedTransitions := metrics.attemptedTransitions + directAttempts
              elapsedMs := now - start })
          let (actions, context, helperRequested, helperActionCount) ← withMainContext do
            let context ← rankContext node
            let helperRequested := config.enableLlmHelpers &&
              helperNeedProbability context >= config.helperProbabilityThreshold
            let helperCuts ← if helperRequested then helperActions config context else pure []
            pure (helperCuts ++ actions, context, helperRequested, helperCuts.length)
          let (actions, calls) ← if calls >= config.maxJevCalls then pure (actions, calls) else do
            let now ← IO.monoMsNow
            let context := { context with remainingWallMs := deadline - now }
            pure (← ranker context actions, calls + 1)
          let (successors, usedAttempts) ← expandUpTo node actions
            (config.maxHeartbeats - attempts - directAttempts) (some deadline)
          let successors := successors.filter fun successor =>
            successor.depth <= config.maxDepth && successor.cost <= config.maxCost
          let mut table := table
          let mut admitted := []
          let mut duplicates := 0
          for successor in successors do
            if (bestCost? table successor.fingerprint).any fun cost => cost <= successor.cost then
              duplicates := duplicates + 1
            else
              table := rememberState config.maxTranspositions table successor
              admitted := admitted.concat successor
          let now ← IO.monoMsNow
          let metrics := { metrics with
            expandedNodes := metrics.expandedNodes + 1
            jevCalls := calls
            helperRequests := metrics.helperRequests + if helperRequested then 1 else 0
            helperActions := metrics.helperActions + helperActionCount
            attemptedTransitions := metrics.attemptedTransitions + directAttempts + usedAttempts
            admittedSuccessors := metrics.admittedSuccessors + admitted.length
            duplicateSuccessors := metrics.duplicateSuccessors + duplicates
            repeatedActionFamilies := metrics.repeatedActionFamilies + familyRepeats actions
            transpositionEntries := table.length
            elapsedMs := now - start }
          if let some closed := admitted.find? fun successor => successor.goals.isEmpty then
            return (some closed, metrics)
          visit (admitted ++ rest) table nodeFuel (attempts + directAttempts + usedAttempts) calls metrics
  try
    visit [root] (([(root.fingerprint, root.cost)] : List (String × Nat)).take config.maxTranspositions)
      config.maxNodes 0 0 {}
  finally
    original.restore
    setGoals originalGoals

/-- Compatibility wrapper for callers that need only the closing route. -/
def searchWith (config : Config) (source : ActionSource) (ranker : ActionRanker) : TacticM (Option Node) :=
  return (← searchWithMetrics config source ranker).1

/-- Replay a path as ordinary tactic source on Lean's current ordered goals. -/
def replay (path : List Action) : TacticM Unit := do
  for action in path do
    evalTactic action.tacticSyntax

private abbrev ProofLine := Nat × String

/-- Render replayable source rather than the possibly prose ranking description. -/
private def Action.replaySource (action : Action) : String :=
  action.replayText?.getD action.text

private partial def renderGoal (depth : Nat) (steps : List (Action × Nat)) :
    TacticM (List ProofLine × List (Action × Nat)) := do
  let (action, childCount) :: rest := steps |
    throwError "cannot format an incomplete Jev proof path"
  if childCount == 0 then
    return ([(depth, action.replaySource)], rest)
  if childCount == 1 then
    let (child, rest) ← renderGoal depth rest
    return ((depth, action.replaySource) :: child, rest)
  let mut rest := rest
  let mut lines : List ProofLine := [(depth, action.replaySource)]
  for _ in [:childCount] do
    let (child, remaining) ← renderGoal (depth + 1) rest
    let (_, first) :: tail := child |
      throwError "cannot format an empty Jev proof branch"
    lines := lines ++ (depth, s!"· {first}") :: tail
    rest := remaining
  return (lines, rest)

private def renderForest (rootCount indent : Nat) (steps : List (Action × Nat)) :
    TacticM String := do
  let mut rest := steps
  let mut lines : List ProofLine := []
  for _ in [:rootCount] do
    let (root, remaining) ← renderGoal (if rootCount == 1 then 0 else 1) rest
    if rootCount == 1 then
      lines := root
    else
      let (_, first) :: tail := root |
        throwError "cannot format an empty Jev proof root"
      lines := lines ++ (0, s!"· {first}") :: tail
    rest := remaining
  unless rest.isEmpty do
    throwError "cannot format a Jev proof path with unused steps"
  let some (_, first) := lines.head? |
    throwError "cannot format an empty Jev proof path"
  return lines.tail.foldl (init := first) fun text line =>
    text ++ "\n" ++ String.ofList (List.replicate (indent + 2 * line.1) ' ') ++ line.2

/-- Replay a closing path and format its branching structure as an indented tactic sequence. -/
def replaySuggestion (path : List Action) (indent : Nat := 0) : TacticM String := do
  let rootCount := (← getUnsolvedGoals).length
  let mut steps : List (Action × Nat) := []
  for action in path do
    let goalsBefore ← getUnsolvedGoals
    let siblingCount := goalsBefore.length - 1
    evalTactic action.tacticSyntax
    let goalsAfter ← getUnsolvedGoals
    if goalsAfter.length < siblingCount then
      throwError "a Jev replay action changed an untouched sibling goal"
    steps := steps.concat (action, goalsAfter.length - siblingCount)
  renderForest rootCount indent steps

private def metricsJson (metrics : SearchMetrics) : Json := Json.mkObj [
  ("expanded_nodes", Json.num metrics.expandedNodes),
  ("jev_calls", Json.num metrics.jevCalls),
  ("helper_requests", Json.num metrics.helperRequests),
  ("helper_actions", Json.num metrics.helperActions),
  ("attempted_transitions", Json.num metrics.attemptedTransitions),
  ("admitted_successors", Json.num metrics.admittedSuccessors),
  ("duplicate_successors", Json.num metrics.duplicateSuccessors),
  ("repeated_action_families", Json.num metrics.repeatedActionFamilies),
  ("transposition_entries", Json.num metrics.transpositionEntries),
  ("elapsed_ms", Json.num metrics.elapsedMs)
]

private def searchConfig : TacticM Config := do
  let helpersEnabled := (← IO.getEnv "JEV_LLM_HELPERS") == some "1"
  let wall := ((← IO.getEnv "JEV_MAX_WALL_MS").bind String.toNat?).getD 10_000
  return { enableLlmHelpers := helpersEnabled, maxWallMs := wall }

/-- Search ordinary locally generated actions and provide a replayable replacement. -/
elab "jev?" : tactic => withMainContext do
  let config ← searchConfig
  match ← searchWith config catalogue rank with
  | none => throwError "jev? found no closing path in its bounded catalogue"
  | some node =>
    let ref ← getRef
    let some range := ref.getRange? |
      throwError "jev? cannot format a suggestion without a source range"
    let (indent, _) := Lean.Meta.Tactic.TryThis.getIndentAndColumn (← getFileMap) range
    let suggestion ← replaySuggestion node.path indent
    Lean.Meta.Tactic.TryThis.addSuggestion ref { suggestion }

/-- Headless benchmark entry point. It emits one machine-readable result after replaying a close. -/
elab "jev_benchmark?" : tactic => withMainContext do
  let config ← searchConfig
  let (result, metrics) ← searchWithMetrics config catalogue rank
  match result with
  | none =>
    logInfo m!"JEVLEAN_BENCHMARK_RESULT {Json.mkObj [
      ("status", Json.str "failed"),
      ("failure", Json.str "bounded search found no closing path"),
      ("proof", Json.null),
      ("metrics", metricsJson metrics),
      ("usage", Json.mkObj [
        ("jev_calls", Json.num metrics.jevCalls),
        ("helper_requests", Json.num metrics.helperRequests),
        ("helper_actions", Json.num metrics.helperActions)
      ])
    ] |>.compress}"
    throwError "jev_benchmark?: bounded search found no closing path"
  | some node =>
    let proof ← replaySuggestion node.path
    logInfo m!"JEVLEAN_BENCHMARK_RESULT {Json.mkObj [
      ("status", Json.str "solved"),
      ("failure", Json.null),
      ("proof", Json.str proof),
      ("metrics", metricsJson metrics),
      ("usage", Json.mkObj [
        ("jev_calls", Json.num metrics.jevCalls),
        ("helper_requests", Json.num metrics.helperRequests),
        ("helper_actions", Json.num metrics.helperActions)
      ])
    ] |>.compress}"

end Search


end JevLean


end
