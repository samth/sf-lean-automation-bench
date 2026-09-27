/-
Baseline tactics for the sf-in-lean comparison.  They are Lean analogues of the
non-Jev rows in Koppel's table:

* `sf_auto` — "automation only, no hints": close the goal with one standard
  decision procedure, without case analysis or induction.
* `sf_induct` — "every induction/case split": try `sf_auto`, then every
  single structural induction or case split on a local, closing every
  resulting goal with `sf_auto`.
-/
module

public meta import Lean

public meta section


namespace SFBench

open Lean Elab Tactic Meta

/-- One-shot automation without induction. -/
macro "sf_auto" : tactic =>
  `(tactic| first
      | rfl
      | (intros; simp_all; done)
      | grind
      | (intros; omega)
      | (intros; decide))

private def inductiveLocal (decl : LocalDecl) : MetaM Bool := do
  if decl.isImplementationDetail then return false
  let type ← whnf decl.type
  match type.getAppFn with
  | .const name _ => isInductive name
  | _ => return false

/-- Try each single induction or case split on a local, then `sf_auto` on every goal. -/
elab "sf_induct" : tactic => do
  let closeAll : TacticM Unit := evalTactic (← `(tactic| all_goals sf_auto))
  let saved ← saveState
  try
    evalTactic (← `(tactic| sf_auto))
    return
  catch _ => saved.restore
  evalTactic (← `(tactic| intros))
  let afterIntros ← saveState
  let locals ← withMainContext do
    let lctx ← getLCtx
    lctx.foldlM (init := #[]) fun acc decl => do
      if ← inductiveLocal decl then return acc.push decl.fvarId else return acc
  for fvar in locals do
    for useCases in [false, true] do
      afterIntros.restore
      try
        withMainContext do
          let term ← Term.exprToSyntax (mkFVar fvar)
          if useCases then evalTactic (← `(tactic| cases $term:term))
          else evalTactic (← `(tactic| induction $term:term))
        closeAll
        if (← getUnsolvedGoals).isEmpty then return
      catch _ => pure ()
  afterIntros.restore
  throwError "sf_induct: no single induction or case split closed the goal"

end SFBench


end
