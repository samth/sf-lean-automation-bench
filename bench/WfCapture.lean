/-
Experiment tactic: run `waterfall` (default search mode and options) through
`waterfall.Observe.capture` and print one JSON line summarizing where its
attempts went.  It closes the goal only when the search succeeded, exactly as
`waterfall` would; otherwise it fails.
-/
module

public meta import waterfall
public meta import waterfall.Observe

public meta section

open Lean Elab Tactic

namespace WfCapture

private def groupName (g : waterfall.Group) : String := (toJson g).compress

/-- One action-phase row as JSON: its order, group, ordinal, label and outcome. -/
private def actionRow (r : waterfall.Observe.Row) : Option Json := do
  guard (r.span.phase == .action)
  let a ← r.span.action
  return Json.mkObj [("id", toJson r.id), ("parent", toJson r.parent), ("group", toJson a.group),
    ("index", toJson a.index), ("label", toJson r.span.label), ("depth", toJson r.span.depth),
    ("strength", toJson r.span.strength), ("ok", toJson (r.outcome.success.getD false))]

elab "wf_capture" : tactic => do
  let options : waterfall.Options := {}
  let rules : Array (TSyntax `term) := #[]
  let report ← waterfall.Observe.capture options.toConfig rules "sf" (costs := true) (plans := true)
    (hooks := options.mode.hooks rules)
  let actions := report.rows.filterMap actionRow
  let steps := match report.plan with
    | some plan => plan.steps.map fun s => Json.mkObj [("group", toJson s.action.group),
        ("index", toJson s.action.index), ("label", toJson s.label), ("strength", toJson s.strength),
        ("remaining", toJson s.remaining), ("children", toJson s.children)]
    | none => #[]
  -- Parent chains let the analysis attribute attempts to search nodes.
  let parents := report.rows.map fun r => Json.mkObj [("id", toJson r.id), ("parent", toJson r.parent),
    ("phase", toJson r.span.phase), ("depth", toJson r.span.depth), ("strength", toJson r.span.strength)]
  logInfo m!"WFCAPTURE {(Json.mkObj [("success", toJson report.success),
    ("error", toJson report.error), ("actions", Json.arr actions), ("steps", Json.arr steps),
    ("rows", Json.arr parents)]).compress}"
  unless report.success do throwError "wf_capture: {report.error.getD "failed"}"

end WfCapture
