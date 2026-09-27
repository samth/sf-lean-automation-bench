/-
Print, for every `theorem` and `example` command in a Lean file, the UTF-8 byte
offsets of the command start, the proof (`declVal`) start, and the command end.
Run with `lake env lean --run Positions.lean <file>` inside a context workspace.
-/
import Lean

open Lean Elab

unsafe def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: Positions <file>"; return 2
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let input ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext input path
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx (trustLevel := 1024)
    (mainModule := `SFBenchPositionsMain)
  let commandState := Command.mkState env messages {}
  let state ← IO.processCommands inputCtx parserState commandState
  IO.eprintln s!"commands: {state.commands.size}"
  for msg in state.commandState.messages.toList do
    if msg.severity == .error then IO.eprintln (← msg.toString)
  for cmd in state.commands do
    unless cmd.getKind == ``Lean.Parser.Command.declaration do continue
    let decl := cmd[1]
    let (kind, name, val) :=
      if decl.getKind == ``Lean.Parser.Command.theorem then
        ("theorem", decl[1][0].getId.toString, decl[3])
      else if decl.getKind == ``Lean.Parser.Command.example then
        ("example", "", decl[2])
      else ("", "", Syntax.missing)
    if kind.isEmpty then continue
    let some start := cmd.getPos? | continue
    let some valStart := val.getPos? | continue
    let some stop := cmd.getTailPos? | continue
    IO.println <| Json.compress <| Json.mkObj [
      ("kind", Json.str kind), ("name", Json.str name),
      ("start", Json.num start.byteIdx), ("proof", Json.num valStart.byteIdx),
      ("end", Json.num stop.byteIdx)]
  return 0
