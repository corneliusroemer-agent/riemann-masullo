import Lean
open Lean

/-!
Dump, from a built library, what a split of some modules needs.

    lake env lean --run SplitDeps.lean <split modules, comma-separated> <all modules...>

Output lines (tab-separated):
- `DEF  const  module  line`: every constant of a split module, with the source line of the declaration
  it belongs to (auxiliary constants take the line of their parent).
- `USE  module  line  const  constmodule  private`: for constants of a split module, every constant
  their statement or body uses (`line` is that of the user).
- `EXT  module  const  constmodule`: for constants of other modules, each use of a constant of a
  split module.
-/

partial def lineOf (env : Environment) (n : Name) : IO (Option Nat) := do
  let (r, _) ← (findDeclarationRanges? n : CoreM _).toIO { fileName := "", fileMap := default } { env }
  match r with
  | some r => return some r.range.pos.line
  | _ =>
  -- `_private.<module>.0.<name>`: the ranges may be stored under the user name
  if let some u := privateToUserName? n then
    if let some l ← lineOf env u then return some l
  match n with
    | .str p _ | .num p _ => if p.isAnonymous then return none else lineOf env p
    | .anonymous => return none

def main (args : List String) : IO UInt32 := do
  let split := (args.head!.splitOn ",").map (·.toName)
  let modules := (args.drop 1).toArray.map (·.toName)
  initSearchPath (← findSysroot)
  let env ← importModules (modules.map fun m => { module := m, importAll := true }) {}
    (trustLevel := 1024)
  let modOf (n : Name) : Name :=
    match env.getModuleIdxFor? n with
    | some i => env.header.moduleNames[i.toNat]!
    | none => .anonymous
  for (n, c) in env.constants.toList do
    let m := modOf n
    unless (`RiemannMasullo).isPrefixOf m do continue
    let body : Option Expr := match c with
      | .thmInfo t => some t.value | .defnInfo d => some d.value | .opaqueInfo o => some o.value
      | _ => none
    let used := c.type.getUsedConstants ++ (body.map (·.getUsedConstants)).getD #[]
    if split.contains m then
      let line := (← lineOf env n).getD 0
      IO.println s!"DEF\t{n}\t{m}\t{line}"
      let mut seen : NameSet := {}
      for u in used do
        if seen.contains u then continue
        seen := seen.insert u
        let um := modOf u
        if um != m && (`RiemannMasullo).isPrefixOf um then
          IO.println s!"USE\t{m}\t{line}\t{u}\t{um}\t{isPrivateName u}"
        else if um == m then
          IO.println s!"USE\t{m}\t{line}\t{u}\t{um}\t{isPrivateName u}"
    else
      let mut seen : NameSet := {}
      for u in used do
        if seen.contains u then continue
        seen := seen.insert u
        let um := modOf u
        if split.contains um then
          IO.println s!"EXT\t{m}\t{n}\t{u}\t{um}"
  return 0
