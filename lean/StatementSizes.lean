/-!
Scratch scan: size of every public statement of the library, as distinct nodes and as a tree.
Goals start from statements, and `kabstract` (`rw`, `generalize`, `obtain`/`cases` on a term)
walks the goal as a tree, so a large tree/distinct ratio marks declarations whose proofs pay
for it. Run with `scripts/scan_statements.sh lean/StatementSizes.lean` after `lake build`. Scratch only.

Output: one line per declaration with tree size ≥ 10⁶, largest first, then the subterm heads
that recur most often among mid-sized subterms (tree size 2,000–50,000) of those statements:
these are the candidates for a name.
-/

open Lean Meta

partial def treeSizes (e : Expr) : StateM (Std.HashMap Expr Nat) Nat := do
  if let some n := (← get)[e]? then return n
  let n ← match e with
    | .app f a => pure (1 + (← treeSizes f) + (← treeSizes a))
    | .mdata _ b => pure (1 + (← treeSizes b))
    | .proj _ _ b => pure (1 + (← treeSizes b))
    | .letE _ t v b _ => pure (1 + (← treeSizes t) + (← treeSizes v) + (← treeSizes b))
    | .lam _ d b _ => pure (1 + (← treeSizes d) + (← treeSizes b))
    | .forallE _ d b _ => pure (1 + (← treeSizes d) + (← treeSizes b))
    | _ => pure 1
  modify (·.insert e n)
  return n

#eval show CoreM Unit from do
  let env ← getEnv
  let mut rows : Array (Nat × Nat × Name × Name) := #[]
  let mut heads : Std.HashMap String (Nat × Nat) := {}
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`RiemannMasullo).isPrefixOf mod do continue
    if n.isInternal then continue
    let t := ci.type
    let (tree, m) := (treeSizes t).run {} |>.run
    if tree < 1000000 then continue
    let dag ← (t.numObjs : IO Nat)
    rows := rows.push (tree, dag, n, mod)
    for (s, k) in m.toList do
      if 2000 ≤ k && k ≤ 50000 then
        let h := s!"{s.getAppFn.constName?.getD `_}/{s.getAppNumArgs}"
        let (c, mx) := heads.getD h (0, 0)
        heads := heads.insert h (c + 1, max mx k)
  let sorted := rows.qsort (fun a b => a.1 > b.1)
  IO.println s!"{sorted.size} statements with tree size ≥ 10^6"
  for (tree, dag, n, mod) in sorted.toList.take 60 do
    IO.println s!"STMT {tree} {dag} {n} {mod}"
  let hs := heads.toArray.qsort (fun a b => a.2.1 > b.2.1)
  for (h, c, mx) in hs.toList.take 40 do
    IO.println s!"HEAD {c} {mx} {h}"
