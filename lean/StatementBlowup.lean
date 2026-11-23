/-!
Scratch: for chosen statements, which subterms account for their tree size. Each distinct subterm
gets its multiplicity (how many times it occurs when the statement is written out as a tree).
Subterms of moderate size with a large multiplicity are what a name would shrink.
Run with `scripts/scan_statements.sh lean/StatementBlowup.lean` after listing the declarations in
`targets`.
-/

open Lean Meta

/-- Children of a node, in the order a tree walk visits them. -/
def kids : Expr → List Expr
  | .app f a => [f, a]
  | .mdata _ b => [b]
  | .proj _ _ b => [b]
  | .letE _ t v b _ => [t, v, b]
  | .lam _ d b _ => [d, b]
  | .forallE _ d b _ => [d, b]
  | _ => []

/-- Distinct subterms in post-order, and the tree size of each. -/
partial def order (e : Expr) : StateM (Std.HashMap Expr Nat × Array Expr) Nat := do
  if let some n := (← get).1[e]? then return n
  let mut n := 1
  for k in kids e do n := n + (← order k)
  modify fun (m, a) => (m.insert e n, a.push e)
  return n

def blowup (t : Expr) (lo hi : Nat) : IO Unit := do
  let (total, (sizes, post)) := (order t).run ({}, #[]) |>.run
  -- multiplicities, parents before children: reverse post-order
  let mut mult : Std.HashMap Expr Nat := ({} : Std.HashMap Expr Nat).insert t 1
  for e in post.reverse do
    let me := mult.getD e 0
    for k in kids e do
      mult := mult.insert k (mult.getD k 0 + me)
  let mut rows : Array (Nat × Nat × Nat × Nat × String) := #[]
  for e in post do
    let s := sizes.getD e 0
    if lo ≤ s && s ≤ hi then
      let m := mult.getD e 0
      rows := rows.push (m * s, m, s, ← e.numObjs,
        s!"{e.getAppFn.constName?.getD `_}/{e.getAppNumArgs}")
  let sorted := rows.qsort (fun a b => a.1 > b.1)
  IO.println s!"  total tree {total}, distinct {← t.numObjs}"
  for (share, m, s, d, h) in sorted.toList.take 12 do
    IO.println s!"  share {share} = {m} × tree {s} (distinct {d}): {h}"

#eval show CoreM Unit from do
  let env ← getEnv
  let targets := [`RiemannMasullo.sLocalThetaSobolev_isotypeDecomposition,
    `RiemannMasullo.primeOrbitalSobolevConvolution_traceNorm_continuous,
    `RiemannMasullo.sLocalDecayFourier_eq_weightedFourier,
    `RiemannMasullo.orbitalSobolevPairing_pullback]
  for n in targets do
    let some ci := env.find? n | IO.println s!"{n}: not found"
    IO.println s!"{n}"
    blowup ci.type 500 60000
