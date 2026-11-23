/-! Scratch: print the subterm of a statement with the largest multiplicity × tree size among
those whose tree size lies in [lo, hi] and whose head is the given constant. Run with
`scripts/scan_statements.sh lean/ShowSubterm.lean`. -/

open Lean Meta

def kids' : Expr → List Expr
  | .app f a => [f, a]
  | .mdata _ b => [b]
  | .proj _ _ b => [b]
  | .letE _ t v b _ => [t, v, b]
  | .lam _ d b _ => [d, b]
  | .forallE _ d b _ => [d, b]
  | _ => []

partial def order' (e : Expr) : StateM (Std.HashMap Expr Nat × Array Expr) Nat := do
  if let some n := (← get).1[e]? then return n
  let mut n := 1
  for k in kids' e do n := n + (← order' k)
  modify fun (m, a) => (m.insert e n, a.push e)
  return n

def showTop (n : Name) (head : Name) (lo hi : Nat) : MetaM Unit := do
  let some ci := (← getEnv).find? n | IO.println s!"{n}: not found"
  let t := ci.type
  let (_, (sizes, post)) := (order' t).run ({}, #[]) |>.run
  let mut mult : Std.HashMap Expr Nat := ({} : Std.HashMap Expr Nat).insert t 1
  for e in post.reverse do
    let me := mult.getD e 0
    for k in kids' e do mult := mult.insert k (mult.getD k 0 + me)
  let mut best : Option (Nat × Expr) := none
  for e in post do
    let s := sizes.getD e 0
    if lo ≤ s && s ≤ hi && e.getAppFn.constName? == some head then
      let sh := mult.getD e 0 * s
      if best.all (·.1 < sh) then best := some (sh, e)
  match best with
  | none => IO.println s!"{n}: no {head} subterm in range"
  | some (_, e) =>
    let placeholders := (List.range e.looseBVarRange).toArray.map
      fun i => mkConst (Name.mkSimple s!"bv{i}")
    let closed := e.instantiate placeholders
    let fmt ← withOptions (fun o => (o.setBool `pp.explicit false).insert
      `pp.deepTerms.threshold (.ofNat 8)) (ppExpr closed)
    IO.println s!"{n}, {head}:\n{(toString fmt).take 1500}"

#eval show MetaM Unit from do
  showTop `RiemannMasullo.sLocalThetaSobolev_isotypeDecomposition `Subgroup.map 10000 30000
  showTop `RiemannMasullo.primeOrbitalSobolevConvolution_traceNorm_continuous
    `MeasureTheory.Measure.withDensity 10000 20000
