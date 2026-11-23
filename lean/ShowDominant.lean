/-! Scratch: pretty-print the dominant subterm (largest multiplicity × tree size, size in
[lo, hi]) of chosen statements, whatever its head. -/

open Lean Meta

def kidsD : Expr → List Expr
  | .app f a => [f, a]
  | .mdata _ b => [b]
  | .proj _ _ b => [b]
  | .letE _ t v b _ => [t, v, b]
  | .lam _ d b _ => [d, b]
  | .forallE _ d b _ => [d, b]
  | _ => []

partial def orderD (e : Expr) : StateM (Std.HashMap Expr Nat × Array Expr) Nat := do
  if let some n := (← get).1[e]? then return n
  let mut n := 1
  for k in kidsD e do n := n + (← orderD k)
  modify fun (m, a) => (m.insert e n, a.push e)
  return n

def showDominant (n : Name) (lo hi : Nat) : MetaM Unit := do
  let some ci := (← getEnv).find? n | IO.println s!"{n}: not found"
  let t := ci.type
  let (_, (sizes, post)) := (orderD t).run ({}, #[]) |>.run
  let mut mult : Std.HashMap Expr Nat := ({} : Std.HashMap Expr Nat).insert t 1
  for e in post.reverse do
    let me := mult.getD e 0
    for k in kidsD e do mult := mult.insert k (mult.getD k 0 + me)
  let mut best : Option (Nat × Nat × Nat × Expr) := none
  for e in post do
    let s := sizes.getD e 0
    if lo ≤ s && s ≤ hi then
      let m := mult.getD e 0
      if best.all (·.1 < m * s) then best := some (m * s, m, s, e)
  match best with
  | none => IO.println s!"{n}: nothing in range"
  | some (_, m, s, e) =>
    let placeholders := (List.range e.looseBVarRange).toArray.map
      fun i => mkConst (Name.mkSimple s!"bv{i}")
    let closed := e.instantiate placeholders
    let fmt ← withOptions (fun o => (o.setBool `pp.explicit false).insert
      `pp.deepTerms.threshold (.ofNat 6)) (ppExpr closed)
    IO.println s!"===== {n}: {m} × {s} nodes\n{(toString fmt).take 1800}\n"

#eval show MetaM Unit from do
  showDominant `RiemannMasullo.absolutePWCondensation_traceNorm_tendsto 50000 100000
  showDominant `RiemannMasullo.sLocalThetaSobolev_isotypeDecomposition 60000 80000
  showDominant `RiemannMasullo.primeOrbitalSobolevConvolution_traceNorm_continuous 6000 7000
  showDominant `RiemannMasullo.sLocalThetaIsotypeSum_inherited_properties 20000 30000
  showDominant `RiemannMasullo.sLocalDecayFourier_eq_weightedFourier 1000 2000
