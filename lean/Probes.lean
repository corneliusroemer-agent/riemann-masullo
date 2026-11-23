/-
Probe tactics for measuring goal size and `kabstract` cost. Scratch use only: paste this block
into a scratch copy (see `scripts/scratch_copy.py`) before the declaration you want to look at,
and call the tactics inside its proof. Do not commit it to the library; AGENTS.md forbids new
elaborators there.

* `probe_size e`   — distinct nodes (`numObjs`) and tree size (`sizeWithoutSharing`) of the goal,
                     and how many subterms `kabstract` would test against `e` (same head symbol
                     and arity). A tree size far above the distinct size is what makes `rw`,
                     `obtain … := <term>`, `cases <term>` and `generalize` slow: `kabstract` walks
                     the goal as a tree, without a cache.
* `probe_gen e`    — times what `generalize` does for `obtain … := e`: `kabstract` of `e` in the
                     goal, then `isTypeCorrect` of the result.
* `probe_blowup`   — lists the subterms of the goal whose tree size lies in [lo, hi], largest
                     first, with head constant and distinct size. Run it with a low window
                     (300–5000) to find the repeated base term, and a high one (> 10⁵) to see
                     where the copies nest.
-/

open Lean Meta Elab Tactic in
elab "probe_size " t:term : tactic => withMainContext do
  let e ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let p ← instantiateMVars e
  let target ← instantiateMVars (← getMainTarget)
  let dag ← target.numObjs
  let tree := target.sizeWithoutSharing
  let hp := p.toHeadIndex
  let np := p.headNumArgs
  let rec walk (e : Expr) : StateM Nat Unit := do
    if !e.hasLooseBVars && e.toHeadIndex == hp && e.headNumArgs == np then
      modify (· + 1)
    match e with
    | .app f a => walk f; walk a
    | .mdata _ b => walk b
    | .proj _ _ b => walk b
    | .letE _ t v b _ => walk t; walk v; walk b
    | .lam _ d b _ => walk d; walk b
    | .forallE _ d b _ => walk d; walk b
    | _ => pure ()
  -- Walking the tree takes as long as kabstract does; skip it when the tree is huge.
  let cand := if tree ≤ 50000000 then some ((walk target).run 0).2 else none
  logInfo m!"goal: {dag} distinct nodes, {tree} as a tree, depth {target.approxDepth}; \
    kabstract candidates for the pattern: {cand}"

open Lean Meta Elab Tactic in
elab "probe_gen " t:term : tactic => withMainContext do
  let e ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let target ← instantiateMVars (← getMainTarget)
  let t0 ← IO.monoMsNow
  let abs ← withTransparency .instances <| kabstract target e
  let t1 ← IO.monoMsNow
  let ok ← isTypeCorrect (Lean.mkForall `x .default (← inferType e) abs)
  let t2 ← IO.monoMsNow
  logInfo m!"kabstract {t1 - t0} ms (found: {abs.hasLooseBVars}); \
    isTypeCorrect {t2 - t1} ms (ok: {ok})"

open Lean Meta Elab Tactic in
elab "probe_blowup " lo:num hi:num : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let rec sizes (e : Expr) : StateM (Std.HashMap Expr Nat) Nat := do
    if let some n := (← get)[e]? then return n
    let n ← match e with
      | .app f a => pure (1 + (← sizes f) + (← sizes a))
      | .mdata _ b => pure (1 + (← sizes b))
      | .proj _ _ b => pure (1 + (← sizes b))
      | .letE _ t v b _ => pure (1 + (← sizes t) + (← sizes v) + (← sizes b))
      | .lam _ d b _ => pure (1 + (← sizes d) + (← sizes b))
      | .forallE _ d b _ => pure (1 + (← sizes d) + (← sizes b))
      | _ => pure 1
    modify (·.insert e n)
    return n
  let m : Std.HashMap Expr Nat := (Id.run ((sizes target).run {})).2
  let mut rows : Array (Nat × Nat × String) := #[]
  for (e, n) in m.toList do
    if lo.getNat ≤ n && n ≤ hi.getNat then
      rows := rows.push (n, ← e.numObjs,
        s!"{e.getAppFn.constName?.getD `_} ({e.getAppNumArgs} args)")
  let sorted := rows.qsort (fun a b => a.1 > b.1)
  for (n, dag, h) in sorted.toList.take 25 do
    logInfo m!"tree {n}, distinct {dag}: {h}"
