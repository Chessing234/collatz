# The absolute-bound induction for inverse-tree counts

*Round LXXVI.7–9.  The proof scheme behind `Strategy/TreeTwoThirds`,
`Strategy/TreeSevenTenths`, and the level-12/13 certificates of
`scripts/kl_certify.py`.  Written out at general level so that a certificate
too large for the kernel is still a proof.*

## Objects

`T` is the accelerated map.  A node `a` is *fertile* when odd and prime to
`3`.  For fertile `a` and `i ≥ 0`, the `i`-th fertile child is
`c = fch a i = (2^v a − 1)/3` with `v = fval a i`, so `3c + 1 = 2^v a` and
`T^v c = a`; the fertile children of `a` are exactly the fertile odd `n` with
`T^w n = a` for the first time at an even-only ray, and `(a, i) ↦ fch a i` is
injective (`TreeBranching.fch_inj`).  The class of `c` modulo `3^(k−1)` is
`childRes (a mod 3^k) v` (`ClassChild.child_mod_pow`), and `v` depends on `a`
only modulo `9`.

For a root `a` and a bound `Y`, `S(a, Y)` counts the fertile `n ≤ Y` whose
orbit hits `a` within `Y` steps (`Subtree.S`).  A *root* is fertile, `≥ 5`, and
reaches `1`.  For a root, the subtrees of distinct children are disjoint
(`Subtree.no_common_subtree`: otherwise `a` would be periodic, or a child would
sit on another child's doubling ray), so

    S_rec :  Σ_{i<6} S(c_i, Y_i) ≤ S(a, Y)   whenever each Y_i + 18 ≤ Y.     (R)

## Claims

Fix a level `k`, a number of types `J`, a ratio `λ = P/Q > 1`, and tables
`W_j(r) ∈ ℕ` for `0 ≤ j ≤ J` and fertile `r < 3^k`, and a scale `K`.  The claim
of type `j`, index `y`, root `a` is

    C_j(y, a):   W_j(a mod 3^k) · P^y ≤ Q^y · K · S(a, 3^j · 2^y · a).

Its *bound* is `Y = 3^j 2^y a`.

## The inequalities

For type `j`, class `r`, child slot `i` with valuation `v = fval r i` and
child class `c = childRes r v` (mod `3^(k−1)`), and an option `j' ≤ min(J, j+1)`
with shift `e = ⌊(j + 1 − j') log₂ 3⌋`, define the *term*

    t(j, r, i, j') = λ^{e − v} · min_{r' lifts c} W_{j'}(r').

The certificate asserts, for every type `j` and fertile class `r`,

    W_j(r) ≤ Σ_{i<6} max_{j'} t(j, r, i, j'),                              (C)

cleared to integers by `P^V Q^E` (`V = 24 ≥ v`, `E = max e`), and the base
bound `W_j(r) · P^y ≤ Q^y · K` for `y ≤ 22`.  `scripts/kl_certify.py` checks
(C) and the base bound with Python integers.

## Theorem

*If the certificate holds, then `C_j(y, a)` holds for every type, every index
and every root.*

Proof by strong induction on the bound `Y`.  Let `C_j(y, a)` have bound `Y`
and assume every claim with a smaller bound.  If `y ≤ 22`, `S ≥ 1` (the root
itself) and the base bound give the claim.  Let `y ≥ 23`.  For each child
`c_i` (a root, by `TreeHalf.root_fch`) with valuation `v_i ≤ 18 ≤ y − 5`:

* `3^{j+1} 2^{y−v_i} c_i = 3^j 2^{y−v_i} (2^{v_i} a − 1) = Y − 3^j 2^{y−v_i}`, and
  `3^j 2^{y−v_i} ≥ 2^5 ≥ 18`.  So (R) applies with `Y_i := 3^{j+1} 2^{y−v_i} c_i`.
* For every option `j'`, `3^{j'} 2^{y − v_i + e} c_i ≤ Y_i < Y` because
  `2^e ≤ 3^{j+1−j'}`.  So the claim `C_{j'}(y − v_i + e, c_i)` is available
  (smaller bound — this is the whole point: the index `y − v_i + e` may exceed
  `y`), and `S(c_i, Y_i) ≥ S(c_i, 3^{j'} 2^{y−v_i+e} c_i)` by monotonicity.
  Hence `Q^y K S(c_i, Y_i) ≥ Q^{v_i − e} · W_{j'}(c_i mod 3^k) · P^{y − v_i + e}`
  for every option, and `W_{j'}(c_i mod 3^k) ≥ min over the lifts of the
  child's class mod `3^(k−1)`, which is what the certificate knows.
* Summing (R) against (C) for `r = a mod 3^k`, multiplied by `P^{y}` and the
  clearing factor, gives `C_j(y, a)`.  (`TreeTwoThirds.stepF`/`stepH` are this
  computation for `J = 1`.)

The induction is well founded because every bound used is strictly smaller.
No restriction to "retarded" terms is needed — which is exactly the
restriction Krasikov–Lagarias (2003, §3) remove by their back-substitution
theorem for the linear-program family `L_k^{NT}`.

## Consequence

From `C_0(y, 5)`: `S(5, 2^y · 5) ≥ W_0(5) λ^y / K`, and every element counted
reaches `1` within `2^y · 5 + 4` steps, so with `10 · 2^y ≤ N < 20 · 2^y`,

    #{ n ≤ N : n reaches 1 }  ≥  (W_0(5)/K) · λ^y  ≥  c · N^{log₂ λ}.

## What is kernel-checked and what is not

Levels `k ≤ 6` with `J = 1` are kernel-checked (`TreeHalf`, `TreeTwoThirds`,
`TreeSevenTenths`; certificates closed by `decide`).  Levels `12` and `13`
with `J = 11` have `12 · 2 · 3^{k−1}` inequalities — millions — and are
checked by `scripts/kl_certify.py` with exact integer arithmetic; the theorem
above is the paper proof they rest on.  The continuous system (all real
scales, `scripts/kl_levels.py`) is the Krasikov–Lagarias system itself; it
reproduces their `0.84` at level `11` (`0.8418` here).
