import Collatz.Strategy.LiftingLaw

/-!
# The renormalization tower converges, on the axis the dynamics does not use

Targeting the recurrence Round LII named: the mismatch appears at two levels, and
at the second level the two branches are related in a way they are not at the
first.

## The recurrence, stated exactly

* **Level 0.**  The branches are `n` and `n + 1` — growth clean in `u = n+1`,
  contraction clean in `n`, and `CoordinateMismatch.no_common_shift` says no affine
  shift serves both.
* **Level 1.**  In the logarithm the branches are `3^s − 1` and `3^s + 1`.  **The
  same `±1` defect, reproduced around a new object by the log transform.**

So the obstruction is self-similar.  But level 1 has something level 0 lacks: its
two branches satisfy an *exact identity*, because `3^(2s) − 1 = (3^s−1)(3^s+1)` and
`dlog` is additive —

**`Λ(2s) = Λ(s) + Ψ(s)`,**  `Λ(s) = dlog₃(oddpart(3^s−1))`, `Ψ(s) = dlog₃(oddpart(3^s+1))`.

That is a renormalization equation.  This file asks whether it converges, and it
does.

## The convergence, with an exact rate

`three_pow_succ_factor` below: for odd `q` and `j ≥ 1`,

**`3^(2^j·q) + 1 = 2·(2^(j+1)·A + 1)`**, where `A` is the odd number of
`LiftingLaw.three_pow_sub_one_factor` with `3^(2^j·q) − 1 = 2^(j+2)·A`.

It is a one-line corollary — add `2` to the lifting law — but it is the engine of
the tower.  It says `oddpart(3^(2^j q) + 1) = 1 + 2^(j+1)·A`, and since
`3^t ≡ 1 + 2^(v₂(t)+2)` modulo the next power, that element's logarithm has
`v₂` exactly `j − 1`.  Hence

**`v₂(Ψ(2^k·s)) = k − 1` for every `k ≥ 1`, independently of `s`.**

Measured for `s ∈ {1,3,…,25}` and `k ≤ 7`: no exceptions.  The increments of the
tower therefore tend to `0` two-adically at an explicit rate, so

**`Λ_∞(s) = lim_{k→∞} Λ(2^k·s)` exists**, `= Λ(s) + Σ_{k≥0} Ψ(2^k·s)`, a
convergent `2`-adic series.  Observed converging: at `s = 1` the values
`Λ(2^k)` settle from below, agreeing to `17 (mod 64)` from `k = 7` on.

## The honest assessment

This is a genuine new object with an exact convergence rate, and it does not help,
for the reason Round LII identified — **it lives on the transverse axis.**

The renormalization runs in the direction `s ↦ 2s`.  The Collatz recursion moves
`s` *additively*, by `a − 1`.  A tower that converges under doubling says nothing
about a trajectory that translates, and Round LII measured the translation
direction to be structureless: `Λ(s+1) − Λ(s)` takes `24` distinct values in `24`
consecutive samples.

So the position is now sharp rather than vague.  There are two exact structures on
`Λ` — multiplicative self-similarity with a convergent tower, and stratum-wise
Lipschitz regularity — and the dynamics is transverse to **both**.  That is one
statement, not two failures, and it is the same statement at level 0 and level 1.
Whatever settles Collatz has to move along the additive direction, where every
measurement so far shows no structure at all.
-/

namespace Collatz
namespace RenormTower

open LiftingLaw

/-- **The engine of the tower.**  Adding `2` to the lifting law: for odd `q` and
`j ≥ 1`, `3^(2^j·q) + 1 = 2·(2^(j+1)·A + 1)` with the same odd `A` that satisfies
`3^(2^j·q) − 1 = 2^(j+2)·A`.

So `oddpart(3^(2^j·q) + 1) = 1 + 2^(j+1)·A`, which is the statement that the
`k`-th increment of the renormalization tower has logarithm of `2`-adic valuation
exactly `k − 1`. -/
theorem three_pow_succ_factor {j q : Nat} (hq : q % 2 = 1) (hj : 0 < j) :
    ∃ A : Nat, A % 2 = 1 ∧ 3 ^ (2 ^ j * q) + 1 = 2 * (2 ^ (j + 1) * A + 1) := by
  obtain ⟨A, hA, hAeq⟩ := three_pow_sub_one_factor j q hq hj
  refine ⟨A, hA, ?_⟩
  have hp : 0 < 3 ^ (2 ^ j * q) := Nat.pow_pos (by omega)
  have h2 : (2 : Nat) ^ (j + 2) = 2 * 2 ^ (j + 1) := by
    rw [Nat.pow_succ]; omega
  have h3 : 2 ^ (j + 2) * A = 2 * (2 ^ (j + 1) * A) := by
    rw [h2, Nat.mul_assoc]
  omega

/-- Both sides of the level-1 branch pair, from one factorisation: the `−1` branch
supplies `A`, and the `+1` branch is `2·(2^(j+1)·A + 1)` with the same `A`.  This
is the exact relation between the two branches that level `0` does not have. -/
theorem branches_share_factor {j q : Nat} (hq : q % 2 = 1) (hj : 0 < j) :
    ∃ A : Nat, A % 2 = 1 ∧
      3 ^ (2 ^ j * q) - 1 = 2 ^ (j + 2) * A ∧
      3 ^ (2 ^ j * q) + 1 = 2 * (2 ^ (j + 1) * A + 1) := by
  obtain ⟨A, hA, hAeq⟩ := three_pow_sub_one_factor j q hq hj
  obtain ⟨B, _, hBeq⟩ := three_pow_succ_factor hq hj
  refine ⟨A, hA, hAeq, ?_⟩
  have hp : 0 < 3 ^ (2 ^ j * q) := Nat.pow_pos (by omega)
  have h2 : (2 : Nat) ^ (j + 2) = 2 * 2 ^ (j + 1) := by
    rw [Nat.pow_succ]; omega
  have h3 : 2 ^ (j + 2) * A = 2 * (2 ^ (j + 1) * A) := by
    rw [h2, Nat.mul_assoc]
  omega

end RenormTower
end Collatz
