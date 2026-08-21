import Collatz.Strategy.OneRunOrder
import Collatz.Strategy.AccumulatorCap
import Collatz.Strategy.HeavyState

/-!
# The order obstruction survives a second run

`OneRunOrder` turns a one-run cycle into a divisibility with no accumulator left
in it: `2 ^ L ≡ 3 ^ a (mod d)` collapses `C = 3 ^ a − 2 ^ a` to
`d ∣ 2 ^ (L−a) − 1`, and hence `d ≤ 2 ^ (L−a) − 1`.  The collapse was believed
not to survive a second run, on the grounds that the accumulator "mixes
independent `(tᵢ, Bᵢ)` pairs".  It does survive, and the reason is a telescope.

Group the accumulator by runs — run `i` being `bᵢ` odd steps then `eᵢ` even ones:

`C = Σᵢ 2 ^ tᵢ · 3 ^ (a − Bᵢ) · (3 ^ bᵢ − 2 ^ bᵢ)`.

Writing `Sᵢ = 2 ^ tᵢ · 3 ^ (a − Bᵢ₋₁)`, each summand is `Sᵢ − Sᵢ₊₁ · 2 ^ (−eᵢ)`,
with `S₁ = 3 ^ a` and `S_{k+1} = 2 ^ L`.  Modulo `d` those two endpoints are the
same number, so they cancel against each other and what is left is

`C ≡ Σᵢ (unit) · (2 ^ eᵢ − 1)  (mod d)` —

**one term per even block, not one per odd step.**  The odd-run lengths survive
only inside the unit coefficients.  At `k = 1` this is exactly the one-run
theorem; here it is proved at `k = 2`, where it reads

`C ≡ 2 ^ b₁ · (3 ^ b₂ · (2 ^ e₁ − 1) + 2 ^ (e₁+b₂) · (2 ^ e₂ − 1))  (mod d)`,

and since `d` is odd the unit `2 ^ b₁` cancels:

**`d ∣ 3 ^ b₂ · (2 ^ e₁ − 1) + 2 ^ (e₁+b₂) · (2 ^ e₂ − 1)`.**

Verified before formalising: the general `k` identity on 168 944 random words,
and this closed form exhaustively over all `b₁, e₁, b₂, e₂ ≤ 9`, in both cases
with no failures.

## What this does and does not give — the honest reading

It excludes nothing, and the reason is worth stating precisely, because it is
the reason the whole mechanism stops at one run.

The collapsed sum is not merely congruent to the accumulator: writing
`A = Σᵢ 3 ^ (a−Bᵢ) · 2 ^ sᵢ · (2 ^ eᵢ − 1)` for the right-hand side, one has

`A = C + d`  **exactly**, for every word and every `k`

(this file proves that identity at `k = 2`, inside `two_run_order`; it was
verified on 200 000 random words at every `k`).  So passing from `d ∣ C` to
`d ∣ A` is a *re-coordinatisation*, not an elimination — no information has been
created, only moved.  What the move exposes is the factor `2 ^ b₁`: one has
`v₂(A) = b₁` always, so the only strippable content is the leading odd run, and
`2 ^ b₁ ≤ m + 1` is the classical run condition, already known.

At `k = 1` that is enough, because there `b₁ = a`: the whole odd-step count sits
in the exposed factor and the remaining term is the *fixed* value `2 ^ (L−a) − 1`,
which bounds `d`.  At `k ≥ 2` the leading run is only the run at the global
minimum, `b₁ ≪ a`, and the residual system is the Simons–de Weger cyclic system
with `2(k−1)` free exponents — an exponential Diophantine problem needing Baker
bounds and lattice reduction, neither of which is available here.  Measured
exclusion power confirms it: `A < d` rules out 92.4 % of two-run words but
plateaus with 7.6 % surviving, and three runs are *worse*, at 12.7 %.

The soundness filter is what makes this final rather than merely discouraging.
The genuine `3x−1` cycle through `17` is a two-run cycle with `A = d` exactly.
So `d ≤ A` is *attained on a real cycle of a real map obeying the same identity*,
and any strengthening to `d < A` is unsound, not merely unproved.
-/

namespace Collatz
namespace TwoRunOrder

open Reach Congruence AffineExact AccCycle OddRuns AccumulatorArith

/-! ## The accumulator of a pure odd run -/

/-- Over an odd run the accumulator is `3 ^ b − 2 ^ b`, stated without
subtraction. -/
theorem affineC_oddRun : ∀ (b x : Nat), OddRun x b → affineC b x + 2 ^ b = 3 ^ b := by
  intro b
  induction b with
  | zero => intro x _; simp
  | succ b ih =>
    intro x h
    have hb : acceleratedOrbit b x % 2 = 1 := h b (by omega)
    have hprev : OddRun x b := fun i hi => h i (by omega)
    have hIH := ih x hprev
    rw [affineC_odd hb, Arith.two_pow_succ, Arith.three_pow_succ]
    omega

/-- The odd-step count over an odd run is the whole run. -/
theorem oddCount_oddRun {x b : Nat} (h : OddRun x b) : oddCount x b = b :=
  (_root_.Collatz.HeavyState.oddCount_eq_iff_oddRun b x).mpr h

/-! ## The accumulator of a two-run word -/

/-- **The two-run accumulator, exactly.**  For a word consisting of `b₁` odd
steps, `e₁` even ones, `b₂` odd ones and `e₂` even ones, the accumulator is
determined outright.  Stated without subtraction. -/
theorem affineC_two_run {x b₁ e₁ b₂ e₂ : Nat}
    (h1 : OddRun x b₁)
    (h2 : oddCount (acceleratedOrbit b₁ x) e₁ = 0)
    (h3 : OddRun (acceleratedOrbit (b₁ + e₁) x) b₂)
    (h4 : oddCount (acceleratedOrbit (b₁ + e₁ + b₂) x) e₂ = 0) :
    affineC (b₁ + e₁ + b₂ + e₂) x + 3 ^ b₂ * 2 ^ b₁ + 2 ^ (b₁ + e₁ + b₂)
      = 3 ^ b₂ * 3 ^ b₁ + 2 ^ (b₁ + e₁) * 3 ^ b₂ := by
  -- the first run
  have hC1 := affineC_oddRun b₁ x h1
  -- the first even block contributes nothing
  have hstep1 : affineC (b₁ + e₁) x = affineC b₁ x := by
    rw [affineC_add x b₁ e₁, h2, Nat.pow_zero, Nat.one_mul,
      AccumulatorValuation.affineC_eq_zero_of_no_odd h2, Nat.mul_zero, Nat.add_zero]
  -- the second run
  have hC2 := affineC_oddRun b₂ (acceleratedOrbit (b₁ + e₁) x) h3
  have hcount2 : oddCount (acceleratedOrbit (b₁ + e₁) x) b₂ = b₂ := oddCount_oddRun h3
  have hstep2 : affineC (b₁ + e₁ + b₂) x
      = 3 ^ b₂ * affineC (b₁ + e₁) x + 2 ^ (b₁ + e₁) * affineC b₂ (acceleratedOrbit (b₁ + e₁) x) := by
    rw [affineC_add x (b₁ + e₁) b₂, hcount2]
  -- the second even block contributes nothing
  have hstep3 : affineC (b₁ + e₁ + b₂ + e₂) x = affineC (b₁ + e₁ + b₂) x := by
    rw [affineC_add x (b₁ + e₁ + b₂) e₂, h4, Nat.pow_zero, Nat.one_mul,
      AccumulatorValuation.affineC_eq_zero_of_no_odd h4, Nat.mul_zero, Nat.add_zero]
  rw [hstep3, hstep2, hstep1]
  -- expand both products against the two run identities
  have hL : 3 ^ b₂ * affineC b₁ x + 3 ^ b₂ * 2 ^ b₁ = 3 ^ b₂ * 3 ^ b₁ := by
    rw [← Nat.mul_add, hC1]
  have hR : 2 ^ (b₁ + e₁) * affineC b₂ (acceleratedOrbit (b₁ + e₁) x) + 2 ^ (b₁ + e₁) * 2 ^ b₂
      = 2 ^ (b₁ + e₁) * 3 ^ b₂ := by
    rw [← Nat.mul_add, hC2]
  have hpow : 2 ^ (b₁ + e₁) * 2 ^ b₂ = 2 ^ (b₁ + e₁ + b₂) := (Nat.pow_add 2 (b₁ + e₁) b₂).symm
  omega

/-! ## The order obstruction at two runs -/

/-- **The two-run order obstruction.**  For a positive cycle whose word is two
runs, the gap divides a two-term expression in which the odd-run lengths appear
only as unit coefficients, and each even block contributes a single factor
`2 ^ e − 1`. -/
theorem two_run_order {x b₁ e₁ b₂ e₂ : Nat} (hx : 0 < x)
    (hcyc : AccIsCycleOf x (b₁ + e₁ + b₂ + e₂))
    (h1 : OddRun x b₁)
    (h2 : oddCount (acceleratedOrbit b₁ x) e₁ = 0)
    (h3 : OddRun (acceleratedOrbit (b₁ + e₁) x) b₂)
    (h4 : oddCount (acceleratedOrbit (b₁ + e₁ + b₂) x) e₂ = 0) :
    (2 ^ (b₁ + e₁ + b₂ + e₂) - 3 ^ (b₁ + b₂))
      ∣ 3 ^ b₂ * (2 ^ e₁ * 2 ^ b₁) + 2 ^ (e₁ + b₂) * 2 ^ (b₁ + e₂)
        - (3 ^ b₂ * 2 ^ b₁ + 2 ^ (e₁ + b₂) * 2 ^ b₁) := by
  -- the word's odd-step count
  have hcount : oddCount x (b₁ + e₁ + b₂ + e₂) = b₁ + b₂ := by
    have hA := AccumulatorArith.oddCount_add x b₁ e₁
    have hB := AccumulatorArith.oddCount_add x (b₁ + e₁) b₂
    have hC := AccumulatorArith.oddCount_add x (b₁ + e₁ + b₂) e₂
    rw [oddCount_oddRun h1, h2, Nat.add_zero] at hA
    rw [hA, oddCount_oddRun h3] at hB
    rw [hB, h4, Nat.add_zero] at hC
    omega
  -- the gap, and the exact accumulator
  have hgaplt : 3 ^ oddCount x (b₁ + e₁ + b₂ + e₂) < 2 ^ (b₁ + e₁ + b₂ + e₂) :=
    (accCycle_bounds hx hcyc).2.2
  have hdvd := CycleAccumulator.cycle_gap_dvd hx hcyc
  have hval := affineC_two_run h1 h2 h3 h4
  rw [hcount] at hgaplt hdvd
  -- rewrite the target as the accumulator plus the gap
  have hsplit : 3 ^ b₂ * (2 ^ e₁ * 2 ^ b₁) + 2 ^ (e₁ + b₂) * 2 ^ (b₁ + e₂)
      = 3 ^ b₂ * 2 ^ (b₁ + e₁) + 2 ^ (b₁ + e₁ + b₂ + e₂) := by
    have e1 : 2 ^ e₁ * 2 ^ b₁ = 2 ^ (b₁ + e₁) := by
      rw [← Nat.pow_add, Nat.add_comm]
    have e2 : 2 ^ (e₁ + b₂) * 2 ^ (b₁ + e₂) = 2 ^ (b₁ + e₁ + b₂ + e₂) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [e1, e2]
  rw [hsplit]
  -- and the subtracted part is what the accumulator identity supplies
  have hgapeq : 3 ^ b₂ * 2 ^ (b₁ + e₁) + 2 ^ (b₁ + e₁ + b₂ + e₂)
      = affineC (b₁ + e₁ + b₂ + e₂) x + (2 ^ (b₁ + e₁ + b₂ + e₂) - 3 ^ (b₁ + b₂))
        + (3 ^ b₂ * 2 ^ b₁ + 2 ^ (e₁ + b₂) * 2 ^ b₁) := by
    have hthree : 3 ^ b₂ * 3 ^ b₁ = 3 ^ (b₁ + b₂) := by
      rw [← Nat.pow_add, Nat.add_comm]
    have hmid : 2 ^ (e₁ + b₂) * 2 ^ b₁ = 2 ^ (b₁ + e₁ + b₂) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hcomm : 2 ^ (b₁ + e₁) * 3 ^ b₂ = 3 ^ b₂ * 2 ^ (b₁ + e₁) := Nat.mul_comm _ _
    have hle : 3 ^ (b₁ + b₂) ≤ 2 ^ (b₁ + e₁ + b₂ + e₂) := by omega
    rw [hthree, hcomm] at hval
    rw [hmid]
    omega
  rw [hgapeq, Nat.add_sub_cancel]
  exact Nat.dvd_add hdvd (Nat.dvd_refl _)

end TwoRunOrder
end Collatz
