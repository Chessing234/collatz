import Collatz.Strategy.AccumulatorValuation

/-!
# A cycle is its accumulator divided by the gap

Put `T^L(n) = n` into the exact affine identity and the orbit disappears:

`2 ^ L · n = 3 ^ a · n + C_L(n)`,  i.e.  `(2 ^ L − 3 ^ a) · n = C_L(n)`.

Everything about a hypothetical cycle is now arithmetic between three integers:
the gap `2 ^ L − 3 ^ a`, the accumulator `C`, and the cycle point itself.  Two of
the three determine the third, so:

* `cycle_gap_dvd` — the gap divides the accumulator, exactly;
* `cycle_eq_div` — the cycle point is `C / (2 ^ L − 3 ^ a)`, so it is *not free*:
  it is a function of the parity word;
* `cycle_unique_of_word` — two cycle points of the same length with the same
  multiplier and the same accumulator are equal;
* `cycle_unique_of_mod` — since `AccumulatorClass` makes both of those class
  functions, **at most one cycle point of length `L` lies in each residue class
  modulo `2 ^ L`**.

The last one is the structural statement worth having.  It converts the search
for a cycle of length `L` from a search over integers to a search over the `2 ^ L`
parity words, with the candidate value *computed* rather than quantified.  It is
also the precise sense in which "every word is realised by a class" (Terras) does
not help the adversary: a word realises a class, but a *cycle* additionally
demands that the gap divide the accumulator, and that is an arithmetic condition
on the word alone.

`v₂` is already decided here: the gap `2 ^ L − 3 ^ a` is odd for `L ≥ 1, a ≥ 1`,
so `v₂(n) = v₂(C)` — the cycle point's 2-adic valuation is the timestamp of the
first odd step (`AccumulatorValuation.affineC_valuation`).
-/

namespace Collatz
namespace CycleAccumulator

open Congruence AffineExact AccCycle AccumulatorClass

/-! ## Positivity of the accumulator -/

/-- Once an odd step has occurred the accumulator is positive. -/
theorem affineC_pos {x : Nat} : ∀ {j : Nat}, 0 < oddCount x j → 0 < affineC j x := by
  intro j
  induction j with
  | zero => intro h; simp at h
  | succ j ih =>
    intro h
    have hlast := Density.oddCount_succ_last x j
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j x) with he | ho
    · have hj : 0 < oddCount x j := by omega
      rw [affineC_even he]
      exact ih hj
    · rw [affineC_odd ho]
      have := Arith.two_pow_pos j
      omega

/-! ## The cycle equation -/

/-- **The cycle equation.**  A cycle point satisfies the affine identity with
the orbit term replaced by itself. -/
theorem cycle_affine {n L : Nat} (h : AccIsCycleOf n L) :
    2 ^ L * n = 3 ^ oddCount n L * n + affineC L n := by
  have hex := affine_exact n L
  rw [h.2] at hex
  exact hex

/-- **The gap times the point is the accumulator.**  Subtraction is legitimate
here because `3 ^ a < 2 ^ L` for a positive cycle (`accCycle_bounds`). -/
theorem cycle_gap_mul {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) :
    (2 ^ L - 3 ^ oddCount n L) * n = affineC L n := by
  have hlt := (accCycle_bounds hn h).2.2
  have heq := cycle_affine h
  have hsub : (2 ^ L - 3 ^ oddCount n L) * n = 2 ^ L * n - 3 ^ oddCount n L * n :=
    Nat.sub_mul _ _ _
  have hmono : 3 ^ oddCount n L * n ≤ 2 ^ L * n := Nat.mul_le_mul_right n (by omega)
  omega

/-- The gap divides the accumulator. -/
theorem cycle_gap_dvd {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) :
    (2 ^ L - 3 ^ oddCount n L) ∣ affineC L n :=
  ⟨n, (cycle_gap_mul hn h).symm⟩

/-- **The cycle point is computed, not chosen.**  It is the accumulator divided
by the gap. -/
theorem cycle_eq_div {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) :
    n = affineC L n / (2 ^ L - 3 ^ oddCount n L) := by
  have hlt := (accCycle_bounds hn h).2.2
  have hgap : 0 < 2 ^ L - 3 ^ oddCount n L := by omega
  rw [← cycle_gap_mul hn h, Nat.mul_div_cancel_left _ hgap]

/-! ## One cycle per word -/

/-- **Same word, same cycle.**  Two positive cycle points of the same length
whose multipliers and accumulators agree are the same number. -/
theorem cycle_unique_of_word {m n L : Nat} (hm : 0 < m) (hn : 0 < n)
    (hcm : AccIsCycleOf m L) (hcn : AccIsCycleOf n L)
    (hcount : oddCount m L = oddCount n L) (hC : affineC L m = affineC L n) :
    m = n := by
  have hlt := (accCycle_bounds hm hcm).2.2
  have hgap : 0 < 2 ^ L - 3 ^ oddCount m L := by omega
  have hm' := cycle_gap_mul hm hcm
  have hn' := cycle_gap_mul hn hcn
  rw [← hcount] at hn'
  have : (2 ^ L - 3 ^ oddCount m L) * m = (2 ^ L - 3 ^ oddCount m L) * n := by
    rw [hm', hn', hC]
  exact Nat.eq_of_mul_eq_mul_left hgap this

/-- **At most one cycle point of length `L` per residue class mod `2 ^ L`.**
The multiplier and the accumulator are class functions, so the cycle equation
determines the point from its class. -/
theorem cycle_unique_of_mod {m n L : Nat} (hm : 0 < m) (hn : 0 < n)
    (hcm : AccIsCycleOf m L) (hcn : AccIsCycleOf n L)
    (hmod : m % 2 ^ L = n % 2 ^ L) :
    m = n :=
  cycle_unique_of_word hm hn hcm hcn (oddCount_congr_of_mod hmod) (affineC_congr_of_mod hmod)

/-! ## The gap is odd -/

/-- For a positive cycle the gap `2 ^ L − 3 ^ a` is odd, so it cannot absorb any
of the accumulator's 2-adic valuation: `v₂(n) = v₂(C_L(n))`. -/
theorem cycle_gap_odd {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) :
    (2 ^ L - 3 ^ oddCount n L) % 2 = 1 := by
  have hbounds := accCycle_bounds hn h
  have hL : 0 < L := h.1
  have h2 : 2 ^ L % 2 = 0 := by
    have : 2 ^ L = 2 * 2 ^ (L - 1) := by
      rw [← Arith.two_pow_succ]
      congr 1
      omega
    omega
  have h3 : 3 ^ oddCount n L % 2 = 1 := Arith.three_pow_odd _
  omega

end CycleAccumulator
end Collatz
