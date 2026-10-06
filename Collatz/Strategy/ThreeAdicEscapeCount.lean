import Collatz.Strategy.ThreeAdicEscape
import Collatz.Core.Sum

/-!
# Exact finite counting of the three-adic survivors

`survivorCount k N` counts starting values in `[0,N)` whose accelerated
k-th iterate is divisible by three. Aligned intervals of length `3*2^k`
contain exactly one survivor each. These are counts of inputs with
multiplicity, rather than counts of distinct orbit outputs.
-/

namespace Collatz.ThreeAdicEscape
open Collatz.Sum

/-- Indicator count of multiples of a modulus in a half-open interval. -/
def multipleCount (d N : Nat) : Nat :=
  sumRange N (fun n => if n % d = 0 then 1 else 0)

/-- Count the initial values whose k-th iterate is divisible by three. -/
def survivorCount (k N : Nat) : Nat :=
  sumRange N (fun n => if acceleratedOrbit k n % 3 = 0 then 1 else 0)

/-- The orbit-based computation agrees with a static divisibility test. -/
theorem survivorCount_eq_multipleCount (k N : Nat) :
    survivorCount k N = multipleCount (3 * 2 ^ k) N := by
  unfold survivorCount multipleCount
  apply sumRange_congr
  intro i _
  have h : acceleratedOrbit k i % 3 = 0 ↔ i % (3 * 2 ^ k) = 0 := by
    simpa only [Nat.dvd_iff_mod_eq_zero] using orbit_divisible_three_iff k i
  simp only [h]

/-- The origin contributes once to every nonempty half-open interval. -/
theorem sum_origin_indicator (d : Nat) (hd : 0 < d) :
    sumRange d (fun i => if i = 0 then 1 else 0) = 1 := by
  cases d with
  | zero => omega
  | succ d =>
    induction d with
    | zero => decide
    | succ d ih =>
      rw [sumRange_succ]
      simp only [Nat.succ_ne_zero, if_false, Nat.add_zero]
      exact ih (by omega)

/-- Each complete modulus block has one multiple, at its left endpoint. -/
theorem multiple_block (d q : Nat) (hd : 0 < d) :
    sumRange d (fun i => if (d * q + i) % d = 0 then 1 else 0) = 1 := by
  calc
    _ = sumRange d (fun i => if i = 0 then 1 else 0) := by
      apply sumRange_congr
      intro i hi
      have he : (d * q + i) % d = i := by
        simp [Nat.add_mod, Nat.mod_eq_of_lt hi]
      rw [he]
    _ = 1 := sum_origin_indicator d hd

/-- Exact count on any number of aligned blocks. -/
theorem multipleCount_aligned (d q : Nat) (hd : 0 < d) :
    multipleCount d (d * q) = q := by
  induction q with
  | zero => simp [multipleCount]
  | succ q ih =>
    unfold multipleCount at ih ⊢
    rw [Nat.mul_succ, sumRange_split, ih, multiple_block d q hd]

/-- The exact finite survivor proportion is `1/(3*2^k)`. -/
theorem survivorCount_aligned (k q : Nat) :
    survivorCount k ((3 * 2 ^ k) * q) = q := by
  rw [survivorCount_eq_multipleCount]
  apply multipleCount_aligned
  exact Nat.mul_pos (by decide) (Nat.pow_pos (by decide))

/-- Counts are monotone in the input cutoff. -/
theorem multipleCount_mono (d : Nat) {N M : Nat} (h : N ≤ M) :
    multipleCount d N ≤ multipleCount d M :=
  sumRange_mono_length _ h

/-- An arbitrary cutoff differs from its aligned count by at most one. -/
theorem multipleCount_bounds (d N : Nat) (hd : 0 < d) :
    N / d ≤ multipleCount d N ∧ multipleCount d N ≤ N / d + 1 := by
  have hrem : N % d < d := Nat.mod_lt N hd
  have hsplit := Nat.div_add_mod N d
  have hlo : d * (N / d) ≤ N := by omega
  have hhi : N ≤ d * (N / d + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  constructor
  · have h := multipleCount_mono d hlo
    rw [multipleCount_aligned d (N / d) hd] at h
    exact h
  · have h := multipleCount_mono d hhi
    rw [multipleCount_aligned d (N / d + 1) hd] at h
    exact h

/-- Finite survivor counts at arbitrary cutoffs have a one-input error bound. -/
theorem survivorCount_bounds (k N : Nat) :
    N / (3 * 2 ^ k) ≤ survivorCount k N ∧
    survivorCount k N ≤ N / (3 * 2 ^ k) + 1 := by
  rw [survivorCount_eq_multipleCount]
  exact multipleCount_bounds _ _
    (Nat.mul_pos (by decide) (Nat.pow_pos (by decide)))

/-- An incomplete block contributes only its left endpoint when nonempty. -/
theorem multiple_partial_block (d q r : Nat) (_hd : 0 < d) (hr : r ≤ d) :
    sumRange r (fun i => if (d * q + i) % d = 0 then 1 else 0) =
      (if r = 0 then 0 else 1) := by
  by_cases hz : r = 0
  · subst r
    simp
  · rw [if_neg hz]
    calc
      _ = sumRange r (fun i => if i = 0 then 1 else 0) := by
        apply sumRange_congr
        intro i hi
        have hid : i < d := by omega
        have he : (d * q + i) % d = i := by
          simp [Nat.add_mod, Nat.mod_eq_of_lt hid]
        rw [he]
      _ = 1 := sum_origin_indicator r (by omega)

/-- Exact arbitrary-cutoff count: one input per full block and one if needed. -/
theorem multipleCount_exact (d N : Nat) (hd : 0 < d) :
    multipleCount d N = N / d + (if N % d = 0 then 0 else 1) := by
  have hsplit := Nat.div_add_mod N d
  unfold multipleCount
  rw [← hsplit, sumRange_split]
  change multipleCount d (d * (N / d)) + _ = _
  rw [multipleCount_aligned d (N / d) hd]
  rw [multiple_partial_block d (N / d) (N % d) hd (Nat.le_of_lt (Nat.mod_lt N hd))]
  rw [hsplit]

/-- Exact count of the three-adic survivors for every finite cutoff. -/
theorem survivorCount_exact (k N : Nat) :
    survivorCount k N = N / (3 * 2 ^ k) +
      (if N % (3 * 2 ^ k) = 0 then 0 else 1) := by
  rw [survivorCount_eq_multipleCount]
  exact multipleCount_exact _ _
    (Nat.mul_pos (by decide) (Nat.pow_pos (by decide)))

/-- At every fixed depth, the surviving set is infinite. -/
theorem survivors_above (k B : Nat) :
    ∃ n : Nat, B < n ∧ 3 ∣ acceleratedOrbit k n := by
  let d := 3 * 2 ^ k
  have hd : 0 < d := Nat.mul_pos (by decide) (Nat.pow_pos (by decide))
  refine ⟨d * (B + 1), ?_, (orbit_divisible_three_iff k _).mpr ?_⟩
  · have hm := Nat.mul_le_mul_right (B + 1) hd
    omega
  · exact ⟨B + 1, rfl⟩

/-- One-step population: 10 of 60 inputs still land in residue zero. -/
example : survivorCount 1 60 = 10 := by decide

set_option maxRecDepth 4000 in
/-- Five-step population: 10 of 960 inputs still land in residue zero. -/
example : survivorCount 5 960 = 10 := by decide

end Collatz.ThreeAdicEscape
