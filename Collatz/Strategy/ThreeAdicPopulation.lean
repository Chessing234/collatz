import Collatz.Strategy.ThreeAdicEscape
import Collatz.Structure.Congruence
import Collatz.Core.Sum

/-!
# Exact finite-time populations modulo three

Uniform inputs over a complete block of length `3*2^k` are not uniformly
distributed modulo three after k accelerated steps. A doubling pairing gives
an exact recurrence, with no probability or independence assumptions.
-/

namespace Collatz.ThreeAdicPopulation
open Collatz.Sum

/-- The input period used for the k-step residue population. -/
def period (k : Nat) : Nat := 3 * 2 ^ k

/-- Number of inputs in one period landing in a prescribed residue modulo 3. -/
def population (k r : Nat) : Nat :=
  sumRange (period k) (fun n => if acceleratedOrbit k n % 3 = r then 1 else 0)

/-- Doubling the depth doubles the input period. -/
theorem period_succ (k : Nat) : period (k + 1) = 2 * period k := by
  unfold period
  rw [Nat.pow_succ]
  omega

/-- An even step multiplies the residue modulo three by two. -/
theorem even_image_mod_three {n : Nat} (hn : n % 2 = 0) :
    acceleratedStep n % 3 = (2 * (n % 3)) % 3 := by
  simp only [acceleratedStep, if_pos hn]
  omega

/-- Opposite parity states with equal residues form one odd and one even branch. -/
theorem residue_pair {x y : Nat} (hmod : x % 3 = y % 3)
    (hpar : (x + y) % 2 = 1) (r : Nat) :
    (if acceleratedStep x % 3 = r then 1 else 0) +
      (if acceleratedStep y % 3 = r then 1 else 0) =
    (if r = 2 then 1 else 0) +
      (if (2 * (x % 3)) % 3 = r then 1 else 0) := by
  by_cases hx : x % 2 = 0
  · have hy : y % 2 = 1 := by omega
    rw [even_image_mod_three hx, ThreeAdicEscape.odd_image_mod_three hy]
    simp only [eq_comm (a := 2) (b := r)]
    omega
  · have hxo : x % 2 = 1 := by omega
    have hy : y % 2 = 0 := by omega
    rw [ThreeAdicEscape.odd_image_mod_three hxo, even_image_mod_three hy, ← hmod]
    simp only [eq_comm (a := 2) (b := r)]

/-- A period shift preserves residue modulo three at the current depth. -/
theorem orbit_period_shift (k n : Nat) :
    acceleratedOrbit k (period k + n) =
      3 ^ oddCount n k * 3 + acceleratedOrbit k n := by
  have h := Congruence.accOrbit_pow_two_mul_add k 3 n
  simpa only [period, Nat.mul_comm (2 ^ k) 3] using h

/-- Current-depth paired outputs have the same residue modulo three. -/
theorem paired_outputs_mod_three (k n : Nat) :
    acceleratedOrbit k n % 3 = acceleratedOrbit k (period k + n) % 3 := by
  rw [orbit_period_shift]
  omega

/-- Current-depth paired outputs have opposite parities. -/
theorem paired_outputs_opposite_parity (k n : Nat) :
    (acceleratedOrbit k n + acceleratedOrbit k (period k + n)) % 2 = 1 := by
  rw [orbit_period_shift]
  have ho := Arith.three_pow_odd (oddCount n k)
  have hc : (3 ^ oddCount n k * 3) % 2 = 1 := by
    simp [Nat.mul_mod, ho]
  omega

/-- The paired contribution to next-depth populations is explicit. -/
theorem orbit_residue_pair (k n r : Nat) :
    (if acceleratedOrbit (k + 1) n % 3 = r then 1 else 0) +
      (if acceleratedOrbit (k + 1) (period k + n) % 3 = r then 1 else 0) =
    (if r = 2 then 1 else 0) +
      (if (2 * (acceleratedOrbit k n % 3)) % 3 = r then 1 else 0) := by
  rw [acceleratedOrbit_succ_step, acceleratedOrbit_succ_step]
  exact residue_pair (paired_outputs_mod_three k n)
    (paired_outputs_opposite_parity k n) r

/-- Multiplication by two modulo three swaps the two nonzero residues. -/
theorem mapped_residue_iff (x r : Nat) (hr : r < 3) :
    (2 * (x % 3)) % 3 = r ↔ x % 3 = (2 * r) % 3 := by
  omega

/-- Exact one-step population transport on a complete input period. -/
theorem population_succ (k r : Nat) (hr : r < 3) :
    population (k + 1) r =
      period k * (if r = 2 then 1 else 0) + population k ((2 * r) % 3) := by
  unfold population
  rw [period_succ, sumRange_two_mul, ← sumRange_add]
  have hp : sumRange (period k)
      (fun n => (if acceleratedOrbit (k + 1) n % 3 = r then 1 else 0) +
        (if acceleratedOrbit (k + 1) (period k + n) % 3 = r then 1 else 0)) =
      sumRange (period k) (fun n => (if r = 2 then 1 else 0) +
        (if acceleratedOrbit k n % 3 = (2 * r) % 3 then 1 else 0)) := by
    apply sumRange_congr
    intro n _
    rw [orbit_residue_pair]
    simp only [mapped_residue_iff _ r hr]
  rw [hp, sumRange_add, sumRange_const]

/-- The residue-zero population is unchanged at each depth. -/
theorem population_zero_succ (k : Nat) : population (k + 1) 0 = population k 0 := by
  simpa using population_succ k 0 (by decide)

/-- Residue one at the next depth comes from residue two via an even step. -/
theorem population_one_succ (k : Nat) : population (k + 1) 1 = population k 2 := by
  simpa using population_succ k 1 (by decide)

/-- Residue two receives every odd branch plus the residue-one even branches. -/
theorem population_two_succ (k : Nat) :
    population (k + 1) 2 = period k + population k 1 := by
  simpa using population_succ k 2 (by decide)

/-- At depth zero each residue is represented once. -/
theorem population_initial (r : Nat) (hr : r < 3) : population 0 r = 1 := by
  have hc : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases hc with h | h | h <;> subst r <;> decide

end Collatz.ThreeAdicPopulation
