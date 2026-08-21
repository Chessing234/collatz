import Collatz.Strategy.ClassCap

/-!
# The exact residue mod three, read off the current even run

`AccumulatorArith.three_not_dvd_orbit_of_odd_step` says an orbit point is never
divisible by three once an odd step has occurred.  That is a *non*-statement: it
excludes one of three residues.  The residue is in fact completely determined,
and by something local — the length of the halving run the orbit is currently in.

The mechanism is the accumulator.  Modulo three, `C_{j+1} = 3 C_j + 2 ^ j`
forgets everything before the last odd step: `C ≡ 2 ^ t (mod 3)` where `t` is the
time of the **last** odd step (`affineC_mod_three_last_odd`).  Feeding that into
`2 ^ j · T^j(x) ≡ C (mod 3)` and cancelling the unit `2 ^ j` leaves

`T^j(x) ≡ 2 ^ (t − j) ≡ (−1) ^ (j − t)  (mod 3)`,

so with `k = j − t − 1` halvings since that odd step:

**`T^j(x) ≡ 2 (mod 3)` when `k` is even, `≡ 1 (mod 3)` when `k` is odd**
(`orbit_mod_three_of_last_odd`).

The orbit's 3-adic residue is therefore a *clock reading of the parity word*,
exactly as `v₂(C)` was.  Nothing about the size of `x` enters, and nothing about
the word before the last odd step survives.
-/

namespace Collatz
namespace ThreeResidue

open Congruence AffineExact AccumulatorArith AccumulatorValuation

/-! ## Powers of two modulo three -/

/-- `2 ^ j` alternates between `1` and `2` modulo three, tracking the parity of
`j`. -/
theorem two_pow_mod_three_parity : ∀ j : Nat,
    (j % 2 = 0 ∧ 2 ^ j % 3 = 1) ∨ (j % 2 = 1 ∧ 2 ^ j % 3 = 2) := by
  intro j
  induction j with
  | zero => left; exact ⟨rfl, rfl⟩
  | succ j ih =>
    rw [Arith.two_pow_succ]
    rcases ih with ⟨hp, hv⟩ | ⟨hp, hv⟩
    · right
      refine ⟨by omega, ?_⟩
      omega
    · left
      refine ⟨by omega, ?_⟩
      omega

/-! ## The accumulator modulo three forgets all but the last odd step -/

/-- **Only the last odd step is visible modulo three.**  If the step at time `t`
is odd and every step after it in the window is even, then `C ≡ 2 ^ t (mod 3)`. -/
theorem affineC_mod_three_last_odd {x t k : Nat} (hodd : acceleratedOrbit t x % 2 = 1)
    (htail : oddCount (acceleratedOrbit (t + 1) x) k = 0) :
    affineC (t + 1 + k) x % 3 = 2 ^ t % 3 := by
  have hsplit := affineC_add x (t + 1) k
  rw [htail, Nat.pow_zero, Nat.one_mul,
    affineC_eq_zero_of_no_odd htail, Nat.mul_zero, Nat.add_zero] at hsplit
  rw [hsplit, affineC_odd hodd]
  omega

/-! ## The residue of the orbit point -/

/-- The window still contains an odd step, so the multiplier is a genuine power
of three and the reduction of `affine_exact` modulo three is available. -/
theorem oddCount_pos_of_last_odd {x t k : Nat} (hodd : acceleratedOrbit t x % 2 = 1)
    (htail : oddCount (acceleratedOrbit (t + 1) x) k = 0) :
    0 < oddCount x (t + 1 + k) := by
  have hadd := oddCount_add x (t + 1) k
  rw [htail, Nat.add_zero] at hadd
  have hlast := Density.oddCount_succ_last x t
  rw [hodd] at hlast
  omega

/-- **The residue is a clock.**  With `k` halvings since the last odd step, the
orbit point is `2` mod three when `k` is even and `1` mod three when `k` is
odd. -/
theorem orbit_mod_three_of_last_odd {x t k : Nat} (hodd : acceleratedOrbit t x % 2 = 1)
    (htail : oddCount (acceleratedOrbit (t + 1) x) k = 0) :
    (k % 2 = 0 → acceleratedOrbit (t + 1 + k) x % 3 = 2) ∧
    (k % 2 = 1 → acceleratedOrbit (t + 1 + k) x % 3 = 1) := by
  have hpos := oddCount_pos_of_last_odd hodd htail
  have hform := orbit_three_pow_form (x := x) (j := t + 1 + k) (k := 1) (by omega)
  rw [Nat.pow_one] at hform
  have hmod3 : (2 ^ (t + 1 + k) * acceleratedOrbit (t + 1 + k) x) % 3
      = affineC (t + 1 + k) x % 3 := by
    rw [hform, Nat.add_comm, Nat.add_mul_mod_self_left]
  rw [affineC_mod_three_last_odd hodd htail, Nat.mul_mod] at hmod3
  have hj := two_pow_mod_three_parity (t + 1 + k)
  have ht := two_pow_mod_three_parity t
  have hr : acceleratedOrbit (t + 1 + k) x % 3 = 0
      ∨ acceleratedOrbit (t + 1 + k) x % 3 = 1
      ∨ acceleratedOrbit (t + 1 + k) x % 3 = 2 := by omega
  constructor
  · intro hk
    rcases hj with ⟨hjp, hjv⟩ | ⟨hjp, hjv⟩ <;> rcases ht with ⟨htp, htv⟩ | ⟨htp, htv⟩ <;>
      rcases hr with h | h | h <;> rw [hjv, h] at hmod3 <;> omega
  · intro hk
    rcases hj with ⟨hjp, hjv⟩ | ⟨hjp, hjv⟩ <;> rcases ht with ⟨htp, htv⟩ | ⟨htp, htv⟩ <;>
      rcases hr with h | h | h <;> rw [hjv, h] at hmod3 <;> omega


/-! ## The deterministic placement of three-divisibility

`RESEARCH.md` recorded, from measurement, that "32 % of even steps inject
3-divisibility", and read that as a statistical fact.  It is not statistical at
all.  In the shifted coordinate `u = x + 1`, `3 ∣ u` says `x ≡ 2 (mod 3)`, which
by the clock above happens exactly when the number of halvings since the last
odd step is **even**.  So along an even run the divisibility alternates with
period two, starting at the run's first point — deterministic placement, not a
frequency. -/

/-- **Three divides `x + 1` at exactly every second point of an even run.**  The
condition is the parity of the number of halvings since the last odd step. -/
theorem three_dvd_succ_iff_even_halvings {x t k : Nat} (hodd : acceleratedOrbit t x % 2 = 1)
    (htail : oddCount (acceleratedOrbit (t + 1) x) k = 0) :
    3 ∣ (acceleratedOrbit (t + 1 + k) x + 1) ↔ k % 2 = 0 := by
  obtain ⟨heven, hoddk⟩ := orbit_mod_three_of_last_odd hodd htail
  constructor
  · intro hdvd
    rcases Arith.mod_two_eq_zero_or_one k with hk | hk
    · exact hk
    · exfalso
      obtain ⟨c, hc⟩ := hdvd
      have h1 := hoddk hk
      omega
  · intro hk
    have h2 := heven hk
    exact ⟨(acceleratedOrbit (t + 1 + k) x + 1) / 3, by omega⟩

end ThreeResidue
end Collatz
