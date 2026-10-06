import Collatz.Structure.ParityMoments
import Collatz.Structure.GeometricPrecision
import Collatz.Papers.Korec1994

/-!
# Turning a parity threshold into an actual power bound

These estimates keep the affine correction. They give an actual Collatz
orbit below n^(4/5) on a sufficiently large multiplicative interval when the
125s-step parity count is at most 63s. Counting the exceptional inputs is a
separate step.
-/
namespace Collatz.PowerOrbitScale
open AffineExact ParityMoments

/-- The affine remainder is controlled by the same multiplier as the main
term when the input is bounded by a fixed multiple of the parity modulus. -/
theorem orbit_upper {n k L : Nat} (hn : n≤L*2^k) :
    acceleratedOrbit k n≤(L+1)*3^oddCount n k := by
  have he := affine_exact n k
  have hc := affineC_le n k
  have hp : 2^(k-oddCount n k)≤(2:Nat)^k :=
    Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have hcm := Nat.mul_le_mul_right (3^oddCount n k) hp
  have hm := Nat.mul_le_mul_left (3^oddCount n k) hn
  have hsum := Nat.add_le_add hm (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans hc hcm))
  rw [← he] at hsum
  have hnorm : 2^k*acceleratedOrbit k n≤2^k*((L+1)*3^oddCount n k) := by
    simpa only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm] using hsum
  exact Nat.le_of_mul_le_mul_left hnorm (Nat.pow_pos (by decide))

/-- A sufficiently large block count absorbs every fixed affine prefactor. -/
theorem multiplier_precision (L s : Nat) (hs : (L+1)^5*3^315≤s) :
    ((L+1)*3^(63*s))^5 < (2^(125*s))^4 := by
  have h := GeometricPrecision.scaled_power_lt (3^315) (2^500) ((L+1)^5) s
    (Nat.pow_pos (by decide)) four_fifths_multiplier_gap hs
  simpa only [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_assoc, Nat.mul_comm,
    Nat.mul_left_comm] using h

/-- A light parity endpoint in a sufficiently large scale interval gives
an actual strict 4/5-power orbit bound. -/
theorem four_fifths_on_scale {n L s : Nat}
    (hs : (L+1)^5*3^315≤s)
    (hnlo : 2^(125*s)≤n) (hnhi : n≤L*2^(125*s))
    (ha : oddCount n (125*s)≤63*s) :
    Papers.Korec1994.OrbitBelowPower 4 5 n := by
  have hu := orbit_upper hnhi
  have hp := Nat.mul_le_mul_left (L+1)
    (Nat.pow_le_pow_right (by decide : 1≤(3:Nat)) ha)
  have hsmall := Nat.pow_le_pow_left (Nat.le_trans hu hp) 5
  have hlarge := Nat.pow_le_pow_left hnlo 4
  exact ⟨125*s, Nat.lt_of_le_of_lt hsmall
    (Nat.lt_of_lt_of_le (multiplier_precision L s hs) hlarge)⟩

/-- Contrapositive form used to count failures: every exception in the scale
interval belongs to the high-odd-count residue tail. -/
theorem failure_has_many_odd {n L s : Nat}
    (hs : (L+1)^5*3^315≤s)
    (hnlo : 2^(125*s)≤n) (hnhi : n≤L*2^(125*s))
    (hfail : ¬Papers.Korec1994.OrbitBelowPower 4 5 n) :
    63*s≤oddCount n (125*s) := by
  by_cases ha : oddCount n (125*s)≤63*s
  · exact False.elim (hfail (four_fifths_on_scale hs hnlo hnhi ha))
  · omega

end Collatz.PowerOrbitScale
