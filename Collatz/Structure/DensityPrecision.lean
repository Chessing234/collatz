import Collatz.Structure.Density

/-!
# An explicit horizon for an arbitrary heavy-residue precision

This converts the existing geometric fifth-power bound into a simple integer
precision statement. The horizon 80s is deliberately coarse; it is chosen for
an elementary doubling-block proof, not for an optimized stopping-time estimate.
-/
namespace Collatz.DensityPrecision

/-- Sixteen steps gain at least a factor of two in the geometric ratio. -/
theorem block_gain : 2*(243:Nat)^16 ≤ 256^16 := by decide

/-- At horizon 16t, the denominator of the geometric estimate gains 2^t. -/
theorem iterated_gain (t : Nat) : 2^t*(243:Nat)^(16*t) ≤ 256^(16*t) := by
  have h := Nat.pow_le_pow_left block_gain t
  simpa only [Nat.mul_pow, ← Nat.pow_mul] using h

/-- A coarse horizon at which the heavy fraction is at most 1/s (for s>0). -/
theorem heavy_precision (s : Nat) :
    s*Density.heavyCount (80*s) ≤ 2^(80*s) := by
  let H := 80*s
  have he : 16*(5*s)=H := by simp only [H]; omega
  have hg := iterated_gain (5*s)
  rw [he] at hg
  have hs : s^5≤(2:Nat)^(5*s) := by
    have h := Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow_self (n := s))) 5
    simpa only [← Nat.pow_mul, Nat.mul_comm s 5] using h
  have hbase := Density.heavyCount_pow_five_ratio H
  have hc : (s*Density.heavyCount H)^5*243^H ≤ (2^H)^5*243^H := by
    calc
      (s*Density.heavyCount H)^5*243^H
          = (s^5*243^H)*Density.heavyCount H^5 := by rw [Nat.mul_pow]; ac_rfl
      _ ≤ (2^(5*s)*243^H)*Density.heavyCount H^5 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hs)
      _ ≤ 256^H*Density.heavyCount H^5 := Nat.mul_le_mul_right _ hg
      _ = Density.heavyCount H^5*256^H := Nat.mul_comm _ _
      _ ≤ 243^H*(2^H)^5 := hbase
      _ = (2^H)^5*243^H := Nat.mul_comm _ _
  by_cases h : s*Density.heavyCount H≤2^H
  · exact h
  · have hp := Nat.pow_lt_pow_left (show 2^H<s*Density.heavyCount H by omega)
      (by decide : (5:Nat)≠0)
    have hpos : 0<(243:Nat)^H := Nat.pow_pos (by decide)
    have hcontra := Nat.mul_lt_mul_of_pos_right hp hpos
    omega

end Collatz.DensityPrecision
