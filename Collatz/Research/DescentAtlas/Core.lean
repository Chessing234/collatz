import Collatz.Structure.Congruence

/-! Exact residue-class descent thresholds, without a convergence assumption. -/
namespace Collatz.Research.DescentAtlas

/-- The positive coefficient deficit available to pay the affine offset. -/
def gap (k r : Nat) : Nat := 2 ^ k - 3 ^ oddCount r k

/-- Under contraction, descent is exactly a linear inequality on the class index.
This equivalence exposes both successful indices and the exceptional finite tail. -/
theorem descent_iff_gap {k r m : Nat} (h : 3 ^ oddCount r k < 2 ^ k) :
    acceleratedOrbit k (2 ^ k * m + r) < 2 ^ k * m + r ↔
      acceleratedOrbit k r < gap k r * m + r := by
  rw [Congruence.accOrbit_pow_two_mul_add]
  have hs : 3 ^ oddCount r k + gap k r = 2 ^ k := by
    unfold gap
    omega
  have hm := congrArg (fun x : Nat => x * m) hs
  rw [Nat.add_mul] at hm
  omega

/-- A concrete certificate can discharge every index, including zero, when
its representative already descends. -/
theorem descent_of_endpoint {k r m : Nat}
    (h : 3 ^ oddCount r k < 2 ^ k)
    (he : acceleratedOrbit k r < r) :
    acceleratedOrbit k (2 ^ k * m + r) < 2 ^ k * m + r := by
  apply (descent_iff_gap h).2
  omega

/-- A noncontracting class cannot descend when its representative does not.
This is a rigorous obstruction for one horizon, not for eventual descent. -/
theorem no_descent_of_noncontracting {k r m : Nat}
    (h : 2 ^ k ≤ 3 ^ oddCount r k)
    (he : r ≤ acceleratedOrbit k r) :
    2 ^ k * m + r ≤ acceleratedOrbit k (2 ^ k * m + r) := by
  rw [Congruence.accOrbit_pow_two_mul_add]
  exact Nat.add_le_add (Nat.mul_le_mul_right m h) he

/-- Increasing the class index preserves a successful contracting certificate. -/
theorem descent_upward_closed {k r m t : Nat}
    (h : 3 ^ oddCount r k < 2 ^ k)
    (hd : acceleratedOrbit k (2 ^ k * m + r) < 2 ^ k * m + r)
    (ht : m ≤ t) :
    acceleratedOrbit k (2 ^ k * t + r) < 2 ^ k * t + r := by
  apply (descent_iff_gap h).2
  have hp := Nat.mul_le_mul_left (gap k r) ht
  have hd' := (descent_iff_gap h).1 hd
  omega

end Collatz.Research.DescentAtlas
