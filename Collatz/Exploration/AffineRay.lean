import Collatz.Exploration.WitnessSize

/-!
# Geometric inverse families from one affine match

Suppose A*m+B is a power of two and a period power has the form A*c+1.
Multiplying the endpoint by that period power transports the index by the
integer affine map m ↦ (A*c+1)*m+c*B. Iteration supplies a whole family of
matching powers without repeating the modular search.

The result is generic arithmetic. It is separated from its later Collatz use
so the exact hypotheses and the geometric growth can be inspected directly.
-/
namespace Collatz.Exploration.AffineRay

/-- Inverse-index transport induced by multiplication by a period power. -/
def nextIndex (A B c m : Nat) : Nat := (A*c+1)*m+c*B

/-- A ray starts at a supplied matching index and repeatedly transports it. -/
def ray (A B c m : Nat) : Nat → Nat
  | 0 => m
  | j+1 => nextIndex A B c (ray A B c m j)

@[simp] theorem ray_zero (A B c m : Nat) : ray A B c m 0 = m := rfl

@[simp] theorem ray_succ (A B c m j : Nat) :
    ray A B c m (j+1) = nextIndex A B c (ray A B c m j) := rfl

/-- Transport is exactly multiplication on the affine endpoint. -/
theorem endpoint_transport (A B c m : Nat) :
    A*nextIndex A B c m+B = (A*c+1)*(A*m+B) := by
  simp only [nextIndex, Nat.mul_add, Nat.add_mul, Nat.one_mul]
  simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm]

/-- Iterating transport multiplies the endpoint by a geometric factor. -/
theorem endpoint_ray (A B c m j : Nat) :
    A*ray A B c m j+B = (A*c+1)^j*(A*m+B) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [ray_succ, endpoint_transport, ih, Nat.pow_succ]
    simp only [Nat.mul_comm, Nat.mul_left_comm]

/-- Matching one power transports to matching powers spaced by the period. -/
theorem power_ray {A B c m p e : Nat}
    (hperiod : A*c+1 = 2^p) (hstart : A*m+B = 2^e) (j : Nat) :
    A*ray A B c m j+B = 2^(p*j+e) := by
  rw [endpoint_ray, hperiod, hstart, ← Nat.pow_mul, ← Nat.pow_add]

/-- Every transport is nondecreasing without additional assumptions. -/
theorem nextIndex_ge (A B c m : Nat) : m ≤ nextIndex A B c m := by
  unfold nextIndex
  have hm := Nat.mul_le_mul_right m (show 1 ≤ A*c+1 by omega)
  simp only [Nat.one_mul] at hm
  omega

/-- A positive index strictly grows if the period multiplier exceeds one. -/
theorem nextIndex_gt {A B c m : Nat} (hfactor : 1 < A*c+1) (hm : 0 < m) :
    m < nextIndex A B c m := by
  unfold nextIndex
  have hh := Nat.mul_lt_mul_of_pos_right hfactor hm
  simp only [Nat.one_mul] at hh
  omega

/-- Positivity of the starting index is preserved along the ray. -/
theorem ray_positive {A B c m : Nat} (hm : 0 < m) (j : Nat) :
    0 < ray A B c m j := by
  induction j with
  | zero => exact hm
  | succ j ih =>
    rw [ray_succ]
    exact Nat.lt_of_lt_of_le ih (nextIndex_ge _ _ _ _)

/-- Under the period condition, successive indices are distinct and increasing. -/
theorem ray_strict_step {A B c m : Nat} (hfactor : 1 < A*c+1)
    (hm : 0 < m) (j : Nat) : ray A B c m j < ray A B c m (j+1) := by
  rw [ray_succ]
  exact nextIndex_gt hfactor (ray_positive hm j)

end Collatz.Exploration.AffineRay
