import Collatz.Exploration.PeriodQuotient

/-!
# Infinite convergent rays in a fixed dyadic class

A single positive affine match determines an executable sequence of inputs.
Every input follows the same accelerated prefix and reaches a power of two.
The endpoint exponent rises by a full ternary period at each iteration. The
inputs strictly increase and retain their requested residue modulo 2^k.

These are explicit convergent families, not an exhaustive parametrization of
convergent numbers. In particular, the ray construction imposes no conclusion
on other members of its residue class.
-/
namespace Collatz.Exploration.InverseClassRay

open AffineRay PeriodQuotient ExponentSearch ComputedClassWitness
open HalvingBlocks TimeChange Congruence OrbitFloor

/-- The input obtained from the j-th transported affine index. -/
def rayInput (k r m j : Nat) : Nat :=
  2^k*ray (3^(oddCount r k)) (acceleratedOrbit k r)
    (periodQuotient (oddCount r k)) m j+r

/-- Every member has the same dyadic residue. -/
theorem rayInput_residue (k r m j : Nat) :
    rayInput k r m j%2^k = r%2^k := by
  unfold rayInput
  simp [Nat.add_mod]

/-- Matching endpoints advance by exactly one ternary period per ray step. -/
theorem rayInput_endpoint {k r m e : Nat}
    (h : 3^(oddCount r k)*m+acceleratedOrbit k r = 2^e) (j : Nat) :
    acceleratedOrbit k (rayInput k r m j) =
      2^(periodLength (oddCount r k)*j+e) := by
  unfold rayInput
  rw [accOrbit_pow_two_mul_add]
  exact power_ray (periodQuotient_exact _) h j

/-- The explicit successful time consists of the retained prefix clock and the
terminal halving exponent. -/
theorem rayInput_hits {k r m e : Nat}
    (h : 3^(oddCount r k)*m+acceleratedOrbit k r = 2^e) (j : Nat) :
    orbit (periodLength (oddCount r k)*j+e+clock (rayInput k r m j) k)
      (rayInput k r m j) = 1 := endpoint_hits (rayInput_endpoint h j)

/-- Every member in the ray converges; this theorem does not need positivity
because the endpoint identity already forces a nonzero orbit. -/
theorem rayInput_converges {k r m e : Nat}
    (h : 3^(oddCount r k)*m+acceleratedOrbit k r = 2^e) (j : Nat) :
    Converges (rayInput k r m j) := by
  exact ⟨_, rayInput_hits h j⟩

/-- Positive starting indices produce strictly increasing inputs. -/
theorem rayInput_strict_step {k r m : Nat} (hm : 0 < m) (j : Nat) :
    rayInput k r m j < rayInput k r m (j+1) := by
  have hi := ray_strict_step (A := 3^(oddCount r k))
    (B := acceleratedOrbit k r) (c := periodQuotient (oddCount r k))
    (period_factor_gt_one _) hm j
  have hh := Nat.mul_lt_mul_of_pos_left hi (Nat.two_pow_pos k)
  exact Nat.add_lt_add_right hh r

/-- The successful time grows at most linearly in the ray index. The input
itself grows geometrically, explaining why an infinite family can be sparse. -/
theorem rayInput_time_bound {k r m e : Nat}
    (h : 3^(oddCount r k)*m+acceleratedOrbit k r = 2^e) (j : Nat) :
    ∃ t, orbit t (rayInput k r m j) = 1 ∧
      t ≤ 2*k+periodLength (oddCount r k)*j+e := by
  obtain ⟨t, ht, hh⟩ := endpoint_time_bound (rayInput_endpoint h j)
  exact ⟨t, hh, by omega⟩

end Collatz.Exploration.InverseClassRay
