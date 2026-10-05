import Collatz.Strategy.FirstDescentClassComplete

/-!
# Convexity of exact first-descent indices inside a fixed dyadic class

At each depth the orbit is affine in the class index. Every proper-prefix
non-drop condition and the endpoint drop condition is an affine inequality.
Consequently the indices with an exact prescribed first-descent time form
an interval: successful endpoints cannot enclose a failing index.
This permits finite intervals as well as unbounded tails and empty sets.
-/

namespace Collatz.FirstDescentClass

/-- An affine nonstrict comparison holding at both endpoints holds in between. -/
theorem affine_le_between {P C r b lo hi m : Nat}
    (hlo : P * lo + r ≤ C * lo + b) (hhi : P * hi + r ≤ C * hi + b)
    (hml : lo ≤ m) (hmh : m ≤ hi) : P * m + r ≤ C * m + b := by
  by_cases hs : P ≤ C
  · have hc : C = P + (C - P) := by omega
    rw [hc, Nat.add_mul] at hlo ⊢
    have hm := Nat.mul_le_mul_left (C - P) hml
    omega
  · have hp : P = C + (P - C) := by omega
    rw [hp, Nat.add_mul] at hhi ⊢
    have hm := Nat.mul_le_mul_left (P - C) hmh
    omega

/-- A strict affine comparison holding at both endpoints holds in between. -/
theorem affine_lt_between {P C r b lo hi m : Nat}
    (hlo : C * lo + b < P * lo + r) (hhi : C * hi + b < P * hi + r)
    (hml : lo ≤ m) (hmh : m ≤ hi) : C * m + b < P * m + r := by
  have hl : C * lo + (b + 1) ≤ P * lo + r := by omega
  have hh : C * hi + (b + 1) ≤ P * hi + r := by omega
  have hm := affine_le_between hl hh hml hmh
  omega

/-- Exact first-descent times cannot have gaps in the dyadic class index. -/
theorem stoppingTime_between {k r lo hi m : Nat}
    (hlo : stoppingTime (2 ^ k * lo + r) k)
    (hhi : stoppingTime (2 ^ k * hi + r) k)
    (hml : lo ≤ m) (hmh : m ≤ hi) : stoppingTime (2 ^ k * m + r) k := by
  refine ⟨hlo.1, ?_, ?_⟩
  · have hl := hlo.2.1
    have hh := hhi.2.1
    rw [Congruence.accOrbit_pow_two_mul_add] at hl hh ⊢
    exact affine_lt_between hl hh hml hmh
  · intro j _ hj
    have hl := FirstDescentResidue.before_first_descent hlo j hj
    have hh := FirstDescentResidue.before_first_descent hhi j hj
    rw [prefix_orbit (Nat.le_of_lt hj)] at hl hh
    have hm := affine_le_between hl hh hml hmh
    rw [prefix_orbit (Nat.le_of_lt hj)]
    omega

/-- Convexity is equally available through executable exact-time certificates. -/
theorem firstDescentB_between {k r lo hi m : Nat}
    (hlo : Search.firstDescentB (2 ^ k * lo + r) k = true)
    (hhi : Search.firstDescentB (2 ^ k * hi + r) k = true)
    (hml : lo ≤ m) (hmh : m ≤ hi) : Search.firstDescentB (2 ^ k * m + r) k = true := by
  apply (Search.firstDescentB_spec _ _).mpr
  exact stoppingTime_between ((Search.firstDescentB_spec _ _).mp hlo)
    ((Search.firstDescentB_spec _ _).mp hhi) hml hmh

/-- A failed intermediate certificate excludes simultaneous success at both endpoints. -/
theorem failure_excludes_two_endpoints {k r lo hi m : Nat}
    (hfail : Search.firstDescentB (2 ^ k * m + r) k ≠ true)
    (hml : lo ≤ m) (hmh : m ≤ hi) :
    ¬ (Search.firstDescentB (2 ^ k * lo + r) k = true ∧
      Search.firstDescentB (2 ^ k * hi + r) k = true) := by
  rintro ⟨hl, hh⟩
  exact hfail (firstDescentB_between hl hh hml hmh)

/-- A checked pair of finite endpoints certifies every index in the intervening interval. -/
theorem stoppingTime_interval_of_certificates {k r lo hi : Nat}
    (hlo : Search.firstDescentB (2 ^ k * lo + r) k = true)
    (hhi : Search.firstDescentB (2 ^ k * hi + r) k = true) :
    ∀ m : Nat, lo ≤ m → m ≤ hi → stoppingTime (2 ^ k * m + r) k := by
  intro m hml hmh
  exact stoppingTime_between ((Search.firstDescentB_spec _ _).mp hlo)
    ((Search.firstDescentB_spec _ _).mp hhi) hml hmh

end Collatz.FirstDescentClass
