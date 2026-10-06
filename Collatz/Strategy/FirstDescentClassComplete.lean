import Collatz.Strategy.FirstDescentClass

/-!
# Completeness of the complete-class first-descent checker

If every member `2^k*m+r` has the same first-descent time k, then every
proper prefix multiplier is noncontracting and the endpoint multiplier
contracts. Thus the finite checker is equivalent to the universal class
statement, not just a sufficient condition. This does not prove that these
classes cover all positive integers at an input-dependent depth.
-/

namespace Collatz.FirstDescentClass

/-- A lower affine comparison for every natural index forces a slope comparison. -/
theorem slope_ge_of_all_ge {P C r b : Nat}
    (h : ∀ m : Nat, P * m + r ≤ C * m + b) : P ≤ C := by
  by_cases hle : P ≤ C
  · exact hle
  · have hs : C + 1 ≤ P := by omega
    have hm := Nat.mul_le_mul_right (b + 1) hs
    rw [Nat.add_mul, Nat.one_mul] at hm
    have hb := h (b + 1)
    omega

/-- A strict upper affine comparison for every natural index bounds its slope. -/
theorem slope_le_of_all_lt {P C r b : Nat}
    (h : ∀ m : Nat, C * m + b < P * m + r) : C ≤ P := by
  by_cases hle : C ≤ P
  · exact hle
  · have hs : P + 1 ≤ C := by omega
    have hm := Nat.mul_le_mul_right (r + 1) hs
    rw [Nat.add_mul, Nat.one_mul] at hm
    have hb := h (r + 1)
    omega

/-- Fixed first descent of every class member supplies the base first descent. -/
theorem base_of_universal {k r : Nat}
    (h : ∀ m : Nat, stoppingTime (2 ^ k * m + r) k) : stoppingTime r k := by
  simpa only [Nat.mul_zero, Nat.zero_add] using h 0

/-- Fixed first descent of the whole class forces a nonlarger endpoint slope. -/
theorem endpoint_slope_le_of_universal {k r : Nat}
    (h : ∀ m : Nat, stoppingTime (2 ^ k * m + r) k) : 3 ^ oddCount r k ≤ 2 ^ k := by
  apply slope_le_of_all_lt (r := r) (b := acceleratedOrbit k r)
  intro m
  have hd := (h m).2.1
  rw [Congruence.accOrbit_pow_two_mul_add] at hd
  exact hd

/-- Powers of three cannot equal the positive-depth power-of-two denominator. -/
theorem endpoint_slope_ne {k r : Nat} (hk : 0 < k) : 3 ^ oddCount r k ≠ 2 ^ k := by
  intro heq
  have ho := Arith.three_pow_odd (oddCount r k)
  have he := Arith.two_pow_even hk
  rw [heq] at ho
  omega

/-- The endpoint slope is strictly contracting, rather than only nonlarger. -/
theorem endpoint_contracts_of_universal {k r : Nat}
    (h : ∀ m : Nat, stoppingTime (2 ^ k * m + r) k) : 3 ^ oddCount r k < 2 ^ k := by
  have hs := endpoint_slope_le_of_universal h
  have hbase := base_of_universal h
  have hne := endpoint_slope_ne (r := r) (show 0 < k by have := hbase.1; omega)
  omega

/-- Every proper prefix of a universally fixed-time class has a noncontracting slope. -/
theorem prefix_heavy_of_universal {k r : Nat}
    (h : ∀ m : Nat, stoppingTime (2 ^ k * m + r) k) (j : Nat) (hj : j < k) :
    2 ^ j ≤ 3 ^ oddCount r j := by
  have hscaled : 2 ^ k ≤ 3 ^ oddCount r j * 2 ^ (k - j) := by
    apply slope_ge_of_all_ge (r := r) (b := acceleratedOrbit j r)
    intro m
    have hp := FirstDescentResidue.before_first_descent (h m) j hj
    rw [prefix_orbit (Nat.le_of_lt hj)] at hp
    exact hp
  rw [split_modulus (Nat.le_of_lt hj)] at hscaled
  by_cases hle : 2 ^ j ≤ 3 ^ oddCount r j
  · exact hle
  · have hlt : 3 ^ oddCount r j < 2 ^ j := by omega
    have hprod := Nat.mul_lt_mul_of_lt_of_le hlt (Nat.le_refl (2 ^ (k - j)))
      (Nat.pow_pos (by decide : 0 < (2 : Nat)))
    omega

/-- Universal exact first descent is recognized by the finite certificate. -/
theorem classCertificate_of_universal {k r : Nat}
    (h : ∀ m : Nat, stoppingTime (2 ^ k * m + r) k) : classCertificateB k r = true := by
  apply (classCertificateB_spec k r).mpr
  exact ⟨endpoint_contracts_of_universal h, base_of_universal h, prefix_heavy_of_universal h⟩

/-- Exact equivalence between a finite computation and the full infinite class statement. -/
theorem classCertificate_iff_universal (k r : Nat) :
    classCertificateB k r = true ↔ ∀ m : Nat, stoppingTime (2 ^ k * m + r) k :=
  ⟨fun h m => stoppingTime_of_classCertificate h m, classCertificate_of_universal⟩

/-- Failure of the checker rules out a universally fixed first-descent time. -/
theorem not_universal_of_certificate_failure {k r : Nat} (h : classCertificateB k r ≠ true) :
    ¬ ∀ m : Nat, stoppingTime (2 ^ k * m + r) k := by
  intro hall
  exact h (classCertificate_of_universal hall)

end Collatz.FirstDescentClass
