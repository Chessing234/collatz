import Collatz.Exploration.RayEnumeration

/-!
# Finite exceptions in a contracting parity class

For an accelerated prefix with affine formula A*m+B and input M*m+r,
A<M makes descent automatic beyond a finite threshold. More precisely, failure
to descend forces (M-A)*m+r ≤ B. The exact inequality identifies the finite
exceptional indices rather than silently discarding the offset.

This is a local criterion useful in universal-descent searches. A global proof
would still have to cover all nontrivial inputs by such successful prefixes or
handle the remaining classes by another argument.
-/
namespace Collatz.Exploration.ContractingClass

open Congruence OrbitFloor TimeChange

/-- Clearing the affine input from a nondecreasing endpoint gives the exact
exception inequality, without rational slopes or natural subtraction errors. -/
theorem affine_nondrop_iff {A M B r m : Nat} (h : A ≤ M) :
    M*m+r ≤ A*m+B ↔ (M-A)*m+r ≤ B := by
  have he : A*m+(M-A)*m = M*m := by
    rw [← Nat.add_mul, Nat.add_sub_of_le h]
  omega

/-- If the slope contracts, exceptional indices are bounded by the offset. -/
theorem affine_exception_bound {A M B r m : Nat} (h : A < M)
    (hn : M*m+r ≤ A*m+B) : m ≤ B := by
  have hd := (affine_nondrop_iff (Nat.le_of_lt h)).mp hn
  have hm := Nat.mul_le_mul_right m (show 1 ≤ M-A by omega)
  simp only [Nat.one_mul] at hm
  omega

/-- A simple sufficient threshold for affine descent in a contracting class. -/
theorem affine_drop {A M B r m : Nat} (h : A < M) (hm : B < m) :
    A*m+B < M*m+r := by
  by_cases hn : M*m+r ≤ A*m+B
  · have hb := affine_exception_bound h hn
    omega
  · omega

/-- The exact exceptional-index criterion for a Collatz accelerated prefix. -/
theorem class_nondrop_iff {k r m : Nat} (h : 3^(oddCount r k) ≤ 2^k) :
    2^k*m+r ≤ acceleratedOrbit k (2^k*m+r) ↔
      (2^k-3^(oddCount r k))*m+r ≤ acceleratedOrbit k r := by
  rw [accOrbit_pow_two_mul_add]
  exact affine_nondrop_iff h

/-- Every sufficiently large index in a contracting parity class descends. -/
theorem class_drop {k r m : Nat} (h : 3^(oddCount r k) < 2^k)
    (hm : acceleratedOrbit k r < m) :
    acceleratedOrbit k (2^k*m+r) < 2^k*m+r := by
  rw [accOrbit_pow_two_mul_add]
  exact affine_drop h hm

/-- Such a prefix supplies a bounded standard descent witness. -/
theorem class_standard_drop {k r m : Nat} (h : 3^(oddCount r k) < 2^k)
    (hm : acceleratedOrbit k r < m) :
    ∃ t, k ≤ t ∧ t ≤ 2*k ∧ orbit t (2^k*m+r) < 2^k*m+r :=
  standard_drop_of_accelerated (class_drop h hm)

/-- A hypothetical orbit floor in a contracting class has only finitely many
possible indices. This restriction follows from one prefix alone. -/
theorem floor_index_bound {k r m : Nat} (h : 3^(oddCount r k) < 2^k)
    (hf : Floor (2^k*m+r)) : m ≤ acceleratedOrbit k r := by
  have hn := (floor_iff _).mp hf
  have he := hn.2 k
  rw [accOrbit_pow_two_mul_add] at he
  exact affine_exception_bound h he

/-- Covering every hypothetical floor by a contracting prefix whose index is
past its exceptional threshold would prove Collatz. The coverage assumption is
explicit and is not established by this local calculation. -/
theorem collatz_of_contracting_floor_cover
    (hcover : ∀ n, Floor n → ∃ k r m,
      n = 2^k*m+r ∧ 3^(oddCount r k) < 2^k ∧ acceleratedOrbit k r < m) :
    CollatzConjecture := by
  apply no_floor_iff_collatz.mp
  intro n hn
  obtain ⟨k, r, m, he, hs, hm⟩ := hcover n hn
  rw [he] at hn
  have hb := floor_index_bound hs hn
  omega

end Collatz.Exploration.ContractingClass
