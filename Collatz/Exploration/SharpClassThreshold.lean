import Collatz.Exploration.ContractingClass

/-!
# Exact quotient threshold for contracting classes

The coarse offset threshold m>B can be replaced by the exact integer division
threshold (B-r)/(M-A), provided r≤B. If B<r the exceptional set is empty,
including at index zero. Keeping these cases separate avoids treating truncated
natural subtraction as if it were signed arithmetic.
-/
namespace Collatz.Exploration.SharpClassThreshold

open ContractingClass Congruence OrbitFloor TimeChange

/-- Last possible nondecreasing index when the input offset does not exceed the
endpoint offset. The specification below requires a strictly contracting slope. -/
def exceptionLimit (A M B r : Nat) : Nat := (B-r)/(M-A)

/-- With ordered offsets, nondecreasing endpoints occupy exactly an initial
integer interval, not merely some unspecified finite set. -/
theorem nondrop_index_iff {A M B r m : Nat} (hs : A < M) (hr : r ≤ B) :
    M*m+r ≤ A*m+B ↔ m ≤ exceptionLimit A M B r := by
  rw [affine_nondrop_iff (Nat.le_of_lt hs)]
  unfold exceptionLimit
  rw [Nat.le_div_iff_mul_le (show 0 < M-A by omega), Nat.mul_comm m (M-A)]
  omega

/-- When the endpoint offset is smaller, every index descends. -/
theorem all_indices_drop {A M B r : Nat} (hs : A ≤ M) (hr : B < r) (m : Nat) :
    A*m+B < M*m+r := by
  have hh := Nat.mul_le_mul_right m hs
  omega

/-- The sharp division threshold is itself bounded by the earlier offset bound. -/
theorem exceptionLimit_le_offset {A M B r : Nat} (_hs : A < M) :
    exceptionLimit A M B r ≤ B := by
  unfold exceptionLimit
  exact Nat.le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)

/-- Exact descent criterion under ordered offsets. -/
theorem drop_index_iff {A M B r m : Nat} (hs : A < M) (hr : r ≤ B) :
    A*m+B < M*m+r ↔ exceptionLimit A M B r < m := by
  have hh := nondrop_index_iff (m := m) hs hr
  omega

/-- Exact contracting-parity-class descent test, expressed only in its finite
prefix data and the affine input index. -/
theorem class_drop_index_iff {k r m : Nat} (hs : 3^(oddCount r k) < 2^k)
    (hr : r ≤ acceleratedOrbit k r) :
    acceleratedOrbit k (2^k*m+r) < 2^k*m+r ↔
      exceptionLimit (3^(oddCount r k)) (2^k) (acceleratedOrbit k r) r < m := by
  rw [accOrbit_pow_two_mul_add]
  exact drop_index_iff hs hr

/-- If the representative itself descends and the slope is no larger than one,
all its dyadic translates descend after the same prefix. -/
theorem representative_drop_extends {k r : Nat} (hs : 3^(oddCount r k) ≤ 2^k)
    (hr : acceleratedOrbit k r < r) (m : Nat) :
    acceleratedOrbit k (2^k*m+r) < 2^k*m+r := by
  rw [accOrbit_pow_two_mul_add]
  exact all_indices_drop hs hr m

/-- A hypothetical floor in a strictly contracting class forces ordered offsets
and an index in the exact exceptional interval. -/
theorem floor_sharp_bound {k r m : Nat} (hs : 3^(oddCount r k) < 2^k)
    (hf : Floor (2^k*m+r)) : r ≤ acceleratedOrbit k r ∧
      m ≤ exceptionLimit (3^(oddCount r k)) (2^k) (acceleratedOrbit k r) r := by
  have hn := ((floor_iff _).mp hf).2 k
  have hd := (class_nondrop_iff (Nat.le_of_lt hs)).mp hn
  have hr : r ≤ acceleratedOrbit k r := by omega
  refine ⟨hr, ?_⟩
  rw [accOrbit_pow_two_mul_add] at hn
  exact (nondrop_index_iff hs hr).mp hn

end Collatz.Exploration.SharpClassThreshold
