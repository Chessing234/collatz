import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0447

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 14614. -/
theorem bounds_15_14614 : exactInterval 15 14614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14614 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14614) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14614 : oddCount 14614 15 = 7 ∧ acceleratedOrbit 15 14614 = 976 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14614 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14614) = 3 ^ 7 * m + 976 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14614.1, data_15_14614.2]

/-- Complete interval computation for depth 15, residue 14615. -/
theorem bounds_15_14615 : exactInterval 15 14615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14615 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14615) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14615 : oddCount 14615 15 = 7 ∧ acceleratedOrbit 15 14615 = 976 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14615 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14615) = 3 ^ 7 * m + 976 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14615.1, data_15_14615.2]

/-- Complete interval computation for depth 15, residue 14616. -/
theorem bounds_15_14616 : exactInterval 15 14616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14616 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14616) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14616 : oddCount 14616 15 = 5 ∧ acceleratedOrbit 15 14616 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14616 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14616) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14616.1, data_15_14616.2]

/-- Complete interval computation for depth 15, residue 14617. -/
theorem bounds_15_14617 : exactInterval 15 14617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14617 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14617) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14617 : oddCount 14617 15 = 7 ∧ acceleratedOrbit 15 14617 = 976 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14617 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14617) = 3 ^ 7 * m + 976 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14617.1, data_15_14617.2]

/-- Complete interval computation for depth 15, residue 14618. -/
theorem bounds_15_14618 : exactInterval 15 14618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14618 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14618) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14618 : oddCount 14618 15 = 5 ∧ acceleratedOrbit 15 14618 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14618 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14618) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14618.1, data_15_14618.2]

/-- Complete interval computation for depth 15, residue 14619. -/
theorem bounds_15_14619 : exactInterval 15 14619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14619 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14619) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14619 : oddCount 14619 15 = 10 ∧ acceleratedOrbit 15 14619 = 26347 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14619 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14619) = 3 ^ 10 * m + 26347 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14619.1, data_15_14619.2]

/-- Complete interval computation for depth 15, residue 14620. -/
theorem bounds_15_14620 : exactInterval 15 14620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14620 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14620) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14620 : oddCount 14620 15 = 8 ∧ acceleratedOrbit 15 14620 = 2929 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14620 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14620) = 3 ^ 8 * m + 2929 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14620.1, data_15_14620.2]

/-- Complete interval computation for depth 15, residue 14621. -/
theorem bounds_15_14621 : exactInterval 15 14621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14621 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14621) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14621 : oddCount 14621 15 = 8 ∧ acceleratedOrbit 15 14621 = 2929 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14621 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14621) = 3 ^ 8 * m + 2929 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14621.1, data_15_14621.2]

/-- Complete interval computation for depth 15, residue 14622. -/
theorem bounds_15_14622 : exactInterval 15 14622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14622 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14622) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14622 : oddCount 14622 15 = 8 ∧ acceleratedOrbit 15 14622 = 2929 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14622 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14622) = 3 ^ 8 * m + 2929 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14622.1, data_15_14622.2]

/-- Complete interval computation for depth 15, residue 14623. -/
theorem bounds_15_14623 : exactInterval 15 14623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14623 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14623) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14623 : oddCount 14623 15 = 9 ∧ acceleratedOrbit 15 14623 = 8785 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14623 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14623) = 3 ^ 9 * m + 8785 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14623.1, data_15_14623.2]

/-- Complete interval computation for depth 15, residue 14624. -/
theorem bounds_15_14624 : exactInterval 15 14624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14624 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14624) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14624 : oddCount 14624 15 = 5 ∧ acceleratedOrbit 15 14624 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14624 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14624) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14624.1, data_15_14624.2]

/-- Complete interval computation for depth 15, residue 14625. -/
theorem bounds_15_14625 : exactInterval 15 14625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14625 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14625) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14625 : oddCount 14625 15 = 6 ∧ acceleratedOrbit 15 14625 = 326 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14625 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14625) = 3 ^ 6 * m + 326 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14625.1, data_15_14625.2]

/-- Complete interval computation for depth 15, residue 14626. -/
theorem bounds_15_14626 : exactInterval 15 14626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14626 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14626) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14626 : oddCount 14626 15 = 7 ∧ acceleratedOrbit 15 14626 = 977 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14626 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14626) = 3 ^ 7 * m + 977 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14626.1, data_15_14626.2]

/-- Complete interval computation for depth 15, residue 14627. -/
theorem bounds_15_14627 : exactInterval 15 14627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14627 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14627) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14627 : oddCount 14627 15 = 7 ∧ acceleratedOrbit 15 14627 = 977 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14627 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14627) = 3 ^ 7 * m + 977 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14627.1, data_15_14627.2]

/-- Complete interval computation for depth 15, residue 14628. -/
theorem bounds_15_14628 : exactInterval 15 14628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14628 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14628) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14628 : oddCount 14628 15 = 7 ∧ acceleratedOrbit 15 14628 = 977 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14628 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14628) = 3 ^ 7 * m + 977 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14628.1, data_15_14628.2]

/-- Complete interval computation for depth 15, residue 14629. -/
theorem bounds_15_14629 : exactInterval 15 14629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14629 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14629) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14629 : oddCount 14629 15 = 7 ∧ acceleratedOrbit 15 14629 = 977 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14629 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14629) = 3 ^ 7 * m + 977 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14629.1, data_15_14629.2]

/-- Complete interval computation for depth 15, residue 14630. -/
theorem bounds_15_14630 : exactInterval 15 14630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14630 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14630) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14630 : oddCount 14630 15 = 7 ∧ acceleratedOrbit 15 14630 = 977 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14630 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14630) = 3 ^ 7 * m + 977 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14630.1, data_15_14630.2]

/-- Complete interval computation for depth 15, residue 14631. -/
theorem bounds_15_14631 : exactInterval 15 14631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14631 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14631) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14631 : oddCount 14631 15 = 8 ∧ acceleratedOrbit 15 14631 = 2930 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14631 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14631) = 3 ^ 8 * m + 2930 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14631.1, data_15_14631.2]

/-- Complete interval computation for depth 15, residue 14632. -/
theorem bounds_15_14632 : exactInterval 15 14632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14632 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14632) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14632 : oddCount 14632 15 = 5 ∧ acceleratedOrbit 15 14632 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14632 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14632) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14632.1, data_15_14632.2]

/-- Complete interval computation for depth 15, residue 14633. -/
theorem bounds_15_14633 : exactInterval 15 14633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14633 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14633) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14633 : oddCount 14633 15 = 9 ∧ acceleratedOrbit 15 14633 = 8792 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14633 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14633) = 3 ^ 9 * m + 8792 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14633.1, data_15_14633.2]

/-- Complete interval computation for depth 15, residue 14634. -/
theorem bounds_15_14634 : exactInterval 15 14634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14634 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14634) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14634 : oddCount 14634 15 = 5 ∧ acceleratedOrbit 15 14634 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14634 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14634) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14634.1, data_15_14634.2]

/-- Complete interval computation for depth 15, residue 14635. -/
theorem bounds_15_14635 : exactInterval 15 14635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14635 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14635) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14635 : oddCount 14635 15 = 7 ∧ acceleratedOrbit 15 14635 = 977 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14635 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14635) = 3 ^ 7 * m + 977 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14635.1, data_15_14635.2]

/-- Complete interval computation for depth 15, residue 14636. -/
theorem bounds_15_14636 : exactInterval 15 14636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14636 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14636) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14636 : oddCount 14636 15 = 5 ∧ acceleratedOrbit 15 14636 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14636 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14636) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14636.1, data_15_14636.2]

/-- Complete interval computation for depth 15, residue 14637. -/
theorem bounds_15_14637 : exactInterval 15 14637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14637 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14637) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14637 : oddCount 14637 15 = 5 ∧ acceleratedOrbit 15 14637 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14637 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14637) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14637.1, data_15_14637.2]

/-- Complete interval computation for depth 15, residue 14638. -/
theorem bounds_15_14638 : exactInterval 15 14638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14638 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14638) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14638 : oddCount 14638 15 = 5 ∧ acceleratedOrbit 15 14638 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14638 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14638) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14638.1, data_15_14638.2]

/-- Complete interval computation for depth 15, residue 14639. -/
theorem bounds_15_14639 : exactInterval 15 14639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14639 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14639) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14639 : oddCount 14639 15 = 9 ∧ acceleratedOrbit 15 14639 = 8795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14639 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14639) = 3 ^ 9 * m + 8795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14639.1, data_15_14639.2]

/-- Complete interval computation for depth 15, residue 14640. -/
theorem bounds_15_14640 : exactInterval 15 14640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14640 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14640) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14640 : oddCount 14640 15 = 5 ∧ acceleratedOrbit 15 14640 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14640 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14640) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14640.1, data_15_14640.2]

/-- Complete interval computation for depth 15, residue 14641. -/
theorem bounds_15_14641 : exactInterval 15 14641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14641 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14641) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14641 : oddCount 14641 15 = 6 ∧ acceleratedOrbit 15 14641 = 326 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14641 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14641) = 3 ^ 6 * m + 326 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14641.1, data_15_14641.2]

/-- Complete interval computation for depth 15, residue 14642. -/
theorem bounds_15_14642 : exactInterval 15 14642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14642 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14642) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14642 : oddCount 14642 15 = 6 ∧ acceleratedOrbit 15 14642 = 326 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14642 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14642) = 3 ^ 6 * m + 326 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14642.1, data_15_14642.2]

/-- Complete interval computation for depth 15, residue 14643. -/
theorem bounds_15_14643 : exactInterval 15 14643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14643 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14643) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14643 : oddCount 14643 15 = 6 ∧ acceleratedOrbit 15 14643 = 326 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14643 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14643) = 3 ^ 6 * m + 326 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14643.1, data_15_14643.2]

/-- Complete interval computation for depth 15, residue 14644. -/
theorem bounds_15_14644 : exactInterval 15 14644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14644 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14644) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14644 : oddCount 14644 15 = 5 ∧ acceleratedOrbit 15 14644 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14644 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14644) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14644.1, data_15_14644.2]

/-- Complete interval computation for depth 15, residue 14645. -/
theorem bounds_15_14645 : exactInterval 15 14645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14645 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14645) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14645 : oddCount 14645 15 = 5 ∧ acceleratedOrbit 15 14645 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14645 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14645) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14645.1, data_15_14645.2]

/-- Complete interval computation for depth 15, residue 14646. -/
theorem bounds_15_14646 : exactInterval 15 14646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14646 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14646) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14646 : oddCount 14646 15 = 10 ∧ acceleratedOrbit 15 14646 = 26399 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14646 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14646) = 3 ^ 10 * m + 26399 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14646.1, data_15_14646.2]

end Collatz.Research.PassageAtlas.Batch0447
