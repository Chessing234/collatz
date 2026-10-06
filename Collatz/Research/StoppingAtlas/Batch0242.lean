import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0242

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 629. -/
theorem bounds_12_629 : exactInterval 12 629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_629 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 629) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_629 : oddCount 629 12 = 5 ∧ acceleratedOrbit 12 629 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_629 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 629) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_629.1, data_12_629.2]

/-- Complete interval computation for depth 12, residue 630. -/
theorem bounds_12_630 : exactInterval 12 630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_630 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 630) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_630 : oddCount 630 12 = 5 ∧ acceleratedOrbit 12 630 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_630 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 630) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_630.1, data_12_630.2]

/-- Complete interval computation for depth 12, residue 631. -/
theorem bounds_12_631 : exactInterval 12 631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_631 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 631) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_631 : oddCount 631 12 = 5 ∧ acceleratedOrbit 12 631 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_631 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 631) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_631.1, data_12_631.2]

/-- Complete interval computation for depth 12, residue 632. -/
theorem bounds_12_632 : exactInterval 12 632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_632 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 632) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_632 : oddCount 632 12 = 5 ∧ acceleratedOrbit 12 632 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_632 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 632) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_632.1, data_12_632.2]

/-- Complete interval computation for depth 12, residue 633. -/
theorem bounds_12_633 : exactInterval 12 633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_633 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 633) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_633 : oddCount 633 12 = 6 ∧ acceleratedOrbit 12 633 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_633 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 633) = 3 ^ 6 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_633.1, data_12_633.2]

/-- Complete interval computation for depth 12, residue 634. -/
theorem bounds_12_634 : exactInterval 12 634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_634 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 634) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_634 : oddCount 634 12 = 5 ∧ acceleratedOrbit 12 634 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_634 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 634) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_634.1, data_12_634.2]

/-- Complete interval computation for depth 12, residue 635. -/
theorem bounds_12_635 : exactInterval 12 635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_635 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 635) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_635 : oddCount 635 12 = 7 ∧ acceleratedOrbit 12 635 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_635 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 635) = 3 ^ 7 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_635.1, data_12_635.2]

/-- Complete interval computation for depth 12, residue 636. -/
theorem bounds_12_636 : exactInterval 12 636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_636 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 636) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_636 : oddCount 636 12 = 9 ∧ acceleratedOrbit 12 636 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_636 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 636) = 3 ^ 9 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_636.1, data_12_636.2]

/-- Complete interval computation for depth 12, residue 637. -/
theorem bounds_12_637 : exactInterval 12 637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_637 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 637) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_637 : oddCount 637 12 = 9 ∧ acceleratedOrbit 12 637 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_637 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 637) = 3 ^ 9 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_637.1, data_12_637.2]

/-- Complete interval computation for depth 12, residue 638. -/
theorem bounds_12_638 : exactInterval 12 638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_638 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 638) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_638 : oddCount 638 12 = 9 ∧ acceleratedOrbit 12 638 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_638 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 638) = 3 ^ 9 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_638.1, data_12_638.2]

/-- Complete interval computation for depth 12, residue 639. -/
theorem bounds_12_639 : exactInterval 12 639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_639 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 639) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_639 : oddCount 639 12 = 10 ∧ acceleratedOrbit 12 639 = 9227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_639 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 639) = 3 ^ 10 * m + 9227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_639.1, data_12_639.2]

/-- Complete interval computation for depth 12, residue 640. -/
theorem bounds_12_640 : exactInterval 12 640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_640 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 640) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_640 : oddCount 640 12 = 2 ∧ acceleratedOrbit 12 640 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_640 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 640) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_640.1, data_12_640.2]

/-- Complete interval computation for depth 12, residue 641. -/
theorem bounds_12_641 : exactInterval 12 641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_641 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 641) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_641 : oddCount 641 12 = 7 ∧ acceleratedOrbit 12 641 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_641 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 641) = 3 ^ 7 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_641.1, data_12_641.2]

/-- Complete interval computation for depth 12, residue 642. -/
theorem bounds_12_642 : exactInterval 12 642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_642 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 642) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_642 : oddCount 642 12 = 4 ∧ acceleratedOrbit 12 642 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_642 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 642) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_642.1, data_12_642.2]

/-- Complete interval computation for depth 12, residue 643. -/
theorem bounds_12_643 : exactInterval 12 643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_643 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 643) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_643 : oddCount 643 12 = 4 ∧ acceleratedOrbit 12 643 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_643 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 643) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_643.1, data_12_643.2]

/-- Complete interval computation for depth 12, residue 644. -/
theorem bounds_12_644 : exactInterval 12 644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_644 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 644) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_644 : oddCount 644 12 = 7 ∧ acceleratedOrbit 12 644 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_644 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 644) = 3 ^ 7 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_644.1, data_12_644.2]

end Collatz.Research.StoppingAtlas.Batch0242
