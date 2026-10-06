import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0042

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 629. -/
theorem bounds_10_629 : exactInterval 10 629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_629 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 629) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_629 : oddCount 629 10 = 5 ∧ acceleratedOrbit 10 629 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_629 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 629) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_629.1, data_10_629.2]

/-- Complete interval computation for depth 10, residue 630. -/
theorem bounds_10_630 : exactInterval 10 630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_630 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 630) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_630 : oddCount 630 10 = 4 ∧ acceleratedOrbit 10 630 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_630 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 630) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_630.1, data_10_630.2]

/-- Complete interval computation for depth 10, residue 631. -/
theorem bounds_10_631 : exactInterval 10 631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_631 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 631) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_631 : oddCount 631 10 = 4 ∧ acceleratedOrbit 10 631 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_631 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 631) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_631.1, data_10_631.2]

/-- Complete interval computation for depth 10, residue 632. -/
theorem bounds_10_632 : exactInterval 10 632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_632 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 632) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_632 : oddCount 632 10 = 5 ∧ acceleratedOrbit 10 632 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_632 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 632) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_632.1, data_10_632.2]

/-- Complete interval computation for depth 10, residue 633. -/
theorem bounds_10_633 : exactInterval 10 633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_633 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 633) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_633 : oddCount 633 10 = 6 ∧ acceleratedOrbit 10 633 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_633 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 633) = 3 ^ 6 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_633.1, data_10_633.2]

/-- Complete interval computation for depth 10, residue 634. -/
theorem bounds_10_634 : exactInterval 10 634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_634 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 634) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_634 : oddCount 634 10 = 5 ∧ acceleratedOrbit 10 634 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_634 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 634) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_634.1, data_10_634.2]

/-- Complete interval computation for depth 10, residue 635. -/
theorem bounds_10_635 : exactInterval 10 635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_635 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 635) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_635 : oddCount 635 10 = 5 ∧ acceleratedOrbit 10 635 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_635 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 635) = 3 ^ 5 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_635.1, data_10_635.2]

/-- Complete interval computation for depth 10, residue 636. -/
theorem bounds_10_636 : exactInterval 10 636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_636 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 636) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_636 : oddCount 636 10 = 7 ∧ acceleratedOrbit 10 636 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_636 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 636) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_636.1, data_10_636.2]

/-- Complete interval computation for depth 10, residue 637. -/
theorem bounds_10_637 : exactInterval 10 637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_637 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 637) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_637 : oddCount 637 10 = 7 ∧ acceleratedOrbit 10 637 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_637 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 637) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_637.1, data_10_637.2]

/-- Complete interval computation for depth 10, residue 638. -/
theorem bounds_10_638 : exactInterval 10 638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_638 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 638) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_638 : oddCount 638 10 = 7 ∧ acceleratedOrbit 10 638 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_638 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 638) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_638.1, data_10_638.2]

/-- Complete interval computation for depth 10, residue 639. -/
theorem bounds_10_639 : exactInterval 10 639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_639 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 639) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_639 : oddCount 639 10 = 9 ∧ acceleratedOrbit 10 639 = 12302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_639 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 639) = 3 ^ 9 * m + 12302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_639.1, data_10_639.2]

/-- Complete interval computation for depth 10, residue 640. -/
theorem bounds_10_640 : exactInterval 10 640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_640 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 640) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_640 : oddCount 640 10 = 1 ∧ acceleratedOrbit 10 640 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_640 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 640) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_640.1, data_10_640.2]

/-- Complete interval computation for depth 10, residue 641. -/
theorem bounds_10_641 : exactInterval 10 641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_641 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 641) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_641 : oddCount 641 10 = 7 ∧ acceleratedOrbit 10 641 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_641 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 641) = 3 ^ 7 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_641.1, data_10_641.2]

/-- Complete interval computation for depth 10, residue 642. -/
theorem bounds_10_642 : exactInterval 10 642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_642 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 642) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_642 : oddCount 642 10 = 3 ∧ acceleratedOrbit 10 642 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_642 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 642) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_642.1, data_10_642.2]

/-- Complete interval computation for depth 10, residue 643. -/
theorem bounds_10_643 : exactInterval 10 643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_643 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 643) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_643 : oddCount 643 10 = 3 ∧ acceleratedOrbit 10 643 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_643 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 643) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_643.1, data_10_643.2]

/-- Complete interval computation for depth 10, residue 644. -/
theorem bounds_10_644 : exactInterval 10 644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_644 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 644) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_644 : oddCount 644 10 = 5 ∧ acceleratedOrbit 10 644 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_644 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 644) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_644.1, data_10_644.2]

end Collatz.Research.StoppingAtlas.Batch0042
