import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0509

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 634. -/
theorem bounds_13_634 : exactInterval 13 634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_634 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 634) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_634 : oddCount 634 13 = 5 ∧ acceleratedOrbit 13 634 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_634 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 634) = 3 ^ 5 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_634.1, data_13_634.2]

/-- Complete interval computation for depth 13, residue 635. -/
theorem bounds_13_635 : exactInterval 13 635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_635 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 635) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_635 : oddCount 635 13 = 8 ∧ acceleratedOrbit 13 635 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_635 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 635) = 3 ^ 8 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_635.1, data_13_635.2]

/-- Complete interval computation for depth 13, residue 636. -/
theorem bounds_13_636 : exactInterval 13 636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_636 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 636) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_636 : oddCount 636 13 = 10 ∧ acceleratedOrbit 13 636 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_636 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 636) = 3 ^ 10 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_636.1, data_13_636.2]

/-- Complete interval computation for depth 13, residue 637. -/
theorem bounds_13_637 : exactInterval 13 637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_637 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 637) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_637 : oddCount 637 13 = 10 ∧ acceleratedOrbit 13 637 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_637 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 637) = 3 ^ 10 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_637.1, data_13_637.2]

/-- Complete interval computation for depth 13, residue 638. -/
theorem bounds_13_638 : exactInterval 13 638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_638 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 638) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_638 : oddCount 638 13 = 10 ∧ acceleratedOrbit 13 638 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_638 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 638) = 3 ^ 10 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_638.1, data_13_638.2]

/-- Complete interval computation for depth 13, residue 639. -/
theorem bounds_13_639 : exactInterval 13 639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_639 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 639) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_639 : oddCount 639 13 = 11 ∧ acceleratedOrbit 13 639 = 13841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_639 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 639) = 3 ^ 11 * m + 13841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_639.1, data_13_639.2]

/-- Complete interval computation for depth 13, residue 640. -/
theorem bounds_13_640 : exactInterval 13 640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_640 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 640) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_640 : oddCount 640 13 = 2 ∧ acceleratedOrbit 13 640 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_640 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 640) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_640.1, data_13_640.2]

/-- Complete interval computation for depth 13, residue 641. -/
theorem bounds_13_641 : exactInterval 13 641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_641 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 641) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_641 : oddCount 641 13 = 7 ∧ acceleratedOrbit 13 641 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_641 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 641) = 3 ^ 7 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_641.1, data_13_641.2]

/-- Complete interval computation for depth 13, residue 642. -/
theorem bounds_13_642 : exactInterval 13 642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_642 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 642) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_642 : oddCount 642 13 = 5 ∧ acceleratedOrbit 13 642 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_642 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 642) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_642.1, data_13_642.2]

/-- Complete interval computation for depth 13, residue 643. -/
theorem bounds_13_643 : exactInterval 13 643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_643 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 643) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_643 : oddCount 643 13 = 5 ∧ acceleratedOrbit 13 643 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_643 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 643) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_643.1, data_13_643.2]

/-- Complete interval computation for depth 13, residue 644. -/
theorem bounds_13_644 : exactInterval 13 644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_644 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 644) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_644 : oddCount 644 13 = 7 ∧ acceleratedOrbit 13 644 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_644 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 644) = 3 ^ 7 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_644.1, data_13_644.2]

/-- Complete interval computation for depth 13, residue 645. -/
theorem bounds_13_645 : exactInterval 13 645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_645 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 645) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_645 : oddCount 645 13 = 7 ∧ acceleratedOrbit 13 645 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_645 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 645) = 3 ^ 7 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_645.1, data_13_645.2]

/-- Complete interval computation for depth 13, residue 646. -/
theorem bounds_13_646 : exactInterval 13 646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_646 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 646) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_646 : oddCount 646 13 = 7 ∧ acceleratedOrbit 13 646 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_646 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 646) = 3 ^ 7 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_646.1, data_13_646.2]

/-- Complete interval computation for depth 13, residue 647. -/
theorem bounds_13_647 : exactInterval 13 647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_647 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 647) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_647 : oddCount 647 13 = 6 ∧ acceleratedOrbit 13 647 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_647 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 647) = 3 ^ 6 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_647.1, data_13_647.2]

/-- Complete interval computation for depth 13, residue 648. -/
theorem bounds_13_648 : exactInterval 13 648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_648 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 648) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_648 : oddCount 648 13 = 5 ∧ acceleratedOrbit 13 648 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_648 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 648) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_648.1, data_13_648.2]

/-- Complete interval computation for depth 13, residue 649. -/
theorem bounds_13_649 : exactInterval 13 649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_649 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 649) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_649 : oddCount 649 13 = 9 ∧ acceleratedOrbit 13 649 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_649 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 649) = 3 ^ 9 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_649.1, data_13_649.2]

end Collatz.Research.StoppingAtlas.Batch0509
