import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0109

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 634. -/
theorem bounds_11_634 : exactInterval 11 634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_634 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 634) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_634 : oddCount 634 11 = 5 ∧ acceleratedOrbit 11 634 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_634 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 634) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_634.1, data_11_634.2]

/-- Complete interval computation for depth 11, residue 635. -/
theorem bounds_11_635 : exactInterval 11 635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_635 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 635) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_635 : oddCount 635 11 = 6 ∧ acceleratedOrbit 11 635 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_635 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 635) = 3 ^ 6 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_635.1, data_11_635.2]

/-- Complete interval computation for depth 11, residue 636. -/
theorem bounds_11_636 : exactInterval 11 636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_636 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 636) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_636 : oddCount 636 11 = 8 ∧ acceleratedOrbit 11 636 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_636 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 636) = 3 ^ 8 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_636.1, data_11_636.2]

/-- Complete interval computation for depth 11, residue 637. -/
theorem bounds_11_637 : exactInterval 11 637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_637 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 637) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_637 : oddCount 637 11 = 8 ∧ acceleratedOrbit 11 637 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_637 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 637) = 3 ^ 8 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_637.1, data_11_637.2]

/-- Complete interval computation for depth 11, residue 638. -/
theorem bounds_11_638 : exactInterval 11 638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_638 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 638) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_638 : oddCount 638 11 = 8 ∧ acceleratedOrbit 11 638 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_638 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 638) = 3 ^ 8 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_638.1, data_11_638.2]

/-- Complete interval computation for depth 11, residue 639. -/
theorem bounds_11_639 : exactInterval 11 639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_639 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 639) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_639 : oddCount 639 11 = 9 ∧ acceleratedOrbit 11 639 = 6151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_639 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 639) = 3 ^ 9 * m + 6151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_639.1, data_11_639.2]

/-- Complete interval computation for depth 11, residue 640. -/
theorem bounds_11_640 : exactInterval 11 640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_640 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 640) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_640 : oddCount 640 11 = 1 ∧ acceleratedOrbit 11 640 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_640 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 640) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_640.1, data_11_640.2]

/-- Complete interval computation for depth 11, residue 641. -/
theorem bounds_11_641 : exactInterval 11 641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_641 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 641) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_641 : oddCount 641 11 = 7 ∧ acceleratedOrbit 11 641 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_641 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 641) = 3 ^ 7 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_641.1, data_11_641.2]

/-- Complete interval computation for depth 11, residue 642. -/
theorem bounds_11_642 : exactInterval 11 642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_642 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 642) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_642 : oddCount 642 11 = 4 ∧ acceleratedOrbit 11 642 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_642 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 642) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_642.1, data_11_642.2]

/-- Complete interval computation for depth 11, residue 643. -/
theorem bounds_11_643 : exactInterval 11 643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_643 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 643) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_643 : oddCount 643 11 = 4 ∧ acceleratedOrbit 11 643 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_643 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 643) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_643.1, data_11_643.2]

/-- Complete interval computation for depth 11, residue 644. -/
theorem bounds_11_644 : exactInterval 11 644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_644 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 644) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_644 : oddCount 644 11 = 6 ∧ acceleratedOrbit 11 644 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_644 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 644) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_644.1, data_11_644.2]

/-- Complete interval computation for depth 11, residue 645. -/
theorem bounds_11_645 : exactInterval 11 645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_645 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 645) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_645 : oddCount 645 11 = 6 ∧ acceleratedOrbit 11 645 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_645 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 645) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_645.1, data_11_645.2]

/-- Complete interval computation for depth 11, residue 646. -/
theorem bounds_11_646 : exactInterval 11 646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_646 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 646) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_646 : oddCount 646 11 = 6 ∧ acceleratedOrbit 11 646 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_646 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 646) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_646.1, data_11_646.2]

/-- Complete interval computation for depth 11, residue 647. -/
theorem bounds_11_647 : exactInterval 11 647 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_647 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 647) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_647 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_647 : oddCount 647 11 = 5 ∧ acceleratedOrbit 11 647 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_647 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 647) = 3 ^ 5 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_647.1, data_11_647.2]

/-- Complete interval computation for depth 11, residue 648. -/
theorem bounds_11_648 : exactInterval 11 648 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_648 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 648) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_648 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_648 : oddCount 648 11 = 5 ∧ acceleratedOrbit 11 648 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_648 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 648) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_648.1, data_11_648.2]

/-- Complete interval computation for depth 11, residue 649. -/
theorem bounds_11_649 : exactInterval 11 649 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_649 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 649) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_649 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_649 : oddCount 649 11 = 7 ∧ acceleratedOrbit 11 649 = 695 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_649 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 649) = 3 ^ 7 * m + 695 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_649.1, data_11_649.2]

end Collatz.Research.StoppingAtlas.Batch0109
