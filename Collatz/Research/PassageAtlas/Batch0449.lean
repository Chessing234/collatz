import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0449

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 14680. -/
theorem bounds_15_14680 : exactInterval 15 14680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14680 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14680) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14680 : oddCount 14680 15 = 5 ∧ acceleratedOrbit 15 14680 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14680 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14680) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14680.1, data_15_14680.2]

/-- Complete interval computation for depth 15, residue 14681. -/
theorem bounds_15_14681 : exactInterval 15 14681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14681 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14681) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14681 : oddCount 14681 15 = 8 ∧ acceleratedOrbit 15 14681 = 2942 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14681 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14681) = 3 ^ 8 * m + 2942 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14681.1, data_15_14681.2]

/-- Complete interval computation for depth 15, residue 14682. -/
theorem bounds_15_14682 : exactInterval 15 14682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14682 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14682) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14682 : oddCount 14682 15 = 5 ∧ acceleratedOrbit 15 14682 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14682 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14682) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14682.1, data_15_14682.2]

/-- Complete interval computation for depth 15, residue 14683. -/
theorem bounds_15_14683 : exactInterval 15 14683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14683 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14683) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14683 : oddCount 14683 15 = 9 ∧ acceleratedOrbit 15 14683 = 8822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14683 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14683) = 3 ^ 9 * m + 8822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14683.1, data_15_14683.2]

/-- Complete interval computation for depth 15, residue 14684. -/
theorem bounds_15_14684 : exactInterval 15 14684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14684 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14684) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14684 : oddCount 14684 15 = 5 ∧ acceleratedOrbit 15 14684 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14684 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14684) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14684.1, data_15_14684.2]

/-- Complete interval computation for depth 15, residue 14685. -/
theorem bounds_15_14685 : exactInterval 15 14685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14685 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14685) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14685 : oddCount 14685 15 = 5 ∧ acceleratedOrbit 15 14685 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14685 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14685) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14685.1, data_15_14685.2]

/-- Complete interval computation for depth 15, residue 14686. -/
theorem bounds_15_14686 : exactInterval 15 14686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14686 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14686) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14686 : oddCount 14686 15 = 9 ∧ acceleratedOrbit 15 14686 = 8824 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14686 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14686) = 3 ^ 9 * m + 8824 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14686.1, data_15_14686.2]

/-- Complete interval computation for depth 15, residue 14687. -/
theorem bounds_15_14687 : exactInterval 15 14687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14687 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14687) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14687 : oddCount 14687 15 = 9 ∧ acceleratedOrbit 15 14687 = 8824 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14687 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14687) = 3 ^ 9 * m + 8824 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14687.1, data_15_14687.2]

/-- Complete interval computation for depth 15, residue 14688. -/
theorem bounds_15_14688 : exactInterval 15 14688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14688 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14688) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14688 : oddCount 14688 15 = 5 ∧ acceleratedOrbit 15 14688 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14688 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14688) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14688.1, data_15_14688.2]

/-- Complete interval computation for depth 15, residue 14689. -/
theorem bounds_15_14689 : exactInterval 15 14689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14689 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14689) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14689 : oddCount 14689 15 = 10 ∧ acceleratedOrbit 15 14689 = 26477 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14689 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14689) = 3 ^ 10 * m + 26477 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14689.1, data_15_14689.2]

/-- Complete interval computation for depth 15, residue 14690. -/
theorem bounds_15_14690 : exactInterval 15 14690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14690 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14690) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14690 : oddCount 14690 15 = 7 ∧ acceleratedOrbit 15 14690 = 982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14690 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14690) = 3 ^ 7 * m + 982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14690.1, data_15_14690.2]

/-- Complete interval computation for depth 15, residue 14691. -/
theorem bounds_15_14691 : exactInterval 15 14691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14691 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14691) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14691 : oddCount 14691 15 = 7 ∧ acceleratedOrbit 15 14691 = 982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14691 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14691) = 3 ^ 7 * m + 982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14691.1, data_15_14691.2]

/-- Complete interval computation for depth 15, residue 14692. -/
theorem bounds_15_14692 : exactInterval 15 14692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14692 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14692) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14692 : oddCount 14692 15 = 7 ∧ acceleratedOrbit 15 14692 = 982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14692 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14692) = 3 ^ 7 * m + 982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14692.1, data_15_14692.2]

/-- Complete interval computation for depth 15, residue 14693. -/
theorem bounds_15_14693 : exactInterval 15 14693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14693 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14693) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14693 : oddCount 14693 15 = 7 ∧ acceleratedOrbit 15 14693 = 982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14693 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14693) = 3 ^ 7 * m + 982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14693.1, data_15_14693.2]

/-- Complete interval computation for depth 15, residue 14694. -/
theorem bounds_15_14694 : exactInterval 15 14694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14694 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14694) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14694 : oddCount 14694 15 = 7 ∧ acceleratedOrbit 15 14694 = 982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14694 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14694) = 3 ^ 7 * m + 982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14694.1, data_15_14694.2]

/-- Complete interval computation for depth 15, residue 14695. -/
theorem bounds_15_14695 : exactInterval 15 14695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14695 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14695) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14695 : oddCount 14695 15 = 11 ∧ acceleratedOrbit 15 14695 = 79451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14695 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14695) = 3 ^ 11 * m + 79451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14695.1, data_15_14695.2]

/-- Complete interval computation for depth 15, residue 14696. -/
theorem bounds_15_14696 : exactInterval 15 14696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14696 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14696) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14696 : oddCount 14696 15 = 5 ∧ acceleratedOrbit 15 14696 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14696 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14696) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14696.1, data_15_14696.2]

/-- Complete interval computation for depth 15, residue 14697. -/
theorem bounds_15_14697 : exactInterval 15 14697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14697 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14697) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14697 : oddCount 14697 15 = 5 ∧ acceleratedOrbit 15 14697 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14697 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14697) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14697.1, data_15_14697.2]

/-- Complete interval computation for depth 15, residue 14698. -/
theorem bounds_15_14698 : exactInterval 15 14698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14698 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14698) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14698 : oddCount 14698 15 = 5 ∧ acceleratedOrbit 15 14698 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14698 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14698) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14698.1, data_15_14698.2]

/-- Complete interval computation for depth 15, residue 14699. -/
theorem bounds_15_14699 : exactInterval 15 14699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14699 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14699) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14699 : oddCount 14699 15 = 8 ∧ acceleratedOrbit 15 14699 = 2944 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14699 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14699) = 3 ^ 8 * m + 2944 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14699.1, data_15_14699.2]

/-- Complete interval computation for depth 15, residue 14700. -/
theorem bounds_15_14700 : exactInterval 15 14700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14700 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14700) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14700 : oddCount 14700 15 = 8 ∧ acceleratedOrbit 15 14700 = 2945 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14700 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14700) = 3 ^ 8 * m + 2945 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14700.1, data_15_14700.2]

/-- Complete interval computation for depth 15, residue 14701. -/
theorem bounds_15_14701 : exactInterval 15 14701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14701 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14701) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14701 : oddCount 14701 15 = 8 ∧ acceleratedOrbit 15 14701 = 2945 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14701 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14701) = 3 ^ 8 * m + 2945 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14701.1, data_15_14701.2]

/-- Complete interval computation for depth 15, residue 14702. -/
theorem bounds_15_14702 : exactInterval 15 14702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14702 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14702) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14702 : oddCount 14702 15 = 8 ∧ acceleratedOrbit 15 14702 = 2945 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14702 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14702) = 3 ^ 8 * m + 2945 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14702.1, data_15_14702.2]

/-- Complete interval computation for depth 15, residue 14703. -/
theorem bounds_15_14703 : exactInterval 15 14703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14703 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14703) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14703 : oddCount 14703 15 = 8 ∧ acceleratedOrbit 15 14703 = 2945 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14703 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14703) = 3 ^ 8 * m + 2945 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14703.1, data_15_14703.2]

/-- Complete interval computation for depth 15, residue 14704. -/
theorem bounds_15_14704 : exactInterval 15 14704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14704 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14704) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14704 : oddCount 14704 15 = 5 ∧ acceleratedOrbit 15 14704 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14704 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14704) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14704.1, data_15_14704.2]

/-- Complete interval computation for depth 15, residue 14705. -/
theorem bounds_15_14705 : exactInterval 15 14705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14705 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14705) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14705 : oddCount 14705 15 = 5 ∧ acceleratedOrbit 15 14705 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14705 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14705) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14705.1, data_15_14705.2]

/-- Complete interval computation for depth 15, residue 14706. -/
theorem bounds_15_14706 : exactInterval 15 14706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14706 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14706) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14706 : oddCount 14706 15 = 7 ∧ acceleratedOrbit 15 14706 = 982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14706 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14706) = 3 ^ 7 * m + 982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14706.1, data_15_14706.2]

/-- Complete interval computation for depth 15, residue 14707. -/
theorem bounds_15_14707 : exactInterval 15 14707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14707 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14707) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14707 : oddCount 14707 15 = 7 ∧ acceleratedOrbit 15 14707 = 982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14707 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14707) = 3 ^ 7 * m + 982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14707.1, data_15_14707.2]

/-- Complete interval computation for depth 15, residue 14708. -/
theorem bounds_15_14708 : exactInterval 15 14708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14708 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14708) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14708 : oddCount 14708 15 = 5 ∧ acceleratedOrbit 15 14708 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14708 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14708) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14708.1, data_15_14708.2]

/-- Complete interval computation for depth 15, residue 14709. -/
theorem bounds_15_14709 : exactInterval 15 14709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14709 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14709) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14709 : oddCount 14709 15 = 5 ∧ acceleratedOrbit 15 14709 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14709 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14709) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14709.1, data_15_14709.2]

/-- Complete interval computation for depth 15, residue 14710. -/
theorem bounds_15_14710 : exactInterval 15 14710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14710 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14710) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14710 : oddCount 14710 15 = 9 ∧ acceleratedOrbit 15 14710 = 8839 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14710 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14710) = 3 ^ 9 * m + 8839 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14710.1, data_15_14710.2]

/-- Complete interval computation for depth 15, residue 14711. -/
theorem bounds_15_14711 : exactInterval 15 14711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14711 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14711) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14711 : oddCount 14711 15 = 9 ∧ acceleratedOrbit 15 14711 = 8839 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14711 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14711) = 3 ^ 9 * m + 8839 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14711.1, data_15_14711.2]

end Collatz.Research.PassageAtlas.Batch0449
