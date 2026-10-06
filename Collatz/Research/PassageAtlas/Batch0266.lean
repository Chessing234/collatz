import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0266

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 8683. -/
theorem bounds_15_8683 : exactInterval 15 8683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8683 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8683) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8683 : oddCount 8683 15 = 12 ∧ acceleratedOrbit 15 8683 = 140858 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8683 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8683) = 3 ^ 12 * m + 140858 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8683.1, data_15_8683.2]

/-- Complete interval computation for depth 15, residue 8684. -/
theorem bounds_15_8684 : exactInterval 15 8684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8684 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8684) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8684 : oddCount 8684 15 = 8 ∧ acceleratedOrbit 15 8684 = 1741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8684 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8684) = 3 ^ 8 * m + 1741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8684.1, data_15_8684.2]

/-- Complete interval computation for depth 15, residue 8685. -/
theorem bounds_15_8685 : exactInterval 15 8685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8685 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8685) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8685 : oddCount 8685 15 = 8 ∧ acceleratedOrbit 15 8685 = 1741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8685 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8685) = 3 ^ 8 * m + 1741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8685.1, data_15_8685.2]

/-- Complete interval computation for depth 15, residue 8686. -/
theorem bounds_15_8686 : exactInterval 15 8686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8686 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8686) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8686 : oddCount 8686 15 = 8 ∧ acceleratedOrbit 15 8686 = 1741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8686 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8686) = 3 ^ 8 * m + 1741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8686.1, data_15_8686.2]

/-- Complete interval computation for depth 15, residue 8687. -/
theorem bounds_15_8687 : exactInterval 15 8687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8687 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8687) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8687 : oddCount 8687 15 = 11 ∧ acceleratedOrbit 15 8687 = 46970 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8687 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8687) = 3 ^ 11 * m + 46970 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8687.1, data_15_8687.2]

/-- Complete interval computation for depth 15, residue 8688. -/
theorem bounds_15_8688 : exactInterval 15 8688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8688 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8688) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8688 : oddCount 8688 15 = 7 ∧ acceleratedOrbit 15 8688 = 581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8688 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8688) = 3 ^ 7 * m + 581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8688.1, data_15_8688.2]

/-- Complete interval computation for depth 15, residue 8689. -/
theorem bounds_15_8689 : exactInterval 15 8689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8689 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8689) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8689 : oddCount 8689 15 = 5 ∧ acceleratedOrbit 15 8689 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8689 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8689) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8689.1, data_15_8689.2]

/-- Complete interval computation for depth 15, residue 8690. -/
theorem bounds_15_8690 : exactInterval 15 8690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8690 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8690) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8690 : oddCount 8690 15 = 9 ∧ acceleratedOrbit 15 8690 = 5224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8690 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8690) = 3 ^ 9 * m + 5224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8690.1, data_15_8690.2]

/-- Complete interval computation for depth 15, residue 8691. -/
theorem bounds_15_8691 : exactInterval 15 8691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8691 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8691) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8691 : oddCount 8691 15 = 9 ∧ acceleratedOrbit 15 8691 = 5224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8691 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8691) = 3 ^ 9 * m + 5224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8691.1, data_15_8691.2]

/-- Complete interval computation for depth 15, residue 8692. -/
theorem bounds_15_8692 : exactInterval 15 8692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8692 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8692) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8692 : oddCount 8692 15 = 7 ∧ acceleratedOrbit 15 8692 = 581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8692 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8692) = 3 ^ 7 * m + 581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8692.1, data_15_8692.2]

/-- Complete interval computation for depth 15, residue 8693. -/
theorem bounds_15_8693 : exactInterval 15 8693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8693 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8693) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8693 : oddCount 8693 15 = 7 ∧ acceleratedOrbit 15 8693 = 581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8693 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8693) = 3 ^ 7 * m + 581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8693.1, data_15_8693.2]

/-- Complete interval computation for depth 15, residue 8694. -/
theorem bounds_15_8694 : exactInterval 15 8694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8694 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8694) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8694 : oddCount 8694 15 = 11 ∧ acceleratedOrbit 15 8694 = 47020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8694 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8694) = 3 ^ 11 * m + 47020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8694.1, data_15_8694.2]

/-- Complete interval computation for depth 15, residue 8695. -/
theorem bounds_15_8695 : exactInterval 15 8695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8695 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8695) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8695 : oddCount 8695 15 = 11 ∧ acceleratedOrbit 15 8695 = 47020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8695 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8695) = 3 ^ 11 * m + 47020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8695.1, data_15_8695.2]

/-- Complete interval computation for depth 15, residue 8696. -/
theorem bounds_15_8696 : exactInterval 15 8696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8696 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8696) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8696 : oddCount 8696 15 = 7 ∧ acceleratedOrbit 15 8696 = 581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8696 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8696) = 3 ^ 7 * m + 581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8696.1, data_15_8696.2]

/-- Complete interval computation for depth 15, residue 8697. -/
theorem bounds_15_8697 : exactInterval 15 8697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8697 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8697) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8697 : oddCount 8697 15 = 8 ∧ acceleratedOrbit 15 8697 = 1742 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8697 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8697) = 3 ^ 8 * m + 1742 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8697.1, data_15_8697.2]

/-- Complete interval computation for depth 15, residue 8698. -/
theorem bounds_15_8698 : exactInterval 15 8698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8698 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8698) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8698 : oddCount 8698 15 = 7 ∧ acceleratedOrbit 15 8698 = 581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8698 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8698) = 3 ^ 7 * m + 581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8698.1, data_15_8698.2]

/-- Complete interval computation for depth 15, residue 8699. -/
theorem bounds_15_8699 : exactInterval 15 8699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8699 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8699) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8699 : oddCount 8699 15 = 9 ∧ acceleratedOrbit 15 8699 = 5228 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8699 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8699) = 3 ^ 9 * m + 5228 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8699.1, data_15_8699.2]

/-- Complete interval computation for depth 15, residue 8700. -/
theorem bounds_15_8700 : exactInterval 15 8700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8700 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8700) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8700 : oddCount 8700 15 = 10 ∧ acceleratedOrbit 15 8700 = 15686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8700 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8700) = 3 ^ 10 * m + 15686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8700.1, data_15_8700.2]

/-- Complete interval computation for depth 15, residue 8701. -/
theorem bounds_15_8701 : exactInterval 15 8701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8701 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8701) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8701 : oddCount 8701 15 = 10 ∧ acceleratedOrbit 15 8701 = 15686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8701 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8701) = 3 ^ 10 * m + 15686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8701.1, data_15_8701.2]

/-- Complete interval computation for depth 15, residue 8702. -/
theorem bounds_15_8702 : exactInterval 15 8702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8702 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8702) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8702 : oddCount 8702 15 = 10 ∧ acceleratedOrbit 15 8702 = 15686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8702 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8702) = 3 ^ 10 * m + 15686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8702.1, data_15_8702.2]

/-- Complete interval computation for depth 15, residue 8703. -/
theorem bounds_15_8703 : exactInterval 15 8703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8703 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8703) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8703 : oddCount 8703 15 = 13 ∧ acceleratedOrbit 15 8703 = 423494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8703 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8703) = 3 ^ 13 * m + 423494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8703.1, data_15_8703.2]

/-- Complete interval computation for depth 15, residue 8704. -/
theorem bounds_15_8704 : exactInterval 15 8704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8704 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8704) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8704 : oddCount 8704 15 = 3 ∧ acceleratedOrbit 15 8704 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8704 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8704) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8704.1, data_15_8704.2]

/-- Complete interval computation for depth 15, residue 8705. -/
theorem bounds_15_8705 : exactInterval 15 8705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8705 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8705) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8705 : oddCount 8705 15 = 8 ∧ acceleratedOrbit 15 8705 = 1745 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8705 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8705) = 3 ^ 8 * m + 1745 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8705.1, data_15_8705.2]

/-- Complete interval computation for depth 15, residue 8706. -/
theorem bounds_15_8706 : exactInterval 15 8706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8706 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8706) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8706 : oddCount 8706 15 = 6 ∧ acceleratedOrbit 15 8706 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8706 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8706) = 3 ^ 6 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8706.1, data_15_8706.2]

/-- Complete interval computation for depth 15, residue 8707. -/
theorem bounds_15_8707 : exactInterval 15 8707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8707 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8707) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8707 : oddCount 8707 15 = 6 ∧ acceleratedOrbit 15 8707 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8707 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8707) = 3 ^ 6 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8707.1, data_15_8707.2]

/-- Complete interval computation for depth 15, residue 8708. -/
theorem bounds_15_8708 : exactInterval 15 8708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8708 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8708) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8708 : oddCount 8708 15 = 6 ∧ acceleratedOrbit 15 8708 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8708 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8708) = 3 ^ 6 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8708.1, data_15_8708.2]

/-- Complete interval computation for depth 15, residue 8709. -/
theorem bounds_15_8709 : exactInterval 15 8709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8709 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8709) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8709 : oddCount 8709 15 = 6 ∧ acceleratedOrbit 15 8709 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8709 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8709) = 3 ^ 6 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8709.1, data_15_8709.2]

/-- Complete interval computation for depth 15, residue 8710. -/
theorem bounds_15_8710 : exactInterval 15 8710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8710 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8710) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8710 : oddCount 8710 15 = 6 ∧ acceleratedOrbit 15 8710 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8710 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8710) = 3 ^ 6 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8710.1, data_15_8710.2]

/-- Complete interval computation for depth 15, residue 8711. -/
theorem bounds_15_8711 : exactInterval 15 8711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8711 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8711) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8711 : oddCount 8711 15 = 10 ∧ acceleratedOrbit 15 8711 = 15704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8711 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8711) = 3 ^ 10 * m + 15704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8711.1, data_15_8711.2]

/-- Complete interval computation for depth 15, residue 8712. -/
theorem bounds_15_8712 : exactInterval 15 8712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8712 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8712) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8712 : oddCount 8712 15 = 5 ∧ acceleratedOrbit 15 8712 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8712 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8712) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8712.1, data_15_8712.2]

/-- Complete interval computation for depth 15, residue 8713. -/
theorem bounds_15_8713 : exactInterval 15 8713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8713 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8713) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8713 : oddCount 8713 15 = 6 ∧ acceleratedOrbit 15 8713 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8713 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8713) = 3 ^ 6 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8713.1, data_15_8713.2]

/-- Complete interval computation for depth 15, residue 8714. -/
theorem bounds_15_8714 : exactInterval 15 8714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8714 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8714) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8714 : oddCount 8714 15 = 5 ∧ acceleratedOrbit 15 8714 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8714 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8714) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8714.1, data_15_8714.2]

/-- Complete interval computation for depth 15, residue 8715. -/
theorem bounds_15_8715 : exactInterval 15 8715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8715 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8715) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8715 : oddCount 8715 15 = 6 ∧ acceleratedOrbit 15 8715 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8715 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8715) = 3 ^ 6 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8715.1, data_15_8715.2]

end Collatz.Research.PassageAtlas.Batch0266
