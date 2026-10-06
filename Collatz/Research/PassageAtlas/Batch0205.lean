import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0205

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 6684. -/
theorem bounds_15_6684 : exactInterval 15 6684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6684 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6684) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6684 : oddCount 6684 15 = 6 ∧ acceleratedOrbit 15 6684 = 149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6684 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6684) = 3 ^ 6 * m + 149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6684.1, data_15_6684.2]

/-- Complete interval computation for depth 15, residue 6685. -/
theorem bounds_15_6685 : exactInterval 15 6685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6685 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6685) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6685 : oddCount 6685 15 = 6 ∧ acceleratedOrbit 15 6685 = 149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6685 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6685) = 3 ^ 6 * m + 149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6685.1, data_15_6685.2]

/-- Complete interval computation for depth 15, residue 6686. -/
theorem bounds_15_6686 : exactInterval 15 6686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6686 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6686) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6686 : oddCount 6686 15 = 6 ∧ acceleratedOrbit 15 6686 = 149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6686 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6686) = 3 ^ 6 * m + 149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6686.1, data_15_6686.2]

/-- Complete interval computation for depth 15, residue 6687. -/
theorem bounds_15_6687 : exactInterval 15 6687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6687 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6687) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6687 : oddCount 6687 15 = 9 ∧ acceleratedOrbit 15 6687 = 4018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6687 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6687) = 3 ^ 9 * m + 4018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6687.1, data_15_6687.2]

/-- Complete interval computation for depth 15, residue 6688. -/
theorem bounds_15_6688 : exactInterval 15 6688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6688 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6688) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6688 : oddCount 6688 15 = 6 ∧ acceleratedOrbit 15 6688 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6688 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6688) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6688.1, data_15_6688.2]

/-- Complete interval computation for depth 15, residue 6689. -/
theorem bounds_15_6689 : exactInterval 15 6689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6689 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6689) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6689 : oddCount 6689 15 = 6 ∧ acceleratedOrbit 15 6689 = 149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6689 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6689) = 3 ^ 6 * m + 149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6689.1, data_15_6689.2]

/-- Complete interval computation for depth 15, residue 6690. -/
theorem bounds_15_6690 : exactInterval 15 6690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6690 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6690) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6690 : oddCount 6690 15 = 7 ∧ acceleratedOrbit 15 6690 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6690 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6690) = 3 ^ 7 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6690.1, data_15_6690.2]

/-- Complete interval computation for depth 15, residue 6691. -/
theorem bounds_15_6691 : exactInterval 15 6691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6691 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6691) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6691 : oddCount 6691 15 = 7 ∧ acceleratedOrbit 15 6691 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6691 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6691) = 3 ^ 7 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6691.1, data_15_6691.2]

/-- Complete interval computation for depth 15, residue 6692. -/
theorem bounds_15_6692 : exactInterval 15 6692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6692 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6692) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6692 : oddCount 6692 15 = 9 ∧ acceleratedOrbit 15 6692 = 4025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6692 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6692) = 3 ^ 9 * m + 4025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6692.1, data_15_6692.2]

/-- Complete interval computation for depth 15, residue 6693. -/
theorem bounds_15_6693 : exactInterval 15 6693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6693 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6693) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6693 : oddCount 6693 15 = 9 ∧ acceleratedOrbit 15 6693 = 4025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6693 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6693) = 3 ^ 9 * m + 4025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6693.1, data_15_6693.2]

/-- Complete interval computation for depth 15, residue 6694. -/
theorem bounds_15_6694 : exactInterval 15 6694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6694 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6694) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6694 : oddCount 6694 15 = 9 ∧ acceleratedOrbit 15 6694 = 4025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6694 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6694) = 3 ^ 9 * m + 4025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6694.1, data_15_6694.2]

/-- Complete interval computation for depth 15, residue 6695. -/
theorem bounds_15_6695 : exactInterval 15 6695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6695 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6695) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6695 : oddCount 6695 15 = 6 ∧ acceleratedOrbit 15 6695 = 149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6695 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6695) = 3 ^ 6 * m + 149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6695.1, data_15_6695.2]

/-- Complete interval computation for depth 15, residue 6696. -/
theorem bounds_15_6696 : exactInterval 15 6696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6696 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6696) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6696 : oddCount 6696 15 = 6 ∧ acceleratedOrbit 15 6696 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6696 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6696) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6696.1, data_15_6696.2]

/-- Complete interval computation for depth 15, residue 6697. -/
theorem bounds_15_6697 : exactInterval 15 6697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6697 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6697) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6697 : oddCount 6697 15 = 9 ∧ acceleratedOrbit 15 6697 = 4024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6697 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6697) = 3 ^ 9 * m + 4024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6697.1, data_15_6697.2]

/-- Complete interval computation for depth 15, residue 6698. -/
theorem bounds_15_6698 : exactInterval 15 6698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6698 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6698) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6698 : oddCount 6698 15 = 6 ∧ acceleratedOrbit 15 6698 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6698 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6698) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6698.1, data_15_6698.2]

/-- Complete interval computation for depth 15, residue 6699. -/
theorem bounds_15_6699 : exactInterval 15 6699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6699 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6699) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6699 : oddCount 6699 15 = 7 ∧ acceleratedOrbit 15 6699 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6699 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6699) = 3 ^ 7 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6699.1, data_15_6699.2]

/-- Complete interval computation for depth 15, residue 6700. -/
theorem bounds_15_6700 : exactInterval 15 6700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6700 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6700) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6700 : oddCount 6700 15 = 7 ∧ acceleratedOrbit 15 6700 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6700 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6700) = 3 ^ 7 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6700.1, data_15_6700.2]

/-- Complete interval computation for depth 15, residue 6701. -/
theorem bounds_15_6701 : exactInterval 15 6701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6701 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6701) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6701 : oddCount 6701 15 = 7 ∧ acceleratedOrbit 15 6701 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6701 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6701) = 3 ^ 7 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6701.1, data_15_6701.2]

/-- Complete interval computation for depth 15, residue 6702. -/
theorem bounds_15_6702 : exactInterval 15 6702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6702 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6702) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6702 : oddCount 6702 15 = 7 ∧ acceleratedOrbit 15 6702 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6702 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6702) = 3 ^ 7 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6702.1, data_15_6702.2]

/-- Complete interval computation for depth 15, residue 6703. -/
theorem bounds_15_6703 : exactInterval 15 6703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6703 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6703) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6703 : oddCount 6703 15 = 10 ∧ acceleratedOrbit 15 6703 = 12082 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6703 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6703) = 3 ^ 10 * m + 12082 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6703.1, data_15_6703.2]

/-- Complete interval computation for depth 15, residue 6704. -/
theorem bounds_15_6704 : exactInterval 15 6704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6704 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6704) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6704 : oddCount 6704 15 = 6 ∧ acceleratedOrbit 15 6704 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6704 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6704) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6704.1, data_15_6704.2]

/-- Complete interval computation for depth 15, residue 6705. -/
theorem bounds_15_6705 : exactInterval 15 6705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6705 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6705) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6705 : oddCount 6705 15 = 7 ∧ acceleratedOrbit 15 6705 = 448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6705 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6705) = 3 ^ 7 * m + 448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6705.1, data_15_6705.2]

/-- Complete interval computation for depth 15, residue 6706. -/
theorem bounds_15_6706 : exactInterval 15 6706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6706 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6706) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6706 : oddCount 6706 15 = 7 ∧ acceleratedOrbit 15 6706 = 448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6706 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6706) = 3 ^ 7 * m + 448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6706.1, data_15_6706.2]

/-- Complete interval computation for depth 15, residue 6707. -/
theorem bounds_15_6707 : exactInterval 15 6707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6707 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6707) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6707 : oddCount 6707 15 = 7 ∧ acceleratedOrbit 15 6707 = 448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6707 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6707) = 3 ^ 7 * m + 448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6707.1, data_15_6707.2]

/-- Complete interval computation for depth 15, residue 6708. -/
theorem bounds_15_6708 : exactInterval 15 6708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6708 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6708) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6708 : oddCount 6708 15 = 6 ∧ acceleratedOrbit 15 6708 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6708 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6708) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6708.1, data_15_6708.2]

/-- Complete interval computation for depth 15, residue 6709. -/
theorem bounds_15_6709 : exactInterval 15 6709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6709 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6709) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6709 : oddCount 6709 15 = 6 ∧ acceleratedOrbit 15 6709 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6709 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6709) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6709.1, data_15_6709.2]

/-- Complete interval computation for depth 15, residue 6710. -/
theorem bounds_15_6710 : exactInterval 15 6710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6710 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6710) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6710 : oddCount 6710 15 = 10 ∧ acceleratedOrbit 15 6710 = 12097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6710 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6710) = 3 ^ 10 * m + 12097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6710.1, data_15_6710.2]

/-- Complete interval computation for depth 15, residue 6711. -/
theorem bounds_15_6711 : exactInterval 15 6711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6711 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6711) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6711 : oddCount 6711 15 = 10 ∧ acceleratedOrbit 15 6711 = 12097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6711 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6711) = 3 ^ 10 * m + 12097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6711.1, data_15_6711.2]

/-- Complete interval computation for depth 15, residue 6712. -/
theorem bounds_15_6712 : exactInterval 15 6712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6712 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6712) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6712 : oddCount 6712 15 = 9 ∧ acceleratedOrbit 15 6712 = 4040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6712 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6712) = 3 ^ 9 * m + 4040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6712.1, data_15_6712.2]

/-- Complete interval computation for depth 15, residue 6713. -/
theorem bounds_15_6713 : exactInterval 15 6713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6713 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6713) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6713 : oddCount 6713 15 = 8 ∧ acceleratedOrbit 15 6713 = 1345 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6713 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6713) = 3 ^ 8 * m + 1345 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6713.1, data_15_6713.2]

/-- Complete interval computation for depth 15, residue 6714. -/
theorem bounds_15_6714 : exactInterval 15 6714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6714 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6714) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6714 : oddCount 6714 15 = 9 ∧ acceleratedOrbit 15 6714 = 4040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6714 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6714) = 3 ^ 9 * m + 4040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6714.1, data_15_6714.2]

/-- Complete interval computation for depth 15, residue 6715. -/
theorem bounds_15_6715 : exactInterval 15 6715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6715 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6715) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6715 : oddCount 6715 15 = 7 ∧ acceleratedOrbit 15 6715 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6715 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6715) = 3 ^ 7 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6715.1, data_15_6715.2]

/-- Complete interval computation for depth 15, residue 6716. -/
theorem bounds_15_6716 : exactInterval 15 6716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6716 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6716) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6716 : oddCount 6716 15 = 9 ∧ acceleratedOrbit 15 6716 = 4040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6716 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6716) = 3 ^ 9 * m + 4040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6716.1, data_15_6716.2]

end Collatz.Research.PassageAtlas.Batch0205
