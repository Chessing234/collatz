import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0907

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 29687. -/
theorem bounds_15_29687 : exactInterval 15 29687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29687 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29687) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29687 : oddCount 29687 15 = 7 ∧ acceleratedOrbit 15 29687 = 1982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29687 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29687) = 3 ^ 7 * m + 1982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29687.1, data_15_29687.2]

/-- Complete interval computation for depth 15, residue 29688. -/
theorem bounds_15_29688 : exactInterval 15 29688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29688 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29688) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29688 : oddCount 29688 15 = 11 ∧ acceleratedOrbit 15 29688 = 160541 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29688 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29688) = 3 ^ 11 * m + 160541 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29688.1, data_15_29688.2]

/-- Complete interval computation for depth 15, residue 29689. -/
theorem bounds_15_29689 : exactInterval 15 29689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29689 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29689) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29689 : oddCount 29689 15 = 8 ∧ acceleratedOrbit 15 29689 = 5945 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29689 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29689) = 3 ^ 8 * m + 5945 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29689.1, data_15_29689.2]

/-- Complete interval computation for depth 15, residue 29690. -/
theorem bounds_15_29690 : exactInterval 15 29690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29690 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29690) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29690 : oddCount 29690 15 = 11 ∧ acceleratedOrbit 15 29690 = 160541 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29690 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29690) = 3 ^ 11 * m + 160541 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29690.1, data_15_29690.2]

/-- Complete interval computation for depth 15, residue 29691. -/
theorem bounds_15_29691 : exactInterval 15 29691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29691 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29691) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29691 : oddCount 29691 15 = 9 ∧ acceleratedOrbit 15 29691 = 17837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29691 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29691) = 3 ^ 9 * m + 17837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29691.1, data_15_29691.2]

/-- Complete interval computation for depth 15, residue 29692. -/
theorem bounds_15_29692 : exactInterval 15 29692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29692 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29692) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29692 : oddCount 29692 15 = 11 ∧ acceleratedOrbit 15 29692 = 160541 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29692 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29692) = 3 ^ 11 * m + 160541 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29692.1, data_15_29692.2]

/-- Complete interval computation for depth 15, residue 29693. -/
theorem bounds_15_29693 : exactInterval 15 29693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29693 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29693) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29693 : oddCount 29693 15 = 11 ∧ acceleratedOrbit 15 29693 = 160541 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29693 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29693) = 3 ^ 11 * m + 160541 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29693.1, data_15_29693.2]

/-- Complete interval computation for depth 15, residue 29694. -/
theorem bounds_15_29694 : exactInterval 15 29694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29694 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29694) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29694 : oddCount 29694 15 = 12 ∧ acceleratedOrbit 15 29694 = 481619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29694 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29694) = 3 ^ 12 * m + 481619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29694.1, data_15_29694.2]

/-- Complete interval computation for depth 15, residue 29695. -/
theorem bounds_15_29695 : exactInterval 15 29695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29695 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29695) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29695 : oddCount 29695 15 = 12 ∧ acceleratedOrbit 15 29695 = 481619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29695 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29695) = 3 ^ 12 * m + 481619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29695.1, data_15_29695.2]

/-- Complete interval computation for depth 15, residue 29696. -/
theorem bounds_15_29696 : exactInterval 15 29696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29696 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29696) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29696 : oddCount 29696 15 = 3 ∧ acceleratedOrbit 15 29696 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29696 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29696) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29696.1, data_15_29696.2]

/-- Complete interval computation for depth 15, residue 29697. -/
theorem bounds_15_29697 : exactInterval 15 29697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29697 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29697) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29697 : oddCount 29697 15 = 6 ∧ acceleratedOrbit 15 29697 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29697 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29697) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29697.1, data_15_29697.2]

/-- Complete interval computation for depth 15, residue 29698. -/
theorem bounds_15_29698 : exactInterval 15 29698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29698 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29698) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29698 : oddCount 29698 15 = 9 ∧ acceleratedOrbit 15 29698 = 17846 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29698 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29698) = 3 ^ 9 * m + 17846 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29698.1, data_15_29698.2]

/-- Complete interval computation for depth 15, residue 29699. -/
theorem bounds_15_29699 : exactInterval 15 29699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29699 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29699) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29699 : oddCount 29699 15 = 9 ∧ acceleratedOrbit 15 29699 = 17846 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29699 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29699) = 3 ^ 9 * m + 17846 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29699.1, data_15_29699.2]

/-- Complete interval computation for depth 15, residue 29700. -/
theorem bounds_15_29700 : exactInterval 15 29700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29700 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29700) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29700 : oddCount 29700 15 = 7 ∧ acceleratedOrbit 15 29700 = 1984 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29700 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29700) = 3 ^ 7 * m + 1984 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29700.1, data_15_29700.2]

/-- Complete interval computation for depth 15, residue 29701. -/
theorem bounds_15_29701 : exactInterval 15 29701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29701 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29701) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29701 : oddCount 29701 15 = 7 ∧ acceleratedOrbit 15 29701 = 1984 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29701 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29701) = 3 ^ 7 * m + 1984 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29701.1, data_15_29701.2]

/-- Complete interval computation for depth 15, residue 29702. -/
theorem bounds_15_29702 : exactInterval 15 29702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29702 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29702) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29702 : oddCount 29702 15 = 7 ∧ acceleratedOrbit 15 29702 = 1984 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29702 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29702) = 3 ^ 7 * m + 1984 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29702.1, data_15_29702.2]

/-- Complete interval computation for depth 15, residue 29703. -/
theorem bounds_15_29703 : exactInterval 15 29703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29703 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29703) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29703 : oddCount 29703 15 = 9 ∧ acceleratedOrbit 15 29703 = 17846 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29703 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29703) = 3 ^ 9 * m + 17846 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29703.1, data_15_29703.2]

/-- Complete interval computation for depth 15, residue 29704. -/
theorem bounds_15_29704 : exactInterval 15 29704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29704 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29704) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29704 : oddCount 29704 15 = 8 ∧ acceleratedOrbit 15 29704 = 5953 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29704 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29704) = 3 ^ 8 * m + 5953 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29704.1, data_15_29704.2]

/-- Complete interval computation for depth 15, residue 29705. -/
theorem bounds_15_29705 : exactInterval 15 29705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29705 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29705) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29705 : oddCount 29705 15 = 9 ∧ acceleratedOrbit 15 29705 = 17846 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29705 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29705) = 3 ^ 9 * m + 17846 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29705.1, data_15_29705.2]

/-- Complete interval computation for depth 15, residue 29706. -/
theorem bounds_15_29706 : exactInterval 15 29706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29706 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29706) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29706 : oddCount 29706 15 = 8 ∧ acceleratedOrbit 15 29706 = 5953 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29706 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29706) = 3 ^ 8 * m + 5953 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29706.1, data_15_29706.2]

/-- Complete interval computation for depth 15, residue 29707. -/
theorem bounds_15_29707 : exactInterval 15 29707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29707 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29707) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29707 : oddCount 29707 15 = 7 ∧ acceleratedOrbit 15 29707 = 1984 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29707 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29707) = 3 ^ 7 * m + 1984 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29707.1, data_15_29707.2]

/-- Complete interval computation for depth 15, residue 29708. -/
theorem bounds_15_29708 : exactInterval 15 29708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29708 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29708) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29708 : oddCount 29708 15 = 8 ∧ acceleratedOrbit 15 29708 = 5953 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29708 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29708) = 3 ^ 8 * m + 5953 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29708.1, data_15_29708.2]

/-- Complete interval computation for depth 15, residue 29709. -/
theorem bounds_15_29709 : exactInterval 15 29709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29709 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29709) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29709 : oddCount 29709 15 = 8 ∧ acceleratedOrbit 15 29709 = 5953 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29709 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29709) = 3 ^ 8 * m + 5953 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29709.1, data_15_29709.2]

/-- Complete interval computation for depth 15, residue 29710. -/
theorem bounds_15_29710 : exactInterval 15 29710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29710 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29710) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29710 : oddCount 29710 15 = 8 ∧ acceleratedOrbit 15 29710 = 5950 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29710 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29710) = 3 ^ 8 * m + 5950 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29710.1, data_15_29710.2]

/-- Complete interval computation for depth 15, residue 29711. -/
theorem bounds_15_29711 : exactInterval 15 29711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29711 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29711) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29711 : oddCount 29711 15 = 8 ∧ acceleratedOrbit 15 29711 = 5950 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29711 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29711) = 3 ^ 8 * m + 5950 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29711.1, data_15_29711.2]

/-- Complete interval computation for depth 15, residue 29712. -/
theorem bounds_15_29712 : exactInterval 15 29712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29712 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29712) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29712 : oddCount 29712 15 = 4 ∧ acceleratedOrbit 15 29712 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29712 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29712) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29712.1, data_15_29712.2]

/-- Complete interval computation for depth 15, residue 29713. -/
theorem bounds_15_29713 : exactInterval 15 29713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29713 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29713) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29713 : oddCount 29713 15 = 8 ∧ acceleratedOrbit 15 29713 = 5953 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29713 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29713) = 3 ^ 8 * m + 5953 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29713.1, data_15_29713.2]

/-- Complete interval computation for depth 15, residue 29714. -/
theorem bounds_15_29714 : exactInterval 15 29714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29714 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29714) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29714 : oddCount 29714 15 = 7 ∧ acceleratedOrbit 15 29714 = 1984 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29714 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29714) = 3 ^ 7 * m + 1984 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29714.1, data_15_29714.2]

/-- Complete interval computation for depth 15, residue 29715. -/
theorem bounds_15_29715 : exactInterval 15 29715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29715 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29715) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29715 : oddCount 29715 15 = 7 ∧ acceleratedOrbit 15 29715 = 1984 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29715 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29715) = 3 ^ 7 * m + 1984 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29715.1, data_15_29715.2]

/-- Complete interval computation for depth 15, residue 29716. -/
theorem bounds_15_29716 : exactInterval 15 29716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29716 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29716) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29716 : oddCount 29716 15 = 4 ∧ acceleratedOrbit 15 29716 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29716 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29716) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29716.1, data_15_29716.2]

/-- Complete interval computation for depth 15, residue 29717. -/
theorem bounds_15_29717 : exactInterval 15 29717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29717 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29717) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29717 : oddCount 29717 15 = 4 ∧ acceleratedOrbit 15 29717 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29717 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29717) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29717.1, data_15_29717.2]

/-- Complete interval computation for depth 15, residue 29718. -/
theorem bounds_15_29718 : exactInterval 15 29718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29718 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29718) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29718 : oddCount 29718 15 = 8 ∧ acceleratedOrbit 15 29718 = 5953 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29718 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29718) = 3 ^ 8 * m + 5953 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29718.1, data_15_29718.2]

/-- Complete interval computation for depth 15, residue 29719. -/
theorem bounds_15_29719 : exactInterval 15 29719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29719 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29719) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29719 : oddCount 29719 15 = 8 ∧ acceleratedOrbit 15 29719 = 5953 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29719 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29719) = 3 ^ 8 * m + 5953 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29719.1, data_15_29719.2]

end Collatz.Research.PassageAtlas.Batch0907
