import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0208

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 6782. -/
theorem bounds_15_6782 : exactInterval 15 6782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6782 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6782) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6782 : oddCount 6782 15 = 10 ∧ acceleratedOrbit 15 6782 = 12226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6782 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6782) = 3 ^ 10 * m + 12226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6782.1, data_15_6782.2]

/-- Complete interval computation for depth 15, residue 6783. -/
theorem bounds_15_6783 : exactInterval 15 6783 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6783 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6783) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6783 : oddCount 6783 15 = 9 ∧ acceleratedOrbit 15 6783 = 4075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6783 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6783) = 3 ^ 9 * m + 4075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6783.1, data_15_6783.2]

/-- Complete interval computation for depth 15, residue 6784. -/
theorem bounds_15_6784 : exactInterval 15 6784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6784 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6784) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6784 : oddCount 6784 15 = 2 ∧ acceleratedOrbit 15 6784 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6784 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6784) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6784.1, data_15_6784.2]

/-- Complete interval computation for depth 15, residue 6785. -/
theorem bounds_15_6785 : exactInterval 15 6785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6785 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6785) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6785 : oddCount 6785 15 = 9 ∧ acceleratedOrbit 15 6785 = 4078 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6785 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6785) = 3 ^ 9 * m + 4078 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6785.1, data_15_6785.2]

/-- Complete interval computation for depth 15, residue 6786. -/
theorem bounds_15_6786 : exactInterval 15 6786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6786 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6786) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6786 : oddCount 6786 15 = 6 ∧ acceleratedOrbit 15 6786 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6786 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6786) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6786.1, data_15_6786.2]

/-- Complete interval computation for depth 15, residue 6787. -/
theorem bounds_15_6787 : exactInterval 15 6787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6787 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6787) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6787 : oddCount 6787 15 = 6 ∧ acceleratedOrbit 15 6787 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6787 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6787) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6787.1, data_15_6787.2]

/-- Complete interval computation for depth 15, residue 6788. -/
theorem bounds_15_6788 : exactInterval 15 6788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6788 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6788) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6788 : oddCount 6788 15 = 7 ∧ acceleratedOrbit 15 6788 = 454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6788 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6788) = 3 ^ 7 * m + 454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6788.1, data_15_6788.2]

/-- Complete interval computation for depth 15, residue 6789. -/
theorem bounds_15_6789 : exactInterval 15 6789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6789 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6789) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6789 : oddCount 6789 15 = 7 ∧ acceleratedOrbit 15 6789 = 454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6789 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6789) = 3 ^ 7 * m + 454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6789.1, data_15_6789.2]

/-- Complete interval computation for depth 15, residue 6790. -/
theorem bounds_15_6790 : exactInterval 15 6790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6790 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6790) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6790 : oddCount 6790 15 = 7 ∧ acceleratedOrbit 15 6790 = 454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6790 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6790) = 3 ^ 7 * m + 454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6790.1, data_15_6790.2]

/-- Complete interval computation for depth 15, residue 6791. -/
theorem bounds_15_6791 : exactInterval 15 6791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6791 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6791) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6791 : oddCount 6791 15 = 7 ∧ acceleratedOrbit 15 6791 = 454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6791 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6791) = 3 ^ 7 * m + 454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6791.1, data_15_6791.2]

/-- Complete interval computation for depth 15, residue 6792. -/
theorem bounds_15_6792 : exactInterval 15 6792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6792 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6792) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6792 : oddCount 6792 15 = 8 ∧ acceleratedOrbit 15 6792 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6792 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6792) = 3 ^ 8 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6792.1, data_15_6792.2]

/-- Complete interval computation for depth 15, residue 6793. -/
theorem bounds_15_6793 : exactInterval 15 6793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6793 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6793) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6793 : oddCount 6793 15 = 8 ∧ acceleratedOrbit 15 6793 = 1361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6793 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6793) = 3 ^ 8 * m + 1361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6793.1, data_15_6793.2]

/-- Complete interval computation for depth 15, residue 6794. -/
theorem bounds_15_6794 : exactInterval 15 6794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6794 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6794) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6794 : oddCount 6794 15 = 8 ∧ acceleratedOrbit 15 6794 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6794 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6794) = 3 ^ 8 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6794.1, data_15_6794.2]

/-- Complete interval computation for depth 15, residue 6795. -/
theorem bounds_15_6795 : exactInterval 15 6795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6795 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6795) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6795 : oddCount 6795 15 = 7 ∧ acceleratedOrbit 15 6795 = 454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6795 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6795) = 3 ^ 7 * m + 454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6795.1, data_15_6795.2]

/-- Complete interval computation for depth 15, residue 6796. -/
theorem bounds_15_6796 : exactInterval 15 6796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6796 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6796) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6796 : oddCount 6796 15 = 8 ∧ acceleratedOrbit 15 6796 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6796 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6796) = 3 ^ 8 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6796.1, data_15_6796.2]

/-- Complete interval computation for depth 15, residue 6797. -/
theorem bounds_15_6797 : exactInterval 15 6797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6797 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6797) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6797 : oddCount 6797 15 = 8 ∧ acceleratedOrbit 15 6797 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6797 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6797) = 3 ^ 8 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6797.1, data_15_6797.2]

/-- Complete interval computation for depth 15, residue 6798. -/
theorem bounds_15_6798 : exactInterval 15 6798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6798 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6798) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6798 : oddCount 6798 15 = 10 ∧ acceleratedOrbit 15 6798 = 12257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6798 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6798) = 3 ^ 10 * m + 12257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6798.1, data_15_6798.2]

/-- Complete interval computation for depth 15, residue 6799. -/
theorem bounds_15_6799 : exactInterval 15 6799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6799 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6799) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6799 : oddCount 6799 15 = 10 ∧ acceleratedOrbit 15 6799 = 12257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6799 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6799) = 3 ^ 10 * m + 12257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6799.1, data_15_6799.2]

/-- Complete interval computation for depth 15, residue 6800. -/
theorem bounds_15_6800 : exactInterval 15 6800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6800 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6800) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6800 : oddCount 6800 15 = 8 ∧ acceleratedOrbit 15 6800 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6800 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6800) = 3 ^ 8 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6800.1, data_15_6800.2]

/-- Complete interval computation for depth 15, residue 6801. -/
theorem bounds_15_6801 : exactInterval 15 6801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6801 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6801) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6801 : oddCount 6801 15 = 9 ∧ acceleratedOrbit 15 6801 = 4090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6801 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6801) = 3 ^ 9 * m + 4090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6801.1, data_15_6801.2]

/-- Complete interval computation for depth 15, residue 6802. -/
theorem bounds_15_6802 : exactInterval 15 6802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6802 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6802) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6802 : oddCount 6802 15 = 9 ∧ acceleratedOrbit 15 6802 = 4090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6802 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6802) = 3 ^ 9 * m + 4090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6802.1, data_15_6802.2]

/-- Complete interval computation for depth 15, residue 6803. -/
theorem bounds_15_6803 : exactInterval 15 6803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6803 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6803) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6803 : oddCount 6803 15 = 9 ∧ acceleratedOrbit 15 6803 = 4090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6803 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6803) = 3 ^ 9 * m + 4090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6803.1, data_15_6803.2]

/-- Complete interval computation for depth 15, residue 6804. -/
theorem bounds_15_6804 : exactInterval 15 6804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6804 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6804) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6804 : oddCount 6804 15 = 8 ∧ acceleratedOrbit 15 6804 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6804 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6804) = 3 ^ 8 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6804.1, data_15_6804.2]

/-- Complete interval computation for depth 15, residue 6805. -/
theorem bounds_15_6805 : exactInterval 15 6805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6805 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6805) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6805 : oddCount 6805 15 = 8 ∧ acceleratedOrbit 15 6805 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6805 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6805) = 3 ^ 8 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6805.1, data_15_6805.2]

/-- Complete interval computation for depth 15, residue 6806. -/
theorem bounds_15_6806 : exactInterval 15 6806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6806 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6806) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6806 : oddCount 6806 15 = 8 ∧ acceleratedOrbit 15 6806 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6806 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6806) = 3 ^ 8 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6806.1, data_15_6806.2]

/-- Complete interval computation for depth 15, residue 6807. -/
theorem bounds_15_6807 : exactInterval 15 6807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6807 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6807) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6807 : oddCount 6807 15 = 8 ∧ acceleratedOrbit 15 6807 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6807 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6807) = 3 ^ 8 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6807.1, data_15_6807.2]

/-- Complete interval computation for depth 15, residue 6808. -/
theorem bounds_15_6808 : exactInterval 15 6808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6808 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6808) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6808 : oddCount 6808 15 = 8 ∧ acceleratedOrbit 15 6808 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6808 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6808) = 3 ^ 8 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6808.1, data_15_6808.2]

/-- Complete interval computation for depth 15, residue 6809. -/
theorem bounds_15_6809 : exactInterval 15 6809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6809 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6809) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6809 : oddCount 6809 15 = 9 ∧ acceleratedOrbit 15 6809 = 4094 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6809 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6809) = 3 ^ 9 * m + 4094 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6809.1, data_15_6809.2]

/-- Complete interval computation for depth 15, residue 6810. -/
theorem bounds_15_6810 : exactInterval 15 6810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6810 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6810) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6810 : oddCount 6810 15 = 8 ∧ acceleratedOrbit 15 6810 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6810 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6810) = 3 ^ 8 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6810.1, data_15_6810.2]

/-- Complete interval computation for depth 15, residue 6811. -/
theorem bounds_15_6811 : exactInterval 15 6811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6811 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6811) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6811 : oddCount 6811 15 = 11 ∧ acceleratedOrbit 15 6811 = 36830 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6811 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6811) = 3 ^ 11 * m + 36830 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6811.1, data_15_6811.2]

/-- Complete interval computation for depth 15, residue 6812. -/
theorem bounds_15_6812 : exactInterval 15 6812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6812 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6812) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6812 : oddCount 6812 15 = 7 ∧ acceleratedOrbit 15 6812 = 455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6812 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6812) = 3 ^ 7 * m + 455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6812.1, data_15_6812.2]

/-- Complete interval computation for depth 15, residue 6813. -/
theorem bounds_15_6813 : exactInterval 15 6813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6813 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6813) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6813 : oddCount 6813 15 = 7 ∧ acceleratedOrbit 15 6813 = 455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6813 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6813) = 3 ^ 7 * m + 455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6813.1, data_15_6813.2]

/-- Complete interval computation for depth 15, residue 6814. -/
theorem bounds_15_6814 : exactInterval 15 6814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6814 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6814) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6814 : oddCount 6814 15 = 7 ∧ acceleratedOrbit 15 6814 = 455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6814 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6814) = 3 ^ 7 * m + 455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6814.1, data_15_6814.2]

end Collatz.Research.PassageAtlas.Batch0208
