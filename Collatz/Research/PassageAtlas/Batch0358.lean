import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0358

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 11698. -/
theorem bounds_15_11698 : exactInterval 15 11698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11698 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11698) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11698 : oddCount 11698 15 = 8 ∧ acceleratedOrbit 15 11698 = 2348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11698 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11698) = 3 ^ 8 * m + 2348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11698.1, data_15_11698.2]

/-- Complete interval computation for depth 15, residue 11699. -/
theorem bounds_15_11699 : exactInterval 15 11699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11699 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11699) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11699 : oddCount 11699 15 = 8 ∧ acceleratedOrbit 15 11699 = 2348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11699 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11699) = 3 ^ 8 * m + 2348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11699.1, data_15_11699.2]

/-- Complete interval computation for depth 15, residue 11700. -/
theorem bounds_15_11700 : exactInterval 15 11700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11700 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11700) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11700 : oddCount 11700 15 = 8 ∧ acceleratedOrbit 15 11700 = 2348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11700 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11700) = 3 ^ 8 * m + 2348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11700.1, data_15_11700.2]

/-- Complete interval computation for depth 15, residue 11701. -/
theorem bounds_15_11701 : exactInterval 15 11701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11701 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11701) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11701 : oddCount 11701 15 = 8 ∧ acceleratedOrbit 15 11701 = 2348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11701 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11701) = 3 ^ 8 * m + 2348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11701.1, data_15_11701.2]

/-- Complete interval computation for depth 15, residue 11702. -/
theorem bounds_15_11702 : exactInterval 15 11702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11702 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11702) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11702 : oddCount 11702 15 = 8 ∧ acceleratedOrbit 15 11702 = 2344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11702 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11702) = 3 ^ 8 * m + 2344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11702.1, data_15_11702.2]

/-- Complete interval computation for depth 15, residue 11703. -/
theorem bounds_15_11703 : exactInterval 15 11703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11703 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11703) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11703 : oddCount 11703 15 = 8 ∧ acceleratedOrbit 15 11703 = 2344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11703 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11703) = 3 ^ 8 * m + 2344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11703.1, data_15_11703.2]

/-- Complete interval computation for depth 15, residue 11704. -/
theorem bounds_15_11704 : exactInterval 15 11704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11704 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11704) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11704 : oddCount 11704 15 = 8 ∧ acceleratedOrbit 15 11704 = 2348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11704 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11704) = 3 ^ 8 * m + 2348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11704.1, data_15_11704.2]

/-- Complete interval computation for depth 15, residue 11705. -/
theorem bounds_15_11705 : exactInterval 15 11705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11705 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11705) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11705 : oddCount 11705 15 = 8 ∧ acceleratedOrbit 15 11705 = 2348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11705 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11705) = 3 ^ 8 * m + 2348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11705.1, data_15_11705.2]

/-- Complete interval computation for depth 15, residue 11706. -/
theorem bounds_15_11706 : exactInterval 15 11706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11706 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11706) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11706 : oddCount 11706 15 = 8 ∧ acceleratedOrbit 15 11706 = 2348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11706 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11706) = 3 ^ 8 * m + 2348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11706.1, data_15_11706.2]

/-- Complete interval computation for depth 15, residue 11707. -/
theorem bounds_15_11707 : exactInterval 15 11707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11707 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11707) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11707 : oddCount 11707 15 = 7 ∧ acceleratedOrbit 15 11707 = 782 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11707 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11707) = 3 ^ 7 * m + 782 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11707.1, data_15_11707.2]

/-- Complete interval computation for depth 15, residue 11708. -/
theorem bounds_15_11708 : exactInterval 15 11708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11708 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11708) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11708 : oddCount 11708 15 = 9 ∧ acceleratedOrbit 15 11708 = 7037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11708 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11708) = 3 ^ 9 * m + 7037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11708.1, data_15_11708.2]

/-- Complete interval computation for depth 15, residue 11709. -/
theorem bounds_15_11709 : exactInterval 15 11709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11709 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11709) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11709 : oddCount 11709 15 = 9 ∧ acceleratedOrbit 15 11709 = 7037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11709 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11709) = 3 ^ 9 * m + 7037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11709.1, data_15_11709.2]

/-- Complete interval computation for depth 15, residue 11710. -/
theorem bounds_15_11710 : exactInterval 15 11710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11710 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11710) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11710 : oddCount 11710 15 = 9 ∧ acceleratedOrbit 15 11710 = 7037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11710 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11710) = 3 ^ 9 * m + 7037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11710.1, data_15_11710.2]

/-- Complete interval computation for depth 15, residue 11711. -/
theorem bounds_15_11711 : exactInterval 15 11711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11711 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11711) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11711 : oddCount 11711 15 = 11 ∧ acceleratedOrbit 15 11711 = 63317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11711 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11711) = 3 ^ 11 * m + 63317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11711.1, data_15_11711.2]

/-- Complete interval computation for depth 15, residue 11712. -/
theorem bounds_15_11712 : exactInterval 15 11712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11712 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11712) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11712 : oddCount 11712 15 = 6 ∧ acceleratedOrbit 15 11712 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11712 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11712) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11712.1, data_15_11712.2]

/-- Complete interval computation for depth 15, residue 11713. -/
theorem bounds_15_11713 : exactInterval 15 11713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11713 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11713) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11713 : oddCount 11713 15 = 9 ∧ acceleratedOrbit 15 11713 = 7040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11713 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11713) = 3 ^ 9 * m + 7040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11713.1, data_15_11713.2]

/-- Complete interval computation for depth 15, residue 11714. -/
theorem bounds_15_11714 : exactInterval 15 11714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11714 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11714) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11714 : oddCount 11714 15 = 9 ∧ acceleratedOrbit 15 11714 = 7040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11714 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11714) = 3 ^ 9 * m + 7040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11714.1, data_15_11714.2]

/-- Complete interval computation for depth 15, residue 11715. -/
theorem bounds_15_11715 : exactInterval 15 11715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11715 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11715) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11715 : oddCount 11715 15 = 9 ∧ acceleratedOrbit 15 11715 = 7040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11715 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11715) = 3 ^ 9 * m + 7040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11715.1, data_15_11715.2]

/-- Complete interval computation for depth 15, residue 11716. -/
theorem bounds_15_11716 : exactInterval 15 11716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11716 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11716) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11716 : oddCount 11716 15 = 6 ∧ acceleratedOrbit 15 11716 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11716 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11716) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11716.1, data_15_11716.2]

/-- Complete interval computation for depth 15, residue 11717. -/
theorem bounds_15_11717 : exactInterval 15 11717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11717 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11717) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11717 : oddCount 11717 15 = 6 ∧ acceleratedOrbit 15 11717 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11717 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11717) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11717.1, data_15_11717.2]

/-- Complete interval computation for depth 15, residue 11718. -/
theorem bounds_15_11718 : exactInterval 15 11718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11718 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11718) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11718 : oddCount 11718 15 = 6 ∧ acceleratedOrbit 15 11718 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11718 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11718) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11718.1, data_15_11718.2]

/-- Complete interval computation for depth 15, residue 11719. -/
theorem bounds_15_11719 : exactInterval 15 11719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11719 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11719) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11719 : oddCount 11719 15 = 8 ∧ acceleratedOrbit 15 11719 = 2348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11719 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11719) = 3 ^ 8 * m + 2348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11719.1, data_15_11719.2]

/-- Complete interval computation for depth 15, residue 11720. -/
theorem bounds_15_11720 : exactInterval 15 11720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11720 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11720) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11720 : oddCount 11720 15 = 4 ∧ acceleratedOrbit 15 11720 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11720 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11720) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11720.1, data_15_11720.2]

/-- Complete interval computation for depth 15, residue 11721. -/
theorem bounds_15_11721 : exactInterval 15 11721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11721 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11721) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11721 : oddCount 11721 15 = 9 ∧ acceleratedOrbit 15 11721 = 7046 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11721 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11721) = 3 ^ 9 * m + 7046 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11721.1, data_15_11721.2]

/-- Complete interval computation for depth 15, residue 11722. -/
theorem bounds_15_11722 : exactInterval 15 11722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11722 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11722) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11722 : oddCount 11722 15 = 4 ∧ acceleratedOrbit 15 11722 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11722 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11722) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11722.1, data_15_11722.2]

/-- Complete interval computation for depth 15, residue 11723. -/
theorem bounds_15_11723 : exactInterval 15 11723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11723 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11723) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11723 : oddCount 11723 15 = 10 ∧ acceleratedOrbit 15 11723 = 21140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11723 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11723) = 3 ^ 10 * m + 21140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11723.1, data_15_11723.2]

/-- Complete interval computation for depth 15, residue 11724. -/
theorem bounds_15_11724 : exactInterval 15 11724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11724 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11724) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11724 : oddCount 11724 15 = 4 ∧ acceleratedOrbit 15 11724 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11724 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11724) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11724.1, data_15_11724.2]

/-- Complete interval computation for depth 15, residue 11725. -/
theorem bounds_15_11725 : exactInterval 15 11725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11725 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11725) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11725 : oddCount 11725 15 = 4 ∧ acceleratedOrbit 15 11725 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11725 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11725) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11725.1, data_15_11725.2]

/-- Complete interval computation for depth 15, residue 11726. -/
theorem bounds_15_11726 : exactInterval 15 11726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11726 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11726) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11726 : oddCount 11726 15 = 10 ∧ acceleratedOrbit 15 11726 = 21136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11726 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11726) = 3 ^ 10 * m + 21136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11726.1, data_15_11726.2]

/-- Complete interval computation for depth 15, residue 11727. -/
theorem bounds_15_11727 : exactInterval 15 11727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11727 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11727) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11727 : oddCount 11727 15 = 10 ∧ acceleratedOrbit 15 11727 = 21136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11727 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11727) = 3 ^ 10 * m + 21136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11727.1, data_15_11727.2]

/-- Complete interval computation for depth 15, residue 11728. -/
theorem bounds_15_11728 : exactInterval 15 11728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11728 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11728) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11728 : oddCount 11728 15 = 6 ∧ acceleratedOrbit 15 11728 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11728 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11728) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11728.1, data_15_11728.2]

/-- Complete interval computation for depth 15, residue 11729. -/
theorem bounds_15_11729 : exactInterval 15 11729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11729 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11729) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11729 : oddCount 11729 15 = 4 ∧ acceleratedOrbit 15 11729 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11729 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11729) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11729.1, data_15_11729.2]

end Collatz.Research.PassageAtlas.Batch0358
