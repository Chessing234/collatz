import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0816

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 26705. -/
theorem bounds_15_26705 : exactInterval 15 26705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26705 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26705) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26705 : oddCount 26705 15 = 7 ∧ acceleratedOrbit 15 26705 = 1783 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26705 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26705) = 3 ^ 7 * m + 1783 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26705.1, data_15_26705.2]

/-- Complete interval computation for depth 15, residue 26706. -/
theorem bounds_15_26706 : exactInterval 15 26706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26706 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26706) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26706 : oddCount 26706 15 = 8 ∧ acceleratedOrbit 15 26706 = 5348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26706 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26706) = 3 ^ 8 * m + 5348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26706.1, data_15_26706.2]

/-- Complete interval computation for depth 15, residue 26707. -/
theorem bounds_15_26707 : exactInterval 15 26707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26707 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26707) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26707 : oddCount 26707 15 = 8 ∧ acceleratedOrbit 15 26707 = 5348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26707 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26707) = 3 ^ 8 * m + 5348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26707.1, data_15_26707.2]

/-- Complete interval computation for depth 15, residue 26708. -/
theorem bounds_15_26708 : exactInterval 15 26708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26708 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26708) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26708 : oddCount 26708 15 = 5 ∧ acceleratedOrbit 15 26708 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26708 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26708) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26708.1, data_15_26708.2]

/-- Complete interval computation for depth 15, residue 26709. -/
theorem bounds_15_26709 : exactInterval 15 26709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26709 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26709) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26709 : oddCount 26709 15 = 5 ∧ acceleratedOrbit 15 26709 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26709 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26709) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26709.1, data_15_26709.2]

/-- Complete interval computation for depth 15, residue 26710. -/
theorem bounds_15_26710 : exactInterval 15 26710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26710 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26710) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26710 : oddCount 26710 15 = 7 ∧ acceleratedOrbit 15 26710 = 1784 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26710 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26710) = 3 ^ 7 * m + 1784 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26710.1, data_15_26710.2]

/-- Complete interval computation for depth 15, residue 26711. -/
theorem bounds_15_26711 : exactInterval 15 26711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26711 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26711) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26711 : oddCount 26711 15 = 7 ∧ acceleratedOrbit 15 26711 = 1784 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26711 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26711) = 3 ^ 7 * m + 1784 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26711.1, data_15_26711.2]

/-- Complete interval computation for depth 15, residue 26712. -/
theorem bounds_15_26712 : exactInterval 15 26712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26712 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26712) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26712 : oddCount 26712 15 = 6 ∧ acceleratedOrbit 15 26712 = 595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26712 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26712) = 3 ^ 6 * m + 595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26712.1, data_15_26712.2]

/-- Complete interval computation for depth 15, residue 26713. -/
theorem bounds_15_26713 : exactInterval 15 26713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26713 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26713) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26713 : oddCount 26713 15 = 7 ∧ acceleratedOrbit 15 26713 = 1784 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26713 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26713) = 3 ^ 7 * m + 1784 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26713.1, data_15_26713.2]

/-- Complete interval computation for depth 15, residue 26714. -/
theorem bounds_15_26714 : exactInterval 15 26714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26714 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26714) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26714 : oddCount 26714 15 = 6 ∧ acceleratedOrbit 15 26714 = 595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26714 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26714) = 3 ^ 6 * m + 595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26714.1, data_15_26714.2]

/-- Complete interval computation for depth 15, residue 26715. -/
theorem bounds_15_26715 : exactInterval 15 26715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26715 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26715) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26715 : oddCount 26715 15 = 11 ∧ acceleratedOrbit 15 26715 = 144433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26715 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26715) = 3 ^ 11 * m + 144433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26715.1, data_15_26715.2]

/-- Complete interval computation for depth 15, residue 26716. -/
theorem bounds_15_26716 : exactInterval 15 26716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26716 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26716) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26716 : oddCount 26716 15 = 6 ∧ acceleratedOrbit 15 26716 = 595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26716 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26716) = 3 ^ 6 * m + 595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26716.1, data_15_26716.2]

/-- Complete interval computation for depth 15, residue 26717. -/
theorem bounds_15_26717 : exactInterval 15 26717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26717 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26717) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26717 : oddCount 26717 15 = 6 ∧ acceleratedOrbit 15 26717 = 595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26717 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26717) = 3 ^ 6 * m + 595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26717.1, data_15_26717.2]

/-- Complete interval computation for depth 15, residue 26718. -/
theorem bounds_15_26718 : exactInterval 15 26718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26718 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26718) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26718 : oddCount 26718 15 = 9 ∧ acceleratedOrbit 15 26718 = 16051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26718 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26718) = 3 ^ 9 * m + 16051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26718.1, data_15_26718.2]

/-- Complete interval computation for depth 15, residue 26719. -/
theorem bounds_15_26719 : exactInterval 15 26719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26719 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26719) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26719 : oddCount 26719 15 = 9 ∧ acceleratedOrbit 15 26719 = 16051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26719 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26719) = 3 ^ 9 * m + 16051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26719.1, data_15_26719.2]

/-- Complete interval computation for depth 15, residue 26720. -/
theorem bounds_15_26720 : exactInterval 15 26720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26720 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26720) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26720 : oddCount 26720 15 = 5 ∧ acceleratedOrbit 15 26720 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26720 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26720) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26720.1, data_15_26720.2]

/-- Complete interval computation for depth 15, residue 26721. -/
theorem bounds_15_26721 : exactInterval 15 26721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26721 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26721) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26721 : oddCount 26721 15 = 8 ∧ acceleratedOrbit 15 26721 = 5351 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26721 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26721) = 3 ^ 8 * m + 5351 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26721.1, data_15_26721.2]

/-- Complete interval computation for depth 15, residue 26722. -/
theorem bounds_15_26722 : exactInterval 15 26722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26722 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26722) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26722 : oddCount 26722 15 = 6 ∧ acceleratedOrbit 15 26722 = 595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26722 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26722) = 3 ^ 6 * m + 595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26722.1, data_15_26722.2]

/-- Complete interval computation for depth 15, residue 26723. -/
theorem bounds_15_26723 : exactInterval 15 26723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26723 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26723) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26723 : oddCount 26723 15 = 6 ∧ acceleratedOrbit 15 26723 = 595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26723 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26723) = 3 ^ 6 * m + 595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26723.1, data_15_26723.2]

/-- Complete interval computation for depth 15, residue 26724. -/
theorem bounds_15_26724 : exactInterval 15 26724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26724 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26724) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26724 : oddCount 26724 15 = 6 ∧ acceleratedOrbit 15 26724 = 595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26724 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26724) = 3 ^ 6 * m + 595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26724.1, data_15_26724.2]

/-- Complete interval computation for depth 15, residue 26725. -/
theorem bounds_15_26725 : exactInterval 15 26725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26725 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26725) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26725 : oddCount 26725 15 = 6 ∧ acceleratedOrbit 15 26725 = 595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26725 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26725) = 3 ^ 6 * m + 595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26725.1, data_15_26725.2]

/-- Complete interval computation for depth 15, residue 26726. -/
theorem bounds_15_26726 : exactInterval 15 26726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26726 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26726) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26726 : oddCount 26726 15 = 6 ∧ acceleratedOrbit 15 26726 = 595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26726 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26726) = 3 ^ 6 * m + 595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26726.1, data_15_26726.2]

/-- Complete interval computation for depth 15, residue 26727. -/
theorem bounds_15_26727 : exactInterval 15 26727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26727 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26727) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26727 : oddCount 26727 15 = 11 ∧ acceleratedOrbit 15 26727 = 144497 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26727 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26727) = 3 ^ 11 * m + 144497 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26727.1, data_15_26727.2]

/-- Complete interval computation for depth 15, residue 26728. -/
theorem bounds_15_26728 : exactInterval 15 26728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26728 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26728) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26728 : oddCount 26728 15 = 5 ∧ acceleratedOrbit 15 26728 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26728 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26728) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26728.1, data_15_26728.2]

/-- Complete interval computation for depth 15, residue 26729. -/
theorem bounds_15_26729 : exactInterval 15 26729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26729 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26729) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26729 : oddCount 26729 15 = 9 ∧ acceleratedOrbit 15 26729 = 16058 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26729 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26729) = 3 ^ 9 * m + 16058 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26729.1, data_15_26729.2]

/-- Complete interval computation for depth 15, residue 26730. -/
theorem bounds_15_26730 : exactInterval 15 26730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26730 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26730) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26730 : oddCount 26730 15 = 5 ∧ acceleratedOrbit 15 26730 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26730 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26730) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26730.1, data_15_26730.2]

/-- Complete interval computation for depth 15, residue 26731. -/
theorem bounds_15_26731 : exactInterval 15 26731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26731 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26731) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26731 : oddCount 26731 15 = 11 ∧ acceleratedOrbit 15 26731 = 144524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26731 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26731) = 3 ^ 11 * m + 144524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26731.1, data_15_26731.2]

/-- Complete interval computation for depth 15, residue 26732. -/
theorem bounds_15_26732 : exactInterval 15 26732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26732 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26732) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26732 : oddCount 26732 15 = 8 ∧ acceleratedOrbit 15 26732 = 5354 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26732 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26732) = 3 ^ 8 * m + 5354 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26732.1, data_15_26732.2]

/-- Complete interval computation for depth 15, residue 26733. -/
theorem bounds_15_26733 : exactInterval 15 26733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26733 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26733) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26733 : oddCount 26733 15 = 8 ∧ acceleratedOrbit 15 26733 = 5354 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26733 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26733) = 3 ^ 8 * m + 5354 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26733.1, data_15_26733.2]

/-- Complete interval computation for depth 15, residue 26734. -/
theorem bounds_15_26734 : exactInterval 15 26734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26734 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26734) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26734 : oddCount 26734 15 = 8 ∧ acceleratedOrbit 15 26734 = 5354 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26734 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26734) = 3 ^ 8 * m + 5354 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26734.1, data_15_26734.2]

/-- Complete interval computation for depth 15, residue 26735. -/
theorem bounds_15_26735 : exactInterval 15 26735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26735 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26735) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26735 : oddCount 26735 15 = 12 ∧ acceleratedOrbit 15 26735 = 433619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26735 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26735) = 3 ^ 12 * m + 433619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26735.1, data_15_26735.2]

/-- Complete interval computation for depth 15, residue 26736. -/
theorem bounds_15_26736 : exactInterval 15 26736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26736 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26736) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26736 : oddCount 26736 15 = 6 ∧ acceleratedOrbit 15 26736 = 596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26736 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26736) = 3 ^ 6 * m + 596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26736.1, data_15_26736.2]

/-- Complete interval computation for depth 15, residue 26737. -/
theorem bounds_15_26737 : exactInterval 15 26737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26737 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26737) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26737 : oddCount 26737 15 = 5 ∧ acceleratedOrbit 15 26737 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26737 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26737) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26737.1, data_15_26737.2]

end Collatz.Research.PassageAtlas.Batch0816
