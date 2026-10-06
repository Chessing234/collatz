import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0938

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 30703. -/
theorem bounds_15_30703 : exactInterval 15 30703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30703 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30703) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30703 : oddCount 30703 15 = 8 ∧ acceleratedOrbit 15 30703 = 6148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30703 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30703) = 3 ^ 8 * m + 6148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30703.1, data_15_30703.2]

/-- Complete interval computation for depth 15, residue 30704. -/
theorem bounds_15_30704 : exactInterval 15 30704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30704 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30704) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30704 : oddCount 30704 15 = 8 ∧ acceleratedOrbit 15 30704 = 6151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30704 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30704) = 3 ^ 8 * m + 6151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30704.1, data_15_30704.2]

/-- Complete interval computation for depth 15, residue 30705. -/
theorem bounds_15_30705 : exactInterval 15 30705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30705 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30705) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30705 : oddCount 30705 15 = 8 ∧ acceleratedOrbit 15 30705 = 6151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30705 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30705) = 3 ^ 8 * m + 6151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30705.1, data_15_30705.2]

/-- Complete interval computation for depth 15, residue 30706. -/
theorem bounds_15_30706 : exactInterval 15 30706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30706 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30706) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30706 : oddCount 30706 15 = 10 ∧ acceleratedOrbit 15 30706 = 55343 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30706 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30706) = 3 ^ 10 * m + 55343 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30706.1, data_15_30706.2]

/-- Complete interval computation for depth 15, residue 30707. -/
theorem bounds_15_30707 : exactInterval 15 30707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30707 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30707) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30707 : oddCount 30707 15 = 10 ∧ acceleratedOrbit 15 30707 = 55343 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30707 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30707) = 3 ^ 10 * m + 55343 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30707.1, data_15_30707.2]

/-- Complete interval computation for depth 15, residue 30708. -/
theorem bounds_15_30708 : exactInterval 15 30708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30708 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30708) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30708 : oddCount 30708 15 = 8 ∧ acceleratedOrbit 15 30708 = 6151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30708 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30708) = 3 ^ 8 * m + 6151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30708.1, data_15_30708.2]

/-- Complete interval computation for depth 15, residue 30709. -/
theorem bounds_15_30709 : exactInterval 15 30709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30709 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30709) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30709 : oddCount 30709 15 = 8 ∧ acceleratedOrbit 15 30709 = 6151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30709 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30709) = 3 ^ 8 * m + 6151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30709.1, data_15_30709.2]

/-- Complete interval computation for depth 15, residue 30710. -/
theorem bounds_15_30710 : exactInterval 15 30710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30710 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30710) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30710 : oddCount 30710 15 = 10 ∧ acceleratedOrbit 15 30710 = 55349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30710 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30710) = 3 ^ 10 * m + 55349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30710.1, data_15_30710.2]

/-- Complete interval computation for depth 15, residue 30711. -/
theorem bounds_15_30711 : exactInterval 15 30711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30711 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30711) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30711 : oddCount 30711 15 = 10 ∧ acceleratedOrbit 15 30711 = 55349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30711 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30711) = 3 ^ 10 * m + 55349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30711.1, data_15_30711.2]

/-- Complete interval computation for depth 15, residue 30712. -/
theorem bounds_15_30712 : exactInterval 15 30712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30712 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30712) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30712 : oddCount 30712 15 = 11 ∧ acceleratedOrbit 15 30712 = 166076 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30712 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30712) = 3 ^ 11 * m + 166076 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30712.1, data_15_30712.2]

/-- Complete interval computation for depth 15, residue 30713. -/
theorem bounds_15_30713 : exactInterval 15 30713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30713 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30713) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30713 : oddCount 30713 15 = 7 ∧ acceleratedOrbit 15 30713 = 2050 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30713 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30713) = 3 ^ 7 * m + 2050 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30713.1, data_15_30713.2]

/-- Complete interval computation for depth 15, residue 30714. -/
theorem bounds_15_30714 : exactInterval 15 30714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30714 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30714) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30714 : oddCount 30714 15 = 11 ∧ acceleratedOrbit 15 30714 = 166076 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30714 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30714) = 3 ^ 11 * m + 166076 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30714.1, data_15_30714.2]

/-- Complete interval computation for depth 15, residue 30715. -/
theorem bounds_15_30715 : exactInterval 15 30715 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30715 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30715) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30715 : oddCount 30715 15 = 9 ∧ acceleratedOrbit 15 30715 = 18451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30715 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30715) = 3 ^ 9 * m + 18451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30715.1, data_15_30715.2]

/-- Complete interval computation for depth 15, residue 30716. -/
theorem bounds_15_30716 : exactInterval 15 30716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30716 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30716) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30716 : oddCount 30716 15 = 11 ∧ acceleratedOrbit 15 30716 = 166076 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30716 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30716) = 3 ^ 11 * m + 166076 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30716.1, data_15_30716.2]

/-- Complete interval computation for depth 15, residue 30717. -/
theorem bounds_15_30717 : exactInterval 15 30717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30717 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30717) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30717 : oddCount 30717 15 = 11 ∧ acceleratedOrbit 15 30717 = 166076 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30717 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30717) = 3 ^ 11 * m + 166076 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30717.1, data_15_30717.2]

/-- Complete interval computation for depth 15, residue 30718. -/
theorem bounds_15_30718 : exactInterval 15 30718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30718 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30718) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30718 : oddCount 30718 15 = 12 ∧ acceleratedOrbit 15 30718 = 498226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30718 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30718) = 3 ^ 12 * m + 498226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30718.1, data_15_30718.2]

/-- Complete interval computation for depth 15, residue 30719. -/
theorem bounds_15_30719 : exactInterval 15 30719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30719 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30719) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30719 : oddCount 30719 15 = 12 ∧ acceleratedOrbit 15 30719 = 498226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30719 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30719) = 3 ^ 12 * m + 498226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30719.1, data_15_30719.2]

/-- Complete interval computation for depth 15, residue 30720. -/
theorem bounds_15_30720 : exactInterval 15 30720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30720 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30720) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30720 : oddCount 30720 15 = 4 ∧ acceleratedOrbit 15 30720 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30720 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30720) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30720.1, data_15_30720.2]

/-- Complete interval computation for depth 15, residue 30721. -/
theorem bounds_15_30721 : exactInterval 15 30721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30721 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30721) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30721 : oddCount 30721 15 = 9 ∧ acceleratedOrbit 15 30721 = 18458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30721 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30721) = 3 ^ 9 * m + 18458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30721.1, data_15_30721.2]

/-- Complete interval computation for depth 15, residue 30722. -/
theorem bounds_15_30722 : exactInterval 15 30722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30722 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30722) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30722 : oddCount 30722 15 = 8 ∧ acceleratedOrbit 15 30722 = 6155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30722 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30722) = 3 ^ 8 * m + 6155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30722.1, data_15_30722.2]

/-- Complete interval computation for depth 15, residue 30723. -/
theorem bounds_15_30723 : exactInterval 15 30723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30723 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30723) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30723 : oddCount 30723 15 = 8 ∧ acceleratedOrbit 15 30723 = 6155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30723 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30723) = 3 ^ 8 * m + 6155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30723.1, data_15_30723.2]

/-- Complete interval computation for depth 15, residue 30724. -/
theorem bounds_15_30724 : exactInterval 15 30724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30724 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30724) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30724 : oddCount 30724 15 = 9 ∧ acceleratedOrbit 15 30724 = 18467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30724 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30724) = 3 ^ 9 * m + 18467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30724.1, data_15_30724.2]

/-- Complete interval computation for depth 15, residue 30725. -/
theorem bounds_15_30725 : exactInterval 15 30725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30725 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30725) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30725 : oddCount 30725 15 = 9 ∧ acceleratedOrbit 15 30725 = 18467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30725 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30725) = 3 ^ 9 * m + 18467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30725.1, data_15_30725.2]

/-- Complete interval computation for depth 15, residue 30726. -/
theorem bounds_15_30726 : exactInterval 15 30726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30726 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30726) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30726 : oddCount 30726 15 = 9 ∧ acceleratedOrbit 15 30726 = 18467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30726 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30726) = 3 ^ 9 * m + 18467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30726.1, data_15_30726.2]

/-- Complete interval computation for depth 15, residue 30727. -/
theorem bounds_15_30727 : exactInterval 15 30727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30727 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30727) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30727 : oddCount 30727 15 = 8 ∧ acceleratedOrbit 15 30727 = 6155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30727 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30727) = 3 ^ 8 * m + 6155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30727.1, data_15_30727.2]

/-- Complete interval computation for depth 15, residue 30728. -/
theorem bounds_15_30728 : exactInterval 15 30728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30728 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30728) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30728 : oddCount 30728 15 = 4 ∧ acceleratedOrbit 15 30728 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30728 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30728) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30728.1, data_15_30728.2]

/-- Complete interval computation for depth 15, residue 30729. -/
theorem bounds_15_30729 : exactInterval 15 30729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30729 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30729) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30729 : oddCount 30729 15 = 9 ∧ acceleratedOrbit 15 30729 = 18461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30729 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30729) = 3 ^ 9 * m + 18461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30729.1, data_15_30729.2]

/-- Complete interval computation for depth 15, residue 30730. -/
theorem bounds_15_30730 : exactInterval 15 30730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30730 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30730) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30730 : oddCount 30730 15 = 4 ∧ acceleratedOrbit 15 30730 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30730 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30730) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30730.1, data_15_30730.2]

/-- Complete interval computation for depth 15, residue 30731. -/
theorem bounds_15_30731 : exactInterval 15 30731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30731 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30731) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30731 : oddCount 30731 15 = 9 ∧ acceleratedOrbit 15 30731 = 18467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30731 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30731) = 3 ^ 9 * m + 18467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30731.1, data_15_30731.2]

/-- Complete interval computation for depth 15, residue 30732. -/
theorem bounds_15_30732 : exactInterval 15 30732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30732 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30732) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30732 : oddCount 30732 15 = 4 ∧ acceleratedOrbit 15 30732 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30732 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30732) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30732.1, data_15_30732.2]

/-- Complete interval computation for depth 15, residue 30733. -/
theorem bounds_15_30733 : exactInterval 15 30733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30733 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30733) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30733 : oddCount 30733 15 = 4 ∧ acceleratedOrbit 15 30733 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30733 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30733) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30733.1, data_15_30733.2]

/-- Complete interval computation for depth 15, residue 30734. -/
theorem bounds_15_30734 : exactInterval 15 30734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30734 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30734) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30734 : oddCount 30734 15 = 9 ∧ acceleratedOrbit 15 30734 = 18467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30734 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30734) = 3 ^ 9 * m + 18467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30734.1, data_15_30734.2]

/-- Complete interval computation for depth 15, residue 30735. -/
theorem bounds_15_30735 : exactInterval 15 30735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30735 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30735) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30735 : oddCount 30735 15 = 9 ∧ acceleratedOrbit 15 30735 = 18467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30735 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30735) = 3 ^ 9 * m + 18467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30735.1, data_15_30735.2]

end Collatz.Research.PassageAtlas.Batch0938
