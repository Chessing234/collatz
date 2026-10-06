import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0694

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 22708. -/
theorem bounds_15_22708 : exactInterval 15 22708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22708 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22708) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22708 : oddCount 22708 15 = 6 ∧ acceleratedOrbit 15 22708 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22708 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22708) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22708.1, data_15_22708.2]

/-- Complete interval computation for depth 15, residue 22709. -/
theorem bounds_15_22709 : exactInterval 15 22709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22709 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22709) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22709 : oddCount 22709 15 = 6 ∧ acceleratedOrbit 15 22709 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22709 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22709) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22709.1, data_15_22709.2]

/-- Complete interval computation for depth 15, residue 22710. -/
theorem bounds_15_22710 : exactInterval 15 22710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22710 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22710) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22710 : oddCount 22710 15 = 10 ∧ acceleratedOrbit 15 22710 = 40931 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22710 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22710) = 3 ^ 10 * m + 40931 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22710.1, data_15_22710.2]

/-- Complete interval computation for depth 15, residue 22711. -/
theorem bounds_15_22711 : exactInterval 15 22711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22711 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22711) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22711 : oddCount 22711 15 = 10 ∧ acceleratedOrbit 15 22711 = 40931 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22711 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22711) = 3 ^ 10 * m + 40931 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22711.1, data_15_22711.2]

/-- Complete interval computation for depth 15, residue 22712. -/
theorem bounds_15_22712 : exactInterval 15 22712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22712 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22712) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22712 : oddCount 22712 15 = 6 ∧ acceleratedOrbit 15 22712 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22712 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22712) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22712.1, data_15_22712.2]

/-- Complete interval computation for depth 15, residue 22713. -/
theorem bounds_15_22713 : exactInterval 15 22713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22713 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22713) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22713 : oddCount 22713 15 = 8 ∧ acceleratedOrbit 15 22713 = 4549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22713 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22713) = 3 ^ 8 * m + 4549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22713.1, data_15_22713.2]

/-- Complete interval computation for depth 15, residue 22714. -/
theorem bounds_15_22714 : exactInterval 15 22714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22714 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22714) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22714 : oddCount 22714 15 = 6 ∧ acceleratedOrbit 15 22714 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22714 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22714) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22714.1, data_15_22714.2]

/-- Complete interval computation for depth 15, residue 22715. -/
theorem bounds_15_22715 : exactInterval 15 22715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22715 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22715) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22715 : oddCount 22715 15 = 9 ∧ acceleratedOrbit 15 22715 = 13646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22715 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22715) = 3 ^ 9 * m + 13646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22715.1, data_15_22715.2]

/-- Complete interval computation for depth 15, residue 22716. -/
theorem bounds_15_22716 : exactInterval 15 22716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22716 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22716) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22716 : oddCount 22716 15 = 10 ∧ acceleratedOrbit 15 22716 = 40945 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22716 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22716) = 3 ^ 10 * m + 40945 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22716.1, data_15_22716.2]

/-- Complete interval computation for depth 15, residue 22717. -/
theorem bounds_15_22717 : exactInterval 15 22717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22717 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22717) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22717 : oddCount 22717 15 = 10 ∧ acceleratedOrbit 15 22717 = 40945 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22717 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22717) = 3 ^ 10 * m + 40945 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22717.1, data_15_22717.2]

/-- Complete interval computation for depth 15, residue 22718. -/
theorem bounds_15_22718 : exactInterval 15 22718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22718 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22718) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22718 : oddCount 22718 15 = 10 ∧ acceleratedOrbit 15 22718 = 40945 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22718 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22718) = 3 ^ 10 * m + 40945 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22718.1, data_15_22718.2]

/-- Complete interval computation for depth 15, residue 22719. -/
theorem bounds_15_22719 : exactInterval 15 22719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22719 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22719) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22719 : oddCount 22719 15 = 9 ∧ acceleratedOrbit 15 22719 = 13648 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22719 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22719) = 3 ^ 9 * m + 13648 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22719.1, data_15_22719.2]

/-- Complete interval computation for depth 15, residue 22720. -/
theorem bounds_15_22720 : exactInterval 15 22720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22720 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22720) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22720 : oddCount 22720 15 = 3 ∧ acceleratedOrbit 15 22720 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22720 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22720) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22720.1, data_15_22720.2]

/-- Complete interval computation for depth 15, residue 22721. -/
theorem bounds_15_22721 : exactInterval 15 22721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22721 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22721) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22721 : oddCount 22721 15 = 7 ∧ acceleratedOrbit 15 22721 = 1517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22721 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22721) = 3 ^ 7 * m + 1517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22721.1, data_15_22721.2]

/-- Complete interval computation for depth 15, residue 22722. -/
theorem bounds_15_22722 : exactInterval 15 22722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22722 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22722) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22722 : oddCount 22722 15 = 7 ∧ acceleratedOrbit 15 22722 = 1517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22722 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22722) = 3 ^ 7 * m + 1517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22722.1, data_15_22722.2]

/-- Complete interval computation for depth 15, residue 22723. -/
theorem bounds_15_22723 : exactInterval 15 22723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22723 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22723) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22723 : oddCount 22723 15 = 7 ∧ acceleratedOrbit 15 22723 = 1517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22723 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22723) = 3 ^ 7 * m + 1517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22723.1, data_15_22723.2]

/-- Complete interval computation for depth 15, residue 22724. -/
theorem bounds_15_22724 : exactInterval 15 22724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22724 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22724) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22724 : oddCount 22724 15 = 8 ∧ acceleratedOrbit 15 22724 = 4556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22724 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22724) = 3 ^ 8 * m + 4556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22724.1, data_15_22724.2]

/-- Complete interval computation for depth 15, residue 22725. -/
theorem bounds_15_22725 : exactInterval 15 22725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22725 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22725) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22725 : oddCount 22725 15 = 8 ∧ acceleratedOrbit 15 22725 = 4556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22725 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22725) = 3 ^ 8 * m + 4556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22725.1, data_15_22725.2]

/-- Complete interval computation for depth 15, residue 22726. -/
theorem bounds_15_22726 : exactInterval 15 22726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22726 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22726) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22726 : oddCount 22726 15 = 8 ∧ acceleratedOrbit 15 22726 = 4556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22726 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22726) = 3 ^ 8 * m + 4556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22726.1, data_15_22726.2]

/-- Complete interval computation for depth 15, residue 22727. -/
theorem bounds_15_22727 : exactInterval 15 22727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22727 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22727) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22727 : oddCount 22727 15 = 7 ∧ acceleratedOrbit 15 22727 = 1517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22727 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22727) = 3 ^ 7 * m + 1517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22727.1, data_15_22727.2]

/-- Complete interval computation for depth 15, residue 22728. -/
theorem bounds_15_22728 : exactInterval 15 22728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22728 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22728) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22728 : oddCount 22728 15 = 8 ∧ acceleratedOrbit 15 22728 = 4556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22728 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22728) = 3 ^ 8 * m + 4556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22728.1, data_15_22728.2]

/-- Complete interval computation for depth 15, residue 22729. -/
theorem bounds_15_22729 : exactInterval 15 22729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22729 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22729) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22729 : oddCount 22729 15 = 6 ∧ acceleratedOrbit 15 22729 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22729 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22729) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22729.1, data_15_22729.2]

/-- Complete interval computation for depth 15, residue 22730. -/
theorem bounds_15_22730 : exactInterval 15 22730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22730 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22730) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22730 : oddCount 22730 15 = 8 ∧ acceleratedOrbit 15 22730 = 4556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22730 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22730) = 3 ^ 8 * m + 4556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22730.1, data_15_22730.2]

/-- Complete interval computation for depth 15, residue 22731. -/
theorem bounds_15_22731 : exactInterval 15 22731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22731 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22731) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22731 : oddCount 22731 15 = 8 ∧ acceleratedOrbit 15 22731 = 4553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22731 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22731) = 3 ^ 8 * m + 4553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22731.1, data_15_22731.2]

/-- Complete interval computation for depth 15, residue 22732. -/
theorem bounds_15_22732 : exactInterval 15 22732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22732 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22732) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22732 : oddCount 22732 15 = 8 ∧ acceleratedOrbit 15 22732 = 4556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22732 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22732) = 3 ^ 8 * m + 4556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22732.1, data_15_22732.2]

/-- Complete interval computation for depth 15, residue 22733. -/
theorem bounds_15_22733 : exactInterval 15 22733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22733 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22733) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22733 : oddCount 22733 15 = 8 ∧ acceleratedOrbit 15 22733 = 4556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22733 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22733) = 3 ^ 8 * m + 4556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22733.1, data_15_22733.2]

/-- Complete interval computation for depth 15, residue 22734. -/
theorem bounds_15_22734 : exactInterval 15 22734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22734 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22734) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22734 : oddCount 22734 15 = 11 ∧ acceleratedOrbit 15 22734 = 122917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22734 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22734) = 3 ^ 11 * m + 122917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22734.1, data_15_22734.2]

/-- Complete interval computation for depth 15, residue 22735. -/
theorem bounds_15_22735 : exactInterval 15 22735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22735 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22735) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22735 : oddCount 22735 15 = 11 ∧ acceleratedOrbit 15 22735 = 122917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22735 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22735) = 3 ^ 11 * m + 122917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22735.1, data_15_22735.2]

/-- Complete interval computation for depth 15, residue 22736. -/
theorem bounds_15_22736 : exactInterval 15 22736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22736 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22736) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22736 : oddCount 22736 15 = 3 ∧ acceleratedOrbit 15 22736 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22736 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22736) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22736.1, data_15_22736.2]

/-- Complete interval computation for depth 15, residue 22737. -/
theorem bounds_15_22737 : exactInterval 15 22737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22737 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22737) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22737 : oddCount 22737 15 = 10 ∧ acceleratedOrbit 15 22737 = 40985 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22737 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22737) = 3 ^ 10 * m + 40985 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22737.1, data_15_22737.2]

/-- Complete interval computation for depth 15, residue 22738. -/
theorem bounds_15_22738 : exactInterval 15 22738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22738 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22738) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22738 : oddCount 22738 15 = 10 ∧ acceleratedOrbit 15 22738 = 40985 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22738 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22738) = 3 ^ 10 * m + 40985 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22738.1, data_15_22738.2]

/-- Complete interval computation for depth 15, residue 22739. -/
theorem bounds_15_22739 : exactInterval 15 22739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22739 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22739) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22739 : oddCount 22739 15 = 10 ∧ acceleratedOrbit 15 22739 = 40985 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22739 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22739) = 3 ^ 10 * m + 40985 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22739.1, data_15_22739.2]

end Collatz.Research.PassageAtlas.Batch0694
