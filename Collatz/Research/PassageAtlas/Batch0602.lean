import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0602

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 19693. -/
theorem bounds_15_19693 : exactInterval 15 19693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19693 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19693) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19693 : oddCount 19693 15 = 7 ∧ acceleratedOrbit 15 19693 = 1316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19693 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19693) = 3 ^ 7 * m + 1316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19693.1, data_15_19693.2]

/-- Complete interval computation for depth 15, residue 19694. -/
theorem bounds_15_19694 : exactInterval 15 19694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19694 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19694) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19694 : oddCount 19694 15 = 7 ∧ acceleratedOrbit 15 19694 = 1316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19694 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19694) = 3 ^ 7 * m + 1316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19694.1, data_15_19694.2]

/-- Complete interval computation for depth 15, residue 19695. -/
theorem bounds_15_19695 : exactInterval 15 19695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19695 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19695) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19695 : oddCount 19695 15 = 12 ∧ acceleratedOrbit 15 19695 = 319439 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19695 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19695) = 3 ^ 12 * m + 319439 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19695.1, data_15_19695.2]

/-- Complete interval computation for depth 15, residue 19696. -/
theorem bounds_15_19696 : exactInterval 15 19696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19696 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19696) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19696 : oddCount 19696 15 = 7 ∧ acceleratedOrbit 15 19696 = 1316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19696 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19696) = 3 ^ 7 * m + 1316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19696.1, data_15_19696.2]

/-- Complete interval computation for depth 15, residue 19697. -/
theorem bounds_15_19697 : exactInterval 15 19697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19697 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19697) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19697 : oddCount 19697 15 = 7 ∧ acceleratedOrbit 15 19697 = 1316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19697 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19697) = 3 ^ 7 * m + 1316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19697.1, data_15_19697.2]

/-- Complete interval computation for depth 15, residue 19698. -/
theorem bounds_15_19698 : exactInterval 15 19698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19698 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19698) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19698 : oddCount 19698 15 = 7 ∧ acceleratedOrbit 15 19698 = 1315 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19698 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19698) = 3 ^ 7 * m + 1315 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19698.1, data_15_19698.2]

/-- Complete interval computation for depth 15, residue 19699. -/
theorem bounds_15_19699 : exactInterval 15 19699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19699 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19699) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19699 : oddCount 19699 15 = 7 ∧ acceleratedOrbit 15 19699 = 1315 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19699 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19699) = 3 ^ 7 * m + 1315 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19699.1, data_15_19699.2]

/-- Complete interval computation for depth 15, residue 19700. -/
theorem bounds_15_19700 : exactInterval 15 19700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19700 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19700) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19700 : oddCount 19700 15 = 7 ∧ acceleratedOrbit 15 19700 = 1316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19700 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19700) = 3 ^ 7 * m + 1316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19700.1, data_15_19700.2]

/-- Complete interval computation for depth 15, residue 19701. -/
theorem bounds_15_19701 : exactInterval 15 19701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19701 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19701) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19701 : oddCount 19701 15 = 7 ∧ acceleratedOrbit 15 19701 = 1316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19701 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19701) = 3 ^ 7 * m + 1316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19701.1, data_15_19701.2]

/-- Complete interval computation for depth 15, residue 19702. -/
theorem bounds_15_19702 : exactInterval 15 19702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19702 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19702) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19702 : oddCount 19702 15 = 7 ∧ acceleratedOrbit 15 19702 = 1316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19702 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19702) = 3 ^ 7 * m + 1316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19702.1, data_15_19702.2]

/-- Complete interval computation for depth 15, residue 19703. -/
theorem bounds_15_19703 : exactInterval 15 19703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19703 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19703) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19703 : oddCount 19703 15 = 7 ∧ acceleratedOrbit 15 19703 = 1316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19703 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19703) = 3 ^ 7 * m + 1316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19703.1, data_15_19703.2]

/-- Complete interval computation for depth 15, residue 19704. -/
theorem bounds_15_19704 : exactInterval 15 19704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19704 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19704) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19704 : oddCount 19704 15 = 8 ∧ acceleratedOrbit 15 19704 = 3947 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19704 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19704) = 3 ^ 8 * m + 3947 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19704.1, data_15_19704.2]

/-- Complete interval computation for depth 15, residue 19705. -/
theorem bounds_15_19705 : exactInterval 15 19705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19705 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19705) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19705 : oddCount 19705 15 = 9 ∧ acceleratedOrbit 15 19705 = 11839 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19705 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19705) = 3 ^ 9 * m + 11839 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19705.1, data_15_19705.2]

/-- Complete interval computation for depth 15, residue 19706. -/
theorem bounds_15_19706 : exactInterval 15 19706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19706 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19706) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19706 : oddCount 19706 15 = 8 ∧ acceleratedOrbit 15 19706 = 3947 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19706 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19706) = 3 ^ 8 * m + 3947 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19706.1, data_15_19706.2]

/-- Complete interval computation for depth 15, residue 19707. -/
theorem bounds_15_19707 : exactInterval 15 19707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19707 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19707) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19707 : oddCount 19707 15 = 10 ∧ acceleratedOrbit 15 19707 = 35516 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19707 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19707) = 3 ^ 10 * m + 35516 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19707.1, data_15_19707.2]

/-- Complete interval computation for depth 15, residue 19708. -/
theorem bounds_15_19708 : exactInterval 15 19708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19708 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19708) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19708 : oddCount 19708 15 = 8 ∧ acceleratedOrbit 15 19708 = 3947 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19708 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19708) = 3 ^ 8 * m + 3947 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19708.1, data_15_19708.2]

/-- Complete interval computation for depth 15, residue 19709. -/
theorem bounds_15_19709 : exactInterval 15 19709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19709 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19709) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19709 : oddCount 19709 15 = 8 ∧ acceleratedOrbit 15 19709 = 3947 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19709 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19709) = 3 ^ 8 * m + 3947 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19709.1, data_15_19709.2]

/-- Complete interval computation for depth 15, residue 19710. -/
theorem bounds_15_19710 : exactInterval 15 19710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19710 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19710) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19710 : oddCount 19710 15 = 12 ∧ acceleratedOrbit 15 19710 = 319697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19710 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19710) = 3 ^ 12 * m + 319697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19710.1, data_15_19710.2]

/-- Complete interval computation for depth 15, residue 19711. -/
theorem bounds_15_19711 : exactInterval 15 19711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19711 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19711) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19711 : oddCount 19711 15 = 12 ∧ acceleratedOrbit 15 19711 = 319697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19711 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19711) = 3 ^ 12 * m + 319697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19711.1, data_15_19711.2]

/-- Complete interval computation for depth 15, residue 19712. -/
theorem bounds_15_19712 : exactInterval 15 19712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19712 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19712) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19712 : oddCount 19712 15 = 3 ∧ acceleratedOrbit 15 19712 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19712 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19712) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19712.1, data_15_19712.2]

/-- Complete interval computation for depth 15, residue 19713. -/
theorem bounds_15_19713 : exactInterval 15 19713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19713 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19713) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19713 : oddCount 19713 15 = 9 ∧ acceleratedOrbit 15 19713 = 11846 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19713 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19713) = 3 ^ 9 * m + 11846 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19713.1, data_15_19713.2]

/-- Complete interval computation for depth 15, residue 19714. -/
theorem bounds_15_19714 : exactInterval 15 19714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19714 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19714) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19714 : oddCount 19714 15 = 9 ∧ acceleratedOrbit 15 19714 = 11846 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19714 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19714) = 3 ^ 9 * m + 11846 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19714.1, data_15_19714.2]

/-- Complete interval computation for depth 15, residue 19715. -/
theorem bounds_15_19715 : exactInterval 15 19715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19715 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19715) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19715 : oddCount 19715 15 = 9 ∧ acceleratedOrbit 15 19715 = 11846 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19715 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19715) = 3 ^ 9 * m + 11846 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19715.1, data_15_19715.2]

/-- Complete interval computation for depth 15, residue 19716. -/
theorem bounds_15_19716 : exactInterval 15 19716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19716 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19716) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19716 : oddCount 19716 15 = 4 ∧ acceleratedOrbit 15 19716 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19716 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19716) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19716.1, data_15_19716.2]

/-- Complete interval computation for depth 15, residue 19717. -/
theorem bounds_15_19717 : exactInterval 15 19717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19717 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19717) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19717 : oddCount 19717 15 = 4 ∧ acceleratedOrbit 15 19717 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19717 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19717) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19717.1, data_15_19717.2]

/-- Complete interval computation for depth 15, residue 19718. -/
theorem bounds_15_19718 : exactInterval 15 19718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19718 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19718) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19718 : oddCount 19718 15 = 4 ∧ acceleratedOrbit 15 19718 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19718 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19718) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19718.1, data_15_19718.2]

/-- Complete interval computation for depth 15, residue 19719. -/
theorem bounds_15_19719 : exactInterval 15 19719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19719 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19719) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19719 : oddCount 19719 15 = 11 ∧ acceleratedOrbit 15 19719 = 106616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19719 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19719) = 3 ^ 11 * m + 106616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19719.1, data_15_19719.2]

/-- Complete interval computation for depth 15, residue 19720. -/
theorem bounds_15_19720 : exactInterval 15 19720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19720 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19720) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19720 : oddCount 19720 15 = 7 ∧ acceleratedOrbit 15 19720 = 1318 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19720 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19720) = 3 ^ 7 * m + 1318 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19720.1, data_15_19720.2]

/-- Complete interval computation for depth 15, residue 19721. -/
theorem bounds_15_19721 : exactInterval 15 19721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19721 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19721) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19721 : oddCount 19721 15 = 9 ∧ acceleratedOrbit 15 19721 = 11848 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19721 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19721) = 3 ^ 9 * m + 11848 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19721.1, data_15_19721.2]

/-- Complete interval computation for depth 15, residue 19722. -/
theorem bounds_15_19722 : exactInterval 15 19722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19722 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19722) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19722 : oddCount 19722 15 = 7 ∧ acceleratedOrbit 15 19722 = 1318 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19722 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19722) = 3 ^ 7 * m + 1318 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19722.1, data_15_19722.2]

/-- Complete interval computation for depth 15, residue 19723. -/
theorem bounds_15_19723 : exactInterval 15 19723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19723 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19723) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19723 : oddCount 19723 15 = 9 ∧ acceleratedOrbit 15 19723 = 11852 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19723 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19723) = 3 ^ 9 * m + 11852 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19723.1, data_15_19723.2]

/-- Complete interval computation for depth 15, residue 19724. -/
theorem bounds_15_19724 : exactInterval 15 19724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19724 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19724) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19724 : oddCount 19724 15 = 7 ∧ acceleratedOrbit 15 19724 = 1318 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19724 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19724) = 3 ^ 7 * m + 1318 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19724.1, data_15_19724.2]

/-- Complete interval computation for depth 15, residue 19725. -/
theorem bounds_15_19725 : exactInterval 15 19725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19725 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19725) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19725 : oddCount 19725 15 = 7 ∧ acceleratedOrbit 15 19725 = 1318 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19725 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19725) = 3 ^ 7 * m + 1318 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19725.1, data_15_19725.2]

end Collatz.Research.PassageAtlas.Batch0602
