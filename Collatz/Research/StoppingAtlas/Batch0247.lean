import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0247

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 706. -/
theorem bounds_12_706 : exactInterval 12 706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_706 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 706) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_706 : oddCount 706 12 = 7 ∧ acceleratedOrbit 12 706 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_706 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 706) = 3 ^ 7 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_706.1, data_12_706.2]

/-- Complete interval computation for depth 12, residue 707. -/
theorem bounds_12_707 : exactInterval 12 707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_707 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 707) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_707 : oddCount 707 12 = 7 ∧ acceleratedOrbit 12 707 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_707 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 707) = 3 ^ 7 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_707.1, data_12_707.2]

/-- Complete interval computation for depth 12, residue 708. -/
theorem bounds_12_708 : exactInterval 12 708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_708 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 708) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_708 : oddCount 708 12 = 5 ∧ acceleratedOrbit 12 708 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_708 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 708) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_708.1, data_12_708.2]

/-- Complete interval computation for depth 12, residue 709. -/
theorem bounds_12_709 : exactInterval 12 709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_709 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 709) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_709 : oddCount 709 12 = 5 ∧ acceleratedOrbit 12 709 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_709 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 709) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_709.1, data_12_709.2]

/-- Complete interval computation for depth 12, residue 710. -/
theorem bounds_12_710 : exactInterval 12 710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_710 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 710) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_710 : oddCount 710 12 = 5 ∧ acceleratedOrbit 12 710 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_710 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 710) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_710.1, data_12_710.2]

/-- Complete interval computation for depth 12, residue 711. -/
theorem bounds_12_711 : exactInterval 12 711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_711 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 711) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_711 : oddCount 711 12 = 6 ∧ acceleratedOrbit 12 711 = 127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_711 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 711) = 3 ^ 6 * m + 127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_711.1, data_12_711.2]

/-- Complete interval computation for depth 12, residue 712. -/
theorem bounds_12_712 : exactInterval 12 712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_712 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 712) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_712 : oddCount 712 12 = 5 ∧ acceleratedOrbit 12 712 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_712 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 712) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_712.1, data_12_712.2]

/-- Complete interval computation for depth 12, residue 713. -/
theorem bounds_12_713 : exactInterval 12 713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_713 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 713) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_713 : oddCount 713 12 = 6 ∧ acceleratedOrbit 12 713 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_713 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 713) = 3 ^ 6 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_713.1, data_12_713.2]

/-- Complete interval computation for depth 12, residue 714. -/
theorem bounds_12_714 : exactInterval 12 714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_714 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 714) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_714 : oddCount 714 12 = 5 ∧ acceleratedOrbit 12 714 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_714 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 714) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_714.1, data_12_714.2]

/-- Complete interval computation for depth 12, residue 715. -/
theorem bounds_12_715 : exactInterval 12 715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_715 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 715) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_715 : oddCount 715 12 = 6 ∧ acceleratedOrbit 12 715 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_715 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 715) = 3 ^ 6 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_715.1, data_12_715.2]

/-- Complete interval computation for depth 12, residue 716. -/
theorem bounds_12_716 : exactInterval 12 716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_716 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 716) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_716 : oddCount 716 12 = 5 ∧ acceleratedOrbit 12 716 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_716 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 716) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_716.1, data_12_716.2]

/-- Complete interval computation for depth 12, residue 717. -/
theorem bounds_12_717 : exactInterval 12 717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_717 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 717) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_717 : oddCount 717 12 = 5 ∧ acceleratedOrbit 12 717 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_717 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 717) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_717.1, data_12_717.2]

/-- Complete interval computation for depth 12, residue 718. -/
theorem bounds_12_718 : exactInterval 12 718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_718 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 718) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_718 : oddCount 718 12 = 8 ∧ acceleratedOrbit 12 718 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_718 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 718) = 3 ^ 8 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_718.1, data_12_718.2]

/-- Complete interval computation for depth 12, residue 719. -/
theorem bounds_12_719 : exactInterval 12 719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_719 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 719) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_719 : oddCount 719 12 = 8 ∧ acceleratedOrbit 12 719 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_719 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 719) = 3 ^ 8 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_719.1, data_12_719.2]

/-- Complete interval computation for depth 12, residue 720. -/
theorem bounds_12_720 : exactInterval 12 720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_720 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 720) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_720 : oddCount 720 12 = 3 ∧ acceleratedOrbit 12 720 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_720 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 720) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_720.1, data_12_720.2]

end Collatz.Research.StoppingAtlas.Batch0247
