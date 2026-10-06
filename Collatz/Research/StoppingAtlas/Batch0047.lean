import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0047

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 706. -/
theorem bounds_10_706 : exactInterval 10 706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_706 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 706) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_706 : oddCount 706 10 = 6 ∧ acceleratedOrbit 10 706 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_706 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 706) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_706.1, data_10_706.2]

/-- Complete interval computation for depth 10, residue 707. -/
theorem bounds_10_707 : exactInterval 10 707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_707 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 707) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_707 : oddCount 707 10 = 6 ∧ acceleratedOrbit 10 707 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_707 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 707) = 3 ^ 6 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_707.1, data_10_707.2]

/-- Complete interval computation for depth 10, residue 708. -/
theorem bounds_10_708 : exactInterval 10 708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_708 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 708) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_708 : oddCount 708 10 = 3 ∧ acceleratedOrbit 10 708 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_708 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 708) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_708.1, data_10_708.2]

/-- Complete interval computation for depth 10, residue 709. -/
theorem bounds_10_709 : exactInterval 10 709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_709 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 709) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_709 : oddCount 709 10 = 3 ∧ acceleratedOrbit 10 709 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_709 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 709) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_709.1, data_10_709.2]

/-- Complete interval computation for depth 10, residue 710. -/
theorem bounds_10_710 : exactInterval 10 710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_710 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 710) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_710 : oddCount 710 10 = 3 ∧ acceleratedOrbit 10 710 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_710 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 710) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_710.1, data_10_710.2]

/-- Complete interval computation for depth 10, residue 711. -/
theorem bounds_10_711 : exactInterval 10 711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_711 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 711) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_711 : oddCount 711 10 = 5 ∧ acceleratedOrbit 10 711 = 169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_711 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 711) = 3 ^ 5 * m + 169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_711.1, data_10_711.2]

/-- Complete interval computation for depth 10, residue 712. -/
theorem bounds_10_712 : exactInterval 10 712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_712 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 712) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_712 : oddCount 712 10 = 3 ∧ acceleratedOrbit 10 712 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_712 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 712) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_712.1, data_10_712.2]

/-- Complete interval computation for depth 10, residue 713. -/
theorem bounds_10_713 : exactInterval 10 713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_713 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 713) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_713 : oddCount 713 10 = 5 ∧ acceleratedOrbit 10 713 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_713 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 713) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_713.1, data_10_713.2]

/-- Complete interval computation for depth 10, residue 714. -/
theorem bounds_10_714 : exactInterval 10 714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_714 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 714) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_714 : oddCount 714 10 = 3 ∧ acceleratedOrbit 10 714 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_714 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 714) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_714.1, data_10_714.2]

/-- Complete interval computation for depth 10, residue 715. -/
theorem bounds_10_715 : exactInterval 10 715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_715 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 715) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_715 : oddCount 715 10 = 6 ∧ acceleratedOrbit 10 715 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_715 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 715) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_715.1, data_10_715.2]

/-- Complete interval computation for depth 10, residue 716. -/
theorem bounds_10_716 : exactInterval 10 716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_716 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 716) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_716 : oddCount 716 10 = 3 ∧ acceleratedOrbit 10 716 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_716 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 716) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_716.1, data_10_716.2]

/-- Complete interval computation for depth 10, residue 717. -/
theorem bounds_10_717 : exactInterval 10 717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_717 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 717) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_717 : oddCount 717 10 = 3 ∧ acceleratedOrbit 10 717 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_717 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 717) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_717.1, data_10_717.2]

/-- Complete interval computation for depth 10, residue 718. -/
theorem bounds_10_718 : exactInterval 10 718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_718 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 718) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_718 : oddCount 718 10 = 8 ∧ acceleratedOrbit 10 718 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_718 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 718) = 3 ^ 8 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_718.1, data_10_718.2]

/-- Complete interval computation for depth 10, residue 719. -/
theorem bounds_10_719 : exactInterval 10 719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_719 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 719) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_719 : oddCount 719 10 = 8 ∧ acceleratedOrbit 10 719 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_719 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 719) = 3 ^ 8 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_719.1, data_10_719.2]

/-- Complete interval computation for depth 10, residue 720. -/
theorem bounds_10_720 : exactInterval 10 720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_720 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 720) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_720 : oddCount 720 10 = 3 ∧ acceleratedOrbit 10 720 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_720 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 720) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_720.1, data_10_720.2]

end Collatz.Research.StoppingAtlas.Batch0047
