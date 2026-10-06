import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0644

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2708. -/
theorem bounds_13_2708 : exactInterval 13 2708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2708 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2708) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2708 : oddCount 2708 13 = 8 ∧ acceleratedOrbit 13 2708 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2708 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2708) = 3 ^ 8 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2708.1, data_13_2708.2]

/-- Complete interval computation for depth 13, residue 2709. -/
theorem bounds_13_2709 : exactInterval 13 2709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2709 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2709) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2709 : oddCount 2709 13 = 8 ∧ acceleratedOrbit 13 2709 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2709 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2709) = 3 ^ 8 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2709.1, data_13_2709.2]

/-- Complete interval computation for depth 13, residue 2710. -/
theorem bounds_13_2710 : exactInterval 13 2710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2710 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2710) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2710 : oddCount 2710 13 = 7 ∧ acceleratedOrbit 13 2710 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2710 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2710) = 3 ^ 7 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2710.1, data_13_2710.2]

/-- Complete interval computation for depth 13, residue 2711. -/
theorem bounds_13_2711 : exactInterval 13 2711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2711 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2711) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2711 : oddCount 2711 13 = 7 ∧ acceleratedOrbit 13 2711 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2711 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2711) = 3 ^ 7 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2711.1, data_13_2711.2]

/-- Complete interval computation for depth 13, residue 2712. -/
theorem bounds_13_2712 : exactInterval 13 2712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2712 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2712) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2712 : oddCount 2712 13 = 8 ∧ acceleratedOrbit 13 2712 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2712 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2712) = 3 ^ 8 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2712.1, data_13_2712.2]

/-- Complete interval computation for depth 13, residue 2713. -/
theorem bounds_13_2713 : exactInterval 13 2713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2713 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2713) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2713 : oddCount 2713 13 = 8 ∧ acceleratedOrbit 13 2713 = 2177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2713 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2713) = 3 ^ 8 * m + 2177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2713.1, data_13_2713.2]

/-- Complete interval computation for depth 13, residue 2714. -/
theorem bounds_13_2714 : exactInterval 13 2714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2714 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2714) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2714 : oddCount 2714 13 = 8 ∧ acceleratedOrbit 13 2714 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2714 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2714) = 3 ^ 8 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2714.1, data_13_2714.2]

/-- Complete interval computation for depth 13, residue 2715. -/
theorem bounds_13_2715 : exactInterval 13 2715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2715 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2715) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2715 : oddCount 2715 13 = 9 ∧ acceleratedOrbit 13 2715 = 6527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2715 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2715) = 3 ^ 9 * m + 6527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2715.1, data_13_2715.2]

/-- Complete interval computation for depth 13, residue 2716. -/
theorem bounds_13_2716 : exactInterval 13 2716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2716 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2716) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2716 : oddCount 2716 13 = 8 ∧ acceleratedOrbit 13 2716 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2716 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2716) = 3 ^ 8 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2716.1, data_13_2716.2]

/-- Complete interval computation for depth 13, residue 2717. -/
theorem bounds_13_2717 : exactInterval 13 2717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2717 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2717) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2717 : oddCount 2717 13 = 8 ∧ acceleratedOrbit 13 2717 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2717 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2717) = 3 ^ 8 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2717.1, data_13_2717.2]

/-- Complete interval computation for depth 13, residue 2718. -/
theorem bounds_13_2718 : exactInterval 13 2718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2718 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2718) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2718 : oddCount 2718 13 = 8 ∧ acceleratedOrbit 13 2718 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2718 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2718) = 3 ^ 8 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2718.1, data_13_2718.2]

/-- Complete interval computation for depth 13, residue 2719. -/
theorem bounds_13_2719 : exactInterval 13 2719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2719 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2719) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2719 : oddCount 2719 13 = 9 ∧ acceleratedOrbit 13 2719 = 6536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2719 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2719) = 3 ^ 9 * m + 6536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2719.1, data_13_2719.2]

/-- Complete interval computation for depth 13, residue 2720. -/
theorem bounds_13_2720 : exactInterval 13 2720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2720 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2720) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2720 : oddCount 2720 13 = 1 ∧ acceleratedOrbit 13 2720 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2720 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2720) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2720.1, data_13_2720.2]

/-- Complete interval computation for depth 13, residue 2721. -/
theorem bounds_13_2721 : exactInterval 13 2721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2721 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2721) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2721 : oddCount 2721 13 = 8 ∧ acceleratedOrbit 13 2721 = 2182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2721 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2721) = 3 ^ 8 * m + 2182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2721.1, data_13_2721.2]

/-- Complete interval computation for depth 13, residue 2722. -/
theorem bounds_13_2722 : exactInterval 13 2722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2722 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2722) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2722 : oddCount 2722 13 = 9 ∧ acceleratedOrbit 13 2722 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2722 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2722) = 3 ^ 9 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2722.1, data_13_2722.2]

end Collatz.Research.StoppingAtlas.Batch0644
