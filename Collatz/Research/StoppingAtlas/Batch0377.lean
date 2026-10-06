import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0377

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2703. -/
theorem bounds_12_2703 : exactInterval 12 2703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2703 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2703) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2703 : oddCount 2703 12 = 8 ∧ acceleratedOrbit 12 2703 = 4333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2703 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2703) = 3 ^ 8 * m + 4333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2703.1, data_12_2703.2]

/-- Complete interval computation for depth 12, residue 2704. -/
theorem bounds_12_2704 : exactInterval 12 2704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2704 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2704) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2704 : oddCount 2704 12 = 7 ∧ acceleratedOrbit 12 2704 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2704 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2704) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2704.1, data_12_2704.2]

/-- Complete interval computation for depth 12, residue 2705. -/
theorem bounds_12_2705 : exactInterval 12 2705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2705 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2705) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2705 : oddCount 2705 12 = 7 ∧ acceleratedOrbit 12 2705 = 1448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2705 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2705) = 3 ^ 7 * m + 1448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2705.1, data_12_2705.2]

/-- Complete interval computation for depth 12, residue 2706. -/
theorem bounds_12_2706 : exactInterval 12 2706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2706 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2706) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2706 : oddCount 2706 12 = 7 ∧ acceleratedOrbit 12 2706 = 1448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2706 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2706) = 3 ^ 7 * m + 1448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2706.1, data_12_2706.2]

/-- Complete interval computation for depth 12, residue 2707. -/
theorem bounds_12_2707 : exactInterval 12 2707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2707 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2707) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2707 : oddCount 2707 12 = 7 ∧ acceleratedOrbit 12 2707 = 1448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2707 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2707) = 3 ^ 7 * m + 1448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2707.1, data_12_2707.2]

/-- Complete interval computation for depth 12, residue 2708. -/
theorem bounds_12_2708 : exactInterval 12 2708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2708 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2708) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2708 : oddCount 2708 12 = 7 ∧ acceleratedOrbit 12 2708 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2708 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2708) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2708.1, data_12_2708.2]

/-- Complete interval computation for depth 12, residue 2709. -/
theorem bounds_12_2709 : exactInterval 12 2709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2709 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2709) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2709 : oddCount 2709 12 = 7 ∧ acceleratedOrbit 12 2709 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2709 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2709) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2709.1, data_12_2709.2]

/-- Complete interval computation for depth 12, residue 2710. -/
theorem bounds_12_2710 : exactInterval 12 2710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2710 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2710) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2710 : oddCount 2710 12 = 6 ∧ acceleratedOrbit 12 2710 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2710 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2710) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2710.1, data_12_2710.2]

/-- Complete interval computation for depth 12, residue 2711. -/
theorem bounds_12_2711 : exactInterval 12 2711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2711 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2711) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2711 : oddCount 2711 12 = 6 ∧ acceleratedOrbit 12 2711 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2711 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2711) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2711.1, data_12_2711.2]

/-- Complete interval computation for depth 12, residue 2712. -/
theorem bounds_12_2712 : exactInterval 12 2712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2712 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2712) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2712 : oddCount 2712 12 = 7 ∧ acceleratedOrbit 12 2712 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2712 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2712) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2712.1, data_12_2712.2]

/-- Complete interval computation for depth 12, residue 2713. -/
theorem bounds_12_2713 : exactInterval 12 2713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2713 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2713) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2713 : oddCount 2713 12 = 7 ∧ acceleratedOrbit 12 2713 = 1451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2713 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2713) = 3 ^ 7 * m + 1451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2713.1, data_12_2713.2]

/-- Complete interval computation for depth 12, residue 2714. -/
theorem bounds_12_2714 : exactInterval 12 2714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2714 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2714) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2714 : oddCount 2714 12 = 7 ∧ acceleratedOrbit 12 2714 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2714 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2714) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2714.1, data_12_2714.2]

/-- Complete interval computation for depth 12, residue 2715. -/
theorem bounds_12_2715 : exactInterval 12 2715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2715 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2715) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2715 : oddCount 2715 12 = 9 ∧ acceleratedOrbit 12 2715 = 13054 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2715 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2715) = 3 ^ 9 * m + 13054 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2715.1, data_12_2715.2]

/-- Complete interval computation for depth 12, residue 2716. -/
theorem bounds_12_2716 : exactInterval 12 2716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2716 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2716) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2716 : oddCount 2716 12 = 7 ∧ acceleratedOrbit 12 2716 = 1453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2716 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2716) = 3 ^ 7 * m + 1453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2716.1, data_12_2716.2]

/-- Complete interval computation for depth 12, residue 2717. -/
theorem bounds_12_2717 : exactInterval 12 2717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2717 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2717) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2717 : oddCount 2717 12 = 7 ∧ acceleratedOrbit 12 2717 = 1453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2717 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2717) = 3 ^ 7 * m + 1453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2717.1, data_12_2717.2]

end Collatz.Research.StoppingAtlas.Batch0377
