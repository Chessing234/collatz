import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0774

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4705. -/
theorem bounds_13_4705 : exactInterval 13 4705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4705 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4705) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4705 : oddCount 4705 13 = 6 ∧ acceleratedOrbit 13 4705 = 419 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4705 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4705) = 3 ^ 6 * m + 419 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4705.1, data_13_4705.2]

/-- Complete interval computation for depth 13, residue 4706. -/
theorem bounds_13_4706 : exactInterval 13 4706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4706 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4706) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4706 : oddCount 4706 13 = 5 ∧ acceleratedOrbit 13 4706 = 140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4706 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4706) = 3 ^ 5 * m + 140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4706.1, data_13_4706.2]

/-- Complete interval computation for depth 13, residue 4707. -/
theorem bounds_13_4707 : exactInterval 13 4707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4707 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4707) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4707 : oddCount 4707 13 = 5 ∧ acceleratedOrbit 13 4707 = 140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4707 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4707) = 3 ^ 5 * m + 140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4707.1, data_13_4707.2]

/-- Complete interval computation for depth 13, residue 4708. -/
theorem bounds_13_4708 : exactInterval 13 4708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4708 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4708) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4708 : oddCount 4708 13 = 5 ∧ acceleratedOrbit 13 4708 = 140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4708 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4708) = 3 ^ 5 * m + 140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4708.1, data_13_4708.2]

/-- Complete interval computation for depth 13, residue 4709. -/
theorem bounds_13_4709 : exactInterval 13 4709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4709 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4709) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4709 : oddCount 4709 13 = 5 ∧ acceleratedOrbit 13 4709 = 140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4709 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4709) = 3 ^ 5 * m + 140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4709.1, data_13_4709.2]

/-- Complete interval computation for depth 13, residue 4710. -/
theorem bounds_13_4710 : exactInterval 13 4710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4710 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4710) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4710 : oddCount 4710 13 = 5 ∧ acceleratedOrbit 13 4710 = 140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4710 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4710) = 3 ^ 5 * m + 140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4710.1, data_13_4710.2]

/-- Complete interval computation for depth 13, residue 4711. -/
theorem bounds_13_4711 : exactInterval 13 4711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4711 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4711) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4711 : oddCount 4711 13 = 7 ∧ acceleratedOrbit 13 4711 = 1258 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4711 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4711) = 3 ^ 7 * m + 1258 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4711.1, data_13_4711.2]

/-- Complete interval computation for depth 13, residue 4712. -/
theorem bounds_13_4712 : exactInterval 13 4712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4712 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4712) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4712 : oddCount 4712 13 = 4 ∧ acceleratedOrbit 13 4712 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4712 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4712) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4712.1, data_13_4712.2]

/-- Complete interval computation for depth 13, residue 4713. -/
theorem bounds_13_4713 : exactInterval 13 4713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4713 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4713) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4713 : oddCount 4713 13 = 9 ∧ acceleratedOrbit 13 4713 = 11330 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4713 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4713) = 3 ^ 9 * m + 11330 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4713.1, data_13_4713.2]

/-- Complete interval computation for depth 13, residue 4714. -/
theorem bounds_13_4714 : exactInterval 13 4714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4714 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4714) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4714 : oddCount 4714 13 = 4 ∧ acceleratedOrbit 13 4714 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4714 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4714) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4714.1, data_13_4714.2]

/-- Complete interval computation for depth 13, residue 4715. -/
theorem bounds_13_4715 : exactInterval 13 4715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4715 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4715) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4715 : oddCount 4715 13 = 8 ∧ acceleratedOrbit 13 4715 = 3779 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4715 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4715) = 3 ^ 8 * m + 3779 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4715.1, data_13_4715.2]

/-- Complete interval computation for depth 13, residue 4716. -/
theorem bounds_13_4716 : exactInterval 13 4716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4716 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4716) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4716 : oddCount 4716 13 = 8 ∧ acceleratedOrbit 13 4716 = 3782 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4716 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4716) = 3 ^ 8 * m + 3782 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4716.1, data_13_4716.2]

/-- Complete interval computation for depth 13, residue 4717. -/
theorem bounds_13_4717 : exactInterval 13 4717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4717 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4717) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4717 : oddCount 4717 13 = 8 ∧ acceleratedOrbit 13 4717 = 3782 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4717 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4717) = 3 ^ 8 * m + 3782 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4717.1, data_13_4717.2]

/-- Complete interval computation for depth 13, residue 4718. -/
theorem bounds_13_4718 : exactInterval 13 4718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4718 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4718) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4718 : oddCount 4718 13 = 8 ∧ acceleratedOrbit 13 4718 = 3782 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4718 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4718) = 3 ^ 8 * m + 3782 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4718.1, data_13_4718.2]

/-- Complete interval computation for depth 13, residue 4719. -/
theorem bounds_13_4719 : exactInterval 13 4719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4719 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4719) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4719 : oddCount 4719 13 = 9 ∧ acceleratedOrbit 13 4719 = 11342 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4719 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4719) = 3 ^ 9 * m + 11342 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4719.1, data_13_4719.2]

end Collatz.Research.StoppingAtlas.Batch0774
