import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0904

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6702. -/
theorem bounds_13_6702 : exactInterval 13 6702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6702 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6702) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6702 : oddCount 6702 13 = 5 ∧ acceleratedOrbit 13 6702 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6702 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6702) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6702.1, data_13_6702.2]

/-- Complete interval computation for depth 13, residue 6703. -/
theorem bounds_13_6703 : exactInterval 13 6703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6703 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6703) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6703 : oddCount 6703 13 = 9 ∧ acceleratedOrbit 13 6703 = 16109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6703 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6703) = 3 ^ 9 * m + 16109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6703.1, data_13_6703.2]

/-- Complete interval computation for depth 13, residue 6704. -/
theorem bounds_13_6704 : exactInterval 13 6704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6704 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6704) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6704 : oddCount 6704 13 = 4 ∧ acceleratedOrbit 13 6704 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6704 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6704) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6704.1, data_13_6704.2]

/-- Complete interval computation for depth 13, residue 6705. -/
theorem bounds_13_6705 : exactInterval 13 6705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6705 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6705) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6705 : oddCount 6705 13 = 7 ∧ acceleratedOrbit 13 6705 = 1792 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6705 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6705) = 3 ^ 7 * m + 1792 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6705.1, data_13_6705.2]

/-- Complete interval computation for depth 13, residue 6706. -/
theorem bounds_13_6706 : exactInterval 13 6706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6706 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6706) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6706 : oddCount 6706 13 = 7 ∧ acceleratedOrbit 13 6706 = 1792 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6706 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6706) = 3 ^ 7 * m + 1792 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6706.1, data_13_6706.2]

/-- Complete interval computation for depth 13, residue 6707. -/
theorem bounds_13_6707 : exactInterval 13 6707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6707 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6707) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6707 : oddCount 6707 13 = 7 ∧ acceleratedOrbit 13 6707 = 1792 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6707 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6707) = 3 ^ 7 * m + 1792 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6707.1, data_13_6707.2]

/-- Complete interval computation for depth 13, residue 6708. -/
theorem bounds_13_6708 : exactInterval 13 6708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6708 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6708) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6708 : oddCount 6708 13 = 4 ∧ acceleratedOrbit 13 6708 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6708 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6708) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6708.1, data_13_6708.2]

/-- Complete interval computation for depth 13, residue 6709. -/
theorem bounds_13_6709 : exactInterval 13 6709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6709 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6709) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6709 : oddCount 6709 13 = 4 ∧ acceleratedOrbit 13 6709 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6709 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6709) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6709.1, data_13_6709.2]

/-- Complete interval computation for depth 13, residue 6710. -/
theorem bounds_13_6710 : exactInterval 13 6710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6710 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6710) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6710 : oddCount 6710 13 = 9 ∧ acceleratedOrbit 13 6710 = 16129 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6710 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6710) = 3 ^ 9 * m + 16129 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6710.1, data_13_6710.2]

/-- Complete interval computation for depth 13, residue 6711. -/
theorem bounds_13_6711 : exactInterval 13 6711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6711 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6711) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6711 : oddCount 6711 13 = 9 ∧ acceleratedOrbit 13 6711 = 16129 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6711 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6711) = 3 ^ 9 * m + 16129 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6711.1, data_13_6711.2]

/-- Complete interval computation for depth 13, residue 6712. -/
theorem bounds_13_6712 : exactInterval 13 6712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6712 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6712) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6712 : oddCount 6712 13 = 7 ∧ acceleratedOrbit 13 6712 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6712 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6712) = 3 ^ 7 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6712.1, data_13_6712.2]

/-- Complete interval computation for depth 13, residue 6713. -/
theorem bounds_13_6713 : exactInterval 13 6713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6713 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6713) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6713 : oddCount 6713 13 = 7 ∧ acceleratedOrbit 13 6713 = 1793 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6713 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6713) = 3 ^ 7 * m + 1793 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6713.1, data_13_6713.2]

/-- Complete interval computation for depth 13, residue 6714. -/
theorem bounds_13_6714 : exactInterval 13 6714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6714 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6714) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6714 : oddCount 6714 13 = 7 ∧ acceleratedOrbit 13 6714 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6714 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6714) = 3 ^ 7 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6714.1, data_13_6714.2]

/-- Complete interval computation for depth 13, residue 6715. -/
theorem bounds_13_6715 : exactInterval 13 6715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6715 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6715) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6715 : oddCount 6715 13 = 6 ∧ acceleratedOrbit 13 6715 = 598 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6715 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6715) = 3 ^ 6 * m + 598 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6715.1, data_13_6715.2]

/-- Complete interval computation for depth 13, residue 6716. -/
theorem bounds_13_6716 : exactInterval 13 6716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6716 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6716) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6716 : oddCount 6716 13 = 7 ∧ acceleratedOrbit 13 6716 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6716 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6716) = 3 ^ 7 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6716.1, data_13_6716.2]

end Collatz.Research.StoppingAtlas.Batch0904
