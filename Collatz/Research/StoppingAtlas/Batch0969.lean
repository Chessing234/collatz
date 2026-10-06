import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0969

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7700. -/
theorem bounds_13_7700 : exactInterval 13 7700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7700 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7700) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7700 : oddCount 7700 13 = 6 ∧ acceleratedOrbit 13 7700 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7700 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7700) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7700.1, data_13_7700.2]

/-- Complete interval computation for depth 13, residue 7701. -/
theorem bounds_13_7701 : exactInterval 13 7701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7701 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7701) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7701 : oddCount 7701 13 = 6 ∧ acceleratedOrbit 13 7701 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7701 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7701) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7701.1, data_13_7701.2]

/-- Complete interval computation for depth 13, residue 7702. -/
theorem bounds_13_7702 : exactInterval 13 7702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7702 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7702) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7702 : oddCount 7702 13 = 6 ∧ acceleratedOrbit 13 7702 = 686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7702 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7702) = 3 ^ 6 * m + 686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7702.1, data_13_7702.2]

/-- Complete interval computation for depth 13, residue 7703. -/
theorem bounds_13_7703 : exactInterval 13 7703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7703 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7703) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7703 : oddCount 7703 13 = 6 ∧ acceleratedOrbit 13 7703 = 686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7703 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7703) = 3 ^ 6 * m + 686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7703.1, data_13_7703.2]

/-- Complete interval computation for depth 13, residue 7704. -/
theorem bounds_13_7704 : exactInterval 13 7704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7704 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7704) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7704 : oddCount 7704 13 = 6 ∧ acceleratedOrbit 13 7704 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7704 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7704) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7704.1, data_13_7704.2]

/-- Complete interval computation for depth 13, residue 7705. -/
theorem bounds_13_7705 : exactInterval 13 7705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7705 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7705) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7705 : oddCount 7705 13 = 6 ∧ acceleratedOrbit 13 7705 = 686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7705 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7705) = 3 ^ 6 * m + 686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7705.1, data_13_7705.2]

/-- Complete interval computation for depth 13, residue 7706. -/
theorem bounds_13_7706 : exactInterval 13 7706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7706 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7706) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7706 : oddCount 7706 13 = 6 ∧ acceleratedOrbit 13 7706 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7706 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7706) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7706.1, data_13_7706.2]

/-- Complete interval computation for depth 13, residue 7707. -/
theorem bounds_13_7707 : exactInterval 13 7707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7707 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7707) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7707 : oddCount 7707 13 = 10 ∧ acceleratedOrbit 13 7707 = 55565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7707 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7707) = 3 ^ 10 * m + 55565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7707.1, data_13_7707.2]

/-- Complete interval computation for depth 13, residue 7708. -/
theorem bounds_13_7708 : exactInterval 13 7708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7708 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7708) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7708 : oddCount 7708 13 = 5 ∧ acceleratedOrbit 13 7708 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7708 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7708) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7708.1, data_13_7708.2]

/-- Complete interval computation for depth 13, residue 7709. -/
theorem bounds_13_7709 : exactInterval 13 7709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7709 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7709) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7709 : oddCount 7709 13 = 5 ∧ acceleratedOrbit 13 7709 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7709 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7709) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7709.1, data_13_7709.2]

/-- Complete interval computation for depth 13, residue 7710. -/
theorem bounds_13_7710 : exactInterval 13 7710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7710 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7710) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7710 : oddCount 7710 13 = 5 ∧ acceleratedOrbit 13 7710 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7710 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7710) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7710.1, data_13_7710.2]

/-- Complete interval computation for depth 13, residue 7711. -/
theorem bounds_13_7711 : exactInterval 13 7711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7711 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7711) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7711 : oddCount 7711 13 = 10 ∧ acceleratedOrbit 13 7711 = 55592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7711 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7711) = 3 ^ 10 * m + 55592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7711.1, data_13_7711.2]

/-- Complete interval computation for depth 13, residue 7712. -/
theorem bounds_13_7712 : exactInterval 13 7712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7712 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7712) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7712 : oddCount 7712 13 = 3 ∧ acceleratedOrbit 13 7712 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7712 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7712) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7712.1, data_13_7712.2]

/-- Complete interval computation for depth 13, residue 7713. -/
theorem bounds_13_7713 : exactInterval 13 7713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7713 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7713) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7713 : oddCount 7713 13 = 8 ∧ acceleratedOrbit 13 7713 = 6182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7713 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7713) = 3 ^ 8 * m + 6182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7713.1, data_13_7713.2]

/-- Complete interval computation for depth 13, residue 7714. -/
theorem bounds_13_7714 : exactInterval 13 7714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7714 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7714) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7714 : oddCount 7714 13 = 6 ∧ acceleratedOrbit 13 7714 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7714 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7714) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7714.1, data_13_7714.2]

end Collatz.Research.StoppingAtlas.Batch0969
