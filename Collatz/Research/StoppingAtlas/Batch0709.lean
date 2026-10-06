import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0709

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3706. -/
theorem bounds_13_3706 : exactInterval 13 3706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3706 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3706) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3706 : oddCount 3706 13 = 7 ∧ acceleratedOrbit 13 3706 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3706 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3706) = 3 ^ 7 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3706.1, data_13_3706.2]

/-- Complete interval computation for depth 13, residue 3707. -/
theorem bounds_13_3707 : exactInterval 13 3707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3707 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3707) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3707 : oddCount 3707 13 = 5 ∧ acceleratedOrbit 13 3707 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3707 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3707) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3707.1, data_13_3707.2]

/-- Complete interval computation for depth 13, residue 3708. -/
theorem bounds_13_3708 : exactInterval 13 3708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3708 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3708) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3708 : oddCount 3708 13 = 7 ∧ acceleratedOrbit 13 3708 = 991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3708 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3708) = 3 ^ 7 * m + 991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3708.1, data_13_3708.2]

/-- Complete interval computation for depth 13, residue 3709. -/
theorem bounds_13_3709 : exactInterval 13 3709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3709 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3709) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3709 : oddCount 3709 13 = 7 ∧ acceleratedOrbit 13 3709 = 991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3709 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3709) = 3 ^ 7 * m + 991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3709.1, data_13_3709.2]

/-- Complete interval computation for depth 13, residue 3710. -/
theorem bounds_13_3710 : exactInterval 13 3710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3710 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3710) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3710 : oddCount 3710 13 = 7 ∧ acceleratedOrbit 13 3710 = 991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3710 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3710) = 3 ^ 7 * m + 991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3710.1, data_13_3710.2]

/-- Complete interval computation for depth 13, residue 3711. -/
theorem bounds_13_3711 : exactInterval 13 3711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3711 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3711) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3711 : oddCount 3711 13 = 12 ∧ acceleratedOrbit 13 3711 = 240812 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3711 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3711) = 3 ^ 12 * m + 240812 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3711.1, data_13_3711.2]

/-- Complete interval computation for depth 13, residue 3712. -/
theorem bounds_13_3712 : exactInterval 13 3712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3712 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3712) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3712 : oddCount 3712 13 = 3 ∧ acceleratedOrbit 13 3712 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3712 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3712) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3712.1, data_13_3712.2]

/-- Complete interval computation for depth 13, residue 3713. -/
theorem bounds_13_3713 : exactInterval 13 3713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3713 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3713) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3713 : oddCount 3713 13 = 9 ∧ acceleratedOrbit 13 3713 = 8930 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3713 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3713) = 3 ^ 9 * m + 8930 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3713.1, data_13_3713.2]

/-- Complete interval computation for depth 13, residue 3714. -/
theorem bounds_13_3714 : exactInterval 13 3714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3714 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3714) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3714 : oddCount 3714 13 = 4 ∧ acceleratedOrbit 13 3714 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3714 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3714) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3714.1, data_13_3714.2]

/-- Complete interval computation for depth 13, residue 3715. -/
theorem bounds_13_3715 : exactInterval 13 3715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3715 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3715) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3715 : oddCount 3715 13 = 4 ∧ acceleratedOrbit 13 3715 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3715 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3715) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3715.1, data_13_3715.2]

/-- Complete interval computation for depth 13, residue 3716. -/
theorem bounds_13_3716 : exactInterval 13 3716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3716 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3716) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3716 : oddCount 3716 13 = 6 ∧ acceleratedOrbit 13 3716 = 332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3716 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3716) = 3 ^ 6 * m + 332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3716.1, data_13_3716.2]

/-- Complete interval computation for depth 13, residue 3717. -/
theorem bounds_13_3717 : exactInterval 13 3717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3717 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3717) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3717 : oddCount 3717 13 = 6 ∧ acceleratedOrbit 13 3717 = 332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3717 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3717) = 3 ^ 6 * m + 332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3717.1, data_13_3717.2]

/-- Complete interval computation for depth 13, residue 3718. -/
theorem bounds_13_3718 : exactInterval 13 3718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3718 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3718) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3718 : oddCount 3718 13 = 6 ∧ acceleratedOrbit 13 3718 = 332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3718 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3718) = 3 ^ 6 * m + 332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3718.1, data_13_3718.2]

/-- Complete interval computation for depth 13, residue 3719. -/
theorem bounds_13_3719 : exactInterval 13 3719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3719 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3719) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3719 : oddCount 3719 13 = 7 ∧ acceleratedOrbit 13 3719 = 994 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3719 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3719) = 3 ^ 7 * m + 994 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3719.1, data_13_3719.2]

/-- Complete interval computation for depth 13, residue 3720. -/
theorem bounds_13_3720 : exactInterval 13 3720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3720 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3720) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3720 : oddCount 3720 13 = 4 ∧ acceleratedOrbit 13 3720 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3720 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3720) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3720.1, data_13_3720.2]

/-- Complete interval computation for depth 13, residue 3721. -/
theorem bounds_13_3721 : exactInterval 13 3721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3721 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3721) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3721 : oddCount 3721 13 = 10 ∧ acceleratedOrbit 13 3721 = 26837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3721 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3721) = 3 ^ 10 * m + 26837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3721.1, data_13_3721.2]

end Collatz.Research.StoppingAtlas.Batch0709
