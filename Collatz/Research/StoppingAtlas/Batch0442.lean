import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0442

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3701. -/
theorem bounds_12_3701 : exactInterval 12 3701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3701 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3701) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3701 : oddCount 3701 12 = 6 ∧ acceleratedOrbit 12 3701 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3701 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3701) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3701.1, data_12_3701.2]

/-- Complete interval computation for depth 12, residue 3702. -/
theorem bounds_12_3702 : exactInterval 12 3702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3702 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3702) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3702 : oddCount 3702 12 = 5 ∧ acceleratedOrbit 12 3702 = 220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3702 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3702) = 3 ^ 5 * m + 220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3702.1, data_12_3702.2]

/-- Complete interval computation for depth 12, residue 3703. -/
theorem bounds_12_3703 : exactInterval 12 3703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3703 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3703) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3703 : oddCount 3703 12 = 5 ∧ acceleratedOrbit 12 3703 = 220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3703 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3703) = 3 ^ 5 * m + 220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3703.1, data_12_3703.2]

/-- Complete interval computation for depth 12, residue 3704. -/
theorem bounds_12_3704 : exactInterval 12 3704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3704 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3704) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3704 : oddCount 3704 12 = 6 ∧ acceleratedOrbit 12 3704 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3704 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3704) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3704.1, data_12_3704.2]

/-- Complete interval computation for depth 12, residue 3705. -/
theorem bounds_12_3705 : exactInterval 12 3705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3705 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3705) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3705 : oddCount 3705 12 = 8 ∧ acceleratedOrbit 12 3705 = 5939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3705 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3705) = 3 ^ 8 * m + 5939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3705.1, data_12_3705.2]

/-- Complete interval computation for depth 12, residue 3706. -/
theorem bounds_12_3706 : exactInterval 12 3706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3706 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3706) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3706 : oddCount 3706 12 = 6 ∧ acceleratedOrbit 12 3706 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3706 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3706) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3706.1, data_12_3706.2]

/-- Complete interval computation for depth 12, residue 3707. -/
theorem bounds_12_3707 : exactInterval 12 3707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3707 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3707) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3707 : oddCount 3707 12 = 5 ∧ acceleratedOrbit 12 3707 = 220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3707 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3707) = 3 ^ 5 * m + 220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3707.1, data_12_3707.2]

/-- Complete interval computation for depth 12, residue 3708. -/
theorem bounds_12_3708 : exactInterval 12 3708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3708 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3708) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3708 : oddCount 3708 12 = 7 ∧ acceleratedOrbit 12 3708 = 1982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3708 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3708) = 3 ^ 7 * m + 1982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3708.1, data_12_3708.2]

/-- Complete interval computation for depth 12, residue 3709. -/
theorem bounds_12_3709 : exactInterval 12 3709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3709 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3709) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3709 : oddCount 3709 12 = 7 ∧ acceleratedOrbit 12 3709 = 1982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3709 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3709) = 3 ^ 7 * m + 1982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3709.1, data_12_3709.2]

/-- Complete interval computation for depth 12, residue 3710. -/
theorem bounds_12_3710 : exactInterval 12 3710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3710 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3710) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3710 : oddCount 3710 12 = 7 ∧ acceleratedOrbit 12 3710 = 1982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3710 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3710) = 3 ^ 7 * m + 1982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3710.1, data_12_3710.2]

/-- Complete interval computation for depth 12, residue 3711. -/
theorem bounds_12_3711 : exactInterval 12 3711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3711 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3711) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3711 : oddCount 3711 12 = 11 ∧ acceleratedOrbit 12 3711 = 160541 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3711 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3711) = 3 ^ 11 * m + 160541 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3711.1, data_12_3711.2]

/-- Complete interval computation for depth 12, residue 3712. -/
theorem bounds_12_3712 : exactInterval 12 3712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3712 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3712) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3712 : oddCount 3712 12 = 3 ∧ acceleratedOrbit 12 3712 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3712 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3712) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3712.1, data_12_3712.2]

/-- Complete interval computation for depth 12, residue 3713. -/
theorem bounds_12_3713 : exactInterval 12 3713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3713 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3713) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3713 : oddCount 3713 12 = 8 ∧ acceleratedOrbit 12 3713 = 5953 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3713 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3713) = 3 ^ 8 * m + 5953 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3713.1, data_12_3713.2]

/-- Complete interval computation for depth 12, residue 3714. -/
theorem bounds_12_3714 : exactInterval 12 3714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3714 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3714) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3714 : oddCount 3714 12 = 4 ∧ acceleratedOrbit 12 3714 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3714 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3714) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3714.1, data_12_3714.2]

/-- Complete interval computation for depth 12, residue 3715. -/
theorem bounds_12_3715 : exactInterval 12 3715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3715 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3715) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3715 : oddCount 3715 12 = 4 ∧ acceleratedOrbit 12 3715 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3715 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3715) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3715.1, data_12_3715.2]

/-- Complete interval computation for depth 12, residue 3716. -/
theorem bounds_12_3716 : exactInterval 12 3716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3716 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3716) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3716 : oddCount 3716 12 = 5 ∧ acceleratedOrbit 12 3716 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3716 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3716) = 3 ^ 5 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3716.1, data_12_3716.2]

end Collatz.Research.StoppingAtlas.Batch0442
