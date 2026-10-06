import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0114

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 3702. -/
theorem bounds_15_3702 : exactInterval 15 3702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3702 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3702) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3702 : oddCount 3702 15 = 6 ∧ acceleratedOrbit 15 3702 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3702 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3702) = 3 ^ 6 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3702.1, data_15_3702.2]

/-- Complete interval computation for depth 15, residue 3703. -/
theorem bounds_15_3703 : exactInterval 15 3703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3703 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3703) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3703 : oddCount 3703 15 = 6 ∧ acceleratedOrbit 15 3703 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3703 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3703) = 3 ^ 6 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3703.1, data_15_3703.2]

/-- Complete interval computation for depth 15, residue 3704. -/
theorem bounds_15_3704 : exactInterval 15 3704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3704 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3704) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3704 : oddCount 3704 15 = 7 ∧ acceleratedOrbit 15 3704 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3704 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3704) = 3 ^ 7 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3704.1, data_15_3704.2]

/-- Complete interval computation for depth 15, residue 3705. -/
theorem bounds_15_3705 : exactInterval 15 3705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3705 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3705) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3705 : oddCount 3705 15 = 10 ∧ acceleratedOrbit 15 3705 = 6682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3705 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3705) = 3 ^ 10 * m + 6682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3705.1, data_15_3705.2]

/-- Complete interval computation for depth 15, residue 3706. -/
theorem bounds_15_3706 : exactInterval 15 3706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3706 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3706) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3706 : oddCount 3706 15 = 7 ∧ acceleratedOrbit 15 3706 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3706 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3706) = 3 ^ 7 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3706.1, data_15_3706.2]

/-- Complete interval computation for depth 15, residue 3707. -/
theorem bounds_15_3707 : exactInterval 15 3707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3707 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3707) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3707 : oddCount 3707 15 = 6 ∧ acceleratedOrbit 15 3707 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3707 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3707) = 3 ^ 6 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3707.1, data_15_3707.2]

/-- Complete interval computation for depth 15, residue 3708. -/
theorem bounds_15_3708 : exactInterval 15 3708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3708 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3708) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3708 : oddCount 3708 15 = 9 ∧ acceleratedOrbit 15 3708 = 2231 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3708 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3708) = 3 ^ 9 * m + 2231 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3708.1, data_15_3708.2]

/-- Complete interval computation for depth 15, residue 3709. -/
theorem bounds_15_3709 : exactInterval 15 3709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3709 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3709) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3709 : oddCount 3709 15 = 9 ∧ acceleratedOrbit 15 3709 = 2231 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3709 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3709) = 3 ^ 9 * m + 2231 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3709.1, data_15_3709.2]

/-- Complete interval computation for depth 15, residue 3710. -/
theorem bounds_15_3710 : exactInterval 15 3710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3710 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3710) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3710 : oddCount 3710 15 = 9 ∧ acceleratedOrbit 15 3710 = 2231 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3710 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3710) = 3 ^ 9 * m + 2231 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3710.1, data_15_3710.2]

/-- Complete interval computation for depth 15, residue 3711. -/
theorem bounds_15_3711 : exactInterval 15 3711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3711 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3711) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3711 : oddCount 3711 15 = 12 ∧ acceleratedOrbit 15 3711 = 60203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3711 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3711) = 3 ^ 12 * m + 60203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3711.1, data_15_3711.2]

/-- Complete interval computation for depth 15, residue 3712. -/
theorem bounds_15_3712 : exactInterval 15 3712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3712 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3712) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3712 : oddCount 3712 15 = 4 ∧ acceleratedOrbit 15 3712 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3712 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3712) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3712.1, data_15_3712.2]

/-- Complete interval computation for depth 15, residue 3713. -/
theorem bounds_15_3713 : exactInterval 15 3713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3713 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3713) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3713 : oddCount 3713 15 = 10 ∧ acceleratedOrbit 15 3713 = 6698 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3713 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3713) = 3 ^ 10 * m + 6698 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3713.1, data_15_3713.2]

/-- Complete interval computation for depth 15, residue 3714. -/
theorem bounds_15_3714 : exactInterval 15 3714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3714 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3714) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3714 : oddCount 3714 15 = 5 ∧ acceleratedOrbit 15 3714 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3714 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3714) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3714.1, data_15_3714.2]

/-- Complete interval computation for depth 15, residue 3715. -/
theorem bounds_15_3715 : exactInterval 15 3715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3715 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3715) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3715 : oddCount 3715 15 = 5 ∧ acceleratedOrbit 15 3715 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3715 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3715) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3715.1, data_15_3715.2]

/-- Complete interval computation for depth 15, residue 3716. -/
theorem bounds_15_3716 : exactInterval 15 3716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3716 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3716) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3716 : oddCount 3716 15 = 6 ∧ acceleratedOrbit 15 3716 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3716 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3716) = 3 ^ 6 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3716.1, data_15_3716.2]

/-- Complete interval computation for depth 15, residue 3717. -/
theorem bounds_15_3717 : exactInterval 15 3717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3717 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3717) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3717 : oddCount 3717 15 = 6 ∧ acceleratedOrbit 15 3717 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3717 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3717) = 3 ^ 6 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3717.1, data_15_3717.2]

/-- Complete interval computation for depth 15, residue 3718. -/
theorem bounds_15_3718 : exactInterval 15 3718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3718 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3718) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3718 : oddCount 3718 15 = 6 ∧ acceleratedOrbit 15 3718 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3718 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3718) = 3 ^ 6 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3718.1, data_15_3718.2]

/-- Complete interval computation for depth 15, residue 3719. -/
theorem bounds_15_3719 : exactInterval 15 3719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3719 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3719) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3719 : oddCount 3719 15 = 8 ∧ acceleratedOrbit 15 3719 = 746 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3719 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3719) = 3 ^ 8 * m + 746 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3719.1, data_15_3719.2]

/-- Complete interval computation for depth 15, residue 3720. -/
theorem bounds_15_3720 : exactInterval 15 3720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3720 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3720) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3720 : oddCount 3720 15 = 5 ∧ acceleratedOrbit 15 3720 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3720 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3720) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3720.1, data_15_3720.2]

/-- Complete interval computation for depth 15, residue 3721. -/
theorem bounds_15_3721 : exactInterval 15 3721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3721 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3721) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3721 : oddCount 3721 15 = 11 ∧ acceleratedOrbit 15 3721 = 20128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3721 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3721) = 3 ^ 11 * m + 20128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3721.1, data_15_3721.2]

/-- Complete interval computation for depth 15, residue 3722. -/
theorem bounds_15_3722 : exactInterval 15 3722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3722 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3722) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3722 : oddCount 3722 15 = 5 ∧ acceleratedOrbit 15 3722 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3722 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3722) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3722.1, data_15_3722.2]

/-- Complete interval computation for depth 15, residue 3723. -/
theorem bounds_15_3723 : exactInterval 15 3723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3723 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3723) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3723 : oddCount 3723 15 = 6 ∧ acceleratedOrbit 15 3723 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3723 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3723) = 3 ^ 6 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3723.1, data_15_3723.2]

/-- Complete interval computation for depth 15, residue 3724. -/
theorem bounds_15_3724 : exactInterval 15 3724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3724 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3724) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3724 : oddCount 3724 15 = 5 ∧ acceleratedOrbit 15 3724 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3724 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3724) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3724.1, data_15_3724.2]

/-- Complete interval computation for depth 15, residue 3725. -/
theorem bounds_15_3725 : exactInterval 15 3725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3725 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3725) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3725 : oddCount 3725 15 = 5 ∧ acceleratedOrbit 15 3725 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3725 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3725) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3725.1, data_15_3725.2]

/-- Complete interval computation for depth 15, residue 3726. -/
theorem bounds_15_3726 : exactInterval 15 3726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3726 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3726) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3726 : oddCount 3726 15 = 10 ∧ acceleratedOrbit 15 3726 = 6722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3726 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3726) = 3 ^ 10 * m + 6722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3726.1, data_15_3726.2]

/-- Complete interval computation for depth 15, residue 3727. -/
theorem bounds_15_3727 : exactInterval 15 3727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3727 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3727) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3727 : oddCount 3727 15 = 10 ∧ acceleratedOrbit 15 3727 = 6722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3727 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3727) = 3 ^ 10 * m + 6722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3727.1, data_15_3727.2]

/-- Complete interval computation for depth 15, residue 3728. -/
theorem bounds_15_3728 : exactInterval 15 3728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3728 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3728) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3728 : oddCount 3728 15 = 7 ∧ acceleratedOrbit 15 3728 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3728 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3728) = 3 ^ 7 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3728.1, data_15_3728.2]

/-- Complete interval computation for depth 15, residue 3729. -/
theorem bounds_15_3729 : exactInterval 15 3729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3729 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3729) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3729 : oddCount 3729 15 = 8 ∧ acceleratedOrbit 15 3729 = 749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3729 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3729) = 3 ^ 8 * m + 749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3729.1, data_15_3729.2]

/-- Complete interval computation for depth 15, residue 3730. -/
theorem bounds_15_3730 : exactInterval 15 3730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3730 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3730) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3730 : oddCount 3730 15 = 8 ∧ acceleratedOrbit 15 3730 = 749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3730 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3730) = 3 ^ 8 * m + 749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3730.1, data_15_3730.2]

/-- Complete interval computation for depth 15, residue 3731. -/
theorem bounds_15_3731 : exactInterval 15 3731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3731 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3731) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3731 : oddCount 3731 15 = 8 ∧ acceleratedOrbit 15 3731 = 749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3731 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3731) = 3 ^ 8 * m + 749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3731.1, data_15_3731.2]

/-- Complete interval computation for depth 15, residue 3732. -/
theorem bounds_15_3732 : exactInterval 15 3732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3732 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3732) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3732 : oddCount 3732 15 = 7 ∧ acceleratedOrbit 15 3732 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3732 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3732) = 3 ^ 7 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3732.1, data_15_3732.2]

/-- Complete interval computation for depth 15, residue 3733. -/
theorem bounds_15_3733 : exactInterval 15 3733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3733 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3733) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3733 : oddCount 3733 15 = 7 ∧ acceleratedOrbit 15 3733 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3733 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3733) = 3 ^ 7 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3733.1, data_15_3733.2]

/-- Complete interval computation for depth 15, residue 3734. -/
theorem bounds_15_3734 : exactInterval 15 3734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3734 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3734) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3734 : oddCount 3734 15 = 5 ∧ acceleratedOrbit 15 3734 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3734 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3734) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3734.1, data_15_3734.2]

end Collatz.Research.PassageAtlas.Batch0114
