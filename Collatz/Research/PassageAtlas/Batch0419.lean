import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0419

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 13697. -/
theorem bounds_15_13697 : exactInterval 15 13697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13697 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13697) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13697 : oddCount 13697 15 = 8 ∧ acceleratedOrbit 15 13697 = 2744 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13697 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13697) = 3 ^ 8 * m + 2744 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13697.1, data_15_13697.2]

/-- Complete interval computation for depth 15, residue 13698. -/
theorem bounds_15_13698 : exactInterval 15 13698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13698 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13698) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13698 : oddCount 13698 15 = 7 ∧ acceleratedOrbit 15 13698 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13698 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13698) = 3 ^ 7 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13698.1, data_15_13698.2]

/-- Complete interval computation for depth 15, residue 13699. -/
theorem bounds_15_13699 : exactInterval 15 13699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13699 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13699) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13699 : oddCount 13699 15 = 7 ∧ acceleratedOrbit 15 13699 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13699 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13699) = 3 ^ 7 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13699.1, data_15_13699.2]

/-- Complete interval computation for depth 15, residue 13700. -/
theorem bounds_15_13700 : exactInterval 15 13700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13700 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13700) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13700 : oddCount 13700 15 = 6 ∧ acceleratedOrbit 15 13700 = 305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13700 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13700) = 3 ^ 6 * m + 305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13700.1, data_15_13700.2]

/-- Complete interval computation for depth 15, residue 13701. -/
theorem bounds_15_13701 : exactInterval 15 13701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13701 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13701) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13701 : oddCount 13701 15 = 6 ∧ acceleratedOrbit 15 13701 = 305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13701 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13701) = 3 ^ 6 * m + 305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13701.1, data_15_13701.2]

/-- Complete interval computation for depth 15, residue 13702. -/
theorem bounds_15_13702 : exactInterval 15 13702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13702 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13702) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13702 : oddCount 13702 15 = 6 ∧ acceleratedOrbit 15 13702 = 305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13702 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13702) = 3 ^ 6 * m + 305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13702.1, data_15_13702.2]

/-- Complete interval computation for depth 15, residue 13703. -/
theorem bounds_15_13703 : exactInterval 15 13703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13703 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13703) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13703 : oddCount 13703 15 = 7 ∧ acceleratedOrbit 15 13703 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13703 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13703) = 3 ^ 7 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13703.1, data_15_13703.2]

/-- Complete interval computation for depth 15, residue 13704. -/
theorem bounds_15_13704 : exactInterval 15 13704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13704 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13704) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13704 : oddCount 13704 15 = 4 ∧ acceleratedOrbit 15 13704 = 34 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13704 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13704) = 3 ^ 4 * m + 34 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13704.1, data_15_13704.2]

/-- Complete interval computation for depth 15, residue 13705. -/
theorem bounds_15_13705 : exactInterval 15 13705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13705 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13705) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13705 : oddCount 13705 15 = 10 ∧ acceleratedOrbit 15 13705 = 24704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13705 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13705) = 3 ^ 10 * m + 24704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13705.1, data_15_13705.2]

/-- Complete interval computation for depth 15, residue 13706. -/
theorem bounds_15_13706 : exactInterval 15 13706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13706 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13706) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13706 : oddCount 13706 15 = 4 ∧ acceleratedOrbit 15 13706 = 34 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13706 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13706) = 3 ^ 4 * m + 34 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13706.1, data_15_13706.2]

/-- Complete interval computation for depth 15, residue 13707. -/
theorem bounds_15_13707 : exactInterval 15 13707 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13707 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13707) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13707 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13707 : oddCount 13707 15 = 6 ∧ acceleratedOrbit 15 13707 = 305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13707 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13707) = 3 ^ 6 * m + 305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13707.1, data_15_13707.2]

/-- Complete interval computation for depth 15, residue 13708. -/
theorem bounds_15_13708 : exactInterval 15 13708 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13708 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13708) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13708 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13708 : oddCount 13708 15 = 4 ∧ acceleratedOrbit 15 13708 = 34 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13708 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13708) = 3 ^ 4 * m + 34 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13708.1, data_15_13708.2]

/-- Complete interval computation for depth 15, residue 13709. -/
theorem bounds_15_13709 : exactInterval 15 13709 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13709 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13709) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13709 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13709 : oddCount 13709 15 = 4 ∧ acceleratedOrbit 15 13709 = 34 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13709 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13709) = 3 ^ 4 * m + 34 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13709.1, data_15_13709.2]

/-- Complete interval computation for depth 15, residue 13710. -/
theorem bounds_15_13710 : exactInterval 15 13710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13710 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13710) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13710 : oddCount 13710 15 = 8 ∧ acceleratedOrbit 15 13710 = 2747 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13710 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13710) = 3 ^ 8 * m + 2747 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13710.1, data_15_13710.2]

/-- Complete interval computation for depth 15, residue 13711. -/
theorem bounds_15_13711 : exactInterval 15 13711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13711 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13711) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13711 : oddCount 13711 15 = 8 ∧ acceleratedOrbit 15 13711 = 2747 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13711 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13711) = 3 ^ 8 * m + 2747 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13711.1, data_15_13711.2]

/-- Complete interval computation for depth 15, residue 13712. -/
theorem bounds_15_13712 : exactInterval 15 13712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13712 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13712) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13712 : oddCount 13712 15 = 4 ∧ acceleratedOrbit 15 13712 = 34 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13712 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13712) = 3 ^ 4 * m + 34 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13712.1, data_15_13712.2]

/-- Complete interval computation for depth 15, residue 13713. -/
theorem bounds_15_13713 : exactInterval 15 13713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13713 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13713) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13713 : oddCount 13713 15 = 7 ∧ acceleratedOrbit 15 13713 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13713 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13713) = 3 ^ 7 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13713.1, data_15_13713.2]

/-- Complete interval computation for depth 15, residue 13714. -/
theorem bounds_15_13714 : exactInterval 15 13714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13714 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13714) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13714 : oddCount 13714 15 = 7 ∧ acceleratedOrbit 15 13714 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13714 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13714) = 3 ^ 7 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13714.1, data_15_13714.2]

/-- Complete interval computation for depth 15, residue 13715. -/
theorem bounds_15_13715 : exactInterval 15 13715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13715 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13715) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13715 : oddCount 13715 15 = 7 ∧ acceleratedOrbit 15 13715 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13715 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13715) = 3 ^ 7 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13715.1, data_15_13715.2]

/-- Complete interval computation for depth 15, residue 13716. -/
theorem bounds_15_13716 : exactInterval 15 13716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13716 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13716) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13716 : oddCount 13716 15 = 4 ∧ acceleratedOrbit 15 13716 = 34 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13716 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13716) = 3 ^ 4 * m + 34 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13716.1, data_15_13716.2]

/-- Complete interval computation for depth 15, residue 13717. -/
theorem bounds_15_13717 : exactInterval 15 13717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13717 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13717) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13717 : oddCount 13717 15 = 4 ∧ acceleratedOrbit 15 13717 = 34 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13717 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13717) = 3 ^ 4 * m + 34 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13717.1, data_15_13717.2]

/-- Complete interval computation for depth 15, residue 13718. -/
theorem bounds_15_13718 : exactInterval 15 13718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13718 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13718) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13718 : oddCount 13718 15 = 8 ∧ acceleratedOrbit 15 13718 = 2749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13718 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13718) = 3 ^ 8 * m + 2749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13718.1, data_15_13718.2]

/-- Complete interval computation for depth 15, residue 13719. -/
theorem bounds_15_13719 : exactInterval 15 13719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13719 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13719) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13719 : oddCount 13719 15 = 8 ∧ acceleratedOrbit 15 13719 = 2749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13719 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13719) = 3 ^ 8 * m + 2749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13719.1, data_15_13719.2]

/-- Complete interval computation for depth 15, residue 13720. -/
theorem bounds_15_13720 : exactInterval 15 13720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13720 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13720) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13720 : oddCount 13720 15 = 4 ∧ acceleratedOrbit 15 13720 = 34 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13720 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13720) = 3 ^ 4 * m + 34 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13720.1, data_15_13720.2]

/-- Complete interval computation for depth 15, residue 13721. -/
theorem bounds_15_13721 : exactInterval 15 13721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13721 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13721) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13721 : oddCount 13721 15 = 8 ∧ acceleratedOrbit 15 13721 = 2749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13721 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13721) = 3 ^ 8 * m + 2749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13721.1, data_15_13721.2]

/-- Complete interval computation for depth 15, residue 13722. -/
theorem bounds_15_13722 : exactInterval 15 13722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13722 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13722) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13722 : oddCount 13722 15 = 4 ∧ acceleratedOrbit 15 13722 = 34 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13722 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13722) = 3 ^ 4 * m + 34 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13722.1, data_15_13722.2]

/-- Complete interval computation for depth 15, residue 13723. -/
theorem bounds_15_13723 : exactInterval 15 13723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13723 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13723) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13723 : oddCount 13723 15 = 7 ∧ acceleratedOrbit 15 13723 = 916 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13723 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13723) = 3 ^ 7 * m + 916 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13723.1, data_15_13723.2]

/-- Complete interval computation for depth 15, residue 13724. -/
theorem bounds_15_13724 : exactInterval 15 13724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13724 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13724) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13724 : oddCount 13724 15 = 11 ∧ acceleratedOrbit 15 13724 = 74222 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13724 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13724) = 3 ^ 11 * m + 74222 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13724.1, data_15_13724.2]

/-- Complete interval computation for depth 15, residue 13725. -/
theorem bounds_15_13725 : exactInterval 15 13725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13725 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13725) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13725 : oddCount 13725 15 = 11 ∧ acceleratedOrbit 15 13725 = 74222 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13725 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13725) = 3 ^ 11 * m + 74222 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13725.1, data_15_13725.2]

/-- Complete interval computation for depth 15, residue 13726. -/
theorem bounds_15_13726 : exactInterval 15 13726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13726 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13726) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13726 : oddCount 13726 15 = 11 ∧ acceleratedOrbit 15 13726 = 74222 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13726 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13726) = 3 ^ 11 * m + 74222 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13726.1, data_15_13726.2]

/-- Complete interval computation for depth 15, residue 13727. -/
theorem bounds_15_13727 : exactInterval 15 13727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13727 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13727) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13727 : oddCount 13727 15 = 11 ∧ acceleratedOrbit 15 13727 = 74216 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13727 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13727) = 3 ^ 11 * m + 74216 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13727.1, data_15_13727.2]

/-- Complete interval computation for depth 15, residue 13728. -/
theorem bounds_15_13728 : exactInterval 15 13728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13728 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13728) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13728 : oddCount 13728 15 = 5 ∧ acceleratedOrbit 15 13728 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13728 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13728) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13728.1, data_15_13728.2]

end Collatz.Research.PassageAtlas.Batch0419
