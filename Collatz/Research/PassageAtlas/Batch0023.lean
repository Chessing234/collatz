import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0023

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 720. -/
theorem bounds_15_720 : exactInterval 15 720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_720 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 720) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_720 : oddCount 720 15 = 4 ∧ acceleratedOrbit 15 720 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_720 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 720) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_720.1, data_15_720.2]

/-- Complete interval computation for depth 15, residue 721. -/
theorem bounds_15_721 : exactInterval 15 721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_721 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 721) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_721 : oddCount 721 15 = 7 ∧ acceleratedOrbit 15 721 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_721 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 721) = 3 ^ 7 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_721.1, data_15_721.2]

/-- Complete interval computation for depth 15, residue 722. -/
theorem bounds_15_722 : exactInterval 15 722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_722 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 722) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_722 : oddCount 722 15 = 7 ∧ acceleratedOrbit 15 722 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_722 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 722) = 3 ^ 7 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_722.1, data_15_722.2]

/-- Complete interval computation for depth 15, residue 723. -/
theorem bounds_15_723 : exactInterval 15 723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_723 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 723) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_723 : oddCount 723 15 = 7 ∧ acceleratedOrbit 15 723 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_723 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 723) = 3 ^ 7 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_723.1, data_15_723.2]

/-- Complete interval computation for depth 15, residue 724. -/
theorem bounds_15_724 : exactInterval 15 724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_724 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 724) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_724 : oddCount 724 15 = 4 ∧ acceleratedOrbit 15 724 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_724 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 724) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_724.1, data_15_724.2]

/-- Complete interval computation for depth 15, residue 725. -/
theorem bounds_15_725 : exactInterval 15 725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_725 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 725) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_725 : oddCount 725 15 = 4 ∧ acceleratedOrbit 15 725 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_725 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 725) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_725.1, data_15_725.2]

/-- Complete interval computation for depth 15, residue 726. -/
theorem bounds_15_726 : exactInterval 15 726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_726 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 726) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_726 : oddCount 726 15 = 7 ∧ acceleratedOrbit 15 726 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_726 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 726) = 3 ^ 7 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_726.1, data_15_726.2]

/-- Complete interval computation for depth 15, residue 727. -/
theorem bounds_15_727 : exactInterval 15 727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_727 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 727) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_727 : oddCount 727 15 = 7 ∧ acceleratedOrbit 15 727 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_727 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 727) = 3 ^ 7 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_727.1, data_15_727.2]

/-- Complete interval computation for depth 15, residue 728. -/
theorem bounds_15_728 : exactInterval 15 728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_728 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 728) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_728 : oddCount 728 15 = 9 ∧ acceleratedOrbit 15 728 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_728 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 728) = 3 ^ 9 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_728.1, data_15_728.2]

/-- Complete interval computation for depth 15, residue 729. -/
theorem bounds_15_729 : exactInterval 15 729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_729 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 729) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_729 : oddCount 729 15 = 6 ∧ acceleratedOrbit 15 729 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_729 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 729) = 3 ^ 6 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_729.1, data_15_729.2]

/-- Complete interval computation for depth 15, residue 730. -/
theorem bounds_15_730 : exactInterval 15 730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_730 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 730) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_730 : oddCount 730 15 = 9 ∧ acceleratedOrbit 15 730 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_730 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 730) = 3 ^ 9 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_730.1, data_15_730.2]

/-- Complete interval computation for depth 15, residue 731. -/
theorem bounds_15_731 : exactInterval 15 731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_731 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 731) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_731 : oddCount 731 15 = 10 ∧ acceleratedOrbit 15 731 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_731 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 731) = 3 ^ 10 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_731.1, data_15_731.2]

/-- Complete interval computation for depth 15, residue 732. -/
theorem bounds_15_732 : exactInterval 15 732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_732 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 732) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_732 : oddCount 732 15 = 9 ∧ acceleratedOrbit 15 732 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_732 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 732) = 3 ^ 9 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_732.1, data_15_732.2]

/-- Complete interval computation for depth 15, residue 733. -/
theorem bounds_15_733 : exactInterval 15 733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_733 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 733) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_733 : oddCount 733 15 = 9 ∧ acceleratedOrbit 15 733 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_733 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 733) = 3 ^ 9 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_733.1, data_15_733.2]

/-- Complete interval computation for depth 15, residue 734. -/
theorem bounds_15_734 : exactInterval 15 734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_734 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 734) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_734 : oddCount 734 15 = 8 ∧ acceleratedOrbit 15 734 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_734 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 734) = 3 ^ 8 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_734.1, data_15_734.2]

/-- Complete interval computation for depth 15, residue 735. -/
theorem bounds_15_735 : exactInterval 15 735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_735 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 735) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_735 : oddCount 735 15 = 8 ∧ acceleratedOrbit 15 735 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_735 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 735) = 3 ^ 8 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_735.1, data_15_735.2]

/-- Complete interval computation for depth 15, residue 736. -/
theorem bounds_15_736 : exactInterval 15 736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_736 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 736) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_736 : oddCount 736 15 = 4 ∧ acceleratedOrbit 15 736 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_736 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 736) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_736.1, data_15_736.2]

/-- Complete interval computation for depth 15, residue 737. -/
theorem bounds_15_737 : exactInterval 15 737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_737 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 737) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_737 : oddCount 737 15 = 10 ∧ acceleratedOrbit 15 737 = 1333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_737 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 737) = 3 ^ 10 * m + 1333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_737.1, data_15_737.2]

/-- Complete interval computation for depth 15, residue 738. -/
theorem bounds_15_738 : exactInterval 15 738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_738 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 738) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_738 : oddCount 738 15 = 4 ∧ acceleratedOrbit 15 738 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_738 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 738) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_738.1, data_15_738.2]

/-- Complete interval computation for depth 15, residue 739. -/
theorem bounds_15_739 : exactInterval 15 739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_739 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 739) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_739 : oddCount 739 15 = 4 ∧ acceleratedOrbit 15 739 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_739 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 739) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_739.1, data_15_739.2]

/-- Complete interval computation for depth 15, residue 740. -/
theorem bounds_15_740 : exactInterval 15 740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_740 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 740) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_740 : oddCount 740 15 = 8 ∧ acceleratedOrbit 15 740 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_740 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 740) = 3 ^ 8 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_740.1, data_15_740.2]

/-- Complete interval computation for depth 15, residue 741. -/
theorem bounds_15_741 : exactInterval 15 741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_741 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 741) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_741 : oddCount 741 15 = 8 ∧ acceleratedOrbit 15 741 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_741 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 741) = 3 ^ 8 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_741.1, data_15_741.2]

/-- Complete interval computation for depth 15, residue 742. -/
theorem bounds_15_742 : exactInterval 15 742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_742 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 742) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_742 : oddCount 742 15 = 8 ∧ acceleratedOrbit 15 742 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_742 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 742) = 3 ^ 8 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_742.1, data_15_742.2]

/-- Complete interval computation for depth 15, residue 743. -/
theorem bounds_15_743 : exactInterval 15 743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_743 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 743) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_743 : oddCount 743 15 = 11 ∧ acceleratedOrbit 15 743 = 4025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_743 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 743) = 3 ^ 11 * m + 4025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_743.1, data_15_743.2]

/-- Complete interval computation for depth 15, residue 744. -/
theorem bounds_15_744 : exactInterval 15 744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_744 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 744) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_744 : oddCount 744 15 = 4 ∧ acceleratedOrbit 15 744 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_744 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 744) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_744.1, data_15_744.2]

/-- Complete interval computation for depth 15, residue 745. -/
theorem bounds_15_745 : exactInterval 15 745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_745 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 745) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_745 : oddCount 745 15 = 11 ∧ acceleratedOrbit 15 745 = 4040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_745 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 745) = 3 ^ 11 * m + 4040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_745.1, data_15_745.2]

/-- Complete interval computation for depth 15, residue 746. -/
theorem bounds_15_746 : exactInterval 15 746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_746 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 746) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_746 : oddCount 746 15 = 4 ∧ acceleratedOrbit 15 746 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_746 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 746) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_746.1, data_15_746.2]

/-- Complete interval computation for depth 15, residue 747. -/
theorem bounds_15_747 : exactInterval 15 747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_747 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 747) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_747 : oddCount 747 15 = 7 ∧ acceleratedOrbit 15 747 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_747 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 747) = 3 ^ 7 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_747.1, data_15_747.2]

/-- Complete interval computation for depth 15, residue 748. -/
theorem bounds_15_748 : exactInterval 15 748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_748 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 748) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_748 : oddCount 748 15 = 8 ∧ acceleratedOrbit 15 748 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_748 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 748) = 3 ^ 8 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_748.1, data_15_748.2]

/-- Complete interval computation for depth 15, residue 749. -/
theorem bounds_15_749 : exactInterval 15 749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_749 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 749) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_749 : oddCount 749 15 = 8 ∧ acceleratedOrbit 15 749 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_749 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 749) = 3 ^ 8 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_749.1, data_15_749.2]

/-- Complete interval computation for depth 15, residue 750. -/
theorem bounds_15_750 : exactInterval 15 750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_750 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 750) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_750 : oddCount 750 15 = 8 ∧ acceleratedOrbit 15 750 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_750 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 750) = 3 ^ 8 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_750.1, data_15_750.2]

/-- Complete interval computation for depth 15, residue 751. -/
theorem bounds_15_751 : exactInterval 15 751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_751 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 751) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_751 : oddCount 751 15 = 11 ∧ acceleratedOrbit 15 751 = 4067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_751 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 751) = 3 ^ 11 * m + 4067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_751.1, data_15_751.2]

/-- Complete interval computation for depth 15, residue 752. -/
theorem bounds_15_752 : exactInterval 15 752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_752 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 752) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_752 : oddCount 752 15 = 8 ∧ acceleratedOrbit 15 752 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_752 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 752) = 3 ^ 8 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_752.1, data_15_752.2]

end Collatz.Research.PassageAtlas.Batch0023
