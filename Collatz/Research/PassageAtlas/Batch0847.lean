import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0847

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 27721. -/
theorem bounds_15_27721 : exactInterval 15 27721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27721 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27721) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27721 : oddCount 27721 15 = 8 ∧ acceleratedOrbit 15 27721 = 5551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27721 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27721) = 3 ^ 8 * m + 5551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27721.1, data_15_27721.2]

/-- Complete interval computation for depth 15, residue 27722. -/
theorem bounds_15_27722 : exactInterval 15 27722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27722 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27722) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27722 : oddCount 27722 15 = 6 ∧ acceleratedOrbit 15 27722 = 617 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27722 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27722) = 3 ^ 6 * m + 617 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27722.1, data_15_27722.2]

/-- Complete interval computation for depth 15, residue 27723. -/
theorem bounds_15_27723 : exactInterval 15 27723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27723 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27723) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27723 : oddCount 27723 15 = 7 ∧ acceleratedOrbit 15 27723 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27723 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27723) = 3 ^ 7 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27723.1, data_15_27723.2]

/-- Complete interval computation for depth 15, residue 27724. -/
theorem bounds_15_27724 : exactInterval 15 27724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27724 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27724) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27724 : oddCount 27724 15 = 6 ∧ acceleratedOrbit 15 27724 = 617 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27724 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27724) = 3 ^ 6 * m + 617 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27724.1, data_15_27724.2]

/-- Complete interval computation for depth 15, residue 27725. -/
theorem bounds_15_27725 : exactInterval 15 27725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27725 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27725) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27725 : oddCount 27725 15 = 6 ∧ acceleratedOrbit 15 27725 = 617 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27725 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27725) = 3 ^ 6 * m + 617 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27725.1, data_15_27725.2]

/-- Complete interval computation for depth 15, residue 27726. -/
theorem bounds_15_27726 : exactInterval 15 27726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27726 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27726) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27726 : oddCount 27726 15 = 6 ∧ acceleratedOrbit 15 27726 = 617 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27726 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27726) = 3 ^ 6 * m + 617 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27726.1, data_15_27726.2]

/-- Complete interval computation for depth 15, residue 27727. -/
theorem bounds_15_27727 : exactInterval 15 27727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27727 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27727) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27727 : oddCount 27727 15 = 6 ∧ acceleratedOrbit 15 27727 = 617 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27727 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27727) = 3 ^ 6 * m + 617 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27727.1, data_15_27727.2]

/-- Complete interval computation for depth 15, residue 27728. -/
theorem bounds_15_27728 : exactInterval 15 27728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27728 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27728) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27728 : oddCount 27728 15 = 3 ∧ acceleratedOrbit 15 27728 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27728 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27728) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27728.1, data_15_27728.2]

/-- Complete interval computation for depth 15, residue 27729. -/
theorem bounds_15_27729 : exactInterval 15 27729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27729 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27729) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27729 : oddCount 27729 15 = 6 ∧ acceleratedOrbit 15 27729 = 617 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27729 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27729) = 3 ^ 6 * m + 617 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27729.1, data_15_27729.2]

/-- Complete interval computation for depth 15, residue 27730. -/
theorem bounds_15_27730 : exactInterval 15 27730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27730 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27730) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27730 : oddCount 27730 15 = 12 ∧ acceleratedOrbit 15 27730 = 449792 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27730 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27730) = 3 ^ 12 * m + 449792 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27730.1, data_15_27730.2]

/-- Complete interval computation for depth 15, residue 27731. -/
theorem bounds_15_27731 : exactInterval 15 27731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27731 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27731) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27731 : oddCount 27731 15 = 12 ∧ acceleratedOrbit 15 27731 = 449792 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27731 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27731) = 3 ^ 12 * m + 449792 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27731.1, data_15_27731.2]

/-- Complete interval computation for depth 15, residue 27732. -/
theorem bounds_15_27732 : exactInterval 15 27732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27732 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27732) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27732 : oddCount 27732 15 = 3 ∧ acceleratedOrbit 15 27732 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27732 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27732) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27732.1, data_15_27732.2]

/-- Complete interval computation for depth 15, residue 27733. -/
theorem bounds_15_27733 : exactInterval 15 27733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27733 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27733) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27733 : oddCount 27733 15 = 3 ∧ acceleratedOrbit 15 27733 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27733 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27733) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27733.1, data_15_27733.2]

/-- Complete interval computation for depth 15, residue 27734. -/
theorem bounds_15_27734 : exactInterval 15 27734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27734 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27734) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27734 : oddCount 27734 15 = 7 ∧ acceleratedOrbit 15 27734 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27734 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27734) = 3 ^ 7 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27734.1, data_15_27734.2]

/-- Complete interval computation for depth 15, residue 27735. -/
theorem bounds_15_27735 : exactInterval 15 27735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27735 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27735) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27735 : oddCount 27735 15 = 7 ∧ acceleratedOrbit 15 27735 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27735 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27735) = 3 ^ 7 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27735.1, data_15_27735.2]

/-- Complete interval computation for depth 15, residue 27736. -/
theorem bounds_15_27736 : exactInterval 15 27736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27736 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27736) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27736 : oddCount 27736 15 = 7 ∧ acceleratedOrbit 15 27736 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27736 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27736) = 3 ^ 7 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27736.1, data_15_27736.2]

/-- Complete interval computation for depth 15, residue 27737. -/
theorem bounds_15_27737 : exactInterval 15 27737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27737 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27737) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27737 : oddCount 27737 15 = 8 ∧ acceleratedOrbit 15 27737 = 5555 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27737 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27737) = 3 ^ 8 * m + 5555 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27737.1, data_15_27737.2]

/-- Complete interval computation for depth 15, residue 27738. -/
theorem bounds_15_27738 : exactInterval 15 27738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27738 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27738) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27738 : oddCount 27738 15 = 7 ∧ acceleratedOrbit 15 27738 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27738 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27738) = 3 ^ 7 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27738.1, data_15_27738.2]

/-- Complete interval computation for depth 15, residue 27739. -/
theorem bounds_15_27739 : exactInterval 15 27739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27739 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27739) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27739 : oddCount 27739 15 = 10 ∧ acceleratedOrbit 15 27739 = 49990 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27739 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27739) = 3 ^ 10 * m + 49990 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27739.1, data_15_27739.2]

/-- Complete interval computation for depth 15, residue 27740. -/
theorem bounds_15_27740 : exactInterval 15 27740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27740 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27740) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27740 : oddCount 27740 15 = 7 ∧ acceleratedOrbit 15 27740 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27740 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27740) = 3 ^ 7 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27740.1, data_15_27740.2]

/-- Complete interval computation for depth 15, residue 27741. -/
theorem bounds_15_27741 : exactInterval 15 27741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27741 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27741) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27741 : oddCount 27741 15 = 7 ∧ acceleratedOrbit 15 27741 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27741 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27741) = 3 ^ 7 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27741.1, data_15_27741.2]

/-- Complete interval computation for depth 15, residue 27742. -/
theorem bounds_15_27742 : exactInterval 15 27742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27742 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27742) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27742 : oddCount 27742 15 = 10 ∧ acceleratedOrbit 15 27742 = 49997 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27742 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27742) = 3 ^ 10 * m + 49997 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27742.1, data_15_27742.2]

/-- Complete interval computation for depth 15, residue 27743. -/
theorem bounds_15_27743 : exactInterval 15 27743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27743 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27743) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27743 : oddCount 27743 15 = 10 ∧ acceleratedOrbit 15 27743 = 49997 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27743 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27743) = 3 ^ 10 * m + 49997 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27743.1, data_15_27743.2]

/-- Complete interval computation for depth 15, residue 27744. -/
theorem bounds_15_27744 : exactInterval 15 27744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27744 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27744) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27744 : oddCount 27744 15 = 3 ∧ acceleratedOrbit 15 27744 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27744 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27744) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27744.1, data_15_27744.2]

/-- Complete interval computation for depth 15, residue 27745. -/
theorem bounds_15_27745 : exactInterval 15 27745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27745 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27745) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27745 : oddCount 27745 15 = 7 ∧ acceleratedOrbit 15 27745 = 1852 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27745 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27745) = 3 ^ 7 * m + 1852 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27745.1, data_15_27745.2]

/-- Complete interval computation for depth 15, residue 27746. -/
theorem bounds_15_27746 : exactInterval 15 27746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27746 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27746) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27746 : oddCount 27746 15 = 9 ∧ acceleratedOrbit 15 27746 = 16676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27746 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27746) = 3 ^ 9 * m + 16676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27746.1, data_15_27746.2]

/-- Complete interval computation for depth 15, residue 27747. -/
theorem bounds_15_27747 : exactInterval 15 27747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27747 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27747) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27747 : oddCount 27747 15 = 9 ∧ acceleratedOrbit 15 27747 = 16676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27747 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27747) = 3 ^ 9 * m + 16676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27747.1, data_15_27747.2]

/-- Complete interval computation for depth 15, residue 27748. -/
theorem bounds_15_27748 : exactInterval 15 27748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27748 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27748) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27748 : oddCount 27748 15 = 9 ∧ acceleratedOrbit 15 27748 = 16676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27748 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27748) = 3 ^ 9 * m + 16676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27748.1, data_15_27748.2]

/-- Complete interval computation for depth 15, residue 27749. -/
theorem bounds_15_27749 : exactInterval 15 27749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27749 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27749) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27749 : oddCount 27749 15 = 9 ∧ acceleratedOrbit 15 27749 = 16676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27749 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27749) = 3 ^ 9 * m + 16676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27749.1, data_15_27749.2]

/-- Complete interval computation for depth 15, residue 27750. -/
theorem bounds_15_27750 : exactInterval 15 27750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27750 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27750) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27750 : oddCount 27750 15 = 9 ∧ acceleratedOrbit 15 27750 = 16676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27750 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27750) = 3 ^ 9 * m + 16676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27750.1, data_15_27750.2]

/-- Complete interval computation for depth 15, residue 27751. -/
theorem bounds_15_27751 : exactInterval 15 27751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27751 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27751) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27751 : oddCount 27751 15 = 11 ∧ acceleratedOrbit 15 27751 = 150032 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27751 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27751) = 3 ^ 11 * m + 150032 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27751.1, data_15_27751.2]

/-- Complete interval computation for depth 15, residue 27752. -/
theorem bounds_15_27752 : exactInterval 15 27752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27752 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27752) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27752 : oddCount 27752 15 = 3 ∧ acceleratedOrbit 15 27752 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27752 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27752) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27752.1, data_15_27752.2]

/-- Complete interval computation for depth 15, residue 27753. -/
theorem bounds_15_27753 : exactInterval 15 27753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27753 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27753) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27753 : oddCount 27753 15 = 10 ∧ acceleratedOrbit 15 27753 = 50017 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27753 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27753) = 3 ^ 10 * m + 50017 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27753.1, data_15_27753.2]

end Collatz.Research.PassageAtlas.Batch0847
