import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0786

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 25722. -/
theorem bounds_15_25722 : exactInterval 15 25722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25722 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25722) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25722 : oddCount 25722 15 = 7 ∧ acceleratedOrbit 15 25722 = 1718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25722 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25722) = 3 ^ 7 * m + 1718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25722.1, data_15_25722.2]

/-- Complete interval computation for depth 15, residue 25723. -/
theorem bounds_15_25723 : exactInterval 15 25723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25723 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25723) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25723 : oddCount 25723 15 = 7 ∧ acceleratedOrbit 15 25723 = 1717 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25723 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25723) = 3 ^ 7 * m + 1717 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25723.1, data_15_25723.2]

/-- Complete interval computation for depth 15, residue 25724. -/
theorem bounds_15_25724 : exactInterval 15 25724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25724 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25724) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25724 : oddCount 25724 15 = 8 ∧ acceleratedOrbit 15 25724 = 5152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25724 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25724) = 3 ^ 8 * m + 5152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25724.1, data_15_25724.2]

/-- Complete interval computation for depth 15, residue 25725. -/
theorem bounds_15_25725 : exactInterval 15 25725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25725 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25725) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25725 : oddCount 25725 15 = 8 ∧ acceleratedOrbit 15 25725 = 5152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25725 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25725) = 3 ^ 8 * m + 5152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25725.1, data_15_25725.2]

/-- Complete interval computation for depth 15, residue 25726. -/
theorem bounds_15_25726 : exactInterval 15 25726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25726 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25726) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25726 : oddCount 25726 15 = 8 ∧ acceleratedOrbit 15 25726 = 5152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25726 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25726) = 3 ^ 8 * m + 5152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25726.1, data_15_25726.2]

/-- Complete interval computation for depth 15, residue 25727. -/
theorem bounds_15_25727 : exactInterval 15 25727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25727 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25727) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25727 : oddCount 25727 15 = 10 ∧ acceleratedOrbit 15 25727 = 46363 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25727 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25727) = 3 ^ 10 * m + 46363 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25727.1, data_15_25727.2]

/-- Complete interval computation for depth 15, residue 25728. -/
theorem bounds_15_25728 : exactInterval 15 25728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25728 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25728) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25728 : oddCount 25728 15 = 4 ∧ acceleratedOrbit 15 25728 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25728 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25728) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25728.1, data_15_25728.2]

/-- Complete interval computation for depth 15, residue 25729. -/
theorem bounds_15_25729 : exactInterval 15 25729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25729 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25729) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25729 : oddCount 25729 15 = 10 ∧ acceleratedOrbit 15 25729 = 46372 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25729 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25729) = 3 ^ 10 * m + 46372 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25729.1, data_15_25729.2]

/-- Complete interval computation for depth 15, residue 25730. -/
theorem bounds_15_25730 : exactInterval 15 25730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25730 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25730) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25730 : oddCount 25730 15 = 5 ∧ acceleratedOrbit 15 25730 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25730 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25730) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25730.1, data_15_25730.2]

/-- Complete interval computation for depth 15, residue 25731. -/
theorem bounds_15_25731 : exactInterval 15 25731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25731 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25731) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25731 : oddCount 25731 15 = 5 ∧ acceleratedOrbit 15 25731 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25731 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25731) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25731.1, data_15_25731.2]

/-- Complete interval computation for depth 15, residue 25732. -/
theorem bounds_15_25732 : exactInterval 15 25732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25732 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25732) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25732 : oddCount 25732 15 = 5 ∧ acceleratedOrbit 15 25732 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25732 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25732) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25732.1, data_15_25732.2]

/-- Complete interval computation for depth 15, residue 25733. -/
theorem bounds_15_25733 : exactInterval 15 25733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25733 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25733) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25733 : oddCount 25733 15 = 5 ∧ acceleratedOrbit 15 25733 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25733 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25733) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25733.1, data_15_25733.2]

/-- Complete interval computation for depth 15, residue 25734. -/
theorem bounds_15_25734 : exactInterval 15 25734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25734 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25734) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25734 : oddCount 25734 15 = 5 ∧ acceleratedOrbit 15 25734 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25734 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25734) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25734.1, data_15_25734.2]

/-- Complete interval computation for depth 15, residue 25735. -/
theorem bounds_15_25735 : exactInterval 15 25735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25735 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25735) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25735 : oddCount 25735 15 = 9 ∧ acceleratedOrbit 15 25735 = 15461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25735 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25735) = 3 ^ 9 * m + 15461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25735.1, data_15_25735.2]

/-- Complete interval computation for depth 15, residue 25736. -/
theorem bounds_15_25736 : exactInterval 15 25736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25736 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25736) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25736 : oddCount 25736 15 = 7 ∧ acceleratedOrbit 15 25736 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25736 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25736) = 3 ^ 7 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25736.1, data_15_25736.2]

/-- Complete interval computation for depth 15, residue 25737. -/
theorem bounds_15_25737 : exactInterval 15 25737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25737 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25737) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25737 : oddCount 25737 15 = 11 ∧ acceleratedOrbit 15 25737 = 139148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25737 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25737) = 3 ^ 11 * m + 139148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25737.1, data_15_25737.2]

/-- Complete interval computation for depth 15, residue 25738. -/
theorem bounds_15_25738 : exactInterval 15 25738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25738 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25738) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25738 : oddCount 25738 15 = 7 ∧ acceleratedOrbit 15 25738 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25738 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25738) = 3 ^ 7 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25738.1, data_15_25738.2]

/-- Complete interval computation for depth 15, residue 25739. -/
theorem bounds_15_25739 : exactInterval 15 25739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25739 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25739) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25739 : oddCount 25739 15 = 9 ∧ acceleratedOrbit 15 25739 = 15464 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25739 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25739) = 3 ^ 9 * m + 15464 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25739.1, data_15_25739.2]

/-- Complete interval computation for depth 15, residue 25740. -/
theorem bounds_15_25740 : exactInterval 15 25740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25740 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25740) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25740 : oddCount 25740 15 = 7 ∧ acceleratedOrbit 15 25740 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25740 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25740) = 3 ^ 7 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25740.1, data_15_25740.2]

/-- Complete interval computation for depth 15, residue 25741. -/
theorem bounds_15_25741 : exactInterval 15 25741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25741 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25741) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25741 : oddCount 25741 15 = 7 ∧ acceleratedOrbit 15 25741 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25741 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25741) = 3 ^ 7 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25741.1, data_15_25741.2]

/-- Complete interval computation for depth 15, residue 25742. -/
theorem bounds_15_25742 : exactInterval 15 25742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25742 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25742) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25742 : oddCount 25742 15 = 8 ∧ acceleratedOrbit 15 25742 = 5156 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25742 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25742) = 3 ^ 8 * m + 5156 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25742.1, data_15_25742.2]

/-- Complete interval computation for depth 15, residue 25743. -/
theorem bounds_15_25743 : exactInterval 15 25743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25743 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25743) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25743 : oddCount 25743 15 = 8 ∧ acceleratedOrbit 15 25743 = 5156 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25743 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25743) = 3 ^ 8 * m + 5156 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25743.1, data_15_25743.2]

/-- Complete interval computation for depth 15, residue 25744. -/
theorem bounds_15_25744 : exactInterval 15 25744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25744 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25744) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25744 : oddCount 25744 15 = 7 ∧ acceleratedOrbit 15 25744 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25744 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25744) = 3 ^ 7 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25744.1, data_15_25744.2]

/-- Complete interval computation for depth 15, residue 25745. -/
theorem bounds_15_25745 : exactInterval 15 25745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25745 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25745) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25745 : oddCount 25745 15 = 9 ∧ acceleratedOrbit 15 25745 = 15470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25745 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25745) = 3 ^ 9 * m + 15470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25745.1, data_15_25745.2]

/-- Complete interval computation for depth 15, residue 25746. -/
theorem bounds_15_25746 : exactInterval 15 25746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25746 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25746) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25746 : oddCount 25746 15 = 9 ∧ acceleratedOrbit 15 25746 = 15470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25746 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25746) = 3 ^ 9 * m + 15470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25746.1, data_15_25746.2]

/-- Complete interval computation for depth 15, residue 25747. -/
theorem bounds_15_25747 : exactInterval 15 25747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25747 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25747) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25747 : oddCount 25747 15 = 9 ∧ acceleratedOrbit 15 25747 = 15470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25747 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25747) = 3 ^ 9 * m + 15470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25747.1, data_15_25747.2]

/-- Complete interval computation for depth 15, residue 25748. -/
theorem bounds_15_25748 : exactInterval 15 25748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25748 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25748) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25748 : oddCount 25748 15 = 7 ∧ acceleratedOrbit 15 25748 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25748 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25748) = 3 ^ 7 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25748.1, data_15_25748.2]

/-- Complete interval computation for depth 15, residue 25749. -/
theorem bounds_15_25749 : exactInterval 15 25749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25749 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25749) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25749 : oddCount 25749 15 = 7 ∧ acceleratedOrbit 15 25749 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25749 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25749) = 3 ^ 7 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25749.1, data_15_25749.2]

/-- Complete interval computation for depth 15, residue 25750. -/
theorem bounds_15_25750 : exactInterval 15 25750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25750 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25750) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25750 : oddCount 25750 15 = 7 ∧ acceleratedOrbit 15 25750 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25750 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25750) = 3 ^ 7 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25750.1, data_15_25750.2]

/-- Complete interval computation for depth 15, residue 25751. -/
theorem bounds_15_25751 : exactInterval 15 25751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25751 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25751) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25751 : oddCount 25751 15 = 7 ∧ acceleratedOrbit 15 25751 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25751 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25751) = 3 ^ 7 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25751.1, data_15_25751.2]

/-- Complete interval computation for depth 15, residue 25752. -/
theorem bounds_15_25752 : exactInterval 15 25752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25752 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25752) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25752 : oddCount 25752 15 = 7 ∧ acceleratedOrbit 15 25752 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25752 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25752) = 3 ^ 7 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25752.1, data_15_25752.2]

/-- Complete interval computation for depth 15, residue 25753. -/
theorem bounds_15_25753 : exactInterval 15 25753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25753 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25753) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25753 : oddCount 25753 15 = 5 ∧ acceleratedOrbit 15 25753 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25753 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25753) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25753.1, data_15_25753.2]

/-- Complete interval computation for depth 15, residue 25754. -/
theorem bounds_15_25754 : exactInterval 15 25754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25754 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25754) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25754 : oddCount 25754 15 = 7 ∧ acceleratedOrbit 15 25754 = 1721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25754 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25754) = 3 ^ 7 * m + 1721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25754.1, data_15_25754.2]

end Collatz.Research.PassageAtlas.Batch0786
