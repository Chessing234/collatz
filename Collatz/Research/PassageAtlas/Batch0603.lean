import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0603

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 19726. -/
theorem bounds_15_19726 : exactInterval 15 19726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19726 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19726) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19726 : oddCount 19726 15 = 6 ∧ acceleratedOrbit 15 19726 = 439 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19726 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19726) = 3 ^ 6 * m + 439 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19726.1, data_15_19726.2]

/-- Complete interval computation for depth 15, residue 19727. -/
theorem bounds_15_19727 : exactInterval 15 19727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19727 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19727) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19727 : oddCount 19727 15 = 6 ∧ acceleratedOrbit 15 19727 = 439 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19727 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19727) = 3 ^ 6 * m + 439 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19727.1, data_15_19727.2]

/-- Complete interval computation for depth 15, residue 19728. -/
theorem bounds_15_19728 : exactInterval 15 19728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19728 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19728) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19728 : oddCount 19728 15 = 7 ∧ acceleratedOrbit 15 19728 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19728 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19728) = 3 ^ 7 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19728.1, data_15_19728.2]

/-- Complete interval computation for depth 15, residue 19729. -/
theorem bounds_15_19729 : exactInterval 15 19729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19729 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19729) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19729 : oddCount 19729 15 = 7 ∧ acceleratedOrbit 15 19729 = 1318 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19729 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19729) = 3 ^ 7 * m + 1318 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19729.1, data_15_19729.2]

/-- Complete interval computation for depth 15, residue 19730. -/
theorem bounds_15_19730 : exactInterval 15 19730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19730 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19730) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19730 : oddCount 19730 15 = 9 ∧ acceleratedOrbit 15 19730 = 11854 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19730 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19730) = 3 ^ 9 * m + 11854 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19730.1, data_15_19730.2]

/-- Complete interval computation for depth 15, residue 19731. -/
theorem bounds_15_19731 : exactInterval 15 19731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19731 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19731) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19731 : oddCount 19731 15 = 9 ∧ acceleratedOrbit 15 19731 = 11854 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19731 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19731) = 3 ^ 9 * m + 11854 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19731.1, data_15_19731.2]

/-- Complete interval computation for depth 15, residue 19732. -/
theorem bounds_15_19732 : exactInterval 15 19732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19732 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19732) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19732 : oddCount 19732 15 = 7 ∧ acceleratedOrbit 15 19732 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19732 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19732) = 3 ^ 7 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19732.1, data_15_19732.2]

/-- Complete interval computation for depth 15, residue 19733. -/
theorem bounds_15_19733 : exactInterval 15 19733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19733 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19733) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19733 : oddCount 19733 15 = 7 ∧ acceleratedOrbit 15 19733 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19733 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19733) = 3 ^ 7 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19733.1, data_15_19733.2]

/-- Complete interval computation for depth 15, residue 19734. -/
theorem bounds_15_19734 : exactInterval 15 19734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19734 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19734) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19734 : oddCount 19734 15 = 7 ∧ acceleratedOrbit 15 19734 = 1318 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19734 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19734) = 3 ^ 7 * m + 1318 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19734.1, data_15_19734.2]

/-- Complete interval computation for depth 15, residue 19735. -/
theorem bounds_15_19735 : exactInterval 15 19735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19735 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19735) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19735 : oddCount 19735 15 = 7 ∧ acceleratedOrbit 15 19735 = 1318 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19735 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19735) = 3 ^ 7 * m + 1318 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19735.1, data_15_19735.2]

/-- Complete interval computation for depth 15, residue 19736. -/
theorem bounds_15_19736 : exactInterval 15 19736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19736 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19736) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19736 : oddCount 19736 15 = 7 ∧ acceleratedOrbit 15 19736 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19736 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19736) = 3 ^ 7 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19736.1, data_15_19736.2]

/-- Complete interval computation for depth 15, residue 19737. -/
theorem bounds_15_19737 : exactInterval 15 19737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19737 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19737) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19737 : oddCount 19737 15 = 8 ∧ acceleratedOrbit 15 19737 = 3953 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19737 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19737) = 3 ^ 8 * m + 3953 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19737.1, data_15_19737.2]

/-- Complete interval computation for depth 15, residue 19738. -/
theorem bounds_15_19738 : exactInterval 15 19738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19738 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19738) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19738 : oddCount 19738 15 = 7 ∧ acceleratedOrbit 15 19738 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19738 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19738) = 3 ^ 7 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19738.1, data_15_19738.2]

/-- Complete interval computation for depth 15, residue 19739. -/
theorem bounds_15_19739 : exactInterval 15 19739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19739 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19739) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19739 : oddCount 19739 15 = 10 ∧ acceleratedOrbit 15 19739 = 35573 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19739 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19739) = 3 ^ 10 * m + 35573 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19739.1, data_15_19739.2]

/-- Complete interval computation for depth 15, residue 19740. -/
theorem bounds_15_19740 : exactInterval 15 19740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19740 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19740) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19740 : oddCount 19740 15 = 10 ∧ acceleratedOrbit 15 19740 = 35585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19740 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19740) = 3 ^ 10 * m + 35585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19740.1, data_15_19740.2]

/-- Complete interval computation for depth 15, residue 19741. -/
theorem bounds_15_19741 : exactInterval 15 19741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19741 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19741) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19741 : oddCount 19741 15 = 10 ∧ acceleratedOrbit 15 19741 = 35585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19741 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19741) = 3 ^ 10 * m + 35585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19741.1, data_15_19741.2]

/-- Complete interval computation for depth 15, residue 19742. -/
theorem bounds_15_19742 : exactInterval 15 19742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19742 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19742) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19742 : oddCount 19742 15 = 10 ∧ acceleratedOrbit 15 19742 = 35585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19742 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19742) = 3 ^ 10 * m + 35585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19742.1, data_15_19742.2]

/-- Complete interval computation for depth 15, residue 19743. -/
theorem bounds_15_19743 : exactInterval 15 19743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19743 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19743) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19743 : oddCount 19743 15 = 7 ∧ acceleratedOrbit 15 19743 = 1318 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19743 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19743) = 3 ^ 7 * m + 1318 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19743.1, data_15_19743.2]

/-- Complete interval computation for depth 15, residue 19744. -/
theorem bounds_15_19744 : exactInterval 15 19744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19744 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19744) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19744 : oddCount 19744 15 = 7 ∧ acceleratedOrbit 15 19744 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19744 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19744) = 3 ^ 7 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19744.1, data_15_19744.2]

/-- Complete interval computation for depth 15, residue 19745. -/
theorem bounds_15_19745 : exactInterval 15 19745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19745 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19745) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19745 : oddCount 19745 15 = 6 ∧ acceleratedOrbit 15 19745 = 440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19745 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19745) = 3 ^ 6 * m + 440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19745.1, data_15_19745.2]

/-- Complete interval computation for depth 15, residue 19746. -/
theorem bounds_15_19746 : exactInterval 15 19746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19746 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19746) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19746 : oddCount 19746 15 = 6 ∧ acceleratedOrbit 15 19746 = 440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19746 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19746) = 3 ^ 6 * m + 440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19746.1, data_15_19746.2]

/-- Complete interval computation for depth 15, residue 19747. -/
theorem bounds_15_19747 : exactInterval 15 19747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19747 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19747) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19747 : oddCount 19747 15 = 6 ∧ acceleratedOrbit 15 19747 = 440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19747 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19747) = 3 ^ 6 * m + 440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19747.1, data_15_19747.2]

/-- Complete interval computation for depth 15, residue 19748. -/
theorem bounds_15_19748 : exactInterval 15 19748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19748 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19748) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19748 : oddCount 19748 15 = 6 ∧ acceleratedOrbit 15 19748 = 440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19748 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19748) = 3 ^ 6 * m + 440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19748.1, data_15_19748.2]

/-- Complete interval computation for depth 15, residue 19749. -/
theorem bounds_15_19749 : exactInterval 15 19749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19749 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19749) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19749 : oddCount 19749 15 = 6 ∧ acceleratedOrbit 15 19749 = 440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19749 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19749) = 3 ^ 6 * m + 440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19749.1, data_15_19749.2]

/-- Complete interval computation for depth 15, residue 19750. -/
theorem bounds_15_19750 : exactInterval 15 19750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19750 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19750) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19750 : oddCount 19750 15 = 6 ∧ acceleratedOrbit 15 19750 = 440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19750 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19750) = 3 ^ 6 * m + 440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19750.1, data_15_19750.2]

/-- Complete interval computation for depth 15, residue 19751. -/
theorem bounds_15_19751 : exactInterval 15 19751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19751 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19751) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19751 : oddCount 19751 15 = 9 ∧ acceleratedOrbit 15 19751 = 11866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19751 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19751) = 3 ^ 9 * m + 11866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19751.1, data_15_19751.2]

/-- Complete interval computation for depth 15, residue 19752. -/
theorem bounds_15_19752 : exactInterval 15 19752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19752 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19752) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19752 : oddCount 19752 15 = 7 ∧ acceleratedOrbit 15 19752 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19752 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19752) = 3 ^ 7 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19752.1, data_15_19752.2]

/-- Complete interval computation for depth 15, residue 19753. -/
theorem bounds_15_19753 : exactInterval 15 19753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19753 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19753) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19753 : oddCount 19753 15 = 11 ∧ acceleratedOrbit 15 19753 = 106798 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19753 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19753) = 3 ^ 11 * m + 106798 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19753.1, data_15_19753.2]

/-- Complete interval computation for depth 15, residue 19754. -/
theorem bounds_15_19754 : exactInterval 15 19754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19754 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19754) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19754 : oddCount 19754 15 = 7 ∧ acceleratedOrbit 15 19754 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19754 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19754) = 3 ^ 7 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19754.1, data_15_19754.2]

/-- Complete interval computation for depth 15, residue 19755. -/
theorem bounds_15_19755 : exactInterval 15 19755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19755 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19755) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19755 : oddCount 19755 15 = 9 ∧ acceleratedOrbit 15 19755 = 11870 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19755 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19755) = 3 ^ 9 * m + 11870 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19755.1, data_15_19755.2]

/-- Complete interval computation for depth 15, residue 19756. -/
theorem bounds_15_19756 : exactInterval 15 19756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19756 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19756) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19756 : oddCount 19756 15 = 7 ∧ acceleratedOrbit 15 19756 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19756 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19756) = 3 ^ 7 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19756.1, data_15_19756.2]

/-- Complete interval computation for depth 15, residue 19757. -/
theorem bounds_15_19757 : exactInterval 15 19757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19757 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19757) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19757 : oddCount 19757 15 = 7 ∧ acceleratedOrbit 15 19757 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19757 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19757) = 3 ^ 7 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19757.1, data_15_19757.2]

/-- Complete interval computation for depth 15, residue 19758. -/
theorem bounds_15_19758 : exactInterval 15 19758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19758 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19758) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19758 : oddCount 19758 15 = 7 ∧ acceleratedOrbit 15 19758 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19758 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19758) = 3 ^ 7 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19758.1, data_15_19758.2]

end Collatz.Research.PassageAtlas.Batch0603
