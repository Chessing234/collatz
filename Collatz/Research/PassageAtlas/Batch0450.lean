import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0450

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 14712. -/
theorem bounds_15_14712 : exactInterval 15 14712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14712 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14712) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14712 : oddCount 14712 15 = 7 ∧ acceleratedOrbit 15 14712 = 983 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14712 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14712) = 3 ^ 7 * m + 983 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14712.1, data_15_14712.2]

/-- Complete interval computation for depth 15, residue 14713. -/
theorem bounds_15_14713 : exactInterval 15 14713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14713 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14713) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14713 : oddCount 14713 15 = 11 ∧ acceleratedOrbit 15 14713 = 79552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14713 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14713) = 3 ^ 11 * m + 79552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14713.1, data_15_14713.2]

/-- Complete interval computation for depth 15, residue 14714. -/
theorem bounds_15_14714 : exactInterval 15 14714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14714 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14714) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14714 : oddCount 14714 15 = 7 ∧ acceleratedOrbit 15 14714 = 983 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14714 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14714) = 3 ^ 7 * m + 983 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14714.1, data_15_14714.2]

/-- Complete interval computation for depth 15, residue 14715. -/
theorem bounds_15_14715 : exactInterval 15 14715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14715 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14715) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14715 : oddCount 14715 15 = 8 ∧ acceleratedOrbit 15 14715 = 2947 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14715 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14715) = 3 ^ 8 * m + 2947 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14715.1, data_15_14715.2]

/-- Complete interval computation for depth 15, residue 14716. -/
theorem bounds_15_14716 : exactInterval 15 14716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14716 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14716) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14716 : oddCount 14716 15 = 7 ∧ acceleratedOrbit 15 14716 = 983 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14716 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14716) = 3 ^ 7 * m + 983 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14716.1, data_15_14716.2]

/-- Complete interval computation for depth 15, residue 14717. -/
theorem bounds_15_14717 : exactInterval 15 14717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14717 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14717) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14717 : oddCount 14717 15 = 7 ∧ acceleratedOrbit 15 14717 = 983 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14717 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14717) = 3 ^ 7 * m + 983 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14717.1, data_15_14717.2]

/-- Complete interval computation for depth 15, residue 14718. -/
theorem bounds_15_14718 : exactInterval 15 14718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14718 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14718) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14718 : oddCount 14718 15 = 10 ∧ acceleratedOrbit 15 14718 = 26527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14718 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14718) = 3 ^ 10 * m + 26527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14718.1, data_15_14718.2]

/-- Complete interval computation for depth 15, residue 14719. -/
theorem bounds_15_14719 : exactInterval 15 14719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14719 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14719) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14719 : oddCount 14719 15 = 10 ∧ acceleratedOrbit 15 14719 = 26527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14719 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14719) = 3 ^ 10 * m + 26527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14719.1, data_15_14719.2]

/-- Complete interval computation for depth 15, residue 14720. -/
theorem bounds_15_14720 : exactInterval 15 14720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14720 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14720) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14720 : oddCount 14720 15 = 4 ∧ acceleratedOrbit 15 14720 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14720 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14720) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14720.1, data_15_14720.2]

/-- Complete interval computation for depth 15, residue 14721. -/
theorem bounds_15_14721 : exactInterval 15 14721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14721 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14721) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14721 : oddCount 14721 15 = 7 ∧ acceleratedOrbit 15 14721 = 983 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14721 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14721) = 3 ^ 7 * m + 983 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14721.1, data_15_14721.2]

/-- Complete interval computation for depth 15, residue 14722. -/
theorem bounds_15_14722 : exactInterval 15 14722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14722 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14722) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14722 : oddCount 14722 15 = 6 ∧ acceleratedOrbit 15 14722 = 328 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14722 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14722) = 3 ^ 6 * m + 328 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14722.1, data_15_14722.2]

/-- Complete interval computation for depth 15, residue 14723. -/
theorem bounds_15_14723 : exactInterval 15 14723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14723 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14723) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14723 : oddCount 14723 15 = 6 ∧ acceleratedOrbit 15 14723 = 328 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14723 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14723) = 3 ^ 6 * m + 328 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14723.1, data_15_14723.2]

/-- Complete interval computation for depth 15, residue 14724. -/
theorem bounds_15_14724 : exactInterval 15 14724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14724 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14724) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14724 : oddCount 14724 15 = 6 ∧ acceleratedOrbit 15 14724 = 328 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14724 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14724) = 3 ^ 6 * m + 328 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14724.1, data_15_14724.2]

/-- Complete interval computation for depth 15, residue 14725. -/
theorem bounds_15_14725 : exactInterval 15 14725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14725 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14725) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14725 : oddCount 14725 15 = 6 ∧ acceleratedOrbit 15 14725 = 328 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14725 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14725) = 3 ^ 6 * m + 328 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14725.1, data_15_14725.2]

/-- Complete interval computation for depth 15, residue 14726. -/
theorem bounds_15_14726 : exactInterval 15 14726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14726 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14726) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14726 : oddCount 14726 15 = 6 ∧ acceleratedOrbit 15 14726 = 328 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14726 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14726) = 3 ^ 6 * m + 328 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14726.1, data_15_14726.2]

/-- Complete interval computation for depth 15, residue 14727. -/
theorem bounds_15_14727 : exactInterval 15 14727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14727 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14727) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14727 : oddCount 14727 15 = 6 ∧ acceleratedOrbit 15 14727 = 328 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14727 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14727) = 3 ^ 6 * m + 328 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14727.1, data_15_14727.2]

/-- Complete interval computation for depth 15, residue 14728. -/
theorem bounds_15_14728 : exactInterval 15 14728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14728 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14728) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14728 : oddCount 14728 15 = 5 ∧ acceleratedOrbit 15 14728 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14728 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14728) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14728.1, data_15_14728.2]

/-- Complete interval computation for depth 15, residue 14729. -/
theorem bounds_15_14729 : exactInterval 15 14729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14729 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14729) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14729 : oddCount 14729 15 = 9 ∧ acceleratedOrbit 15 14729 = 8849 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14729 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14729) = 3 ^ 9 * m + 8849 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14729.1, data_15_14729.2]

/-- Complete interval computation for depth 15, residue 14730. -/
theorem bounds_15_14730 : exactInterval 15 14730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14730 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14730) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14730 : oddCount 14730 15 = 5 ∧ acceleratedOrbit 15 14730 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14730 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14730) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14730.1, data_15_14730.2]

/-- Complete interval computation for depth 15, residue 14731. -/
theorem bounds_15_14731 : exactInterval 15 14731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14731 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14731) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14731 : oddCount 14731 15 = 9 ∧ acceleratedOrbit 15 14731 = 8851 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14731 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14731) = 3 ^ 9 * m + 8851 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14731.1, data_15_14731.2]

/-- Complete interval computation for depth 15, residue 14732. -/
theorem bounds_15_14732 : exactInterval 15 14732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14732 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14732) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14732 : oddCount 14732 15 = 5 ∧ acceleratedOrbit 15 14732 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14732 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14732) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14732.1, data_15_14732.2]

/-- Complete interval computation for depth 15, residue 14733. -/
theorem bounds_15_14733 : exactInterval 15 14733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14733 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14733) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14733 : oddCount 14733 15 = 5 ∧ acceleratedOrbit 15 14733 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14733 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14733) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14733.1, data_15_14733.2]

/-- Complete interval computation for depth 15, residue 14734. -/
theorem bounds_15_14734 : exactInterval 15 14734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14734 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14734) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14734 : oddCount 14734 15 = 9 ∧ acceleratedOrbit 15 14734 = 8855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14734 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14734) = 3 ^ 9 * m + 8855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14734.1, data_15_14734.2]

/-- Complete interval computation for depth 15, residue 14735. -/
theorem bounds_15_14735 : exactInterval 15 14735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14735 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14735) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14735 : oddCount 14735 15 = 9 ∧ acceleratedOrbit 15 14735 = 8855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14735 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14735) = 3 ^ 9 * m + 8855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14735.1, data_15_14735.2]

/-- Complete interval computation for depth 15, residue 14736. -/
theorem bounds_15_14736 : exactInterval 15 14736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14736 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14736) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14736 : oddCount 14736 15 = 5 ∧ acceleratedOrbit 15 14736 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14736 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14736) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14736.1, data_15_14736.2]

/-- Complete interval computation for depth 15, residue 14737. -/
theorem bounds_15_14737 : exactInterval 15 14737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14737 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14737) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14737 : oddCount 14737 15 = 7 ∧ acceleratedOrbit 15 14737 = 985 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14737 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14737) = 3 ^ 7 * m + 985 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14737.1, data_15_14737.2]

/-- Complete interval computation for depth 15, residue 14738. -/
theorem bounds_15_14738 : exactInterval 15 14738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14738 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14738) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14738 : oddCount 14738 15 = 7 ∧ acceleratedOrbit 15 14738 = 985 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14738 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14738) = 3 ^ 7 * m + 985 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14738.1, data_15_14738.2]

/-- Complete interval computation for depth 15, residue 14739. -/
theorem bounds_15_14739 : exactInterval 15 14739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14739 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14739) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14739 : oddCount 14739 15 = 7 ∧ acceleratedOrbit 15 14739 = 985 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14739 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14739) = 3 ^ 7 * m + 985 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14739.1, data_15_14739.2]

/-- Complete interval computation for depth 15, residue 14740. -/
theorem bounds_15_14740 : exactInterval 15 14740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14740 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14740) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14740 : oddCount 14740 15 = 5 ∧ acceleratedOrbit 15 14740 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14740 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14740) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14740.1, data_15_14740.2]

/-- Complete interval computation for depth 15, residue 14741. -/
theorem bounds_15_14741 : exactInterval 15 14741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14741 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14741) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14741 : oddCount 14741 15 = 5 ∧ acceleratedOrbit 15 14741 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14741 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14741) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14741.1, data_15_14741.2]

/-- Complete interval computation for depth 15, residue 14742. -/
theorem bounds_15_14742 : exactInterval 15 14742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14742 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14742) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14742 : oddCount 14742 15 = 7 ∧ acceleratedOrbit 15 14742 = 985 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14742 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14742) = 3 ^ 7 * m + 985 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14742.1, data_15_14742.2]

/-- Complete interval computation for depth 15, residue 14743. -/
theorem bounds_15_14743 : exactInterval 15 14743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14743 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14743) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14743 : oddCount 14743 15 = 7 ∧ acceleratedOrbit 15 14743 = 985 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14743 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14743) = 3 ^ 7 * m + 985 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14743.1, data_15_14743.2]

/-- Complete interval computation for depth 15, residue 14744. -/
theorem bounds_15_14744 : exactInterval 15 14744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14744 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14744) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14744 : oddCount 14744 15 = 5 ∧ acceleratedOrbit 15 14744 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14744 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14744) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14744.1, data_15_14744.2]

end Collatz.Research.PassageAtlas.Batch0450
