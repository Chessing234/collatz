import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0908

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 29720. -/
theorem bounds_15_29720 : exactInterval 15 29720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29720 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29720) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29720 : oddCount 29720 15 = 4 ∧ acceleratedOrbit 15 29720 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29720 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29720) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29720.1, data_15_29720.2]

/-- Complete interval computation for depth 15, residue 29721. -/
theorem bounds_15_29721 : exactInterval 15 29721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29721 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29721) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29721 : oddCount 29721 15 = 10 ∧ acceleratedOrbit 15 29721 = 53567 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29721 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29721) = 3 ^ 10 * m + 53567 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29721.1, data_15_29721.2]

/-- Complete interval computation for depth 15, residue 29722. -/
theorem bounds_15_29722 : exactInterval 15 29722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29722 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29722) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29722 : oddCount 29722 15 = 4 ∧ acceleratedOrbit 15 29722 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29722 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29722) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29722.1, data_15_29722.2]

/-- Complete interval computation for depth 15, residue 29723. -/
theorem bounds_15_29723 : exactInterval 15 29723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29723 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29723) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29723 : oddCount 29723 15 = 11 ∧ acceleratedOrbit 15 29723 = 160694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29723 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29723) = 3 ^ 11 * m + 160694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29723.1, data_15_29723.2]

/-- Complete interval computation for depth 15, residue 29724. -/
theorem bounds_15_29724 : exactInterval 15 29724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29724 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29724) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29724 : oddCount 29724 15 = 9 ∧ acceleratedOrbit 15 29724 = 17860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29724 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29724) = 3 ^ 9 * m + 17860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29724.1, data_15_29724.2]

/-- Complete interval computation for depth 15, residue 29725. -/
theorem bounds_15_29725 : exactInterval 15 29725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29725 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29725) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29725 : oddCount 29725 15 = 9 ∧ acceleratedOrbit 15 29725 = 17860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29725 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29725) = 3 ^ 9 * m + 17860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29725.1, data_15_29725.2]

/-- Complete interval computation for depth 15, residue 29726. -/
theorem bounds_15_29726 : exactInterval 15 29726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29726 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29726) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29726 : oddCount 29726 15 = 9 ∧ acceleratedOrbit 15 29726 = 17860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29726 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29726) = 3 ^ 9 * m + 17860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29726.1, data_15_29726.2]

/-- Complete interval computation for depth 15, residue 29727. -/
theorem bounds_15_29727 : exactInterval 15 29727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29727 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29727) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29727 : oddCount 29727 15 = 11 ∧ acceleratedOrbit 15 29727 = 160714 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29727 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29727) = 3 ^ 11 * m + 160714 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29727.1, data_15_29727.2]

/-- Complete interval computation for depth 15, residue 29728. -/
theorem bounds_15_29728 : exactInterval 15 29728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29728 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29728) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29728 : oddCount 29728 15 = 5 ∧ acceleratedOrbit 15 29728 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29728 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29728) = 3 ^ 5 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29728.1, data_15_29728.2]

/-- Complete interval computation for depth 15, residue 29729. -/
theorem bounds_15_29729 : exactInterval 15 29729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29729 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29729) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29729 : oddCount 29729 15 = 10 ∧ acceleratedOrbit 15 29729 = 53581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29729 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29729) = 3 ^ 10 * m + 53581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29729.1, data_15_29729.2]

/-- Complete interval computation for depth 15, residue 29730. -/
theorem bounds_15_29730 : exactInterval 15 29730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29730 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29730) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29730 : oddCount 29730 15 = 4 ∧ acceleratedOrbit 15 29730 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29730 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29730) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29730.1, data_15_29730.2]

/-- Complete interval computation for depth 15, residue 29731. -/
theorem bounds_15_29731 : exactInterval 15 29731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29731 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29731) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29731 : oddCount 29731 15 = 4 ∧ acceleratedOrbit 15 29731 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29731 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29731) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29731.1, data_15_29731.2]

/-- Complete interval computation for depth 15, residue 29732. -/
theorem bounds_15_29732 : exactInterval 15 29732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29732 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29732) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29732 : oddCount 29732 15 = 7 ∧ acceleratedOrbit 15 29732 = 1985 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29732 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29732) = 3 ^ 7 * m + 1985 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29732.1, data_15_29732.2]

/-- Complete interval computation for depth 15, residue 29733. -/
theorem bounds_15_29733 : exactInterval 15 29733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29733 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29733) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29733 : oddCount 29733 15 = 7 ∧ acceleratedOrbit 15 29733 = 1985 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29733 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29733) = 3 ^ 7 * m + 1985 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29733.1, data_15_29733.2]

/-- Complete interval computation for depth 15, residue 29734. -/
theorem bounds_15_29734 : exactInterval 15 29734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29734 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29734) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29734 : oddCount 29734 15 = 7 ∧ acceleratedOrbit 15 29734 = 1985 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29734 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29734) = 3 ^ 7 * m + 1985 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29734.1, data_15_29734.2]

/-- Complete interval computation for depth 15, residue 29735. -/
theorem bounds_15_29735 : exactInterval 15 29735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29735 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29735) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29735 : oddCount 29735 15 = 9 ∧ acceleratedOrbit 15 29735 = 17864 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29735 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29735) = 3 ^ 9 * m + 17864 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29735.1, data_15_29735.2]

/-- Complete interval computation for depth 15, residue 29736. -/
theorem bounds_15_29736 : exactInterval 15 29736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29736 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29736) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29736 : oddCount 29736 15 = 5 ∧ acceleratedOrbit 15 29736 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29736 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29736) = 3 ^ 5 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29736.1, data_15_29736.2]

/-- Complete interval computation for depth 15, residue 29737. -/
theorem bounds_15_29737 : exactInterval 15 29737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29737 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29737) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29737 : oddCount 29737 15 = 9 ∧ acceleratedOrbit 15 29737 = 17864 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29737 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29737) = 3 ^ 9 * m + 17864 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29737.1, data_15_29737.2]

/-- Complete interval computation for depth 15, residue 29738. -/
theorem bounds_15_29738 : exactInterval 15 29738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29738 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29738) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29738 : oddCount 29738 15 = 5 ∧ acceleratedOrbit 15 29738 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29738 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29738) = 3 ^ 5 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29738.1, data_15_29738.2]

/-- Complete interval computation for depth 15, residue 29739. -/
theorem bounds_15_29739 : exactInterval 15 29739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29739 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29739) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29739 : oddCount 29739 15 = 8 ∧ acceleratedOrbit 15 29739 = 5957 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29739 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29739) = 3 ^ 8 * m + 5957 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29739.1, data_15_29739.2]

/-- Complete interval computation for depth 15, residue 29740. -/
theorem bounds_15_29740 : exactInterval 15 29740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29740 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29740) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29740 : oddCount 29740 15 = 6 ∧ acceleratedOrbit 15 29740 = 662 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29740 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29740) = 3 ^ 6 * m + 662 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29740.1, data_15_29740.2]

/-- Complete interval computation for depth 15, residue 29741. -/
theorem bounds_15_29741 : exactInterval 15 29741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29741 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29741) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29741 : oddCount 29741 15 = 6 ∧ acceleratedOrbit 15 29741 = 662 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29741 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29741) = 3 ^ 6 * m + 662 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29741.1, data_15_29741.2]

/-- Complete interval computation for depth 15, residue 29742. -/
theorem bounds_15_29742 : exactInterval 15 29742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29742 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29742) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29742 : oddCount 29742 15 = 6 ∧ acceleratedOrbit 15 29742 = 662 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29742 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29742) = 3 ^ 6 * m + 662 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29742.1, data_15_29742.2]

/-- Complete interval computation for depth 15, residue 29743. -/
theorem bounds_15_29743 : exactInterval 15 29743 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29743 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29743) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29743 : oddCount 29743 15 = 9 ∧ acceleratedOrbit 15 29743 = 17867 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29743 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29743) = 3 ^ 9 * m + 17867 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29743.1, data_15_29743.2]

/-- Complete interval computation for depth 15, residue 29744. -/
theorem bounds_15_29744 : exactInterval 15 29744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29744 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29744) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29744 : oddCount 29744 15 = 5 ∧ acceleratedOrbit 15 29744 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29744 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29744) = 3 ^ 5 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29744.1, data_15_29744.2]

/-- Complete interval computation for depth 15, residue 29745. -/
theorem bounds_15_29745 : exactInterval 15 29745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29745 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29745) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29745 : oddCount 29745 15 = 6 ∧ acceleratedOrbit 15 29745 = 662 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29745 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29745) = 3 ^ 6 * m + 662 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29745.1, data_15_29745.2]

/-- Complete interval computation for depth 15, residue 29746. -/
theorem bounds_15_29746 : exactInterval 15 29746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29746 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29746) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29746 : oddCount 29746 15 = 6 ∧ acceleratedOrbit 15 29746 = 662 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29746 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29746) = 3 ^ 6 * m + 662 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29746.1, data_15_29746.2]

/-- Complete interval computation for depth 15, residue 29747. -/
theorem bounds_15_29747 : exactInterval 15 29747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29747 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29747) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29747 : oddCount 29747 15 = 6 ∧ acceleratedOrbit 15 29747 = 662 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29747 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29747) = 3 ^ 6 * m + 662 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29747.1, data_15_29747.2]

/-- Complete interval computation for depth 15, residue 29748. -/
theorem bounds_15_29748 : exactInterval 15 29748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29748 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29748) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29748 : oddCount 29748 15 = 5 ∧ acceleratedOrbit 15 29748 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29748 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29748) = 3 ^ 5 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29748.1, data_15_29748.2]

/-- Complete interval computation for depth 15, residue 29749. -/
theorem bounds_15_29749 : exactInterval 15 29749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29749 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29749) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29749 : oddCount 29749 15 = 5 ∧ acceleratedOrbit 15 29749 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29749 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29749) = 3 ^ 5 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29749.1, data_15_29749.2]

/-- Complete interval computation for depth 15, residue 29750. -/
theorem bounds_15_29750 : exactInterval 15 29750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29750 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29750) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29750 : oddCount 29750 15 = 9 ∧ acceleratedOrbit 15 29750 = 17873 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29750 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29750) = 3 ^ 9 * m + 17873 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29750.1, data_15_29750.2]

/-- Complete interval computation for depth 15, residue 29751. -/
theorem bounds_15_29751 : exactInterval 15 29751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29751 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29751) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29751 : oddCount 29751 15 = 9 ∧ acceleratedOrbit 15 29751 = 17873 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29751 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29751) = 3 ^ 9 * m + 17873 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29751.1, data_15_29751.2]

/-- Complete interval computation for depth 15, residue 29752. -/
theorem bounds_15_29752 : exactInterval 15 29752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29752 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29752) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29752 : oddCount 29752 15 = 7 ∧ acceleratedOrbit 15 29752 = 1988 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29752 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29752) = 3 ^ 7 * m + 1988 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29752.1, data_15_29752.2]

end Collatz.Research.PassageAtlas.Batch0908
