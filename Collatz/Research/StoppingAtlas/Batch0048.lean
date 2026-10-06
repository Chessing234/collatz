import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0048

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 721. -/
theorem bounds_10_721 : exactInterval 10 721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_721 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 721) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_721 : oddCount 721 10 = 5 ∧ acceleratedOrbit 10 721 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_721 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 721) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_721.1, data_10_721.2]

/-- Complete interval computation for depth 10, residue 722. -/
theorem bounds_10_722 : exactInterval 10 722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_722 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 722) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_722 : oddCount 722 10 = 5 ∧ acceleratedOrbit 10 722 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_722 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 722) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_722.1, data_10_722.2]

/-- Complete interval computation for depth 10, residue 723. -/
theorem bounds_10_723 : exactInterval 10 723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_723 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 723) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_723 : oddCount 723 10 = 5 ∧ acceleratedOrbit 10 723 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_723 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 723) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_723.1, data_10_723.2]

/-- Complete interval computation for depth 10, residue 724. -/
theorem bounds_10_724 : exactInterval 10 724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_724 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 724) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_724 : oddCount 724 10 = 3 ∧ acceleratedOrbit 10 724 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_724 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 724) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_724.1, data_10_724.2]

/-- Complete interval computation for depth 10, residue 725. -/
theorem bounds_10_725 : exactInterval 10 725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_725 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 725) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_725 : oddCount 725 10 = 3 ∧ acceleratedOrbit 10 725 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_725 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 725) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_725.1, data_10_725.2]

/-- Complete interval computation for depth 10, residue 726. -/
theorem bounds_10_726 : exactInterval 10 726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_726 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 726) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_726 : oddCount 726 10 = 5 ∧ acceleratedOrbit 10 726 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_726 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 726) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_726.1, data_10_726.2]

/-- Complete interval computation for depth 10, residue 727. -/
theorem bounds_10_727 : exactInterval 10 727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_727 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 727) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_727 : oddCount 727 10 = 5 ∧ acceleratedOrbit 10 727 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_727 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 727) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_727.1, data_10_727.2]

/-- Complete interval computation for depth 10, residue 728. -/
theorem bounds_10_728 : exactInterval 10 728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_728 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 728) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_728 : oddCount 728 10 = 5 ∧ acceleratedOrbit 10 728 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_728 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 728) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_728.1, data_10_728.2]

/-- Complete interval computation for depth 10, residue 729. -/
theorem bounds_10_729 : exactInterval 10 729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_729 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 729) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_729 : oddCount 729 10 = 4 ∧ acceleratedOrbit 10 729 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_729 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 729) = 3 ^ 4 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_729.1, data_10_729.2]

/-- Complete interval computation for depth 10, residue 730. -/
theorem bounds_10_730 : exactInterval 10 730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_730 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 730) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_730 : oddCount 730 10 = 5 ∧ acceleratedOrbit 10 730 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_730 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 730) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_730.1, data_10_730.2]

/-- Complete interval computation for depth 10, residue 731. -/
theorem bounds_10_731 : exactInterval 10 731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_731 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 731) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_731 : oddCount 731 10 = 7 ∧ acceleratedOrbit 10 731 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_731 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 731) = 3 ^ 7 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_731.1, data_10_731.2]

/-- Complete interval computation for depth 10, residue 732. -/
theorem bounds_10_732 : exactInterval 10 732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_732 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 732) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_732 : oddCount 732 10 = 5 ∧ acceleratedOrbit 10 732 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_732 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 732) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_732.1, data_10_732.2]

/-- Complete interval computation for depth 10, residue 733. -/
theorem bounds_10_733 : exactInterval 10 733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_733 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 733) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_733 : oddCount 733 10 = 5 ∧ acceleratedOrbit 10 733 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_733 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 733) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_733.1, data_10_733.2]

/-- Complete interval computation for depth 10, residue 734. -/
theorem bounds_10_734 : exactInterval 10 734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_734 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 734) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_734 : oddCount 734 10 = 6 ∧ acceleratedOrbit 10 734 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_734 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 734) = 3 ^ 6 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_734.1, data_10_734.2]

/-- Complete interval computation for depth 10, residue 735. -/
theorem bounds_10_735 : exactInterval 10 735 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_735 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 735) 10 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_735 : oddCount 735 10 = 6 ∧ acceleratedOrbit 10 735 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_735 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 735) = 3 ^ 6 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_735.1, data_10_735.2]

/-- Complete interval computation for depth 10, residue 736. -/
theorem bounds_10_736 : exactInterval 10 736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_736 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 736) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_736 : oddCount 736 10 = 3 ∧ acceleratedOrbit 10 736 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_736 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 736) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_736.1, data_10_736.2]

end Collatz.Research.StoppingAtlas.Batch0048
