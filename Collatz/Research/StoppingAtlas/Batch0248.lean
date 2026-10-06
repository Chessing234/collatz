import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0248

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 721. -/
theorem bounds_12_721 : exactInterval 12 721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_721 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 721) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_721 : oddCount 721 12 = 5 ∧ acceleratedOrbit 12 721 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_721 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 721) = 3 ^ 5 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_721.1, data_12_721.2]

/-- Complete interval computation for depth 12, residue 722. -/
theorem bounds_12_722 : exactInterval 12 722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_722 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 722) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_722 : oddCount 722 12 = 5 ∧ acceleratedOrbit 12 722 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_722 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 722) = 3 ^ 5 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_722.1, data_12_722.2]

/-- Complete interval computation for depth 12, residue 723. -/
theorem bounds_12_723 : exactInterval 12 723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_723 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 723) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_723 : oddCount 723 12 = 5 ∧ acceleratedOrbit 12 723 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_723 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 723) = 3 ^ 5 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_723.1, data_12_723.2]

/-- Complete interval computation for depth 12, residue 724. -/
theorem bounds_12_724 : exactInterval 12 724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_724 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 724) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_724 : oddCount 724 12 = 3 ∧ acceleratedOrbit 12 724 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_724 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 724) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_724.1, data_12_724.2]

/-- Complete interval computation for depth 12, residue 725. -/
theorem bounds_12_725 : exactInterval 12 725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_725 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 725) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_725 : oddCount 725 12 = 3 ∧ acceleratedOrbit 12 725 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_725 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 725) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_725.1, data_12_725.2]

/-- Complete interval computation for depth 12, residue 726. -/
theorem bounds_12_726 : exactInterval 12 726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_726 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 726) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_726 : oddCount 726 12 = 6 ∧ acceleratedOrbit 12 726 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_726 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 726) = 3 ^ 6 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_726.1, data_12_726.2]

/-- Complete interval computation for depth 12, residue 727. -/
theorem bounds_12_727 : exactInterval 12 727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_727 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 727) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_727 : oddCount 727 12 = 6 ∧ acceleratedOrbit 12 727 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_727 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 727) = 3 ^ 6 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_727.1, data_12_727.2]

/-- Complete interval computation for depth 12, residue 728. -/
theorem bounds_12_728 : exactInterval 12 728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_728 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 728) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_728 : oddCount 728 12 = 7 ∧ acceleratedOrbit 12 728 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_728 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 728) = 3 ^ 7 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_728.1, data_12_728.2]

/-- Complete interval computation for depth 12, residue 729. -/
theorem bounds_12_729 : exactInterval 12 729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_729 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 729) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_729 : oddCount 729 12 = 5 ∧ acceleratedOrbit 12 729 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_729 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 729) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_729.1, data_12_729.2]

/-- Complete interval computation for depth 12, residue 730. -/
theorem bounds_12_730 : exactInterval 12 730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_730 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 730) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_730 : oddCount 730 12 = 7 ∧ acceleratedOrbit 12 730 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_730 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 730) = 3 ^ 7 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_730.1, data_12_730.2]

/-- Complete interval computation for depth 12, residue 731. -/
theorem bounds_12_731 : exactInterval 12 731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_731 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 731) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_731 : oddCount 731 12 = 8 ∧ acceleratedOrbit 12 731 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_731 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 731) = 3 ^ 8 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_731.1, data_12_731.2]

/-- Complete interval computation for depth 12, residue 732. -/
theorem bounds_12_732 : exactInterval 12 732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_732 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 732) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_732 : oddCount 732 12 = 7 ∧ acceleratedOrbit 12 732 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_732 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 732) = 3 ^ 7 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_732.1, data_12_732.2]

/-- Complete interval computation for depth 12, residue 733. -/
theorem bounds_12_733 : exactInterval 12 733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_733 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 733) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_733 : oddCount 733 12 = 7 ∧ acceleratedOrbit 12 733 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_733 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 733) = 3 ^ 7 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_733.1, data_12_733.2]

/-- Complete interval computation for depth 12, residue 734. -/
theorem bounds_12_734 : exactInterval 12 734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_734 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 734) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_734 : oddCount 734 12 = 6 ∧ acceleratedOrbit 12 734 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_734 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 734) = 3 ^ 6 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_734.1, data_12_734.2]

/-- Complete interval computation for depth 12, residue 735. -/
theorem bounds_12_735 : exactInterval 12 735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_735 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 735) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_735 : oddCount 735 12 = 6 ∧ acceleratedOrbit 12 735 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_735 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 735) = 3 ^ 6 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_735.1, data_12_735.2]

/-- Complete interval computation for depth 12, residue 736. -/
theorem bounds_12_736 : exactInterval 12 736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_736 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 736) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_736 : oddCount 736 12 = 3 ∧ acceleratedOrbit 12 736 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_736 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 736) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_736.1, data_12_736.2]

end Collatz.Research.StoppingAtlas.Batch0248
