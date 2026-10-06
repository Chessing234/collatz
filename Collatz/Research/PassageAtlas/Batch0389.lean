import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0389

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 12713. -/
theorem bounds_15_12713 : exactInterval 15 12713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12713 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12713) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12713 : oddCount 12713 15 = 10 ∧ acceleratedOrbit 15 12713 = 22913 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12713 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12713) = 3 ^ 10 * m + 22913 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12713.1, data_15_12713.2]

/-- Complete interval computation for depth 15, residue 12714. -/
theorem bounds_15_12714 : exactInterval 15 12714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12714 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12714) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12714 : oddCount 12714 15 = 3 ∧ acceleratedOrbit 15 12714 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12714 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12714) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12714.1, data_15_12714.2]

/-- Complete interval computation for depth 15, residue 12715. -/
theorem bounds_15_12715 : exactInterval 15 12715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12715 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12715) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12715 : oddCount 12715 15 = 10 ∧ acceleratedOrbit 15 12715 = 22918 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12715 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12715) = 3 ^ 10 * m + 22918 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12715.1, data_15_12715.2]

/-- Complete interval computation for depth 15, residue 12716. -/
theorem bounds_15_12716 : exactInterval 15 12716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12716 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12716) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12716 : oddCount 12716 15 = 8 ∧ acceleratedOrbit 15 12716 = 2548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12716 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12716) = 3 ^ 8 * m + 2548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12716.1, data_15_12716.2]

/-- Complete interval computation for depth 15, residue 12717. -/
theorem bounds_15_12717 : exactInterval 15 12717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12717 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12717) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12717 : oddCount 12717 15 = 8 ∧ acceleratedOrbit 15 12717 = 2548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12717 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12717) = 3 ^ 8 * m + 2548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12717.1, data_15_12717.2]

/-- Complete interval computation for depth 15, residue 12718. -/
theorem bounds_15_12718 : exactInterval 15 12718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12718 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12718) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12718 : oddCount 12718 15 = 8 ∧ acceleratedOrbit 15 12718 = 2548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12718 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12718) = 3 ^ 8 * m + 2548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12718.1, data_15_12718.2]

/-- Complete interval computation for depth 15, residue 12719. -/
theorem bounds_15_12719 : exactInterval 15 12719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12719 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12719) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12719 : oddCount 12719 15 = 6 ∧ acceleratedOrbit 15 12719 = 283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12719 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12719) = 3 ^ 6 * m + 283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12719.1, data_15_12719.2]

/-- Complete interval computation for depth 15, residue 12720. -/
theorem bounds_15_12720 : exactInterval 15 12720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12720 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12720) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12720 : oddCount 12720 15 = 9 ∧ acceleratedOrbit 15 12720 = 7654 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12720 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12720) = 3 ^ 9 * m + 7654 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12720.1, data_15_12720.2]

/-- Complete interval computation for depth 15, residue 12721. -/
theorem bounds_15_12721 : exactInterval 15 12721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12721 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12721) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12721 : oddCount 12721 15 = 8 ∧ acceleratedOrbit 15 12721 = 2551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12721 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12721) = 3 ^ 8 * m + 2551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12721.1, data_15_12721.2]

/-- Complete interval computation for depth 15, residue 12722. -/
theorem bounds_15_12722 : exactInterval 15 12722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12722 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12722) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12722 : oddCount 12722 15 = 8 ∧ acceleratedOrbit 15 12722 = 2551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12722 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12722) = 3 ^ 8 * m + 2551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12722.1, data_15_12722.2]

/-- Complete interval computation for depth 15, residue 12723. -/
theorem bounds_15_12723 : exactInterval 15 12723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12723 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12723) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12723 : oddCount 12723 15 = 8 ∧ acceleratedOrbit 15 12723 = 2551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12723 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12723) = 3 ^ 8 * m + 2551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12723.1, data_15_12723.2]

/-- Complete interval computation for depth 15, residue 12724. -/
theorem bounds_15_12724 : exactInterval 15 12724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12724 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12724) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12724 : oddCount 12724 15 = 9 ∧ acceleratedOrbit 15 12724 = 7654 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12724 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12724) = 3 ^ 9 * m + 7654 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12724.1, data_15_12724.2]

/-- Complete interval computation for depth 15, residue 12725. -/
theorem bounds_15_12725 : exactInterval 15 12725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12725 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12725) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12725 : oddCount 12725 15 = 9 ∧ acceleratedOrbit 15 12725 = 7654 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12725 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12725) = 3 ^ 9 * m + 7654 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12725.1, data_15_12725.2]

/-- Complete interval computation for depth 15, residue 12726. -/
theorem bounds_15_12726 : exactInterval 15 12726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12726 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12726) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12726 : oddCount 12726 15 = 8 ∧ acceleratedOrbit 15 12726 = 2549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12726 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12726) = 3 ^ 8 * m + 2549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12726.1, data_15_12726.2]

/-- Complete interval computation for depth 15, residue 12727. -/
theorem bounds_15_12727 : exactInterval 15 12727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12727 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12727) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12727 : oddCount 12727 15 = 8 ∧ acceleratedOrbit 15 12727 = 2549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12727 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12727) = 3 ^ 8 * m + 2549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12727.1, data_15_12727.2]

/-- Complete interval computation for depth 15, residue 12728. -/
theorem bounds_15_12728 : exactInterval 15 12728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12728 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12728) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12728 : oddCount 12728 15 = 9 ∧ acceleratedOrbit 15 12728 = 7654 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12728 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12728) = 3 ^ 9 * m + 7654 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12728.1, data_15_12728.2]

/-- Complete interval computation for depth 15, residue 12729. -/
theorem bounds_15_12729 : exactInterval 15 12729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12729 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12729) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12729 : oddCount 12729 15 = 8 ∧ acceleratedOrbit 15 12729 = 2551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12729 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12729) = 3 ^ 8 * m + 2551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12729.1, data_15_12729.2]

/-- Complete interval computation for depth 15, residue 12730. -/
theorem bounds_15_12730 : exactInterval 15 12730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12730 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12730) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12730 : oddCount 12730 15 = 9 ∧ acceleratedOrbit 15 12730 = 7654 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12730 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12730) = 3 ^ 9 * m + 7654 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12730.1, data_15_12730.2]

/-- Complete interval computation for depth 15, residue 12731. -/
theorem bounds_15_12731 : exactInterval 15 12731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12731 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12731) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12731 : oddCount 12731 15 = 10 ∧ acceleratedOrbit 15 12731 = 22949 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12731 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12731) = 3 ^ 10 * m + 22949 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12731.1, data_15_12731.2]

/-- Complete interval computation for depth 15, residue 12732. -/
theorem bounds_15_12732 : exactInterval 15 12732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12732 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12732) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12732 : oddCount 12732 15 = 9 ∧ acceleratedOrbit 15 12732 = 7651 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12732 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12732) = 3 ^ 9 * m + 7651 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12732.1, data_15_12732.2]

/-- Complete interval computation for depth 15, residue 12733. -/
theorem bounds_15_12733 : exactInterval 15 12733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12733 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12733) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12733 : oddCount 12733 15 = 9 ∧ acceleratedOrbit 15 12733 = 7651 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12733 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12733) = 3 ^ 9 * m + 7651 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12733.1, data_15_12733.2]

/-- Complete interval computation for depth 15, residue 12734. -/
theorem bounds_15_12734 : exactInterval 15 12734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12734 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12734) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12734 : oddCount 12734 15 = 9 ∧ acceleratedOrbit 15 12734 = 7651 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12734 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12734) = 3 ^ 9 * m + 7651 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12734.1, data_15_12734.2]

/-- Complete interval computation for depth 15, residue 12735. -/
theorem bounds_15_12735 : exactInterval 15 12735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12735 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12735) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12735 : oddCount 12735 15 = 10 ∧ acceleratedOrbit 15 12735 = 22951 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12735 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12735) = 3 ^ 10 * m + 22951 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12735.1, data_15_12735.2]

/-- Complete interval computation for depth 15, residue 12736. -/
theorem bounds_15_12736 : exactInterval 15 12736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12736 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12736) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12736 : oddCount 12736 15 = 5 ∧ acceleratedOrbit 15 12736 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12736 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12736) = 3 ^ 5 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12736.1, data_15_12736.2]

/-- Complete interval computation for depth 15, residue 12737. -/
theorem bounds_15_12737 : exactInterval 15 12737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12737 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12737) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12737 : oddCount 12737 15 = 10 ∧ acceleratedOrbit 15 12737 = 22963 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12737 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12737) = 3 ^ 10 * m + 22963 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12737.1, data_15_12737.2]

/-- Complete interval computation for depth 15, residue 12738. -/
theorem bounds_15_12738 : exactInterval 15 12738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12738 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12738) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12738 : oddCount 12738 15 = 11 ∧ acceleratedOrbit 15 12738 = 68890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12738 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12738) = 3 ^ 11 * m + 68890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12738.1, data_15_12738.2]

/-- Complete interval computation for depth 15, residue 12739. -/
theorem bounds_15_12739 : exactInterval 15 12739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12739 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12739) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12739 : oddCount 12739 15 = 11 ∧ acceleratedOrbit 15 12739 = 68890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12739 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12739) = 3 ^ 11 * m + 68890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12739.1, data_15_12739.2]

/-- Complete interval computation for depth 15, residue 12740. -/
theorem bounds_15_12740 : exactInterval 15 12740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12740 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12740) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12740 : oddCount 12740 15 = 3 ∧ acceleratedOrbit 15 12740 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12740 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12740) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12740.1, data_15_12740.2]

/-- Complete interval computation for depth 15, residue 12741. -/
theorem bounds_15_12741 : exactInterval 15 12741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12741 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12741) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12741 : oddCount 12741 15 = 3 ∧ acceleratedOrbit 15 12741 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12741 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12741) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12741.1, data_15_12741.2]

/-- Complete interval computation for depth 15, residue 12742. -/
theorem bounds_15_12742 : exactInterval 15 12742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12742 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12742) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12742 : oddCount 12742 15 = 3 ∧ acceleratedOrbit 15 12742 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12742 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12742) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12742.1, data_15_12742.2]

/-- Complete interval computation for depth 15, residue 12743. -/
theorem bounds_15_12743 : exactInterval 15 12743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12743 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12743) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12743 : oddCount 12743 15 = 8 ∧ acceleratedOrbit 15 12743 = 2552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12743 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12743) = 3 ^ 8 * m + 2552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12743.1, data_15_12743.2]

/-- Complete interval computation for depth 15, residue 12744. -/
theorem bounds_15_12744 : exactInterval 15 12744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12744 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12744) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12744 : oddCount 12744 15 = 6 ∧ acceleratedOrbit 15 12744 = 284 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12744 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12744) = 3 ^ 6 * m + 284 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12744.1, data_15_12744.2]

/-- Complete interval computation for depth 15, residue 12745. -/
theorem bounds_15_12745 : exactInterval 15 12745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12745 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12745) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12745 : oddCount 12745 15 = 7 ∧ acceleratedOrbit 15 12745 = 851 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12745 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12745) = 3 ^ 7 * m + 851 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12745.1, data_15_12745.2]

end Collatz.Research.PassageAtlas.Batch0389
