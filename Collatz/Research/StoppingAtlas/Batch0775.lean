import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0775

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4720. -/
theorem bounds_13_4720 : exactInterval 13 4720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4720 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4720) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4720 : oddCount 4720 13 = 6 ∧ acceleratedOrbit 13 4720 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4720 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4720) = 3 ^ 6 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4720.1, data_13_4720.2]

/-- Complete interval computation for depth 13, residue 4721. -/
theorem bounds_13_4721 : exactInterval 13 4721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4721 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4721) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4721 : oddCount 4721 13 = 4 ∧ acceleratedOrbit 13 4721 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4721 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4721) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4721.1, data_13_4721.2]

/-- Complete interval computation for depth 13, residue 4722. -/
theorem bounds_13_4722 : exactInterval 13 4722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4722 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4722) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4722 : oddCount 4722 13 = 7 ∧ acceleratedOrbit 13 4722 = 1262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4722 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4722) = 3 ^ 7 * m + 1262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4722.1, data_13_4722.2]

/-- Complete interval computation for depth 13, residue 4723. -/
theorem bounds_13_4723 : exactInterval 13 4723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4723 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4723) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4723 : oddCount 4723 13 = 7 ∧ acceleratedOrbit 13 4723 = 1262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4723 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4723) = 3 ^ 7 * m + 1262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4723.1, data_13_4723.2]

/-- Complete interval computation for depth 13, residue 4724. -/
theorem bounds_13_4724 : exactInterval 13 4724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4724 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4724) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4724 : oddCount 4724 13 = 6 ∧ acceleratedOrbit 13 4724 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4724 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4724) = 3 ^ 6 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4724.1, data_13_4724.2]

/-- Complete interval computation for depth 13, residue 4725. -/
theorem bounds_13_4725 : exactInterval 13 4725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4725 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4725) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4725 : oddCount 4725 13 = 6 ∧ acceleratedOrbit 13 4725 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4725 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4725) = 3 ^ 6 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4725.1, data_13_4725.2]

/-- Complete interval computation for depth 13, residue 4726. -/
theorem bounds_13_4726 : exactInterval 13 4726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4726 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4726) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4726 : oddCount 4726 13 = 6 ∧ acceleratedOrbit 13 4726 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4726 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4726) = 3 ^ 6 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4726.1, data_13_4726.2]

/-- Complete interval computation for depth 13, residue 4727. -/
theorem bounds_13_4727 : exactInterval 13 4727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4727 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4727) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4727 : oddCount 4727 13 = 6 ∧ acceleratedOrbit 13 4727 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4727 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4727) = 3 ^ 6 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4727.1, data_13_4727.2]

/-- Complete interval computation for depth 13, residue 4728. -/
theorem bounds_13_4728 : exactInterval 13 4728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4728 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4728) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4728 : oddCount 4728 13 = 6 ∧ acceleratedOrbit 13 4728 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4728 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4728) = 3 ^ 6 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4728.1, data_13_4728.2]

/-- Complete interval computation for depth 13, residue 4729. -/
theorem bounds_13_4729 : exactInterval 13 4729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4729 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4729) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4729 : oddCount 4729 13 = 6 ∧ acceleratedOrbit 13 4729 = 421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4729 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4729) = 3 ^ 6 * m + 421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4729.1, data_13_4729.2]

/-- Complete interval computation for depth 13, residue 4730. -/
theorem bounds_13_4730 : exactInterval 13 4730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4730 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4730) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4730 : oddCount 4730 13 = 6 ∧ acceleratedOrbit 13 4730 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4730 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4730) = 3 ^ 6 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4730.1, data_13_4730.2]

/-- Complete interval computation for depth 13, residue 4731. -/
theorem bounds_13_4731 : exactInterval 13 4731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4731 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4731) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4731 : oddCount 4731 13 = 7 ∧ acceleratedOrbit 13 4731 = 1264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4731 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4731) = 3 ^ 7 * m + 1264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4731.1, data_13_4731.2]

/-- Complete interval computation for depth 13, residue 4732. -/
theorem bounds_13_4732 : exactInterval 13 4732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4732 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4732) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4732 : oddCount 4732 13 = 9 ∧ acceleratedOrbit 13 4732 = 11380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4732 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4732) = 3 ^ 9 * m + 11380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4732.1, data_13_4732.2]

/-- Complete interval computation for depth 13, residue 4733. -/
theorem bounds_13_4733 : exactInterval 13 4733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4733 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4733) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4733 : oddCount 4733 13 = 9 ∧ acceleratedOrbit 13 4733 = 11380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4733 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4733) = 3 ^ 9 * m + 11380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4733.1, data_13_4733.2]

/-- Complete interval computation for depth 13, residue 4734. -/
theorem bounds_13_4734 : exactInterval 13 4734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4734 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4734) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4734 : oddCount 4734 13 = 9 ∧ acceleratedOrbit 13 4734 = 11380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4734 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4734) = 3 ^ 9 * m + 11380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4734.1, data_13_4734.2]

/-- Complete interval computation for depth 13, residue 4735. -/
theorem bounds_13_4735 : exactInterval 13 4735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4735 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4735) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4735 : oddCount 4735 13 = 10 ∧ acceleratedOrbit 13 4735 = 34138 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4735 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4735) = 3 ^ 10 * m + 34138 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4735.1, data_13_4735.2]

end Collatz.Research.StoppingAtlas.Batch0775
