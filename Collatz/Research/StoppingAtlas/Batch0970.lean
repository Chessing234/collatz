import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0970

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7715. -/
theorem bounds_13_7715 : exactInterval 13 7715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7715 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7715) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7715 : oddCount 7715 13 = 6 ∧ acceleratedOrbit 13 7715 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7715 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7715) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7715.1, data_13_7715.2]

/-- Complete interval computation for depth 13, residue 7716. -/
theorem bounds_13_7716 : exactInterval 13 7716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7716 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7716) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7716 : oddCount 7716 13 = 7 ∧ acceleratedOrbit 13 7716 = 2062 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7716 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7716) = 3 ^ 7 * m + 2062 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7716.1, data_13_7716.2]

/-- Complete interval computation for depth 13, residue 7717. -/
theorem bounds_13_7717 : exactInterval 13 7717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7717 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7717) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7717 : oddCount 7717 13 = 7 ∧ acceleratedOrbit 13 7717 = 2062 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7717 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7717) = 3 ^ 7 * m + 2062 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7717.1, data_13_7717.2]

/-- Complete interval computation for depth 13, residue 7718. -/
theorem bounds_13_7718 : exactInterval 13 7718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7718 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7718) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7718 : oddCount 7718 13 = 7 ∧ acceleratedOrbit 13 7718 = 2062 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7718 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7718) = 3 ^ 7 * m + 2062 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7718.1, data_13_7718.2]

/-- Complete interval computation for depth 13, residue 7719. -/
theorem bounds_13_7719 : exactInterval 13 7719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7719 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7719) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7719 : oddCount 7719 13 = 5 ∧ acceleratedOrbit 13 7719 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7719 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7719) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7719.1, data_13_7719.2]

/-- Complete interval computation for depth 13, residue 7720. -/
theorem bounds_13_7720 : exactInterval 13 7720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7720 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7720) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7720 : oddCount 7720 13 = 3 ∧ acceleratedOrbit 13 7720 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7720 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7720) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7720.1, data_13_7720.2]

/-- Complete interval computation for depth 13, residue 7721. -/
theorem bounds_13_7721 : exactInterval 13 7721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7721 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7721) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7721 : oddCount 7721 13 = 10 ∧ acceleratedOrbit 13 7721 = 55667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7721 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7721) = 3 ^ 10 * m + 55667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7721.1, data_13_7721.2]

/-- Complete interval computation for depth 13, residue 7722. -/
theorem bounds_13_7722 : exactInterval 13 7722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7722 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7722) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7722 : oddCount 7722 13 = 3 ∧ acceleratedOrbit 13 7722 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7722 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7722) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7722.1, data_13_7722.2]

/-- Complete interval computation for depth 13, residue 7723. -/
theorem bounds_13_7723 : exactInterval 13 7723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7723 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7723) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7723 : oddCount 7723 13 = 6 ∧ acceleratedOrbit 13 7723 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7723 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7723) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7723.1, data_13_7723.2]

/-- Complete interval computation for depth 13, residue 7724. -/
theorem bounds_13_7724 : exactInterval 13 7724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7724 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7724) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7724 : oddCount 7724 13 = 7 ∧ acceleratedOrbit 13 7724 = 2065 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7724 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7724) = 3 ^ 7 * m + 2065 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7724.1, data_13_7724.2]

/-- Complete interval computation for depth 13, residue 7725. -/
theorem bounds_13_7725 : exactInterval 13 7725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7725 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7725) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7725 : oddCount 7725 13 = 7 ∧ acceleratedOrbit 13 7725 = 2065 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7725 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7725) = 3 ^ 7 * m + 2065 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7725.1, data_13_7725.2]

/-- Complete interval computation for depth 13, residue 7726. -/
theorem bounds_13_7726 : exactInterval 13 7726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7726 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7726) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7726 : oddCount 7726 13 = 7 ∧ acceleratedOrbit 13 7726 = 2065 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7726 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7726) = 3 ^ 7 * m + 2065 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7726.1, data_13_7726.2]

/-- Complete interval computation for depth 13, residue 7727. -/
theorem bounds_13_7727 : exactInterval 13 7727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7727 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7727) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7727 : oddCount 7727 13 = 9 ∧ acceleratedOrbit 13 7727 = 18569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7727 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7727) = 3 ^ 9 * m + 18569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7727.1, data_13_7727.2]

/-- Complete interval computation for depth 13, residue 7728. -/
theorem bounds_13_7728 : exactInterval 13 7728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7728 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7728) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7728 : oddCount 7728 13 = 3 ∧ acceleratedOrbit 13 7728 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7728 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7728) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7728.1, data_13_7728.2]

/-- Complete interval computation for depth 13, residue 7729. -/
theorem bounds_13_7729 : exactInterval 13 7729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7729 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7729) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7729 : oddCount 7729 13 = 8 ∧ acceleratedOrbit 13 7729 = 6196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7729 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7729) = 3 ^ 8 * m + 6196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7729.1, data_13_7729.2]

/-- Complete interval computation for depth 13, residue 7730. -/
theorem bounds_13_7730 : exactInterval 13 7730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7730 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7730) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7730 : oddCount 7730 13 = 8 ∧ acceleratedOrbit 13 7730 = 6196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7730 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7730) = 3 ^ 8 * m + 6196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7730.1, data_13_7730.2]

end Collatz.Research.StoppingAtlas.Batch0970
