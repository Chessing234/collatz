import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0772

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4674. -/
theorem bounds_13_4674 : exactInterval 13 4674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4674 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4674) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4674 : oddCount 4674 13 = 5 ∧ acceleratedOrbit 13 4674 = 139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4674 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4674) = 3 ^ 5 * m + 139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4674.1, data_13_4674.2]

/-- Complete interval computation for depth 13, residue 4675. -/
theorem bounds_13_4675 : exactInterval 13 4675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4675 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4675) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4675 : oddCount 4675 13 = 5 ∧ acceleratedOrbit 13 4675 = 139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4675 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4675) = 3 ^ 5 * m + 139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4675.1, data_13_4675.2]

/-- Complete interval computation for depth 13, residue 4676. -/
theorem bounds_13_4676 : exactInterval 13 4676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4676 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4676) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4676 : oddCount 4676 13 = 6 ∧ acceleratedOrbit 13 4676 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4676 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4676) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4676.1, data_13_4676.2]

/-- Complete interval computation for depth 13, residue 4677. -/
theorem bounds_13_4677 : exactInterval 13 4677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4677 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4677) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4677 : oddCount 4677 13 = 6 ∧ acceleratedOrbit 13 4677 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4677 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4677) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4677.1, data_13_4677.2]

/-- Complete interval computation for depth 13, residue 4678. -/
theorem bounds_13_4678 : exactInterval 13 4678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4678 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4678) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4678 : oddCount 4678 13 = 6 ∧ acceleratedOrbit 13 4678 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4678 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4678) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4678.1, data_13_4678.2]

/-- Complete interval computation for depth 13, residue 4679. -/
theorem bounds_13_4679 : exactInterval 13 4679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4679 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4679) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4679 : oddCount 4679 13 = 7 ∧ acceleratedOrbit 13 4679 = 1250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4679 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4679) = 3 ^ 7 * m + 1250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4679.1, data_13_4679.2]

/-- Complete interval computation for depth 13, residue 4680. -/
theorem bounds_13_4680 : exactInterval 13 4680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4680 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4680) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4680 : oddCount 4680 13 = 6 ∧ acceleratedOrbit 13 4680 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4680 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4680) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4680.1, data_13_4680.2]

/-- Complete interval computation for depth 13, residue 4681. -/
theorem bounds_13_4681 : exactInterval 13 4681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4681 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4681) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4681 : oddCount 4681 13 = 8 ∧ acceleratedOrbit 13 4681 = 3752 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4681 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4681) = 3 ^ 8 * m + 3752 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4681.1, data_13_4681.2]

/-- Complete interval computation for depth 13, residue 4682. -/
theorem bounds_13_4682 : exactInterval 13 4682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4682 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4682) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4682 : oddCount 4682 13 = 6 ∧ acceleratedOrbit 13 4682 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4682 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4682) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4682.1, data_13_4682.2]

/-- Complete interval computation for depth 13, residue 4683. -/
theorem bounds_13_4683 : exactInterval 13 4683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4683 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4683) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4683 : oddCount 4683 13 = 6 ∧ acceleratedOrbit 13 4683 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4683 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4683) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4683.1, data_13_4683.2]

/-- Complete interval computation for depth 13, residue 4684. -/
theorem bounds_13_4684 : exactInterval 13 4684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4684 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4684) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4684 : oddCount 4684 13 = 6 ∧ acceleratedOrbit 13 4684 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4684 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4684) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4684.1, data_13_4684.2]

/-- Complete interval computation for depth 13, residue 4685. -/
theorem bounds_13_4685 : exactInterval 13 4685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4685 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4685) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4685 : oddCount 4685 13 = 6 ∧ acceleratedOrbit 13 4685 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4685 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4685) = 3 ^ 6 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4685.1, data_13_4685.2]

/-- Complete interval computation for depth 13, residue 4686. -/
theorem bounds_13_4686 : exactInterval 13 4686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4686 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4686) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4686 : oddCount 4686 13 = 7 ∧ acceleratedOrbit 13 4686 = 1252 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4686 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4686) = 3 ^ 7 * m + 1252 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4686.1, data_13_4686.2]

/-- Complete interval computation for depth 13, residue 4687. -/
theorem bounds_13_4687 : exactInterval 13 4687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4687 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4687) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4687 : oddCount 4687 13 = 7 ∧ acceleratedOrbit 13 4687 = 1252 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4687 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4687) = 3 ^ 7 * m + 1252 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4687.1, data_13_4687.2]

/-- Complete interval computation for depth 13, residue 4688. -/
theorem bounds_13_4688 : exactInterval 13 4688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4688 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4688) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4688 : oddCount 4688 13 = 4 ∧ acceleratedOrbit 13 4688 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4688 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4688) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4688.1, data_13_4688.2]

end Collatz.Research.StoppingAtlas.Batch0772
