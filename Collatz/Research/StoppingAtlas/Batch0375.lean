import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0375

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2672. -/
theorem bounds_12_2672 : exactInterval 12 2672 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2672 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2672) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2672 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2672 : oddCount 2672 12 = 6 ∧ acceleratedOrbit 12 2672 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2672 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2672) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2672.1, data_12_2672.2]

/-- Complete interval computation for depth 12, residue 2673. -/
theorem bounds_12_2673 : exactInterval 12 2673 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2673 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2673) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2673 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2673 : oddCount 2673 12 = 5 ∧ acceleratedOrbit 12 2673 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2673 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2673) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2673.1, data_12_2673.2]

/-- Complete interval computation for depth 12, residue 2674. -/
theorem bounds_12_2674 : exactInterval 12 2674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2674 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2674) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2674 : oddCount 2674 12 = 8 ∧ acceleratedOrbit 12 2674 = 4292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2674 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2674) = 3 ^ 8 * m + 4292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2674.1, data_12_2674.2]

/-- Complete interval computation for depth 12, residue 2675. -/
theorem bounds_12_2675 : exactInterval 12 2675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2675 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2675) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2675 : oddCount 2675 12 = 8 ∧ acceleratedOrbit 12 2675 = 4292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2675 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2675) = 3 ^ 8 * m + 4292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2675.1, data_12_2675.2]

/-- Complete interval computation for depth 12, residue 2676. -/
theorem bounds_12_2676 : exactInterval 12 2676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2676 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2676) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2676 : oddCount 2676 12 = 6 ∧ acceleratedOrbit 12 2676 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2676 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2676) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2676.1, data_12_2676.2]

/-- Complete interval computation for depth 12, residue 2677. -/
theorem bounds_12_2677 : exactInterval 12 2677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2677 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2677) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2677 : oddCount 2677 12 = 6 ∧ acceleratedOrbit 12 2677 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2677 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2677) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2677.1, data_12_2677.2]

/-- Complete interval computation for depth 12, residue 2678. -/
theorem bounds_12_2678 : exactInterval 12 2678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2678 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2678) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2678 : oddCount 2678 12 = 4 ∧ acceleratedOrbit 12 2678 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2678 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2678) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2678.1, data_12_2678.2]

/-- Complete interval computation for depth 12, residue 2679. -/
theorem bounds_12_2679 : exactInterval 12 2679 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2679 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2679) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2679 : oddCount 2679 12 = 4 ∧ acceleratedOrbit 12 2679 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2679 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2679) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2679.1, data_12_2679.2]

/-- Complete interval computation for depth 12, residue 2680. -/
theorem bounds_12_2680 : exactInterval 12 2680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2680 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2680) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2680 : oddCount 2680 12 = 6 ∧ acceleratedOrbit 12 2680 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2680 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2680) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2680.1, data_12_2680.2]

/-- Complete interval computation for depth 12, residue 2681. -/
theorem bounds_12_2681 : exactInterval 12 2681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2681 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2681) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2681 : oddCount 2681 12 = 7 ∧ acceleratedOrbit 12 2681 = 1433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2681 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2681) = 3 ^ 7 * m + 1433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2681.1, data_12_2681.2]

/-- Complete interval computation for depth 12, residue 2682. -/
theorem bounds_12_2682 : exactInterval 12 2682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2682 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2682) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2682 : oddCount 2682 12 = 6 ∧ acceleratedOrbit 12 2682 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2682 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2682) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2682.1, data_12_2682.2]

/-- Complete interval computation for depth 12, residue 2683. -/
theorem bounds_12_2683 : exactInterval 12 2683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2683 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2683) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2683 : oddCount 2683 12 = 6 ∧ acceleratedOrbit 12 2683 = 478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2683 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2683) = 3 ^ 6 * m + 478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2683.1, data_12_2683.2]

/-- Complete interval computation for depth 12, residue 2684. -/
theorem bounds_12_2684 : exactInterval 12 2684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2684 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2684) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2684 : oddCount 2684 12 = 8 ∧ acceleratedOrbit 12 2684 = 4306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2684 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2684) = 3 ^ 8 * m + 4306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2684.1, data_12_2684.2]

/-- Complete interval computation for depth 12, residue 2685. -/
theorem bounds_12_2685 : exactInterval 12 2685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2685 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2685) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2685 : oddCount 2685 12 = 8 ∧ acceleratedOrbit 12 2685 = 4306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2685 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2685) = 3 ^ 8 * m + 4306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2685.1, data_12_2685.2]

/-- Complete interval computation for depth 12, residue 2686. -/
theorem bounds_12_2686 : exactInterval 12 2686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2686 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2686) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2686 : oddCount 2686 12 = 8 ∧ acceleratedOrbit 12 2686 = 4306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2686 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2686) = 3 ^ 8 * m + 4306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2686.1, data_12_2686.2]

/-- Complete interval computation for depth 12, residue 2687. -/
theorem bounds_12_2687 : exactInterval 12 2687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2687 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2687) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2687 : oddCount 2687 12 = 9 ∧ acceleratedOrbit 12 2687 = 12917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2687 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2687) = 3 ^ 9 * m + 12917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2687.1, data_12_2687.2]

end Collatz.Research.StoppingAtlas.Batch0375
