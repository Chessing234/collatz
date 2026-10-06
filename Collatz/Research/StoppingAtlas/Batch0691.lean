import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0691

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3430. -/
theorem bounds_13_3430 : exactInterval 13 3430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3430 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3430) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3430 : oddCount 3430 13 = 4 ∧ acceleratedOrbit 13 3430 = 34 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3430 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3430) = 3 ^ 4 * m + 34 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3430.1, data_13_3430.2]

/-- Complete interval computation for depth 13, residue 3431. -/
theorem bounds_13_3431 : exactInterval 13 3431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3431 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3431) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3431 : oddCount 3431 13 = 11 ∧ acceleratedOrbit 13 3431 = 74222 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3431 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3431) = 3 ^ 11 * m + 74222 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3431.1, data_13_3431.2]

/-- Complete interval computation for depth 13, residue 3432. -/
theorem bounds_13_3432 : exactInterval 13 3432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3432 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3432) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3432 : oddCount 3432 13 = 5 ∧ acceleratedOrbit 13 3432 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3432 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3432) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3432.1, data_13_3432.2]

/-- Complete interval computation for depth 13, residue 3433. -/
theorem bounds_13_3433 : exactInterval 13 3433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3433 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3433) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3433 : oddCount 3433 13 = 8 ∧ acceleratedOrbit 13 3433 = 2753 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3433 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3433) = 3 ^ 8 * m + 2753 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3433.1, data_13_3433.2]

/-- Complete interval computation for depth 13, residue 3434. -/
theorem bounds_13_3434 : exactInterval 13 3434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3434 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3434) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3434 : oddCount 3434 13 = 5 ∧ acceleratedOrbit 13 3434 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3434 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3434) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3434.1, data_13_3434.2]

/-- Complete interval computation for depth 13, residue 3435. -/
theorem bounds_13_3435 : exactInterval 13 3435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3435 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3435) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3435 : oddCount 3435 13 = 9 ∧ acceleratedOrbit 13 3435 = 8261 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3435 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3435) = 3 ^ 9 * m + 8261 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3435.1, data_13_3435.2]

/-- Complete interval computation for depth 13, residue 3436. -/
theorem bounds_13_3436 : exactInterval 13 3436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3436 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3436) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3436 : oddCount 3436 13 = 7 ∧ acceleratedOrbit 13 3436 = 919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3436 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3436) = 3 ^ 7 * m + 919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3436.1, data_13_3436.2]

/-- Complete interval computation for depth 13, residue 3437. -/
theorem bounds_13_3437 : exactInterval 13 3437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3437 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3437) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3437 : oddCount 3437 13 = 7 ∧ acceleratedOrbit 13 3437 = 919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3437 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3437) = 3 ^ 7 * m + 919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3437.1, data_13_3437.2]

/-- Complete interval computation for depth 13, residue 3438. -/
theorem bounds_13_3438 : exactInterval 13 3438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3438 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3438) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3438 : oddCount 3438 13 = 7 ∧ acceleratedOrbit 13 3438 = 919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3438 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3438) = 3 ^ 7 * m + 919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3438.1, data_13_3438.2]

/-- Complete interval computation for depth 13, residue 3439. -/
theorem bounds_13_3439 : exactInterval 13 3439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3439 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3439) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3439 : oddCount 3439 13 = 8 ∧ acceleratedOrbit 13 3439 = 2756 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3439 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3439) = 3 ^ 8 * m + 2756 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3439.1, data_13_3439.2]

/-- Complete interval computation for depth 13, residue 3440. -/
theorem bounds_13_3440 : exactInterval 13 3440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3440 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3440) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3440 : oddCount 3440 13 = 5 ∧ acceleratedOrbit 13 3440 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3440 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3440) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3440.1, data_13_3440.2]

/-- Complete interval computation for depth 13, residue 3441. -/
theorem bounds_13_3441 : exactInterval 13 3441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3441 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3441) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3441 : oddCount 3441 13 = 5 ∧ acceleratedOrbit 13 3441 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3441 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3441) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3441.1, data_13_3441.2]

/-- Complete interval computation for depth 13, residue 3442. -/
theorem bounds_13_3442 : exactInterval 13 3442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3442 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3442) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3442 : oddCount 3442 13 = 6 ∧ acceleratedOrbit 13 3442 = 307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3442 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3442) = 3 ^ 6 * m + 307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3442.1, data_13_3442.2]

/-- Complete interval computation for depth 13, residue 3443. -/
theorem bounds_13_3443 : exactInterval 13 3443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3443 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3443) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3443 : oddCount 3443 13 = 6 ∧ acceleratedOrbit 13 3443 = 307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3443 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3443) = 3 ^ 6 * m + 307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3443.1, data_13_3443.2]

/-- Complete interval computation for depth 13, residue 3444. -/
theorem bounds_13_3444 : exactInterval 13 3444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3444 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3444) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3444 : oddCount 3444 13 = 5 ∧ acceleratedOrbit 13 3444 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3444 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3444) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3444.1, data_13_3444.2]

end Collatz.Research.StoppingAtlas.Batch0691
