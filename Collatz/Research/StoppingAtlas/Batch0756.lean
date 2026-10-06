import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0756

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4428. -/
theorem bounds_13_4428 : exactInterval 13 4428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4428 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4428) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4428 : oddCount 4428 13 = 8 ∧ acceleratedOrbit 13 4428 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4428 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4428) = 3 ^ 8 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4428.1, data_13_4428.2]

/-- Complete interval computation for depth 13, residue 4429. -/
theorem bounds_13_4429 : exactInterval 13 4429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4429 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4429) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4429 : oddCount 4429 13 = 8 ∧ acceleratedOrbit 13 4429 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4429 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4429) = 3 ^ 8 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4429.1, data_13_4429.2]

/-- Complete interval computation for depth 13, residue 4430. -/
theorem bounds_13_4430 : exactInterval 13 4430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4430 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4430) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4430 : oddCount 4430 13 = 9 ∧ acceleratedOrbit 13 4430 = 10651 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4430 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4430) = 3 ^ 9 * m + 10651 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4430.1, data_13_4430.2]

/-- Complete interval computation for depth 13, residue 4431. -/
theorem bounds_13_4431 : exactInterval 13 4431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4431 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4431) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4431 : oddCount 4431 13 = 9 ∧ acceleratedOrbit 13 4431 = 10651 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4431 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4431) = 3 ^ 9 * m + 10651 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4431.1, data_13_4431.2]

/-- Complete interval computation for depth 13, residue 4432. -/
theorem bounds_13_4432 : exactInterval 13 4432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4432 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4432) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4432 : oddCount 4432 13 = 2 ∧ acceleratedOrbit 13 4432 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4432 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4432) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4432.1, data_13_4432.2]

/-- Complete interval computation for depth 13, residue 4433. -/
theorem bounds_13_4433 : exactInterval 13 4433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4433 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4433) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4433 : oddCount 4433 13 = 8 ∧ acceleratedOrbit 13 4433 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4433 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4433) = 3 ^ 8 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4433.1, data_13_4433.2]

/-- Complete interval computation for depth 13, residue 4434. -/
theorem bounds_13_4434 : exactInterval 13 4434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4434 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4434) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4434 : oddCount 4434 13 = 10 ∧ acceleratedOrbit 13 4434 = 31985 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4434 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4434) = 3 ^ 10 * m + 31985 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4434.1, data_13_4434.2]

/-- Complete interval computation for depth 13, residue 4435. -/
theorem bounds_13_4435 : exactInterval 13 4435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4435 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4435) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4435 : oddCount 4435 13 = 10 ∧ acceleratedOrbit 13 4435 = 31985 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4435 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4435) = 3 ^ 10 * m + 31985 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4435.1, data_13_4435.2]

/-- Complete interval computation for depth 13, residue 4436. -/
theorem bounds_13_4436 : exactInterval 13 4436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4436 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4436) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4436 : oddCount 4436 13 = 2 ∧ acceleratedOrbit 13 4436 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4436 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4436) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4436.1, data_13_4436.2]

/-- Complete interval computation for depth 13, residue 4437. -/
theorem bounds_13_4437 : exactInterval 13 4437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4437 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4437) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4437 : oddCount 4437 13 = 2 ∧ acceleratedOrbit 13 4437 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4437 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4437) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4437.1, data_13_4437.2]

/-- Complete interval computation for depth 13, residue 4438. -/
theorem bounds_13_4438 : exactInterval 13 4438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4438 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4438) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4438 : oddCount 4438 13 = 7 ∧ acceleratedOrbit 13 4438 = 1187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4438 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4438) = 3 ^ 7 * m + 1187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4438.1, data_13_4438.2]

/-- Complete interval computation for depth 13, residue 4439. -/
theorem bounds_13_4439 : exactInterval 13 4439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4439 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4439) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4439 : oddCount 4439 13 = 7 ∧ acceleratedOrbit 13 4439 = 1187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4439 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4439) = 3 ^ 7 * m + 1187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4439.1, data_13_4439.2]

/-- Complete interval computation for depth 13, residue 4440. -/
theorem bounds_13_4440 : exactInterval 13 4440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4440 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4440) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4440 : oddCount 4440 13 = 4 ∧ acceleratedOrbit 13 4440 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4440 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4440) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4440.1, data_13_4440.2]

/-- Complete interval computation for depth 13, residue 4441. -/
theorem bounds_13_4441 : exactInterval 13 4441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4441 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4441) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4441 : oddCount 4441 13 = 8 ∧ acceleratedOrbit 13 4441 = 3563 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4441 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4441) = 3 ^ 8 * m + 3563 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4441.1, data_13_4441.2]

/-- Complete interval computation for depth 13, residue 4442. -/
theorem bounds_13_4442 : exactInterval 13 4442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4442 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4442) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4442 : oddCount 4442 13 = 4 ∧ acceleratedOrbit 13 4442 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4442 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4442) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4442.1, data_13_4442.2]

/-- Complete interval computation for depth 13, residue 4443. -/
theorem bounds_13_4443 : exactInterval 13 4443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4443 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4443) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4443 : oddCount 4443 13 = 7 ∧ acceleratedOrbit 13 4443 = 1187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4443 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4443) = 3 ^ 7 * m + 1187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4443.1, data_13_4443.2]

end Collatz.Research.StoppingAtlas.Batch0756
