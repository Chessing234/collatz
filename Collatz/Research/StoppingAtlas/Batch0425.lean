import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0425

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3440. -/
theorem bounds_12_3440 : exactInterval 12 3440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3440 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3440) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3440 : oddCount 3440 12 = 5 ∧ acceleratedOrbit 12 3440 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3440 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3440) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3440.1, data_12_3440.2]

/-- Complete interval computation for depth 12, residue 3441. -/
theorem bounds_12_3441 : exactInterval 12 3441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3441 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3441) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3441 : oddCount 3441 12 = 5 ∧ acceleratedOrbit 12 3441 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3441 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3441) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3441.1, data_12_3441.2]

/-- Complete interval computation for depth 12, residue 3442. -/
theorem bounds_12_3442 : exactInterval 12 3442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3442 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3442) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3442 : oddCount 3442 12 = 6 ∧ acceleratedOrbit 12 3442 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3442 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3442) = 3 ^ 6 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3442.1, data_12_3442.2]

/-- Complete interval computation for depth 12, residue 3443. -/
theorem bounds_12_3443 : exactInterval 12 3443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3443 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3443) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3443 : oddCount 3443 12 = 6 ∧ acceleratedOrbit 12 3443 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3443 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3443) = 3 ^ 6 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3443.1, data_12_3443.2]

/-- Complete interval computation for depth 12, residue 3444. -/
theorem bounds_12_3444 : exactInterval 12 3444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3444 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3444) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3444 : oddCount 3444 12 = 5 ∧ acceleratedOrbit 12 3444 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3444 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3444) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3444.1, data_12_3444.2]

/-- Complete interval computation for depth 12, residue 3445. -/
theorem bounds_12_3445 : exactInterval 12 3445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3445 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3445) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3445 : oddCount 3445 12 = 5 ∧ acceleratedOrbit 12 3445 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3445 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3445) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3445.1, data_12_3445.2]

/-- Complete interval computation for depth 12, residue 3446. -/
theorem bounds_12_3446 : exactInterval 12 3446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3446 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3446) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3446 : oddCount 3446 12 = 6 ∧ acceleratedOrbit 12 3446 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3446 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3446) = 3 ^ 6 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3446.1, data_12_3446.2]

/-- Complete interval computation for depth 12, residue 3447. -/
theorem bounds_12_3447 : exactInterval 12 3447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3447 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3447) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3447 : oddCount 3447 12 = 6 ∧ acceleratedOrbit 12 3447 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3447 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3447) = 3 ^ 6 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3447.1, data_12_3447.2]

/-- Complete interval computation for depth 12, residue 3448. -/
theorem bounds_12_3448 : exactInterval 12 3448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3448 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3448) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3448 : oddCount 3448 12 = 5 ∧ acceleratedOrbit 12 3448 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3448 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3448) = 3 ^ 5 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3448.1, data_12_3448.2]

/-- Complete interval computation for depth 12, residue 3449. -/
theorem bounds_12_3449 : exactInterval 12 3449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3449 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3449) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3449 : oddCount 3449 12 = 8 ∧ acceleratedOrbit 12 3449 = 5528 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3449 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3449) = 3 ^ 8 * m + 5528 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3449.1, data_12_3449.2]

/-- Complete interval computation for depth 12, residue 3450. -/
theorem bounds_12_3450 : exactInterval 12 3450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3450 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3450) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3450 : oddCount 3450 12 = 5 ∧ acceleratedOrbit 12 3450 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3450 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3450) = 3 ^ 5 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3450.1, data_12_3450.2]

/-- Complete interval computation for depth 12, residue 3451. -/
theorem bounds_12_3451 : exactInterval 12 3451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3451 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3451) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3451 : oddCount 3451 12 = 7 ∧ acceleratedOrbit 12 3451 = 1844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3451 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3451) = 3 ^ 7 * m + 1844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3451.1, data_12_3451.2]

/-- Complete interval computation for depth 12, residue 3452. -/
theorem bounds_12_3452 : exactInterval 12 3452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3452 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3452) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3452 : oddCount 3452 12 = 5 ∧ acceleratedOrbit 12 3452 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3452 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3452) = 3 ^ 5 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3452.1, data_12_3452.2]

/-- Complete interval computation for depth 12, residue 3453. -/
theorem bounds_12_3453 : exactInterval 12 3453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3453 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3453) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3453 : oddCount 3453 12 = 5 ∧ acceleratedOrbit 12 3453 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3453 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3453) = 3 ^ 5 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3453.1, data_12_3453.2]

/-- Complete interval computation for depth 12, residue 3454. -/
theorem bounds_12_3454 : exactInterval 12 3454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3454 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3454) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3454 : oddCount 3454 12 = 8 ∧ acceleratedOrbit 12 3454 = 5536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3454 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3454) = 3 ^ 8 * m + 5536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3454.1, data_12_3454.2]

/-- Complete interval computation for depth 12, residue 3455. -/
theorem bounds_12_3455 : exactInterval 12 3455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3455 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3455) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3455 : oddCount 3455 12 = 8 ∧ acceleratedOrbit 12 3455 = 5536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3455 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3455) = 3 ^ 8 * m + 5536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3455.1, data_12_3455.2]

end Collatz.Research.StoppingAtlas.Batch0425
