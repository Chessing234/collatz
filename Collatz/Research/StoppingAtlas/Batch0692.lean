import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0692

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3445. -/
theorem bounds_13_3445 : exactInterval 13 3445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3445 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3445) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3445 : oddCount 3445 13 = 5 ∧ acceleratedOrbit 13 3445 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3445 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3445) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3445.1, data_13_3445.2]

/-- Complete interval computation for depth 13, residue 3446. -/
theorem bounds_13_3446 : exactInterval 13 3446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3446 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3446) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3446 : oddCount 3446 13 = 6 ∧ acceleratedOrbit 13 3446 = 307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3446 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3446) = 3 ^ 6 * m + 307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3446.1, data_13_3446.2]

/-- Complete interval computation for depth 13, residue 3447. -/
theorem bounds_13_3447 : exactInterval 13 3447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3447 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3447) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3447 : oddCount 3447 13 = 6 ∧ acceleratedOrbit 13 3447 = 307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3447 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3447) = 3 ^ 6 * m + 307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3447.1, data_13_3447.2]

/-- Complete interval computation for depth 13, residue 3448. -/
theorem bounds_13_3448 : exactInterval 13 3448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3448 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3448) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3448 : oddCount 3448 13 = 6 ∧ acceleratedOrbit 13 3448 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3448 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3448) = 3 ^ 6 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3448.1, data_13_3448.2]

/-- Complete interval computation for depth 13, residue 3449. -/
theorem bounds_13_3449 : exactInterval 13 3449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3449 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3449) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3449 : oddCount 3449 13 = 8 ∧ acceleratedOrbit 13 3449 = 2764 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3449 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3449) = 3 ^ 8 * m + 2764 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3449.1, data_13_3449.2]

/-- Complete interval computation for depth 13, residue 3450. -/
theorem bounds_13_3450 : exactInterval 13 3450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3450 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3450) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3450 : oddCount 3450 13 = 6 ∧ acceleratedOrbit 13 3450 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3450 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3450) = 3 ^ 6 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3450.1, data_13_3450.2]

/-- Complete interval computation for depth 13, residue 3451. -/
theorem bounds_13_3451 : exactInterval 13 3451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3451 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3451) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3451 : oddCount 3451 13 = 7 ∧ acceleratedOrbit 13 3451 = 922 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3451 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3451) = 3 ^ 7 * m + 922 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3451.1, data_13_3451.2]

/-- Complete interval computation for depth 13, residue 3452. -/
theorem bounds_13_3452 : exactInterval 13 3452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3452 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3452) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3452 : oddCount 3452 13 = 6 ∧ acceleratedOrbit 13 3452 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3452 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3452) = 3 ^ 6 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3452.1, data_13_3452.2]

/-- Complete interval computation for depth 13, residue 3453. -/
theorem bounds_13_3453 : exactInterval 13 3453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3453 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3453) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3453 : oddCount 3453 13 = 6 ∧ acceleratedOrbit 13 3453 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3453 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3453) = 3 ^ 6 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3453.1, data_13_3453.2]

/-- Complete interval computation for depth 13, residue 3454. -/
theorem bounds_13_3454 : exactInterval 13 3454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3454 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3454) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3454 : oddCount 3454 13 = 8 ∧ acceleratedOrbit 13 3454 = 2768 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3454 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3454) = 3 ^ 8 * m + 2768 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3454.1, data_13_3454.2]

/-- Complete interval computation for depth 13, residue 3455. -/
theorem bounds_13_3455 : exactInterval 13 3455 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3455 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3455) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3455 : oddCount 3455 13 = 8 ∧ acceleratedOrbit 13 3455 = 2768 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3455 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3455) = 3 ^ 8 * m + 2768 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3455.1, data_13_3455.2]

/-- Complete interval computation for depth 13, residue 3456. -/
theorem bounds_13_3456 : exactInterval 13 3456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3456 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3456) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3456 : oddCount 3456 13 = 5 ∧ acceleratedOrbit 13 3456 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3456 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3456) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3456.1, data_13_3456.2]

/-- Complete interval computation for depth 13, residue 3457. -/
theorem bounds_13_3457 : exactInterval 13 3457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3457 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3457) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3457 : oddCount 3457 13 = 6 ∧ acceleratedOrbit 13 3457 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3457 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3457) = 3 ^ 6 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3457.1, data_13_3457.2]

/-- Complete interval computation for depth 13, residue 3458. -/
theorem bounds_13_3458 : exactInterval 13 3458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3458 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3458) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3458 : oddCount 3458 13 = 5 ∧ acceleratedOrbit 13 3458 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3458 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3458) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3458.1, data_13_3458.2]

/-- Complete interval computation for depth 13, residue 3459. -/
theorem bounds_13_3459 : exactInterval 13 3459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3459 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3459) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3459 : oddCount 3459 13 = 5 ∧ acceleratedOrbit 13 3459 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3459 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3459) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3459.1, data_13_3459.2]

/-- Complete interval computation for depth 13, residue 3460. -/
theorem bounds_13_3460 : exactInterval 13 3460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3460 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3460) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3460 : oddCount 3460 13 = 8 ∧ acceleratedOrbit 13 3460 = 2780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3460 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3460) = 3 ^ 8 * m + 2780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3460.1, data_13_3460.2]

end Collatz.Research.StoppingAtlas.Batch0692
