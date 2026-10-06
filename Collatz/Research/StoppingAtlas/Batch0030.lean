import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0030

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 445. -/
theorem bounds_10_445 : exactInterval 10 445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_445 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 445) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_445 : oddCount 445 10 = 6 ∧ acceleratedOrbit 10 445 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_445 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 445) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_445.1, data_10_445.2]

/-- Complete interval computation for depth 10, residue 446. -/
theorem bounds_10_446 : exactInterval 10 446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_446 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 446) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_446 : oddCount 446 10 = 6 ∧ acceleratedOrbit 10 446 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_446 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 446) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_446.1, data_10_446.2]

/-- Complete interval computation for depth 10, residue 447. -/
theorem bounds_10_447 : exactInterval 10 447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_447 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 447) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_447 : oddCount 447 10 = 9 ∧ acceleratedOrbit 10 447 = 8612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_447 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 447) = 3 ^ 9 * m + 8612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_447.1, data_10_447.2]

/-- Complete interval computation for depth 10, residue 448. -/
theorem bounds_10_448 : exactInterval 10 448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_448 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 448) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_448 : oddCount 448 10 = 3 ∧ acceleratedOrbit 10 448 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_448 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 448) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_448.1, data_10_448.2]

/-- Complete interval computation for depth 10, residue 449. -/
theorem bounds_10_449 : exactInterval 10 449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_449 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 449) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_449 : oddCount 449 10 = 6 ∧ acceleratedOrbit 10 449 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_449 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 449) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_449.1, data_10_449.2]

/-- Complete interval computation for depth 10, residue 450. -/
theorem bounds_10_450 : exactInterval 10 450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_450 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 450) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_450 : oddCount 450 10 = 7 ∧ acceleratedOrbit 10 450 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_450 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 450) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_450.1, data_10_450.2]

/-- Complete interval computation for depth 10, residue 451. -/
theorem bounds_10_451 : exactInterval 10 451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_451 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 451) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_451 : oddCount 451 10 = 7 ∧ acceleratedOrbit 10 451 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_451 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 451) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_451.1, data_10_451.2]

/-- Complete interval computation for depth 10, residue 452. -/
theorem bounds_10_452 : exactInterval 10 452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_452 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 452) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_452 : oddCount 452 10 = 2 ∧ acceleratedOrbit 10 452 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_452 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 452) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_452.1, data_10_452.2]

/-- Complete interval computation for depth 10, residue 453. -/
theorem bounds_10_453 : exactInterval 10 453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_453 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 453) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_453 : oddCount 453 10 = 2 ∧ acceleratedOrbit 10 453 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_453 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 453) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_453.1, data_10_453.2]

/-- Complete interval computation for depth 10, residue 454. -/
theorem bounds_10_454 : exactInterval 10 454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_454 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 454) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_454 : oddCount 454 10 = 2 ∧ acceleratedOrbit 10 454 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_454 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 454) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_454.1, data_10_454.2]

/-- Complete interval computation for depth 10, residue 455. -/
theorem bounds_10_455 : exactInterval 10 455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_455 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 455) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_455 : oddCount 455 10 = 6 ∧ acceleratedOrbit 10 455 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_455 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 455) = 3 ^ 6 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_455.1, data_10_455.2]

/-- Complete interval computation for depth 10, residue 456. -/
theorem bounds_10_456 : exactInterval 10 456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_456 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 456) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_456 : oddCount 456 10 = 4 ∧ acceleratedOrbit 10 456 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_456 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 456) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_456.1, data_10_456.2]

/-- Complete interval computation for depth 10, residue 457. -/
theorem bounds_10_457 : exactInterval 10 457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_457 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 457) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_457 : oddCount 457 10 = 5 ∧ acceleratedOrbit 10 457 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_457 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 457) = 3 ^ 5 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_457.1, data_10_457.2]

/-- Complete interval computation for depth 10, residue 458. -/
theorem bounds_10_458 : exactInterval 10 458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_458 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 458) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_458 : oddCount 458 10 = 4 ∧ acceleratedOrbit 10 458 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_458 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 458) = 3 ^ 4 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_458.1, data_10_458.2]

/-- Complete interval computation for depth 10, residue 459. -/
theorem bounds_10_459 : exactInterval 10 459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_459 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 459) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_459 : oddCount 459 10 = 5 ∧ acceleratedOrbit 10 459 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_459 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 459) = 3 ^ 5 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_459.1, data_10_459.2]

end Collatz.Research.StoppingAtlas.Batch0030
