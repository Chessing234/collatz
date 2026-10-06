import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0230

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 445. -/
theorem bounds_12_445 : exactInterval 12 445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_445 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 445) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_445 : oddCount 445 12 = 8 ∧ acceleratedOrbit 12 445 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_445 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 445) = 3 ^ 8 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_445.1, data_12_445.2]

/-- Complete interval computation for depth 12, residue 446. -/
theorem bounds_12_446 : exactInterval 12 446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_446 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 446) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_446 : oddCount 446 12 = 8 ∧ acceleratedOrbit 12 446 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_446 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 446) = 3 ^ 8 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_446.1, data_12_446.2]

/-- Complete interval computation for depth 12, residue 447. -/
theorem bounds_12_447 : exactInterval 12 447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_447 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 447) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_447 : oddCount 447 12 = 9 ∧ acceleratedOrbit 12 447 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_447 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 447) = 3 ^ 9 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_447.1, data_12_447.2]

/-- Complete interval computation for depth 12, residue 448. -/
theorem bounds_12_448 : exactInterval 12 448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_448 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 448) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_448 : oddCount 448 12 = 4 ∧ acceleratedOrbit 12 448 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_448 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 448) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_448.1, data_12_448.2]

/-- Complete interval computation for depth 12, residue 449. -/
theorem bounds_12_449 : exactInterval 12 449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_449 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 449) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_449 : oddCount 449 12 = 8 ∧ acceleratedOrbit 12 449 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_449 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 449) = 3 ^ 8 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_449.1, data_12_449.2]

/-- Complete interval computation for depth 12, residue 450. -/
theorem bounds_12_450 : exactInterval 12 450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_450 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 450) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_450 : oddCount 450 12 = 9 ∧ acceleratedOrbit 12 450 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_450 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 450) = 3 ^ 9 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_450.1, data_12_450.2]

/-- Complete interval computation for depth 12, residue 451. -/
theorem bounds_12_451 : exactInterval 12 451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_451 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 451) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_451 : oddCount 451 12 = 9 ∧ acceleratedOrbit 12 451 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_451 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 451) = 3 ^ 9 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_451.1, data_12_451.2]

/-- Complete interval computation for depth 12, residue 452. -/
theorem bounds_12_452 : exactInterval 12 452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_452 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 452) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_452 : oddCount 452 12 = 2 ∧ acceleratedOrbit 12 452 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_452 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 452) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_452.1, data_12_452.2]

/-- Complete interval computation for depth 12, residue 453. -/
theorem bounds_12_453 : exactInterval 12 453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_453 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 453) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_453 : oddCount 453 12 = 2 ∧ acceleratedOrbit 12 453 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_453 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 453) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_453.1, data_12_453.2]

/-- Complete interval computation for depth 12, residue 454. -/
theorem bounds_12_454 : exactInterval 12 454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_454 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 454) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_454 : oddCount 454 12 = 2 ∧ acceleratedOrbit 12 454 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_454 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 454) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_454.1, data_12_454.2]

/-- Complete interval computation for depth 12, residue 455. -/
theorem bounds_12_455 : exactInterval 12 455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_455 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 455) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_455 : oddCount 455 12 = 7 ∧ acceleratedOrbit 12 455 = 244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_455 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 455) = 3 ^ 7 * m + 244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_455.1, data_12_455.2]

/-- Complete interval computation for depth 12, residue 456. -/
theorem bounds_12_456 : exactInterval 12 456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_456 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 456) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_456 : oddCount 456 12 = 5 ∧ acceleratedOrbit 12 456 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_456 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 456) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_456.1, data_12_456.2]

/-- Complete interval computation for depth 12, residue 457. -/
theorem bounds_12_457 : exactInterval 12 457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_457 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 457) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_457 : oddCount 457 12 = 6 ∧ acceleratedOrbit 12 457 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_457 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 457) = 3 ^ 6 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_457.1, data_12_457.2]

/-- Complete interval computation for depth 12, residue 458. -/
theorem bounds_12_458 : exactInterval 12 458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_458 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 458) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_458 : oddCount 458 12 = 5 ∧ acceleratedOrbit 12 458 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_458 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 458) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_458.1, data_12_458.2]

/-- Complete interval computation for depth 12, residue 459. -/
theorem bounds_12_459 : exactInterval 12 459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_459 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 459) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_459 : oddCount 459 12 = 6 ∧ acceleratedOrbit 12 459 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_459 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 459) = 3 ^ 6 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_459.1, data_12_459.2]

end Collatz.Research.StoppingAtlas.Batch0230
