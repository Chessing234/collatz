import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0565

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 18481. -/
theorem bounds_15_18481 : exactInterval 15 18481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18481 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18481) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18481 : oddCount 18481 15 = 7 ∧ acceleratedOrbit 15 18481 = 1234 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18481 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18481) = 3 ^ 7 * m + 1234 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18481.1, data_15_18481.2]

/-- Complete interval computation for depth 15, residue 18482. -/
theorem bounds_15_18482 : exactInterval 15 18482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18482 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18482) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18482 : oddCount 18482 15 = 7 ∧ acceleratedOrbit 15 18482 = 1234 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18482 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18482) = 3 ^ 7 * m + 1234 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18482.1, data_15_18482.2]

/-- Complete interval computation for depth 15, residue 18483. -/
theorem bounds_15_18483 : exactInterval 15 18483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18483 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18483) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18483 : oddCount 18483 15 = 7 ∧ acceleratedOrbit 15 18483 = 1234 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18483 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18483) = 3 ^ 7 * m + 1234 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18483.1, data_15_18483.2]

/-- Complete interval computation for depth 15, residue 18484. -/
theorem bounds_15_18484 : exactInterval 15 18484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18484 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18484) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18484 : oddCount 18484 15 = 4 ∧ acceleratedOrbit 15 18484 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18484 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18484) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18484.1, data_15_18484.2]

/-- Complete interval computation for depth 15, residue 18485. -/
theorem bounds_15_18485 : exactInterval 15 18485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18485 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18485) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18485 : oddCount 18485 15 = 4 ∧ acceleratedOrbit 15 18485 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18485 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18485) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18485.1, data_15_18485.2]

/-- Complete interval computation for depth 15, residue 18486. -/
theorem bounds_15_18486 : exactInterval 15 18486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18486 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18486) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18486 : oddCount 18486 15 = 12 ∧ acceleratedOrbit 15 18486 = 299861 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18486 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18486) = 3 ^ 12 * m + 299861 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18486.1, data_15_18486.2]

/-- Complete interval computation for depth 15, residue 18487. -/
theorem bounds_15_18487 : exactInterval 15 18487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18487 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18487) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18487 : oddCount 18487 15 = 12 ∧ acceleratedOrbit 15 18487 = 299861 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18487 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18487) = 3 ^ 12 * m + 299861 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18487.1, data_15_18487.2]

/-- Complete interval computation for depth 15, residue 18488. -/
theorem bounds_15_18488 : exactInterval 15 18488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18488 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18488) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18488 : oddCount 18488 15 = 7 ∧ acceleratedOrbit 15 18488 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18488 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18488) = 3 ^ 7 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18488.1, data_15_18488.2]

/-- Complete interval computation for depth 15, residue 18489. -/
theorem bounds_15_18489 : exactInterval 15 18489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18489 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18489) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18489 : oddCount 18489 15 = 7 ∧ acceleratedOrbit 15 18489 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18489 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18489) = 3 ^ 7 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18489.1, data_15_18489.2]

/-- Complete interval computation for depth 15, residue 18490. -/
theorem bounds_15_18490 : exactInterval 15 18490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18490 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18490) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18490 : oddCount 18490 15 = 7 ∧ acceleratedOrbit 15 18490 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18490 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18490) = 3 ^ 7 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18490.1, data_15_18490.2]

/-- Complete interval computation for depth 15, residue 18491. -/
theorem bounds_15_18491 : exactInterval 15 18491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18491 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18491) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18491 : oddCount 18491 15 = 9 ∧ acceleratedOrbit 15 18491 = 11110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18491 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18491) = 3 ^ 9 * m + 11110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18491.1, data_15_18491.2]

/-- Complete interval computation for depth 15, residue 18492. -/
theorem bounds_15_18492 : exactInterval 15 18492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18492 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18492) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18492 : oddCount 18492 15 = 7 ∧ acceleratedOrbit 15 18492 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18492 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18492) = 3 ^ 7 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18492.1, data_15_18492.2]

/-- Complete interval computation for depth 15, residue 18493. -/
theorem bounds_15_18493 : exactInterval 15 18493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18493 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18493) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18493 : oddCount 18493 15 = 7 ∧ acceleratedOrbit 15 18493 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18493 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18493) = 3 ^ 7 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18493.1, data_15_18493.2]

/-- Complete interval computation for depth 15, residue 18494. -/
theorem bounds_15_18494 : exactInterval 15 18494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18494 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18494) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18494 : oddCount 18494 15 = 11 ∧ acceleratedOrbit 15 18494 = 99994 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18494 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18494) = 3 ^ 11 * m + 99994 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18494.1, data_15_18494.2]

/-- Complete interval computation for depth 15, residue 18495. -/
theorem bounds_15_18495 : exactInterval 15 18495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18495 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18495) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18495 : oddCount 18495 15 = 11 ∧ acceleratedOrbit 15 18495 = 99994 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18495 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18495) = 3 ^ 11 * m + 99994 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18495.1, data_15_18495.2]

/-- Complete interval computation for depth 15, residue 18496. -/
theorem bounds_15_18496 : exactInterval 15 18496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18496 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18496) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18496 : oddCount 18496 15 = 4 ∧ acceleratedOrbit 15 18496 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18496 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18496) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18496.1, data_15_18496.2]

/-- Complete interval computation for depth 15, residue 18497. -/
theorem bounds_15_18497 : exactInterval 15 18497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18497 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18497) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18497 : oddCount 18497 15 = 9 ∧ acceleratedOrbit 15 18497 = 11117 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18497 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18497) = 3 ^ 9 * m + 11117 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18497.1, data_15_18497.2]

/-- Complete interval computation for depth 15, residue 18498. -/
theorem bounds_15_18498 : exactInterval 15 18498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18498 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18498) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18498 : oddCount 18498 15 = 9 ∧ acceleratedOrbit 15 18498 = 11117 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18498 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18498) = 3 ^ 9 * m + 11117 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18498.1, data_15_18498.2]

/-- Complete interval computation for depth 15, residue 18499. -/
theorem bounds_15_18499 : exactInterval 15 18499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18499 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18499) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18499 : oddCount 18499 15 = 9 ∧ acceleratedOrbit 15 18499 = 11117 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18499 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18499) = 3 ^ 9 * m + 11117 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18499.1, data_15_18499.2]

/-- Complete interval computation for depth 15, residue 18500. -/
theorem bounds_15_18500 : exactInterval 15 18500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18500 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18500) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18500 : oddCount 18500 15 = 4 ∧ acceleratedOrbit 15 18500 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18500 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18500) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18500.1, data_15_18500.2]

/-- Complete interval computation for depth 15, residue 18501. -/
theorem bounds_15_18501 : exactInterval 15 18501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18501 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18501) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18501 : oddCount 18501 15 = 4 ∧ acceleratedOrbit 15 18501 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18501 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18501) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18501.1, data_15_18501.2]

/-- Complete interval computation for depth 15, residue 18502. -/
theorem bounds_15_18502 : exactInterval 15 18502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18502 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18502) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18502 : oddCount 18502 15 = 4 ∧ acceleratedOrbit 15 18502 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18502 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18502) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18502.1, data_15_18502.2]

/-- Complete interval computation for depth 15, residue 18503. -/
theorem bounds_15_18503 : exactInterval 15 18503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18503 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18503) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18503 : oddCount 18503 15 = 10 ∧ acceleratedOrbit 15 18503 = 33347 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18503 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18503) = 3 ^ 10 * m + 33347 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18503.1, data_15_18503.2]

/-- Complete interval computation for depth 15, residue 18504. -/
theorem bounds_15_18504 : exactInterval 15 18504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18504 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18504) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18504 : oddCount 18504 15 = 6 ∧ acceleratedOrbit 15 18504 = 412 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18504 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18504) = 3 ^ 6 * m + 412 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18504.1, data_15_18504.2]

/-- Complete interval computation for depth 15, residue 18505. -/
theorem bounds_15_18505 : exactInterval 15 18505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18505 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18505) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18505 : oddCount 18505 15 = 11 ∧ acceleratedOrbit 15 18505 = 100055 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18505 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18505) = 3 ^ 11 * m + 100055 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18505.1, data_15_18505.2]

/-- Complete interval computation for depth 15, residue 18506. -/
theorem bounds_15_18506 : exactInterval 15 18506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18506 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18506) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18506 : oddCount 18506 15 = 6 ∧ acceleratedOrbit 15 18506 = 412 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18506 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18506) = 3 ^ 6 * m + 412 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18506.1, data_15_18506.2]

/-- Complete interval computation for depth 15, residue 18507. -/
theorem bounds_15_18507 : exactInterval 15 18507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18507 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18507) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18507 : oddCount 18507 15 = 4 ∧ acceleratedOrbit 15 18507 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18507 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18507) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18507.1, data_15_18507.2]

/-- Complete interval computation for depth 15, residue 18508. -/
theorem bounds_15_18508 : exactInterval 15 18508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18508 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18508) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18508 : oddCount 18508 15 = 6 ∧ acceleratedOrbit 15 18508 = 412 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18508 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18508) = 3 ^ 6 * m + 412 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18508.1, data_15_18508.2]

/-- Complete interval computation for depth 15, residue 18509. -/
theorem bounds_15_18509 : exactInterval 15 18509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18509 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18509) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18509 : oddCount 18509 15 = 6 ∧ acceleratedOrbit 15 18509 = 412 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18509 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18509) = 3 ^ 6 * m + 412 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18509.1, data_15_18509.2]

/-- Complete interval computation for depth 15, residue 18510. -/
theorem bounds_15_18510 : exactInterval 15 18510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18510 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18510) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18510 : oddCount 18510 15 = 9 ∧ acceleratedOrbit 15 18510 = 11123 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18510 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18510) = 3 ^ 9 * m + 11123 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18510.1, data_15_18510.2]

/-- Complete interval computation for depth 15, residue 18511. -/
theorem bounds_15_18511 : exactInterval 15 18511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18511 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18511) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18511 : oddCount 18511 15 = 9 ∧ acceleratedOrbit 15 18511 = 11123 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18511 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18511) = 3 ^ 9 * m + 11123 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18511.1, data_15_18511.2]

/-- Complete interval computation for depth 15, residue 18512. -/
theorem bounds_15_18512 : exactInterval 15 18512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18512 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18512) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18512 : oddCount 18512 15 = 4 ∧ acceleratedOrbit 15 18512 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18512 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18512) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18512.1, data_15_18512.2]

end Collatz.Research.PassageAtlas.Batch0565
