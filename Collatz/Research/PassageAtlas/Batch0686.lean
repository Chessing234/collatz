import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0686

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 22446. -/
theorem bounds_15_22446 : exactInterval 15 22446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22446 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22446) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22446 : oddCount 22446 15 = 10 ∧ acceleratedOrbit 15 22446 = 40459 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22446 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22446) = 3 ^ 10 * m + 40459 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22446.1, data_15_22446.2]

/-- Complete interval computation for depth 15, residue 22447. -/
theorem bounds_15_22447 : exactInterval 15 22447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22447 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22447) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22447 : oddCount 22447 15 = 9 ∧ acceleratedOrbit 15 22447 = 13486 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22447 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22447) = 3 ^ 9 * m + 13486 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22447.1, data_15_22447.2]

/-- Complete interval computation for depth 15, residue 22448. -/
theorem bounds_15_22448 : exactInterval 15 22448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22448 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22448) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22448 : oddCount 22448 15 = 6 ∧ acceleratedOrbit 15 22448 = 500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22448 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22448) = 3 ^ 6 * m + 500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22448.1, data_15_22448.2]

/-- Complete interval computation for depth 15, residue 22449. -/
theorem bounds_15_22449 : exactInterval 15 22449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22449 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22449) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22449 : oddCount 22449 15 = 4 ∧ acceleratedOrbit 15 22449 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22449 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22449) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22449.1, data_15_22449.2]

/-- Complete interval computation for depth 15, residue 22450. -/
theorem bounds_15_22450 : exactInterval 15 22450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22450 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22450) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22450 : oddCount 22450 15 = 4 ∧ acceleratedOrbit 15 22450 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22450 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22450) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22450.1, data_15_22450.2]

/-- Complete interval computation for depth 15, residue 22451. -/
theorem bounds_15_22451 : exactInterval 15 22451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22451 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22451) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22451 : oddCount 22451 15 = 4 ∧ acceleratedOrbit 15 22451 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22451 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22451) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22451.1, data_15_22451.2]

/-- Complete interval computation for depth 15, residue 22452. -/
theorem bounds_15_22452 : exactInterval 15 22452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22452 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22452) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22452 : oddCount 22452 15 = 6 ∧ acceleratedOrbit 15 22452 = 500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22452 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22452) = 3 ^ 6 * m + 500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22452.1, data_15_22452.2]

/-- Complete interval computation for depth 15, residue 22453. -/
theorem bounds_15_22453 : exactInterval 15 22453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22453 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22453) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22453 : oddCount 22453 15 = 6 ∧ acceleratedOrbit 15 22453 = 500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22453 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22453) = 3 ^ 6 * m + 500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22453.1, data_15_22453.2]

/-- Complete interval computation for depth 15, residue 22454. -/
theorem bounds_15_22454 : exactInterval 15 22454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22454 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22454) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22454 : oddCount 22454 15 = 7 ∧ acceleratedOrbit 15 22454 = 1499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22454 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22454) = 3 ^ 7 * m + 1499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22454.1, data_15_22454.2]

/-- Complete interval computation for depth 15, residue 22455. -/
theorem bounds_15_22455 : exactInterval 15 22455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22455 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22455) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22455 : oddCount 22455 15 = 7 ∧ acceleratedOrbit 15 22455 = 1499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22455 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22455) = 3 ^ 7 * m + 1499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22455.1, data_15_22455.2]

/-- Complete interval computation for depth 15, residue 22456. -/
theorem bounds_15_22456 : exactInterval 15 22456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22456 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22456) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22456 : oddCount 22456 15 = 6 ∧ acceleratedOrbit 15 22456 = 500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22456 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22456) = 3 ^ 6 * m + 500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22456.1, data_15_22456.2]

/-- Complete interval computation for depth 15, residue 22457. -/
theorem bounds_15_22457 : exactInterval 15 22457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22457 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22457) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22457 : oddCount 22457 15 = 8 ∧ acceleratedOrbit 15 22457 = 4499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22457 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22457) = 3 ^ 8 * m + 4499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22457.1, data_15_22457.2]

/-- Complete interval computation for depth 15, residue 22458. -/
theorem bounds_15_22458 : exactInterval 15 22458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22458 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22458) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22458 : oddCount 22458 15 = 6 ∧ acceleratedOrbit 15 22458 = 500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22458 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22458) = 3 ^ 6 * m + 500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22458.1, data_15_22458.2]

/-- Complete interval computation for depth 15, residue 22459. -/
theorem bounds_15_22459 : exactInterval 15 22459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22459 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22459) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22459 : oddCount 22459 15 = 8 ∧ acceleratedOrbit 15 22459 = 4499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22459 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22459) = 3 ^ 8 * m + 4499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22459.1, data_15_22459.2]

/-- Complete interval computation for depth 15, residue 22460. -/
theorem bounds_15_22460 : exactInterval 15 22460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22460 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22460) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22460 : oddCount 22460 15 = 8 ∧ acceleratedOrbit 15 22460 = 4498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22460 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22460) = 3 ^ 8 * m + 4498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22460.1, data_15_22460.2]

/-- Complete interval computation for depth 15, residue 22461. -/
theorem bounds_15_22461 : exactInterval 15 22461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22461 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22461) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22461 : oddCount 22461 15 = 8 ∧ acceleratedOrbit 15 22461 = 4498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22461 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22461) = 3 ^ 8 * m + 4498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22461.1, data_15_22461.2]

/-- Complete interval computation for depth 15, residue 22462. -/
theorem bounds_15_22462 : exactInterval 15 22462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22462 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22462) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22462 : oddCount 22462 15 = 8 ∧ acceleratedOrbit 15 22462 = 4498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22462 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22462) = 3 ^ 8 * m + 4498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22462.1, data_15_22462.2]

/-- Complete interval computation for depth 15, residue 22463. -/
theorem bounds_15_22463 : exactInterval 15 22463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22463 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22463) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22463 : oddCount 22463 15 = 11 ∧ acceleratedOrbit 15 22463 = 121445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22463 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22463) = 3 ^ 11 * m + 121445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22463.1, data_15_22463.2]

/-- Complete interval computation for depth 15, residue 22464. -/
theorem bounds_15_22464 : exactInterval 15 22464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22464 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22464) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22464 : oddCount 22464 15 = 5 ∧ acceleratedOrbit 15 22464 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22464 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22464) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22464.1, data_15_22464.2]

/-- Complete interval computation for depth 15, residue 22465. -/
theorem bounds_15_22465 : exactInterval 15 22465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22465 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22465) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22465 : oddCount 22465 15 = 6 ∧ acceleratedOrbit 15 22465 = 500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22465 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22465) = 3 ^ 6 * m + 500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22465.1, data_15_22465.2]

/-- Complete interval computation for depth 15, residue 22466. -/
theorem bounds_15_22466 : exactInterval 15 22466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22466 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22466) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22466 : oddCount 22466 15 = 9 ∧ acceleratedOrbit 15 22466 = 13499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22466 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22466) = 3 ^ 9 * m + 13499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22466.1, data_15_22466.2]

/-- Complete interval computation for depth 15, residue 22467. -/
theorem bounds_15_22467 : exactInterval 15 22467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22467 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22467) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22467 : oddCount 22467 15 = 9 ∧ acceleratedOrbit 15 22467 = 13499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22467 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22467) = 3 ^ 9 * m + 13499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22467.1, data_15_22467.2]

/-- Complete interval computation for depth 15, residue 22468. -/
theorem bounds_15_22468 : exactInterval 15 22468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22468 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22468) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22468 : oddCount 22468 15 = 5 ∧ acceleratedOrbit 15 22468 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22468 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22468) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22468.1, data_15_22468.2]

/-- Complete interval computation for depth 15, residue 22469. -/
theorem bounds_15_22469 : exactInterval 15 22469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22469 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22469) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22469 : oddCount 22469 15 = 5 ∧ acceleratedOrbit 15 22469 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22469 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22469) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22469.1, data_15_22469.2]

/-- Complete interval computation for depth 15, residue 22470. -/
theorem bounds_15_22470 : exactInterval 15 22470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22470 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22470) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22470 : oddCount 22470 15 = 5 ∧ acceleratedOrbit 15 22470 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22470 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22470) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22470.1, data_15_22470.2]

/-- Complete interval computation for depth 15, residue 22471. -/
theorem bounds_15_22471 : exactInterval 15 22471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22471 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22471) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22471 : oddCount 22471 15 = 10 ∧ acceleratedOrbit 15 22471 = 40499 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22471 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22471) = 3 ^ 10 * m + 40499 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22471.1, data_15_22471.2]

/-- Complete interval computation for depth 15, residue 22472. -/
theorem bounds_15_22472 : exactInterval 15 22472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22472 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22472) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22472 : oddCount 22472 15 = 7 ∧ acceleratedOrbit 15 22472 = 1502 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22472 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22472) = 3 ^ 7 * m + 1502 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22472.1, data_15_22472.2]

/-- Complete interval computation for depth 15, residue 22473. -/
theorem bounds_15_22473 : exactInterval 15 22473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22473 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22473) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22473 : oddCount 22473 15 = 9 ∧ acceleratedOrbit 15 22473 = 13502 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22473 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22473) = 3 ^ 9 * m + 13502 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22473.1, data_15_22473.2]

/-- Complete interval computation for depth 15, residue 22474. -/
theorem bounds_15_22474 : exactInterval 15 22474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22474 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22474) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22474 : oddCount 22474 15 = 7 ∧ acceleratedOrbit 15 22474 = 1502 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22474 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22474) = 3 ^ 7 * m + 1502 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22474.1, data_15_22474.2]

/-- Complete interval computation for depth 15, residue 22475. -/
theorem bounds_15_22475 : exactInterval 15 22475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22475 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22475) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22475 : oddCount 22475 15 = 7 ∧ acceleratedOrbit 15 22475 = 1502 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22475 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22475) = 3 ^ 7 * m + 1502 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22475.1, data_15_22475.2]

/-- Complete interval computation for depth 15, residue 22476. -/
theorem bounds_15_22476 : exactInterval 15 22476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22476 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22476) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22476 : oddCount 22476 15 = 7 ∧ acceleratedOrbit 15 22476 = 1502 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22476 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22476) = 3 ^ 7 * m + 1502 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22476.1, data_15_22476.2]

/-- Complete interval computation for depth 15, residue 22477. -/
theorem bounds_15_22477 : exactInterval 15 22477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22477 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22477) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22477 : oddCount 22477 15 = 7 ∧ acceleratedOrbit 15 22477 = 1502 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22477 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22477) = 3 ^ 7 * m + 1502 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22477.1, data_15_22477.2]

end Collatz.Research.PassageAtlas.Batch0686
