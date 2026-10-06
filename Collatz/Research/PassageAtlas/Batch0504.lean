import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0504

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 16482. -/
theorem bounds_15_16482 : exactInterval 15 16482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16482 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16482) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16482 : oddCount 16482 15 = 6 ∧ acceleratedOrbit 15 16482 = 367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16482 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16482) = 3 ^ 6 * m + 367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16482.1, data_15_16482.2]

/-- Complete interval computation for depth 15, residue 16483. -/
theorem bounds_15_16483 : exactInterval 15 16483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16483 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16483) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16483 : oddCount 16483 15 = 6 ∧ acceleratedOrbit 15 16483 = 367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16483 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16483) = 3 ^ 6 * m + 367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16483.1, data_15_16483.2]

/-- Complete interval computation for depth 15, residue 16484. -/
theorem bounds_15_16484 : exactInterval 15 16484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16484 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16484) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16484 : oddCount 16484 15 = 6 ∧ acceleratedOrbit 15 16484 = 367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16484 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16484) = 3 ^ 6 * m + 367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16484.1, data_15_16484.2]

/-- Complete interval computation for depth 15, residue 16485. -/
theorem bounds_15_16485 : exactInterval 15 16485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16485 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16485) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16485 : oddCount 16485 15 = 6 ∧ acceleratedOrbit 15 16485 = 367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16485 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16485) = 3 ^ 6 * m + 367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16485.1, data_15_16485.2]

/-- Complete interval computation for depth 15, residue 16486. -/
theorem bounds_15_16486 : exactInterval 15 16486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16486 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16486) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16486 : oddCount 16486 15 = 6 ∧ acceleratedOrbit 15 16486 = 367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16486 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16486) = 3 ^ 6 * m + 367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16486.1, data_15_16486.2]

/-- Complete interval computation for depth 15, residue 16487. -/
theorem bounds_15_16487 : exactInterval 15 16487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16487 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16487) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16487 : oddCount 16487 15 = 10 ∧ acceleratedOrbit 15 16487 = 29713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16487 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16487) = 3 ^ 10 * m + 29713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16487.1, data_15_16487.2]

/-- Complete interval computation for depth 15, residue 16488. -/
theorem bounds_15_16488 : exactInterval 15 16488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16488 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16488) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16488 : oddCount 16488 15 = 4 ∧ acceleratedOrbit 15 16488 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16488 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16488) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16488.1, data_15_16488.2]

/-- Complete interval computation for depth 15, residue 16489. -/
theorem bounds_15_16489 : exactInterval 15 16489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16489 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16489) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16489 : oddCount 16489 15 = 9 ∧ acceleratedOrbit 15 16489 = 9908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16489 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16489) = 3 ^ 9 * m + 9908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16489.1, data_15_16489.2]

/-- Complete interval computation for depth 15, residue 16490. -/
theorem bounds_15_16490 : exactInterval 15 16490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16490 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16490) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16490 : oddCount 16490 15 = 4 ∧ acceleratedOrbit 15 16490 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16490 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16490) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16490.1, data_15_16490.2]

/-- Complete interval computation for depth 15, residue 16491. -/
theorem bounds_15_16491 : exactInterval 15 16491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16491 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16491) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16491 : oddCount 16491 15 = 10 ∧ acceleratedOrbit 15 16491 = 29722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16491 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16491) = 3 ^ 10 * m + 29722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16491.1, data_15_16491.2]

/-- Complete interval computation for depth 15, residue 16492. -/
theorem bounds_15_16492 : exactInterval 15 16492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16492 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16492) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16492 : oddCount 16492 15 = 9 ∧ acceleratedOrbit 15 16492 = 9910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16492 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16492) = 3 ^ 9 * m + 9910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16492.1, data_15_16492.2]

/-- Complete interval computation for depth 15, residue 16493. -/
theorem bounds_15_16493 : exactInterval 15 16493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16493 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16493) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16493 : oddCount 16493 15 = 9 ∧ acceleratedOrbit 15 16493 = 9910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16493 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16493) = 3 ^ 9 * m + 9910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16493.1, data_15_16493.2]

/-- Complete interval computation for depth 15, residue 16494. -/
theorem bounds_15_16494 : exactInterval 15 16494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16494 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16494) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16494 : oddCount 16494 15 = 9 ∧ acceleratedOrbit 15 16494 = 9910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16494 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16494) = 3 ^ 9 * m + 9910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16494.1, data_15_16494.2]

/-- Complete interval computation for depth 15, residue 16495. -/
theorem bounds_15_16495 : exactInterval 15 16495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16495 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16495) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16495 : oddCount 16495 15 = 13 ∧ acceleratedOrbit 15 16495 = 802628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16495 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16495) = 3 ^ 13 * m + 802628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16495.1, data_15_16495.2]

/-- Complete interval computation for depth 15, residue 16496. -/
theorem bounds_15_16496 : exactInterval 15 16496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16496 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16496) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16496 : oddCount 16496 15 = 6 ∧ acceleratedOrbit 15 16496 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16496 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16496) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16496.1, data_15_16496.2]

/-- Complete interval computation for depth 15, residue 16497. -/
theorem bounds_15_16497 : exactInterval 15 16497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16497 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16497) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16497 : oddCount 16497 15 = 4 ∧ acceleratedOrbit 15 16497 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16497 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16497) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16497.1, data_15_16497.2]

/-- Complete interval computation for depth 15, residue 16498. -/
theorem bounds_15_16498 : exactInterval 15 16498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16498 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16498) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16498 : oddCount 16498 15 = 7 ∧ acceleratedOrbit 15 16498 = 1102 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16498 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16498) = 3 ^ 7 * m + 1102 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16498.1, data_15_16498.2]

/-- Complete interval computation for depth 15, residue 16499. -/
theorem bounds_15_16499 : exactInterval 15 16499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16499 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16499) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16499 : oddCount 16499 15 = 7 ∧ acceleratedOrbit 15 16499 = 1102 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16499 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16499) = 3 ^ 7 * m + 1102 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16499.1, data_15_16499.2]

/-- Complete interval computation for depth 15, residue 16500. -/
theorem bounds_15_16500 : exactInterval 15 16500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16500 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16500) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16500 : oddCount 16500 15 = 6 ∧ acceleratedOrbit 15 16500 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16500 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16500) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16500.1, data_15_16500.2]

/-- Complete interval computation for depth 15, residue 16501. -/
theorem bounds_15_16501 : exactInterval 15 16501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16501 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16501) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16501 : oddCount 16501 15 = 6 ∧ acceleratedOrbit 15 16501 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16501 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16501) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16501.1, data_15_16501.2]

/-- Complete interval computation for depth 15, residue 16502. -/
theorem bounds_15_16502 : exactInterval 15 16502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16502 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16502) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16502 : oddCount 16502 15 = 7 ∧ acceleratedOrbit 15 16502 = 1102 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16502 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16502) = 3 ^ 7 * m + 1102 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16502.1, data_15_16502.2]

/-- Complete interval computation for depth 15, residue 16503. -/
theorem bounds_15_16503 : exactInterval 15 16503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16503 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16503) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16503 : oddCount 16503 15 = 7 ∧ acceleratedOrbit 15 16503 = 1102 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16503 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16503) = 3 ^ 7 * m + 1102 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16503.1, data_15_16503.2]

/-- Complete interval computation for depth 15, residue 16504. -/
theorem bounds_15_16504 : exactInterval 15 16504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16504 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16504) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16504 : oddCount 16504 15 = 6 ∧ acceleratedOrbit 15 16504 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16504 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16504) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16504.1, data_15_16504.2]

/-- Complete interval computation for depth 15, residue 16505. -/
theorem bounds_15_16505 : exactInterval 15 16505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16505 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16505) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16505 : oddCount 16505 15 = 10 ∧ acceleratedOrbit 15 16505 = 29747 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16505 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16505) = 3 ^ 10 * m + 29747 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16505.1, data_15_16505.2]

/-- Complete interval computation for depth 15, residue 16506. -/
theorem bounds_15_16506 : exactInterval 15 16506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16506 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16506) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16506 : oddCount 16506 15 = 6 ∧ acceleratedOrbit 15 16506 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16506 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16506) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16506.1, data_15_16506.2]

/-- Complete interval computation for depth 15, residue 16507. -/
theorem bounds_15_16507 : exactInterval 15 16507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16507 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16507) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16507 : oddCount 16507 15 = 10 ∧ acceleratedOrbit 15 16507 = 29753 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16507 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16507) = 3 ^ 10 * m + 29753 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16507.1, data_15_16507.2]

/-- Complete interval computation for depth 15, residue 16508. -/
theorem bounds_15_16508 : exactInterval 15 16508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16508 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16508) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16508 : oddCount 16508 15 = 9 ∧ acceleratedOrbit 15 16508 = 9919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16508 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16508) = 3 ^ 9 * m + 9919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16508.1, data_15_16508.2]

/-- Complete interval computation for depth 15, residue 16509. -/
theorem bounds_15_16509 : exactInterval 15 16509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16509 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16509) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16509 : oddCount 16509 15 = 9 ∧ acceleratedOrbit 15 16509 = 9919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16509 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16509) = 3 ^ 9 * m + 9919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16509.1, data_15_16509.2]

/-- Complete interval computation for depth 15, residue 16510. -/
theorem bounds_15_16510 : exactInterval 15 16510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16510 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16510) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16510 : oddCount 16510 15 = 9 ∧ acceleratedOrbit 15 16510 = 9919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16510 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16510) = 3 ^ 9 * m + 9919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16510.1, data_15_16510.2]

/-- Complete interval computation for depth 15, residue 16511. -/
theorem bounds_15_16511 : exactInterval 15 16511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16511 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16511) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16511 : oddCount 16511 15 = 10 ∧ acceleratedOrbit 15 16511 = 29756 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16511 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16511) = 3 ^ 10 * m + 29756 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16511.1, data_15_16511.2]

/-- Complete interval computation for depth 15, residue 16512. -/
theorem bounds_15_16512 : exactInterval 15 16512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16512 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16512) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16512 : oddCount 16512 15 = 5 ∧ acceleratedOrbit 15 16512 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16512 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16512) = 3 ^ 5 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16512.1, data_15_16512.2]

/-- Complete interval computation for depth 15, residue 16513. -/
theorem bounds_15_16513 : exactInterval 15 16513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16513 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16513) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16513 : oddCount 16513 15 = 9 ∧ acceleratedOrbit 15 16513 = 9922 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16513 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16513) = 3 ^ 9 * m + 9922 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16513.1, data_15_16513.2]

/-- Complete interval computation for depth 15, residue 16514. -/
theorem bounds_15_16514 : exactInterval 15 16514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16514 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16514) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16514 : oddCount 16514 15 = 8 ∧ acceleratedOrbit 15 16514 = 3311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16514 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16514) = 3 ^ 8 * m + 3311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16514.1, data_15_16514.2]

end Collatz.Research.PassageAtlas.Batch0504
