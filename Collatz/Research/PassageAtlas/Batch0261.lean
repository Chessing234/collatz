import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0261

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 8519. -/
theorem bounds_15_8519 : exactInterval 15 8519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8519 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8519) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8519 : oddCount 8519 15 = 11 ∧ acceleratedOrbit 15 8519 = 46064 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8519 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8519) = 3 ^ 11 * m + 46064 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8519.1, data_15_8519.2]

/-- Complete interval computation for depth 15, residue 8520. -/
theorem bounds_15_8520 : exactInterval 15 8520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8520 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8520) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8520 : oddCount 8520 15 = 8 ∧ acceleratedOrbit 15 8520 = 1709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8520 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8520) = 3 ^ 8 * m + 1709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8520.1, data_15_8520.2]

/-- Complete interval computation for depth 15, residue 8521. -/
theorem bounds_15_8521 : exactInterval 15 8521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8521 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8521) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8521 : oddCount 8521 15 = 7 ∧ acceleratedOrbit 15 8521 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8521 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8521) = 3 ^ 7 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8521.1, data_15_8521.2]

/-- Complete interval computation for depth 15, residue 8522. -/
theorem bounds_15_8522 : exactInterval 15 8522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8522 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8522) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8522 : oddCount 8522 15 = 8 ∧ acceleratedOrbit 15 8522 = 1709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8522 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8522) = 3 ^ 8 * m + 1709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8522.1, data_15_8522.2]

/-- Complete interval computation for depth 15, residue 8523. -/
theorem bounds_15_8523 : exactInterval 15 8523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8523 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8523) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8523 : oddCount 8523 15 = 6 ∧ acceleratedOrbit 15 8523 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8523 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8523) = 3 ^ 6 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8523.1, data_15_8523.2]

/-- Complete interval computation for depth 15, residue 8524. -/
theorem bounds_15_8524 : exactInterval 15 8524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8524 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8524) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8524 : oddCount 8524 15 = 8 ∧ acceleratedOrbit 15 8524 = 1709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8524 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8524) = 3 ^ 8 * m + 1709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8524.1, data_15_8524.2]

/-- Complete interval computation for depth 15, residue 8525. -/
theorem bounds_15_8525 : exactInterval 15 8525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8525 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8525) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8525 : oddCount 8525 15 = 8 ∧ acceleratedOrbit 15 8525 = 1709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8525 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8525) = 3 ^ 8 * m + 1709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8525.1, data_15_8525.2]

/-- Complete interval computation for depth 15, residue 8526. -/
theorem bounds_15_8526 : exactInterval 15 8526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8526 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8526) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8526 : oddCount 8526 15 = 11 ∧ acceleratedOrbit 15 8526 = 46109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8526 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8526) = 3 ^ 11 * m + 46109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8526.1, data_15_8526.2]

/-- Complete interval computation for depth 15, residue 8527. -/
theorem bounds_15_8527 : exactInterval 15 8527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8527 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8527) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8527 : oddCount 8527 15 = 11 ∧ acceleratedOrbit 15 8527 = 46109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8527 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8527) = 3 ^ 11 * m + 46109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8527.1, data_15_8527.2]

/-- Complete interval computation for depth 15, residue 8528. -/
theorem bounds_15_8528 : exactInterval 15 8528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8528 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8528) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8528 : oddCount 8528 15 = 4 ∧ acceleratedOrbit 15 8528 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8528 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8528) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8528.1, data_15_8528.2]

/-- Complete interval computation for depth 15, residue 8529. -/
theorem bounds_15_8529 : exactInterval 15 8529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8529 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8529) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8529 : oddCount 8529 15 = 8 ∧ acceleratedOrbit 15 8529 = 1709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8529 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8529) = 3 ^ 8 * m + 1709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8529.1, data_15_8529.2]

/-- Complete interval computation for depth 15, residue 8530. -/
theorem bounds_15_8530 : exactInterval 15 8530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8530 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8530) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8530 : oddCount 8530 15 = 11 ∧ acceleratedOrbit 15 8530 = 46133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8530 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8530) = 3 ^ 11 * m + 46133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8530.1, data_15_8530.2]

/-- Complete interval computation for depth 15, residue 8531. -/
theorem bounds_15_8531 : exactInterval 15 8531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8531 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8531) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8531 : oddCount 8531 15 = 11 ∧ acceleratedOrbit 15 8531 = 46133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8531 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8531) = 3 ^ 11 * m + 46133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8531.1, data_15_8531.2]

/-- Complete interval computation for depth 15, residue 8532. -/
theorem bounds_15_8532 : exactInterval 15 8532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8532 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8532) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8532 : oddCount 8532 15 = 4 ∧ acceleratedOrbit 15 8532 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8532 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8532) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8532.1, data_15_8532.2]

/-- Complete interval computation for depth 15, residue 8533. -/
theorem bounds_15_8533 : exactInterval 15 8533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8533 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8533) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8533 : oddCount 8533 15 = 4 ∧ acceleratedOrbit 15 8533 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8533 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8533) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8533.1, data_15_8533.2]

/-- Complete interval computation for depth 15, residue 8534. -/
theorem bounds_15_8534 : exactInterval 15 8534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8534 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8534) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8534 : oddCount 8534 15 = 6 ∧ acceleratedOrbit 15 8534 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8534 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8534) = 3 ^ 6 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8534.1, data_15_8534.2]

/-- Complete interval computation for depth 15, residue 8535. -/
theorem bounds_15_8535 : exactInterval 15 8535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8535 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8535) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8535 : oddCount 8535 15 = 6 ∧ acceleratedOrbit 15 8535 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8535 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8535) = 3 ^ 6 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8535.1, data_15_8535.2]

/-- Complete interval computation for depth 15, residue 8536. -/
theorem bounds_15_8536 : exactInterval 15 8536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8536 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8536) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8536 : oddCount 8536 15 = 6 ∧ acceleratedOrbit 15 8536 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8536 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8536) = 3 ^ 6 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8536.1, data_15_8536.2]

/-- Complete interval computation for depth 15, residue 8537. -/
theorem bounds_15_8537 : exactInterval 15 8537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8537 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8537) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8537 : oddCount 8537 15 = 8 ∧ acceleratedOrbit 15 8537 = 1711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8537 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8537) = 3 ^ 8 * m + 1711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8537.1, data_15_8537.2]

/-- Complete interval computation for depth 15, residue 8538. -/
theorem bounds_15_8538 : exactInterval 15 8538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8538 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8538) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8538 : oddCount 8538 15 = 6 ∧ acceleratedOrbit 15 8538 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8538 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8538) = 3 ^ 6 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8538.1, data_15_8538.2]

/-- Complete interval computation for depth 15, residue 8539. -/
theorem bounds_15_8539 : exactInterval 15 8539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8539 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8539) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8539 : oddCount 8539 15 = 6 ∧ acceleratedOrbit 15 8539 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8539 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8539) = 3 ^ 6 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8539.1, data_15_8539.2]

/-- Complete interval computation for depth 15, residue 8540. -/
theorem bounds_15_8540 : exactInterval 15 8540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8540 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8540) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8540 : oddCount 8540 15 = 6 ∧ acceleratedOrbit 15 8540 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8540 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8540) = 3 ^ 6 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8540.1, data_15_8540.2]

/-- Complete interval computation for depth 15, residue 8541. -/
theorem bounds_15_8541 : exactInterval 15 8541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8541 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8541) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8541 : oddCount 8541 15 = 6 ∧ acceleratedOrbit 15 8541 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8541 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8541) = 3 ^ 6 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8541.1, data_15_8541.2]

/-- Complete interval computation for depth 15, residue 8542. -/
theorem bounds_15_8542 : exactInterval 15 8542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8542 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8542) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8542 : oddCount 8542 15 = 8 ∧ acceleratedOrbit 15 8542 = 1711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8542 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8542) = 3 ^ 8 * m + 1711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8542.1, data_15_8542.2]

/-- Complete interval computation for depth 15, residue 8543. -/
theorem bounds_15_8543 : exactInterval 15 8543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8543 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8543) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8543 : oddCount 8543 15 = 8 ∧ acceleratedOrbit 15 8543 = 1711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8543 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8543) = 3 ^ 8 * m + 1711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8543.1, data_15_8543.2]

/-- Complete interval computation for depth 15, residue 8544. -/
theorem bounds_15_8544 : exactInterval 15 8544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8544 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8544) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8544 : oddCount 8544 15 = 5 ∧ acceleratedOrbit 15 8544 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8544 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8544) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8544.1, data_15_8544.2]

/-- Complete interval computation for depth 15, residue 8545. -/
theorem bounds_15_8545 : exactInterval 15 8545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8545 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8545) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8545 : oddCount 8545 15 = 8 ∧ acceleratedOrbit 15 8545 = 1712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8545 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8545) = 3 ^ 8 * m + 1712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8545.1, data_15_8545.2]

/-- Complete interval computation for depth 15, residue 8546. -/
theorem bounds_15_8546 : exactInterval 15 8546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8546 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8546) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8546 : oddCount 8546 15 = 6 ∧ acceleratedOrbit 15 8546 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8546 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8546) = 3 ^ 6 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8546.1, data_15_8546.2]

/-- Complete interval computation for depth 15, residue 8547. -/
theorem bounds_15_8547 : exactInterval 15 8547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8547 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8547) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8547 : oddCount 8547 15 = 6 ∧ acceleratedOrbit 15 8547 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8547 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8547) = 3 ^ 6 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8547.1, data_15_8547.2]

/-- Complete interval computation for depth 15, residue 8548. -/
theorem bounds_15_8548 : exactInterval 15 8548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8548 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8548) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8548 : oddCount 8548 15 = 6 ∧ acceleratedOrbit 15 8548 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8548 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8548) = 3 ^ 6 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8548.1, data_15_8548.2]

/-- Complete interval computation for depth 15, residue 8549. -/
theorem bounds_15_8549 : exactInterval 15 8549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8549 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8549) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8549 : oddCount 8549 15 = 6 ∧ acceleratedOrbit 15 8549 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8549 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8549) = 3 ^ 6 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8549.1, data_15_8549.2]

/-- Complete interval computation for depth 15, residue 8550. -/
theorem bounds_15_8550 : exactInterval 15 8550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8550 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8550) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8550 : oddCount 8550 15 = 6 ∧ acceleratedOrbit 15 8550 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8550 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8550) = 3 ^ 6 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8550.1, data_15_8550.2]

/-- Complete interval computation for depth 15, residue 8551. -/
theorem bounds_15_8551 : exactInterval 15 8551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8551 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8551) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8551 : oddCount 8551 15 = 10 ∧ acceleratedOrbit 15 8551 = 15412 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8551 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8551) = 3 ^ 10 * m + 15412 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8551.1, data_15_8551.2]

end Collatz.Research.PassageAtlas.Batch0261
