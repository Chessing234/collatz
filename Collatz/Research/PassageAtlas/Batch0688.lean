import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0688

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 22511. -/
theorem bounds_15_22511 : exactInterval 15 22511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22511 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22511) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22511 : oddCount 22511 15 = 8 ∧ acceleratedOrbit 15 22511 = 4508 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22511 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22511) = 3 ^ 8 * m + 4508 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22511.1, data_15_22511.2]

/-- Complete interval computation for depth 15, residue 22512. -/
theorem bounds_15_22512 : exactInterval 15 22512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22512 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22512) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22512 : oddCount 22512 15 = 8 ∧ acceleratedOrbit 15 22512 = 4511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22512 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22512) = 3 ^ 8 * m + 4511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22512.1, data_15_22512.2]

/-- Complete interval computation for depth 15, residue 22513. -/
theorem bounds_15_22513 : exactInterval 15 22513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22513 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22513) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22513 : oddCount 22513 15 = 8 ∧ acceleratedOrbit 15 22513 = 4511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22513 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22513) = 3 ^ 8 * m + 4511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22513.1, data_15_22513.2]

/-- Complete interval computation for depth 15, residue 22514. -/
theorem bounds_15_22514 : exactInterval 15 22514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22514 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22514) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22514 : oddCount 22514 15 = 11 ∧ acceleratedOrbit 15 22514 = 121742 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22514 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22514) = 3 ^ 11 * m + 121742 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22514.1, data_15_22514.2]

/-- Complete interval computation for depth 15, residue 22515. -/
theorem bounds_15_22515 : exactInterval 15 22515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22515 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22515) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22515 : oddCount 22515 15 = 11 ∧ acceleratedOrbit 15 22515 = 121742 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22515 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22515) = 3 ^ 11 * m + 121742 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22515.1, data_15_22515.2]

/-- Complete interval computation for depth 15, residue 22516. -/
theorem bounds_15_22516 : exactInterval 15 22516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22516 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22516) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22516 : oddCount 22516 15 = 8 ∧ acceleratedOrbit 15 22516 = 4511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22516 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22516) = 3 ^ 8 * m + 4511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22516.1, data_15_22516.2]

/-- Complete interval computation for depth 15, residue 22517. -/
theorem bounds_15_22517 : exactInterval 15 22517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22517 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22517) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22517 : oddCount 22517 15 = 8 ∧ acceleratedOrbit 15 22517 = 4511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22517 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22517) = 3 ^ 8 * m + 4511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22517.1, data_15_22517.2]

/-- Complete interval computation for depth 15, residue 22518. -/
theorem bounds_15_22518 : exactInterval 15 22518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22518 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22518) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22518 : oddCount 22518 15 = 9 ∧ acceleratedOrbit 15 22518 = 13529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22518 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22518) = 3 ^ 9 * m + 13529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22518.1, data_15_22518.2]

/-- Complete interval computation for depth 15, residue 22519. -/
theorem bounds_15_22519 : exactInterval 15 22519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22519 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22519) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22519 : oddCount 22519 15 = 9 ∧ acceleratedOrbit 15 22519 = 13529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22519 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22519) = 3 ^ 9 * m + 13529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22519.1, data_15_22519.2]

/-- Complete interval computation for depth 15, residue 22520. -/
theorem bounds_15_22520 : exactInterval 15 22520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22520 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22520) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22520 : oddCount 22520 15 = 9 ∧ acceleratedOrbit 15 22520 = 13532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22520 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22520) = 3 ^ 9 * m + 13532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22520.1, data_15_22520.2]

/-- Complete interval computation for depth 15, residue 22521. -/
theorem bounds_15_22521 : exactInterval 15 22521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22521 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22521) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22521 : oddCount 22521 15 = 8 ∧ acceleratedOrbit 15 22521 = 4510 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22521 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22521) = 3 ^ 8 * m + 4510 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22521.1, data_15_22521.2]

/-- Complete interval computation for depth 15, residue 22522. -/
theorem bounds_15_22522 : exactInterval 15 22522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22522 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22522) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22522 : oddCount 22522 15 = 9 ∧ acceleratedOrbit 15 22522 = 13532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22522 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22522) = 3 ^ 9 * m + 13532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22522.1, data_15_22522.2]

/-- Complete interval computation for depth 15, residue 22523. -/
theorem bounds_15_22523 : exactInterval 15 22523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22523 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22523) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22523 : oddCount 22523 15 = 10 ∧ acceleratedOrbit 15 22523 = 40591 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22523 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22523) = 3 ^ 10 * m + 40591 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22523.1, data_15_22523.2]

/-- Complete interval computation for depth 15, residue 22524. -/
theorem bounds_15_22524 : exactInterval 15 22524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22524 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22524) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22524 : oddCount 22524 15 = 9 ∧ acceleratedOrbit 15 22524 = 13532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22524 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22524) = 3 ^ 9 * m + 13532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22524.1, data_15_22524.2]

/-- Complete interval computation for depth 15, residue 22525. -/
theorem bounds_15_22525 : exactInterval 15 22525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22525 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22525) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22525 : oddCount 22525 15 = 9 ∧ acceleratedOrbit 15 22525 = 13532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22525 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22525) = 3 ^ 9 * m + 13532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22525.1, data_15_22525.2]

/-- Complete interval computation for depth 15, residue 22526. -/
theorem bounds_15_22526 : exactInterval 15 22526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22526 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22526) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22526 : oddCount 22526 15 = 12 ∧ acceleratedOrbit 15 22526 = 365366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22526 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22526) = 3 ^ 12 * m + 365366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22526.1, data_15_22526.2]

/-- Complete interval computation for depth 15, residue 22527. -/
theorem bounds_15_22527 : exactInterval 15 22527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22527 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22527) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22527 : oddCount 22527 15 = 12 ∧ acceleratedOrbit 15 22527 = 365366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22527 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22527) = 3 ^ 12 * m + 365366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22527.1, data_15_22527.2]

/-- Complete interval computation for depth 15, residue 22528. -/
theorem bounds_15_22528 : exactInterval 15 22528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22528 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22528) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22528 : oddCount 22528 15 = 3 ∧ acceleratedOrbit 15 22528 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22528 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22528) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22528.1, data_15_22528.2]

/-- Complete interval computation for depth 15, residue 22529. -/
theorem bounds_15_22529 : exactInterval 15 22529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22529 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22529) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22529 : oddCount 22529 15 = 7 ∧ acceleratedOrbit 15 22529 = 1504 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22529 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22529) = 3 ^ 7 * m + 1504 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22529.1, data_15_22529.2]

/-- Complete interval computation for depth 15, residue 22530. -/
theorem bounds_15_22530 : exactInterval 15 22530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22530 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22530) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22530 : oddCount 22530 15 = 7 ∧ acceleratedOrbit 15 22530 = 1505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22530 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22530) = 3 ^ 7 * m + 1505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22530.1, data_15_22530.2]

/-- Complete interval computation for depth 15, residue 22531. -/
theorem bounds_15_22531 : exactInterval 15 22531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22531 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22531) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22531 : oddCount 22531 15 = 7 ∧ acceleratedOrbit 15 22531 = 1505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22531 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22531) = 3 ^ 7 * m + 1505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22531.1, data_15_22531.2]

/-- Complete interval computation for depth 15, residue 22532. -/
theorem bounds_15_22532 : exactInterval 15 22532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22532 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22532) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22532 : oddCount 22532 15 = 7 ∧ acceleratedOrbit 15 22532 = 1505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22532 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22532) = 3 ^ 7 * m + 1505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22532.1, data_15_22532.2]

/-- Complete interval computation for depth 15, residue 22533. -/
theorem bounds_15_22533 : exactInterval 15 22533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22533 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22533) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22533 : oddCount 22533 15 = 7 ∧ acceleratedOrbit 15 22533 = 1505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22533 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22533) = 3 ^ 7 * m + 1505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22533.1, data_15_22533.2]

/-- Complete interval computation for depth 15, residue 22534. -/
theorem bounds_15_22534 : exactInterval 15 22534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22534 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22534) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22534 : oddCount 22534 15 = 7 ∧ acceleratedOrbit 15 22534 = 1505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22534 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22534) = 3 ^ 7 * m + 1505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22534.1, data_15_22534.2]

/-- Complete interval computation for depth 15, residue 22535. -/
theorem bounds_15_22535 : exactInterval 15 22535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22535 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22535) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22535 : oddCount 22535 15 = 7 ∧ acceleratedOrbit 15 22535 = 1505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22535 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22535) = 3 ^ 7 * m + 1505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22535.1, data_15_22535.2]

/-- Complete interval computation for depth 15, residue 22536. -/
theorem bounds_15_22536 : exactInterval 15 22536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22536 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22536) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22536 : oddCount 22536 15 = 6 ∧ acceleratedOrbit 15 22536 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22536 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22536) = 3 ^ 6 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22536.1, data_15_22536.2]

/-- Complete interval computation for depth 15, residue 22537. -/
theorem bounds_15_22537 : exactInterval 15 22537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22537 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22537) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22537 : oddCount 22537 15 = 9 ∧ acceleratedOrbit 15 22537 = 13540 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22537 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22537) = 3 ^ 9 * m + 13540 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22537.1, data_15_22537.2]

/-- Complete interval computation for depth 15, residue 22538. -/
theorem bounds_15_22538 : exactInterval 15 22538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22538 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22538) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22538 : oddCount 22538 15 = 6 ∧ acceleratedOrbit 15 22538 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22538 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22538) = 3 ^ 6 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22538.1, data_15_22538.2]

/-- Complete interval computation for depth 15, residue 22539. -/
theorem bounds_15_22539 : exactInterval 15 22539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22539 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22539) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22539 : oddCount 22539 15 = 7 ∧ acceleratedOrbit 15 22539 = 1505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22539 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22539) = 3 ^ 7 * m + 1505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22539.1, data_15_22539.2]

/-- Complete interval computation for depth 15, residue 22540. -/
theorem bounds_15_22540 : exactInterval 15 22540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22540 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22540) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22540 : oddCount 22540 15 = 6 ∧ acceleratedOrbit 15 22540 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22540 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22540) = 3 ^ 6 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22540.1, data_15_22540.2]

/-- Complete interval computation for depth 15, residue 22541. -/
theorem bounds_15_22541 : exactInterval 15 22541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22541 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22541) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22541 : oddCount 22541 15 = 6 ∧ acceleratedOrbit 15 22541 = 503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22541 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22541) = 3 ^ 6 * m + 503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22541.1, data_15_22541.2]

/-- Complete interval computation for depth 15, residue 22542. -/
theorem bounds_15_22542 : exactInterval 15 22542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22542 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22542) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22542 : oddCount 22542 15 = 7 ∧ acceleratedOrbit 15 22542 = 1505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22542 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22542) = 3 ^ 7 * m + 1505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22542.1, data_15_22542.2]

/-- Complete interval computation for depth 15, residue 22543. -/
theorem bounds_15_22543 : exactInterval 15 22543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22543 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22543) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22543 : oddCount 22543 15 = 7 ∧ acceleratedOrbit 15 22543 = 1505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22543 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22543) = 3 ^ 7 * m + 1505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22543.1, data_15_22543.2]

end Collatz.Research.PassageAtlas.Batch0688
