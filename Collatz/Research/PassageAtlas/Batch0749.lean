import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0749

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 24510. -/
theorem bounds_15_24510 : exactInterval 15 24510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24510 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24510) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24510 : oddCount 24510 15 = 7 ∧ acceleratedOrbit 15 24510 = 1636 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24510 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24510) = 3 ^ 7 * m + 1636 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24510.1, data_15_24510.2]

/-- Complete interval computation for depth 15, residue 24511. -/
theorem bounds_15_24511 : exactInterval 15 24511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24511 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24511) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24511 : oddCount 24511 15 = 12 ∧ acceleratedOrbit 15 24511 = 397547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24511 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24511) = 3 ^ 12 * m + 397547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24511.1, data_15_24511.2]

/-- Complete interval computation for depth 15, residue 24512. -/
theorem bounds_15_24512 : exactInterval 15 24512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24512 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24512) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24512 : oddCount 24512 15 = 7 ∧ acceleratedOrbit 15 24512 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24512 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24512) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24512.1, data_15_24512.2]

/-- Complete interval computation for depth 15, residue 24513. -/
theorem bounds_15_24513 : exactInterval 15 24513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24513 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24513) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24513 : oddCount 24513 15 = 7 ∧ acceleratedOrbit 15 24513 = 1637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24513 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24513) = 3 ^ 7 * m + 1637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24513.1, data_15_24513.2]

/-- Complete interval computation for depth 15, residue 24514. -/
theorem bounds_15_24514 : exactInterval 15 24514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24514 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24514) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24514 : oddCount 24514 15 = 10 ∧ acceleratedOrbit 15 24514 = 44185 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24514 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24514) = 3 ^ 10 * m + 44185 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24514.1, data_15_24514.2]

/-- Complete interval computation for depth 15, residue 24515. -/
theorem bounds_15_24515 : exactInterval 15 24515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24515 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24515) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24515 : oddCount 24515 15 = 10 ∧ acceleratedOrbit 15 24515 = 44185 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24515 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24515) = 3 ^ 10 * m + 44185 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24515.1, data_15_24515.2]

/-- Complete interval computation for depth 15, residue 24516. -/
theorem bounds_15_24516 : exactInterval 15 24516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24516 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24516) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24516 : oddCount 24516 15 = 7 ∧ acceleratedOrbit 15 24516 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24516 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24516) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24516.1, data_15_24516.2]

/-- Complete interval computation for depth 15, residue 24517. -/
theorem bounds_15_24517 : exactInterval 15 24517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24517 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24517) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24517 : oddCount 24517 15 = 7 ∧ acceleratedOrbit 15 24517 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24517 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24517) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24517.1, data_15_24517.2]

/-- Complete interval computation for depth 15, residue 24518. -/
theorem bounds_15_24518 : exactInterval 15 24518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24518 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24518) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24518 : oddCount 24518 15 = 7 ∧ acceleratedOrbit 15 24518 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24518 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24518) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24518.1, data_15_24518.2]

/-- Complete interval computation for depth 15, residue 24519. -/
theorem bounds_15_24519 : exactInterval 15 24519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24519 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24519) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24519 : oddCount 24519 15 = 10 ∧ acceleratedOrbit 15 24519 = 44189 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24519 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24519) = 3 ^ 10 * m + 44189 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24519.1, data_15_24519.2]

/-- Complete interval computation for depth 15, residue 24520. -/
theorem bounds_15_24520 : exactInterval 15 24520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24520 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24520) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24520 : oddCount 24520 15 = 9 ∧ acceleratedOrbit 15 24520 = 14741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24520 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24520) = 3 ^ 9 * m + 14741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24520.1, data_15_24520.2]

/-- Complete interval computation for depth 15, residue 24521. -/
theorem bounds_15_24521 : exactInterval 15 24521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24521 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24521) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24521 : oddCount 24521 15 = 9 ∧ acceleratedOrbit 15 24521 = 14732 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24521 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24521) = 3 ^ 9 * m + 14732 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24521.1, data_15_24521.2]

/-- Complete interval computation for depth 15, residue 24522. -/
theorem bounds_15_24522 : exactInterval 15 24522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24522 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24522) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24522 : oddCount 24522 15 = 9 ∧ acceleratedOrbit 15 24522 = 14741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24522 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24522) = 3 ^ 9 * m + 14741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24522.1, data_15_24522.2]

/-- Complete interval computation for depth 15, residue 24523. -/
theorem bounds_15_24523 : exactInterval 15 24523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24523 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24523) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24523 : oddCount 24523 15 = 5 ∧ acceleratedOrbit 15 24523 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24523 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24523) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24523.1, data_15_24523.2]

/-- Complete interval computation for depth 15, residue 24524. -/
theorem bounds_15_24524 : exactInterval 15 24524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24524 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24524) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24524 : oddCount 24524 15 = 9 ∧ acceleratedOrbit 15 24524 = 14741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24524 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24524) = 3 ^ 9 * m + 14741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24524.1, data_15_24524.2]

/-- Complete interval computation for depth 15, residue 24525. -/
theorem bounds_15_24525 : exactInterval 15 24525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24525 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24525) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24525 : oddCount 24525 15 = 9 ∧ acceleratedOrbit 15 24525 = 14741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24525 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24525) = 3 ^ 9 * m + 14741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24525.1, data_15_24525.2]

/-- Complete interval computation for depth 15, residue 24526. -/
theorem bounds_15_24526 : exactInterval 15 24526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24526 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24526) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24526 : oddCount 24526 15 = 9 ∧ acceleratedOrbit 15 24526 = 14735 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24526 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24526) = 3 ^ 9 * m + 14735 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24526.1, data_15_24526.2]

/-- Complete interval computation for depth 15, residue 24527. -/
theorem bounds_15_24527 : exactInterval 15 24527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24527 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24527) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24527 : oddCount 24527 15 = 9 ∧ acceleratedOrbit 15 24527 = 14735 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24527 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24527) = 3 ^ 9 * m + 14735 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24527.1, data_15_24527.2]

/-- Complete interval computation for depth 15, residue 24528. -/
theorem bounds_15_24528 : exactInterval 15 24528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24528 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24528) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24528 : oddCount 24528 15 = 7 ∧ acceleratedOrbit 15 24528 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24528 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24528) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24528.1, data_15_24528.2]

/-- Complete interval computation for depth 15, residue 24529. -/
theorem bounds_15_24529 : exactInterval 15 24529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24529 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24529) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24529 : oddCount 24529 15 = 9 ∧ acceleratedOrbit 15 24529 = 14741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24529 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24529) = 3 ^ 9 * m + 14741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24529.1, data_15_24529.2]

/-- Complete interval computation for depth 15, residue 24530. -/
theorem bounds_15_24530 : exactInterval 15 24530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24530 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24530) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24530 : oddCount 24530 15 = 9 ∧ acceleratedOrbit 15 24530 = 14737 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24530 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24530) = 3 ^ 9 * m + 14737 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24530.1, data_15_24530.2]

/-- Complete interval computation for depth 15, residue 24531. -/
theorem bounds_15_24531 : exactInterval 15 24531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24531 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24531) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24531 : oddCount 24531 15 = 9 ∧ acceleratedOrbit 15 24531 = 14737 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24531 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24531) = 3 ^ 9 * m + 14737 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24531.1, data_15_24531.2]

/-- Complete interval computation for depth 15, residue 24532. -/
theorem bounds_15_24532 : exactInterval 15 24532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24532 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24532) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24532 : oddCount 24532 15 = 7 ∧ acceleratedOrbit 15 24532 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24532 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24532) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24532.1, data_15_24532.2]

/-- Complete interval computation for depth 15, residue 24533. -/
theorem bounds_15_24533 : exactInterval 15 24533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24533 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24533) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24533 : oddCount 24533 15 = 7 ∧ acceleratedOrbit 15 24533 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24533 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24533) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24533.1, data_15_24533.2]

/-- Complete interval computation for depth 15, residue 24534. -/
theorem bounds_15_24534 : exactInterval 15 24534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24534 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24534) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24534 : oddCount 24534 15 = 10 ∧ acceleratedOrbit 15 24534 = 44219 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24534 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24534) = 3 ^ 10 * m + 44219 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24534.1, data_15_24534.2]

/-- Complete interval computation for depth 15, residue 24535. -/
theorem bounds_15_24535 : exactInterval 15 24535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24535 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24535) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24535 : oddCount 24535 15 = 10 ∧ acceleratedOrbit 15 24535 = 44219 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24535 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24535) = 3 ^ 10 * m + 44219 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24535.1, data_15_24535.2]

/-- Complete interval computation for depth 15, residue 24536. -/
theorem bounds_15_24536 : exactInterval 15 24536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24536 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24536) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24536 : oddCount 24536 15 = 8 ∧ acceleratedOrbit 15 24536 = 4916 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24536 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24536) = 3 ^ 8 * m + 4916 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24536.1, data_15_24536.2]

/-- Complete interval computation for depth 15, residue 24537. -/
theorem bounds_15_24537 : exactInterval 15 24537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24537 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24537) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24537 : oddCount 24537 15 = 7 ∧ acceleratedOrbit 15 24537 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24537 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24537) = 3 ^ 7 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24537.1, data_15_24537.2]

/-- Complete interval computation for depth 15, residue 24538. -/
theorem bounds_15_24538 : exactInterval 15 24538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24538 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24538) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24538 : oddCount 24538 15 = 8 ∧ acceleratedOrbit 15 24538 = 4916 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24538 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24538) = 3 ^ 8 * m + 4916 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24538.1, data_15_24538.2]

/-- Complete interval computation for depth 15, residue 24539. -/
theorem bounds_15_24539 : exactInterval 15 24539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24539 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24539) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24539 : oddCount 24539 15 = 11 ∧ acceleratedOrbit 15 24539 = 132677 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24539 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24539) = 3 ^ 11 * m + 132677 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24539.1, data_15_24539.2]

/-- Complete interval computation for depth 15, residue 24540. -/
theorem bounds_15_24540 : exactInterval 15 24540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24540 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24540) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24540 : oddCount 24540 15 = 8 ∧ acceleratedOrbit 15 24540 = 4916 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24540 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24540) = 3 ^ 8 * m + 4916 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24540.1, data_15_24540.2]

/-- Complete interval computation for depth 15, residue 24541. -/
theorem bounds_15_24541 : exactInterval 15 24541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24541 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24541) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24541 : oddCount 24541 15 = 8 ∧ acceleratedOrbit 15 24541 = 4916 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24541 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24541) = 3 ^ 8 * m + 4916 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24541.1, data_15_24541.2]

/-- Complete interval computation for depth 15, residue 24542. -/
theorem bounds_15_24542 : exactInterval 15 24542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24542 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24542) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24542 : oddCount 24542 15 = 9 ∧ acceleratedOrbit 15 24542 = 14744 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24542 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24542) = 3 ^ 9 * m + 14744 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24542.1, data_15_24542.2]

end Collatz.Research.PassageAtlas.Batch0749
