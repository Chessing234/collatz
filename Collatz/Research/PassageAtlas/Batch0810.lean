import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0810

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 26509. -/
theorem bounds_15_26509 : exactInterval 15 26509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26509 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26509) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26509 : oddCount 26509 15 = 6 ∧ acceleratedOrbit 15 26509 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26509 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26509) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26509.1, data_15_26509.2]

/-- Complete interval computation for depth 15, residue 26510. -/
theorem bounds_15_26510 : exactInterval 15 26510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26510 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26510) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26510 : oddCount 26510 15 = 10 ∧ acceleratedOrbit 15 26510 = 47780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26510 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26510) = 3 ^ 10 * m + 47780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26510.1, data_15_26510.2]

/-- Complete interval computation for depth 15, residue 26511. -/
theorem bounds_15_26511 : exactInterval 15 26511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26511 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26511) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26511 : oddCount 26511 15 = 10 ∧ acceleratedOrbit 15 26511 = 47780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26511 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26511) = 3 ^ 10 * m + 47780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26511.1, data_15_26511.2]

/-- Complete interval computation for depth 15, residue 26512. -/
theorem bounds_15_26512 : exactInterval 15 26512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26512 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26512) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26512 : oddCount 26512 15 = 7 ∧ acceleratedOrbit 15 26512 = 1772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26512 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26512) = 3 ^ 7 * m + 1772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26512.1, data_15_26512.2]

/-- Complete interval computation for depth 15, residue 26513. -/
theorem bounds_15_26513 : exactInterval 15 26513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26513 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26513) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26513 : oddCount 26513 15 = 6 ∧ acceleratedOrbit 15 26513 = 590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26513 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26513) = 3 ^ 6 * m + 590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26513.1, data_15_26513.2]

/-- Complete interval computation for depth 15, residue 26514. -/
theorem bounds_15_26514 : exactInterval 15 26514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26514 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26514) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26514 : oddCount 26514 15 = 6 ∧ acceleratedOrbit 15 26514 = 590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26514 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26514) = 3 ^ 6 * m + 590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26514.1, data_15_26514.2]

/-- Complete interval computation for depth 15, residue 26515. -/
theorem bounds_15_26515 : exactInterval 15 26515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26515 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26515) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26515 : oddCount 26515 15 = 6 ∧ acceleratedOrbit 15 26515 = 590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26515 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26515) = 3 ^ 6 * m + 590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26515.1, data_15_26515.2]

/-- Complete interval computation for depth 15, residue 26516. -/
theorem bounds_15_26516 : exactInterval 15 26516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26516 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26516) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26516 : oddCount 26516 15 = 7 ∧ acceleratedOrbit 15 26516 = 1772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26516 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26516) = 3 ^ 7 * m + 1772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26516.1, data_15_26516.2]

/-- Complete interval computation for depth 15, residue 26517. -/
theorem bounds_15_26517 : exactInterval 15 26517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26517 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26517) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26517 : oddCount 26517 15 = 7 ∧ acceleratedOrbit 15 26517 = 1772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26517 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26517) = 3 ^ 7 * m + 1772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26517.1, data_15_26517.2]

/-- Complete interval computation for depth 15, residue 26518. -/
theorem bounds_15_26518 : exactInterval 15 26518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26518 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26518) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26518 : oddCount 26518 15 = 7 ∧ acceleratedOrbit 15 26518 = 1772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26518 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26518) = 3 ^ 7 * m + 1772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26518.1, data_15_26518.2]

/-- Complete interval computation for depth 15, residue 26519. -/
theorem bounds_15_26519 : exactInterval 15 26519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26519 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26519) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26519 : oddCount 26519 15 = 7 ∧ acceleratedOrbit 15 26519 = 1772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26519 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26519) = 3 ^ 7 * m + 1772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26519.1, data_15_26519.2]

/-- Complete interval computation for depth 15, residue 26520. -/
theorem bounds_15_26520 : exactInterval 15 26520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26520 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26520) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26520 : oddCount 26520 15 = 7 ∧ acceleratedOrbit 15 26520 = 1772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26520 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26520) = 3 ^ 7 * m + 1772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26520.1, data_15_26520.2]

/-- Complete interval computation for depth 15, residue 26521. -/
theorem bounds_15_26521 : exactInterval 15 26521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26521 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26521) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26521 : oddCount 26521 15 = 7 ∧ acceleratedOrbit 15 26521 = 1772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26521 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26521) = 3 ^ 7 * m + 1772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26521.1, data_15_26521.2]

/-- Complete interval computation for depth 15, residue 26522. -/
theorem bounds_15_26522 : exactInterval 15 26522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26522 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26522) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26522 : oddCount 26522 15 = 7 ∧ acceleratedOrbit 15 26522 = 1772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26522 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26522) = 3 ^ 7 * m + 1772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26522.1, data_15_26522.2]

/-- Complete interval computation for depth 15, residue 26523. -/
theorem bounds_15_26523 : exactInterval 15 26523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26523 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26523) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26523 : oddCount 26523 15 = 8 ∧ acceleratedOrbit 15 26523 = 5311 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26523 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26523) = 3 ^ 8 * m + 5311 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26523.1, data_15_26523.2]

/-- Complete interval computation for depth 15, residue 26524. -/
theorem bounds_15_26524 : exactInterval 15 26524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26524 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26524) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26524 : oddCount 26524 15 = 8 ∧ acceleratedOrbit 15 26524 = 5312 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26524 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26524) = 3 ^ 8 * m + 5312 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26524.1, data_15_26524.2]

/-- Complete interval computation for depth 15, residue 26525. -/
theorem bounds_15_26525 : exactInterval 15 26525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26525 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26525) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26525 : oddCount 26525 15 = 8 ∧ acceleratedOrbit 15 26525 = 5312 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26525 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26525) = 3 ^ 8 * m + 5312 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26525.1, data_15_26525.2]

/-- Complete interval computation for depth 15, residue 26526. -/
theorem bounds_15_26526 : exactInterval 15 26526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26526 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26526) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26526 : oddCount 26526 15 = 8 ∧ acceleratedOrbit 15 26526 = 5312 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26526 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26526) = 3 ^ 8 * m + 5312 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26526.1, data_15_26526.2]

/-- Complete interval computation for depth 15, residue 26527. -/
theorem bounds_15_26527 : exactInterval 15 26527 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26527 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26527) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26527 : oddCount 26527 15 = 9 ∧ acceleratedOrbit 15 26527 = 15935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26527 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26527) = 3 ^ 9 * m + 15935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26527.1, data_15_26527.2]

/-- Complete interval computation for depth 15, residue 26528. -/
theorem bounds_15_26528 : exactInterval 15 26528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26528 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26528) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26528 : oddCount 26528 15 = 6 ∧ acceleratedOrbit 15 26528 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26528 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26528) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26528.1, data_15_26528.2]

/-- Complete interval computation for depth 15, residue 26529. -/
theorem bounds_15_26529 : exactInterval 15 26529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26529 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26529) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26529 : oddCount 26529 15 = 7 ∧ acceleratedOrbit 15 26529 = 1772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26529 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26529) = 3 ^ 7 * m + 1772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26529.1, data_15_26529.2]

/-- Complete interval computation for depth 15, residue 26530. -/
theorem bounds_15_26530 : exactInterval 15 26530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26530 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26530) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26530 : oddCount 26530 15 = 7 ∧ acceleratedOrbit 15 26530 = 1772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26530 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26530) = 3 ^ 7 * m + 1772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26530.1, data_15_26530.2]

/-- Complete interval computation for depth 15, residue 26531. -/
theorem bounds_15_26531 : exactInterval 15 26531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26531 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26531) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26531 : oddCount 26531 15 = 7 ∧ acceleratedOrbit 15 26531 = 1772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26531 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26531) = 3 ^ 7 * m + 1772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26531.1, data_15_26531.2]

/-- Complete interval computation for depth 15, residue 26532. -/
theorem bounds_15_26532 : exactInterval 15 26532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26532 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26532) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26532 : oddCount 26532 15 = 8 ∧ acceleratedOrbit 15 26532 = 5314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26532 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26532) = 3 ^ 8 * m + 5314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26532.1, data_15_26532.2]

/-- Complete interval computation for depth 15, residue 26533. -/
theorem bounds_15_26533 : exactInterval 15 26533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26533 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26533) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26533 : oddCount 26533 15 = 8 ∧ acceleratedOrbit 15 26533 = 5314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26533 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26533) = 3 ^ 8 * m + 5314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26533.1, data_15_26533.2]

/-- Complete interval computation for depth 15, residue 26534. -/
theorem bounds_15_26534 : exactInterval 15 26534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26534 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26534) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26534 : oddCount 26534 15 = 8 ∧ acceleratedOrbit 15 26534 = 5314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26534 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26534) = 3 ^ 8 * m + 5314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26534.1, data_15_26534.2]

/-- Complete interval computation for depth 15, residue 26535. -/
theorem bounds_15_26535 : exactInterval 15 26535 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26535 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26535) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26535 : oddCount 26535 15 = 9 ∧ acceleratedOrbit 15 26535 = 15940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26535 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26535) = 3 ^ 9 * m + 15940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26535.1, data_15_26535.2]

/-- Complete interval computation for depth 15, residue 26536. -/
theorem bounds_15_26536 : exactInterval 15 26536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26536 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26536) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26536 : oddCount 26536 15 = 6 ∧ acceleratedOrbit 15 26536 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26536 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26536) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26536.1, data_15_26536.2]

/-- Complete interval computation for depth 15, residue 26537. -/
theorem bounds_15_26537 : exactInterval 15 26537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26537 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26537) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26537 : oddCount 26537 15 = 11 ∧ acceleratedOrbit 15 26537 = 143471 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26537 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26537) = 3 ^ 11 * m + 143471 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26537.1, data_15_26537.2]

/-- Complete interval computation for depth 15, residue 26538. -/
theorem bounds_15_26538 : exactInterval 15 26538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26538 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26538) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26538 : oddCount 26538 15 = 6 ∧ acceleratedOrbit 15 26538 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26538 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26538) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26538.1, data_15_26538.2]

/-- Complete interval computation for depth 15, residue 26539. -/
theorem bounds_15_26539 : exactInterval 15 26539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26539 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26539) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26539 : oddCount 26539 15 = 10 ∧ acceleratedOrbit 15 26539 = 47830 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26539 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26539) = 3 ^ 10 * m + 47830 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26539.1, data_15_26539.2]

/-- Complete interval computation for depth 15, residue 26540. -/
theorem bounds_15_26540 : exactInterval 15 26540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26540 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26540) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26540 : oddCount 26540 15 = 9 ∧ acceleratedOrbit 15 26540 = 15947 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26540 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26540) = 3 ^ 9 * m + 15947 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26540.1, data_15_26540.2]

/-- Complete interval computation for depth 15, residue 26541. -/
theorem bounds_15_26541 : exactInterval 15 26541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26541 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26541) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26541 : oddCount 26541 15 = 9 ∧ acceleratedOrbit 15 26541 = 15947 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26541 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26541) = 3 ^ 9 * m + 15947 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26541.1, data_15_26541.2]

end Collatz.Research.PassageAtlas.Batch0810
