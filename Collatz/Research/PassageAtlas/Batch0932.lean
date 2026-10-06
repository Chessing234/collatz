import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0932

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 30507. -/
theorem bounds_15_30507 : exactInterval 15 30507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30507 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30507) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30507 : oddCount 30507 15 = 6 ∧ acceleratedOrbit 15 30507 = 679 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30507 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30507) = 3 ^ 6 * m + 679 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30507.1, data_15_30507.2]

/-- Complete interval computation for depth 15, residue 30508. -/
theorem bounds_15_30508 : exactInterval 15 30508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30508 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30508) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30508 : oddCount 30508 15 = 7 ∧ acceleratedOrbit 15 30508 = 2038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30508 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30508) = 3 ^ 7 * m + 2038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30508.1, data_15_30508.2]

/-- Complete interval computation for depth 15, residue 30509. -/
theorem bounds_15_30509 : exactInterval 15 30509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30509 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30509) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30509 : oddCount 30509 15 = 7 ∧ acceleratedOrbit 15 30509 = 2038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30509 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30509) = 3 ^ 7 * m + 2038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30509.1, data_15_30509.2]

/-- Complete interval computation for depth 15, residue 30510. -/
theorem bounds_15_30510 : exactInterval 15 30510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30510 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30510) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30510 : oddCount 30510 15 = 7 ∧ acceleratedOrbit 15 30510 = 2038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30510 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30510) = 3 ^ 7 * m + 2038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30510.1, data_15_30510.2]

/-- Complete interval computation for depth 15, residue 30511. -/
theorem bounds_15_30511 : exactInterval 15 30511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30511 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30511) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30511 : oddCount 30511 15 = 8 ∧ acceleratedOrbit 15 30511 = 6110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30511 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30511) = 3 ^ 8 * m + 6110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30511.1, data_15_30511.2]

/-- Complete interval computation for depth 15, residue 30512. -/
theorem bounds_15_30512 : exactInterval 15 30512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30512 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30512) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30512 : oddCount 30512 15 = 5 ∧ acceleratedOrbit 15 30512 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30512 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30512) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30512.1, data_15_30512.2]

/-- Complete interval computation for depth 15, residue 30513. -/
theorem bounds_15_30513 : exactInterval 15 30513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30513 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30513) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30513 : oddCount 30513 15 = 7 ∧ acceleratedOrbit 15 30513 = 2038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30513 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30513) = 3 ^ 7 * m + 2038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30513.1, data_15_30513.2]

/-- Complete interval computation for depth 15, residue 30514. -/
theorem bounds_15_30514 : exactInterval 15 30514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30514 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30514) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30514 : oddCount 30514 15 = 7 ∧ acceleratedOrbit 15 30514 = 2038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30514 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30514) = 3 ^ 7 * m + 2038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30514.1, data_15_30514.2]

/-- Complete interval computation for depth 15, residue 30515. -/
theorem bounds_15_30515 : exactInterval 15 30515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30515 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30515) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30515 : oddCount 30515 15 = 7 ∧ acceleratedOrbit 15 30515 = 2038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30515 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30515) = 3 ^ 7 * m + 2038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30515.1, data_15_30515.2]

/-- Complete interval computation for depth 15, residue 30516. -/
theorem bounds_15_30516 : exactInterval 15 30516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30516 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30516) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30516 : oddCount 30516 15 = 5 ∧ acceleratedOrbit 15 30516 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30516 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30516) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30516.1, data_15_30516.2]

/-- Complete interval computation for depth 15, residue 30517. -/
theorem bounds_15_30517 : exactInterval 15 30517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30517 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30517) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30517 : oddCount 30517 15 = 5 ∧ acceleratedOrbit 15 30517 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30517 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30517) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30517.1, data_15_30517.2]

/-- Complete interval computation for depth 15, residue 30518. -/
theorem bounds_15_30518 : exactInterval 15 30518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30518 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30518) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30518 : oddCount 30518 15 = 6 ∧ acceleratedOrbit 15 30518 = 679 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30518 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30518) = 3 ^ 6 * m + 679 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30518.1, data_15_30518.2]

/-- Complete interval computation for depth 15, residue 30519. -/
theorem bounds_15_30519 : exactInterval 15 30519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30519 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30519) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30519 : oddCount 30519 15 = 6 ∧ acceleratedOrbit 15 30519 = 679 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30519 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30519) = 3 ^ 6 * m + 679 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30519.1, data_15_30519.2]

/-- Complete interval computation for depth 15, residue 30520. -/
theorem bounds_15_30520 : exactInterval 15 30520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30520 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30520) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30520 : oddCount 30520 15 = 8 ∧ acceleratedOrbit 15 30520 = 6113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30520 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30520) = 3 ^ 8 * m + 6113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30520.1, data_15_30520.2]

/-- Complete interval computation for depth 15, residue 30521. -/
theorem bounds_15_30521 : exactInterval 15 30521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30521 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30521) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30521 : oddCount 30521 15 = 8 ∧ acceleratedOrbit 15 30521 = 6112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30521 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30521) = 3 ^ 8 * m + 6112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30521.1, data_15_30521.2]

/-- Complete interval computation for depth 15, residue 30522. -/
theorem bounds_15_30522 : exactInterval 15 30522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30522 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30522) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30522 : oddCount 30522 15 = 8 ∧ acceleratedOrbit 15 30522 = 6113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30522 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30522) = 3 ^ 8 * m + 6113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30522.1, data_15_30522.2]

/-- Complete interval computation for depth 15, residue 30523. -/
theorem bounds_15_30523 : exactInterval 15 30523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30523 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30523) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30523 : oddCount 30523 15 = 7 ∧ acceleratedOrbit 15 30523 = 2038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30523 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30523) = 3 ^ 7 * m + 2038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30523.1, data_15_30523.2]

/-- Complete interval computation for depth 15, residue 30524. -/
theorem bounds_15_30524 : exactInterval 15 30524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30524 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30524) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30524 : oddCount 30524 15 = 8 ∧ acceleratedOrbit 15 30524 = 6113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30524 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30524) = 3 ^ 8 * m + 6113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30524.1, data_15_30524.2]

/-- Complete interval computation for depth 15, residue 30525. -/
theorem bounds_15_30525 : exactInterval 15 30525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30525 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30525) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30525 : oddCount 30525 15 = 8 ∧ acceleratedOrbit 15 30525 = 6113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30525 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30525) = 3 ^ 8 * m + 6113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30525.1, data_15_30525.2]

/-- Complete interval computation for depth 15, residue 30526. -/
theorem bounds_15_30526 : exactInterval 15 30526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30526 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30526) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30526 : oddCount 30526 15 = 8 ∧ acceleratedOrbit 15 30526 = 6113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30526 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30526) = 3 ^ 8 * m + 6113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30526.1, data_15_30526.2]

/-- Complete interval computation for depth 15, residue 30527. -/
theorem bounds_15_30527 : exactInterval 15 30527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30527 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30527) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30527 : oddCount 30527 15 = 8 ∧ acceleratedOrbit 15 30527 = 6113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30527 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30527) = 3 ^ 8 * m + 6113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30527.1, data_15_30527.2]

/-- Complete interval computation for depth 15, residue 30528. -/
theorem bounds_15_30528 : exactInterval 15 30528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30528 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30528) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30528 : oddCount 30528 15 = 4 ∧ acceleratedOrbit 15 30528 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30528 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30528) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30528.1, data_15_30528.2]

/-- Complete interval computation for depth 15, residue 30529. -/
theorem bounds_15_30529 : exactInterval 15 30529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30529 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30529) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30529 : oddCount 30529 15 = 5 ∧ acceleratedOrbit 15 30529 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30529 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30529) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30529.1, data_15_30529.2]

/-- Complete interval computation for depth 15, residue 30530. -/
theorem bounds_15_30530 : exactInterval 15 30530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30530 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30530) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30530 : oddCount 30530 15 = 8 ∧ acceleratedOrbit 15 30530 = 6115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30530 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30530) = 3 ^ 8 * m + 6115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30530.1, data_15_30530.2]

/-- Complete interval computation for depth 15, residue 30531. -/
theorem bounds_15_30531 : exactInterval 15 30531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30531 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30531) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30531 : oddCount 30531 15 = 8 ∧ acceleratedOrbit 15 30531 = 6115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30531 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30531) = 3 ^ 8 * m + 6115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30531.1, data_15_30531.2]

/-- Complete interval computation for depth 15, residue 30532. -/
theorem bounds_15_30532 : exactInterval 15 30532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30532 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30532) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30532 : oddCount 30532 15 = 5 ∧ acceleratedOrbit 15 30532 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30532 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30532) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30532.1, data_15_30532.2]

/-- Complete interval computation for depth 15, residue 30533. -/
theorem bounds_15_30533 : exactInterval 15 30533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30533 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30533) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30533 : oddCount 30533 15 = 5 ∧ acceleratedOrbit 15 30533 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30533 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30533) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30533.1, data_15_30533.2]

/-- Complete interval computation for depth 15, residue 30534. -/
theorem bounds_15_30534 : exactInterval 15 30534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30534 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30534) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30534 : oddCount 30534 15 = 5 ∧ acceleratedOrbit 15 30534 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30534 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30534) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30534.1, data_15_30534.2]

/-- Complete interval computation for depth 15, residue 30535. -/
theorem bounds_15_30535 : exactInterval 15 30535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30535 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30535) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30535 : oddCount 30535 15 = 9 ∧ acceleratedOrbit 15 30535 = 18343 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30535 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30535) = 3 ^ 9 * m + 18343 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30535.1, data_15_30535.2]

/-- Complete interval computation for depth 15, residue 30536. -/
theorem bounds_15_30536 : exactInterval 15 30536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30536 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30536) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30536 : oddCount 30536 15 = 7 ∧ acceleratedOrbit 15 30536 = 2039 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30536 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30536) = 3 ^ 7 * m + 2039 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30536.1, data_15_30536.2]

/-- Complete interval computation for depth 15, residue 30537. -/
theorem bounds_15_30537 : exactInterval 15 30537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30537 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30537) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30537 : oddCount 30537 15 = 9 ∧ acceleratedOrbit 15 30537 = 18346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30537 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30537) = 3 ^ 9 * m + 18346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30537.1, data_15_30537.2]

/-- Complete interval computation for depth 15, residue 30538. -/
theorem bounds_15_30538 : exactInterval 15 30538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30538 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30538) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30538 : oddCount 30538 15 = 7 ∧ acceleratedOrbit 15 30538 = 2039 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30538 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30538) = 3 ^ 7 * m + 2039 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30538.1, data_15_30538.2]

end Collatz.Research.PassageAtlas.Batch0932
