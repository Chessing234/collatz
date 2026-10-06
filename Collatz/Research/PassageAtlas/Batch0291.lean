import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0291

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 9502. -/
theorem bounds_15_9502 : exactInterval 15 9502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9502 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9502) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9502 : oddCount 9502 15 = 10 ∧ acceleratedOrbit 15 9502 = 17131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9502 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9502) = 3 ^ 10 * m + 17131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9502.1, data_15_9502.2]

/-- Complete interval computation for depth 15, residue 9503. -/
theorem bounds_15_9503 : exactInterval 15 9503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9503 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9503) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9503 : oddCount 9503 15 = 9 ∧ acceleratedOrbit 15 9503 = 5710 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9503 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9503) = 3 ^ 9 * m + 5710 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9503.1, data_15_9503.2]

/-- Complete interval computation for depth 15, residue 9504. -/
theorem bounds_15_9504 : exactInterval 15 9504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9504 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9504) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9504 : oddCount 9504 15 = 7 ∧ acceleratedOrbit 15 9504 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9504 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9504) = 3 ^ 7 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9504.1, data_15_9504.2]

/-- Complete interval computation for depth 15, residue 9505. -/
theorem bounds_15_9505 : exactInterval 15 9505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9505 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9505) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9505 : oddCount 9505 15 = 5 ∧ acceleratedOrbit 15 9505 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9505 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9505) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9505.1, data_15_9505.2]

/-- Complete interval computation for depth 15, residue 9506. -/
theorem bounds_15_9506 : exactInterval 15 9506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9506 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9506) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9506 : oddCount 9506 15 = 8 ∧ acceleratedOrbit 15 9506 = 1907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9506 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9506) = 3 ^ 8 * m + 1907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9506.1, data_15_9506.2]

/-- Complete interval computation for depth 15, residue 9507. -/
theorem bounds_15_9507 : exactInterval 15 9507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9507 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9507) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9507 : oddCount 9507 15 = 8 ∧ acceleratedOrbit 15 9507 = 1907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9507 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9507) = 3 ^ 8 * m + 1907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9507.1, data_15_9507.2]

/-- Complete interval computation for depth 15, residue 9508. -/
theorem bounds_15_9508 : exactInterval 15 9508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9508 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9508) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9508 : oddCount 9508 15 = 8 ∧ acceleratedOrbit 15 9508 = 1907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9508 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9508) = 3 ^ 8 * m + 1907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9508.1, data_15_9508.2]

/-- Complete interval computation for depth 15, residue 9509. -/
theorem bounds_15_9509 : exactInterval 15 9509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9509 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9509) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9509 : oddCount 9509 15 = 8 ∧ acceleratedOrbit 15 9509 = 1907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9509 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9509) = 3 ^ 8 * m + 1907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9509.1, data_15_9509.2]

/-- Complete interval computation for depth 15, residue 9510. -/
theorem bounds_15_9510 : exactInterval 15 9510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9510 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9510) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9510 : oddCount 9510 15 = 8 ∧ acceleratedOrbit 15 9510 = 1907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9510 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9510) = 3 ^ 8 * m + 1907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9510.1, data_15_9510.2]

/-- Complete interval computation for depth 15, residue 9511. -/
theorem bounds_15_9511 : exactInterval 15 9511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9511 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9511) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9511 : oddCount 9511 15 = 7 ∧ acceleratedOrbit 15 9511 = 635 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9511 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9511) = 3 ^ 7 * m + 635 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9511.1, data_15_9511.2]

/-- Complete interval computation for depth 15, residue 9512. -/
theorem bounds_15_9512 : exactInterval 15 9512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9512 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9512) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9512 : oddCount 9512 15 = 7 ∧ acceleratedOrbit 15 9512 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9512 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9512) = 3 ^ 7 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9512.1, data_15_9512.2]

/-- Complete interval computation for depth 15, residue 9513. -/
theorem bounds_15_9513 : exactInterval 15 9513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9513 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9513) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9513 : oddCount 9513 15 = 10 ∧ acceleratedOrbit 15 9513 = 17147 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9513 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9513) = 3 ^ 10 * m + 17147 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9513.1, data_15_9513.2]

/-- Complete interval computation for depth 15, residue 9514. -/
theorem bounds_15_9514 : exactInterval 15 9514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9514 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9514) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9514 : oddCount 9514 15 = 7 ∧ acceleratedOrbit 15 9514 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9514 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9514) = 3 ^ 7 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9514.1, data_15_9514.2]

/-- Complete interval computation for depth 15, residue 9515. -/
theorem bounds_15_9515 : exactInterval 15 9515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9515 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9515) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9515 : oddCount 9515 15 = 8 ∧ acceleratedOrbit 15 9515 = 1907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9515 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9515) = 3 ^ 8 * m + 1907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9515.1, data_15_9515.2]

/-- Complete interval computation for depth 15, residue 9516. -/
theorem bounds_15_9516 : exactInterval 15 9516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9516 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9516) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9516 : oddCount 9516 15 = 7 ∧ acceleratedOrbit 15 9516 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9516 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9516) = 3 ^ 7 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9516.1, data_15_9516.2]

/-- Complete interval computation for depth 15, residue 9517. -/
theorem bounds_15_9517 : exactInterval 15 9517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9517 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9517) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9517 : oddCount 9517 15 = 7 ∧ acceleratedOrbit 15 9517 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9517 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9517) = 3 ^ 7 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9517.1, data_15_9517.2]

/-- Complete interval computation for depth 15, residue 9518. -/
theorem bounds_15_9518 : exactInterval 15 9518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9518 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9518) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9518 : oddCount 9518 15 = 7 ∧ acceleratedOrbit 15 9518 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9518 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9518) = 3 ^ 7 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9518.1, data_15_9518.2]

/-- Complete interval computation for depth 15, residue 9519. -/
theorem bounds_15_9519 : exactInterval 15 9519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9519 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9519) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9519 : oddCount 9519 15 = 9 ∧ acceleratedOrbit 15 9519 = 5719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9519 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9519) = 3 ^ 9 * m + 5719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9519.1, data_15_9519.2]

/-- Complete interval computation for depth 15, residue 9520. -/
theorem bounds_15_9520 : exactInterval 15 9520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9520 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9520) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9520 : oddCount 9520 15 = 7 ∧ acceleratedOrbit 15 9520 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9520 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9520) = 3 ^ 7 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9520.1, data_15_9520.2]

/-- Complete interval computation for depth 15, residue 9521. -/
theorem bounds_15_9521 : exactInterval 15 9521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9521 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9521) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9521 : oddCount 9521 15 = 6 ∧ acceleratedOrbit 15 9521 = 212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9521 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9521) = 3 ^ 6 * m + 212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9521.1, data_15_9521.2]

/-- Complete interval computation for depth 15, residue 9522. -/
theorem bounds_15_9522 : exactInterval 15 9522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9522 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9522) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9522 : oddCount 9522 15 = 6 ∧ acceleratedOrbit 15 9522 = 212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9522 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9522) = 3 ^ 6 * m + 212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9522.1, data_15_9522.2]

/-- Complete interval computation for depth 15, residue 9523. -/
theorem bounds_15_9523 : exactInterval 15 9523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9523 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9523) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9523 : oddCount 9523 15 = 6 ∧ acceleratedOrbit 15 9523 = 212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9523 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9523) = 3 ^ 6 * m + 212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9523.1, data_15_9523.2]

/-- Complete interval computation for depth 15, residue 9524. -/
theorem bounds_15_9524 : exactInterval 15 9524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9524 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9524) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9524 : oddCount 9524 15 = 7 ∧ acceleratedOrbit 15 9524 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9524 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9524) = 3 ^ 7 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9524.1, data_15_9524.2]

/-- Complete interval computation for depth 15, residue 9525. -/
theorem bounds_15_9525 : exactInterval 15 9525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9525 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9525) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9525 : oddCount 9525 15 = 7 ∧ acceleratedOrbit 15 9525 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9525 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9525) = 3 ^ 7 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9525.1, data_15_9525.2]

/-- Complete interval computation for depth 15, residue 9526. -/
theorem bounds_15_9526 : exactInterval 15 9526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9526 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9526) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9526 : oddCount 9526 15 = 12 ∧ acceleratedOrbit 15 9526 = 154547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9526 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9526) = 3 ^ 12 * m + 154547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9526.1, data_15_9526.2]

/-- Complete interval computation for depth 15, residue 9527. -/
theorem bounds_15_9527 : exactInterval 15 9527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9527 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9527) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9527 : oddCount 9527 15 = 12 ∧ acceleratedOrbit 15 9527 = 154547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9527 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9527) = 3 ^ 12 * m + 154547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9527.1, data_15_9527.2]

/-- Complete interval computation for depth 15, residue 9528. -/
theorem bounds_15_9528 : exactInterval 15 9528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9528 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9528) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9528 : oddCount 9528 15 = 8 ∧ acceleratedOrbit 15 9528 = 1910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9528 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9528) = 3 ^ 8 * m + 1910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9528.1, data_15_9528.2]

/-- Complete interval computation for depth 15, residue 9529. -/
theorem bounds_15_9529 : exactInterval 15 9529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9529 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9529) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9529 : oddCount 9529 15 = 9 ∧ acceleratedOrbit 15 9529 = 5726 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9529 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9529) = 3 ^ 9 * m + 5726 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9529.1, data_15_9529.2]

/-- Complete interval computation for depth 15, residue 9530. -/
theorem bounds_15_9530 : exactInterval 15 9530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9530 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9530) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9530 : oddCount 9530 15 = 8 ∧ acceleratedOrbit 15 9530 = 1910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9530 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9530) = 3 ^ 8 * m + 1910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9530.1, data_15_9530.2]

/-- Complete interval computation for depth 15, residue 9531. -/
theorem bounds_15_9531 : exactInterval 15 9531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9531 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9531) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9531 : oddCount 9531 15 = 7 ∧ acceleratedOrbit 15 9531 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9531 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9531) = 3 ^ 7 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9531.1, data_15_9531.2]

/-- Complete interval computation for depth 15, residue 9532. -/
theorem bounds_15_9532 : exactInterval 15 9532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9532 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9532) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9532 : oddCount 9532 15 = 8 ∧ acceleratedOrbit 15 9532 = 1910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9532 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9532) = 3 ^ 8 * m + 1910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9532.1, data_15_9532.2]

/-- Complete interval computation for depth 15, residue 9533. -/
theorem bounds_15_9533 : exactInterval 15 9533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9533 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9533) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9533 : oddCount 9533 15 = 8 ∧ acceleratedOrbit 15 9533 = 1910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9533 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9533) = 3 ^ 8 * m + 1910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9533.1, data_15_9533.2]

/-- Complete interval computation for depth 15, residue 9534. -/
theorem bounds_15_9534 : exactInterval 15 9534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9534 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9534) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9534 : oddCount 9534 15 = 10 ∧ acceleratedOrbit 15 9534 = 17185 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9534 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9534) = 3 ^ 10 * m + 17185 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9534.1, data_15_9534.2]

end Collatz.Research.PassageAtlas.Batch0291
