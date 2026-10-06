import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0993

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 32505. -/
theorem bounds_15_32505 : exactInterval 15 32505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32505 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32505) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32505 : oddCount 32505 15 = 7 ∧ acceleratedOrbit 15 32505 = 2170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32505 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32505) = 3 ^ 7 * m + 2170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32505.1, data_15_32505.2]

/-- Complete interval computation for depth 15, residue 32506. -/
theorem bounds_15_32506 : exactInterval 15 32506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32506 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32506) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32506 : oddCount 32506 15 = 7 ∧ acceleratedOrbit 15 32506 = 2170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32506 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32506) = 3 ^ 7 * m + 2170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32506.1, data_15_32506.2]

/-- Complete interval computation for depth 15, residue 32507. -/
theorem bounds_15_32507 : exactInterval 15 32507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32507 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32507) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32507 : oddCount 32507 15 = 10 ∧ acceleratedOrbit 15 32507 = 58583 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32507 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32507) = 3 ^ 10 * m + 58583 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32507.1, data_15_32507.2]

/-- Complete interval computation for depth 15, residue 32508. -/
theorem bounds_15_32508 : exactInterval 15 32508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32508 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32508) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32508 : oddCount 32508 15 = 10 ∧ acceleratedOrbit 15 32508 = 58589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32508 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32508) = 3 ^ 10 * m + 58589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32508.1, data_15_32508.2]

/-- Complete interval computation for depth 15, residue 32509. -/
theorem bounds_15_32509 : exactInterval 15 32509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32509 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32509) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32509 : oddCount 32509 15 = 10 ∧ acceleratedOrbit 15 32509 = 58589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32509 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32509) = 3 ^ 10 * m + 58589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32509.1, data_15_32509.2]

/-- Complete interval computation for depth 15, residue 32510. -/
theorem bounds_15_32510 : exactInterval 15 32510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32510 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32510) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32510 : oddCount 32510 15 = 10 ∧ acceleratedOrbit 15 32510 = 58589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32510 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32510) = 3 ^ 10 * m + 58589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32510.1, data_15_32510.2]

/-- Complete interval computation for depth 15, residue 32511. -/
theorem bounds_15_32511 : exactInterval 15 32511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32511 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32511) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32511 : oddCount 32511 15 = 13 ∧ acceleratedOrbit 15 32511 = 1581869 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32511 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32511) = 3 ^ 13 * m + 1581869 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32511.1, data_15_32511.2]

/-- Complete interval computation for depth 15, residue 32512. -/
theorem bounds_15_32512 : exactInterval 15 32512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32512 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32512) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32512 : oddCount 32512 15 = 7 ∧ acceleratedOrbit 15 32512 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32512 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32512) = 3 ^ 7 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32512.1, data_15_32512.2]

/-- Complete interval computation for depth 15, residue 32513. -/
theorem bounds_15_32513 : exactInterval 15 32513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32513 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32513) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32513 : oddCount 32513 15 = 6 ∧ acceleratedOrbit 15 32513 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32513 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32513) = 3 ^ 6 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32513.1, data_15_32513.2]

/-- Complete interval computation for depth 15, residue 32514. -/
theorem bounds_15_32514 : exactInterval 15 32514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32514 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32514) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32514 : oddCount 32514 15 = 7 ∧ acceleratedOrbit 15 32514 = 2171 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32514 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32514) = 3 ^ 7 * m + 2171 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32514.1, data_15_32514.2]

/-- Complete interval computation for depth 15, residue 32515. -/
theorem bounds_15_32515 : exactInterval 15 32515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32515 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32515) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32515 : oddCount 32515 15 = 7 ∧ acceleratedOrbit 15 32515 = 2171 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32515 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32515) = 3 ^ 7 * m + 2171 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32515.1, data_15_32515.2]

/-- Complete interval computation for depth 15, residue 32516. -/
theorem bounds_15_32516 : exactInterval 15 32516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32516 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32516) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32516 : oddCount 32516 15 = 6 ∧ acceleratedOrbit 15 32516 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32516 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32516) = 3 ^ 6 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32516.1, data_15_32516.2]

/-- Complete interval computation for depth 15, residue 32517. -/
theorem bounds_15_32517 : exactInterval 15 32517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32517 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32517) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32517 : oddCount 32517 15 = 6 ∧ acceleratedOrbit 15 32517 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32517 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32517) = 3 ^ 6 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32517.1, data_15_32517.2]

/-- Complete interval computation for depth 15, residue 32518. -/
theorem bounds_15_32518 : exactInterval 15 32518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32518 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32518) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32518 : oddCount 32518 15 = 6 ∧ acceleratedOrbit 15 32518 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32518 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32518) = 3 ^ 6 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32518.1, data_15_32518.2]

/-- Complete interval computation for depth 15, residue 32519. -/
theorem bounds_15_32519 : exactInterval 15 32519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32519 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32519) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32519 : oddCount 32519 15 = 7 ∧ acceleratedOrbit 15 32519 = 2171 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32519 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32519) = 3 ^ 7 * m + 2171 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32519.1, data_15_32519.2]

/-- Complete interval computation for depth 15, residue 32520. -/
theorem bounds_15_32520 : exactInterval 15 32520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32520 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32520) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32520 : oddCount 32520 15 = 9 ∧ acceleratedOrbit 15 32520 = 19547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32520 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32520) = 3 ^ 9 * m + 19547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32520.1, data_15_32520.2]

/-- Complete interval computation for depth 15, residue 32521. -/
theorem bounds_15_32521 : exactInterval 15 32521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32521 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32521) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32521 : oddCount 32521 15 = 8 ∧ acceleratedOrbit 15 32521 = 6512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32521 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32521) = 3 ^ 8 * m + 6512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32521.1, data_15_32521.2]

/-- Complete interval computation for depth 15, residue 32522. -/
theorem bounds_15_32522 : exactInterval 15 32522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32522 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32522) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32522 : oddCount 32522 15 = 9 ∧ acceleratedOrbit 15 32522 = 19547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32522 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32522) = 3 ^ 9 * m + 19547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32522.1, data_15_32522.2]

/-- Complete interval computation for depth 15, residue 32523. -/
theorem bounds_15_32523 : exactInterval 15 32523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32523 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32523) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32523 : oddCount 32523 15 = 7 ∧ acceleratedOrbit 15 32523 = 2171 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32523 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32523) = 3 ^ 7 * m + 2171 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32523.1, data_15_32523.2]

/-- Complete interval computation for depth 15, residue 32524. -/
theorem bounds_15_32524 : exactInterval 15 32524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32524 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32524) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32524 : oddCount 32524 15 = 9 ∧ acceleratedOrbit 15 32524 = 19547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32524 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32524) = 3 ^ 9 * m + 19547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32524.1, data_15_32524.2]

/-- Complete interval computation for depth 15, residue 32525. -/
theorem bounds_15_32525 : exactInterval 15 32525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32525 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32525) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32525 : oddCount 32525 15 = 9 ∧ acceleratedOrbit 15 32525 = 19547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32525 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32525) = 3 ^ 9 * m + 19547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32525.1, data_15_32525.2]

/-- Complete interval computation for depth 15, residue 32526. -/
theorem bounds_15_32526 : exactInterval 15 32526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32526 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32526) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32526 : oddCount 32526 15 = 6 ∧ acceleratedOrbit 15 32526 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32526 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32526) = 3 ^ 6 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32526.1, data_15_32526.2]

/-- Complete interval computation for depth 15, residue 32527. -/
theorem bounds_15_32527 : exactInterval 15 32527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32527 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32527) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32527 : oddCount 32527 15 = 6 ∧ acceleratedOrbit 15 32527 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32527 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32527) = 3 ^ 6 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32527.1, data_15_32527.2]

/-- Complete interval computation for depth 15, residue 32528. -/
theorem bounds_15_32528 : exactInterval 15 32528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32528 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32528) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32528 : oddCount 32528 15 = 6 ∧ acceleratedOrbit 15 32528 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32528 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32528) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32528.1, data_15_32528.2]

/-- Complete interval computation for depth 15, residue 32529. -/
theorem bounds_15_32529 : exactInterval 15 32529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32529 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32529) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32529 : oddCount 32529 15 = 9 ∧ acceleratedOrbit 15 32529 = 19547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32529 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32529) = 3 ^ 9 * m + 19547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32529.1, data_15_32529.2]

/-- Complete interval computation for depth 15, residue 32530. -/
theorem bounds_15_32530 : exactInterval 15 32530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32530 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32530) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32530 : oddCount 32530 15 = 9 ∧ acceleratedOrbit 15 32530 = 19543 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32530 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32530) = 3 ^ 9 * m + 19543 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32530.1, data_15_32530.2]

/-- Complete interval computation for depth 15, residue 32531. -/
theorem bounds_15_32531 : exactInterval 15 32531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32531 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32531) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32531 : oddCount 32531 15 = 9 ∧ acceleratedOrbit 15 32531 = 19543 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32531 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32531) = 3 ^ 9 * m + 19543 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32531.1, data_15_32531.2]

/-- Complete interval computation for depth 15, residue 32532. -/
theorem bounds_15_32532 : exactInterval 15 32532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32532 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32532) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32532 : oddCount 32532 15 = 6 ∧ acceleratedOrbit 15 32532 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32532 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32532) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32532.1, data_15_32532.2]

/-- Complete interval computation for depth 15, residue 32533. -/
theorem bounds_15_32533 : exactInterval 15 32533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32533 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32533) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32533 : oddCount 32533 15 = 6 ∧ acceleratedOrbit 15 32533 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32533 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32533) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32533.1, data_15_32533.2]

/-- Complete interval computation for depth 15, residue 32534. -/
theorem bounds_15_32534 : exactInterval 15 32534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32534 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32534) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32534 : oddCount 32534 15 = 9 ∧ acceleratedOrbit 15 32534 = 19547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32534 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32534) = 3 ^ 9 * m + 19547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32534.1, data_15_32534.2]

/-- Complete interval computation for depth 15, residue 32535. -/
theorem bounds_15_32535 : exactInterval 15 32535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32535 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32535) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32535 : oddCount 32535 15 = 9 ∧ acceleratedOrbit 15 32535 = 19547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32535 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32535) = 3 ^ 9 * m + 19547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32535.1, data_15_32535.2]

/-- Complete interval computation for depth 15, residue 32536. -/
theorem bounds_15_32536 : exactInterval 15 32536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32536 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32536) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32536 : oddCount 32536 15 = 6 ∧ acceleratedOrbit 15 32536 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32536 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32536) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32536.1, data_15_32536.2]

/-- Complete interval computation for depth 15, residue 32537. -/
theorem bounds_15_32537 : exactInterval 15 32537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32537 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32537) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32537 : oddCount 32537 15 = 10 ∧ acceleratedOrbit 15 32537 = 58639 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32537 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32537) = 3 ^ 10 * m + 58639 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32537.1, data_15_32537.2]

end Collatz.Research.PassageAtlas.Batch0993
