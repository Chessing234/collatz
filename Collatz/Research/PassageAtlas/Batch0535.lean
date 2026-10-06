import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0535

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 17498. -/
theorem bounds_15_17498 : exactInterval 15 17498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17498 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17498) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17498 : oddCount 17498 15 = 8 ∧ acceleratedOrbit 15 17498 = 3509 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17498 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17498) = 3 ^ 8 * m + 3509 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17498.1, data_15_17498.2]

/-- Complete interval computation for depth 15, residue 17499. -/
theorem bounds_15_17499 : exactInterval 15 17499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17499 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17499) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17499 : oddCount 17499 15 = 10 ∧ acceleratedOrbit 15 17499 = 31537 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17499 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17499) = 3 ^ 10 * m + 31537 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17499.1, data_15_17499.2]

/-- Complete interval computation for depth 15, residue 17500. -/
theorem bounds_15_17500 : exactInterval 15 17500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17500 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17500) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17500 : oddCount 17500 15 = 8 ∧ acceleratedOrbit 15 17500 = 3509 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17500 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17500) = 3 ^ 8 * m + 3509 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17500.1, data_15_17500.2]

/-- Complete interval computation for depth 15, residue 17501. -/
theorem bounds_15_17501 : exactInterval 15 17501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17501 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17501) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17501 : oddCount 17501 15 = 8 ∧ acceleratedOrbit 15 17501 = 3509 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17501 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17501) = 3 ^ 8 * m + 3509 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17501.1, data_15_17501.2]

/-- Complete interval computation for depth 15, residue 17502. -/
theorem bounds_15_17502 : exactInterval 15 17502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17502 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17502) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17502 : oddCount 17502 15 = 11 ∧ acceleratedOrbit 15 17502 = 94634 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17502 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17502) = 3 ^ 11 * m + 94634 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17502.1, data_15_17502.2]

/-- Complete interval computation for depth 15, residue 17503. -/
theorem bounds_15_17503 : exactInterval 15 17503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17503 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17503) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17503 : oddCount 17503 15 = 11 ∧ acceleratedOrbit 15 17503 = 94634 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17503 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17503) = 3 ^ 11 * m + 94634 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17503.1, data_15_17503.2]

/-- Complete interval computation for depth 15, residue 17504. -/
theorem bounds_15_17504 : exactInterval 15 17504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17504 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17504) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17504 : oddCount 17504 15 = 4 ∧ acceleratedOrbit 15 17504 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17504 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17504) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17504.1, data_15_17504.2]

/-- Complete interval computation for depth 15, residue 17505. -/
theorem bounds_15_17505 : exactInterval 15 17505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17505 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17505) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17505 : oddCount 17505 15 = 7 ∧ acceleratedOrbit 15 17505 = 1169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17505 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17505) = 3 ^ 7 * m + 1169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17505.1, data_15_17505.2]

/-- Complete interval computation for depth 15, residue 17506. -/
theorem bounds_15_17506 : exactInterval 15 17506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17506 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17506) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17506 : oddCount 17506 15 = 8 ∧ acceleratedOrbit 15 17506 = 3509 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17506 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17506) = 3 ^ 8 * m + 3509 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17506.1, data_15_17506.2]

/-- Complete interval computation for depth 15, residue 17507. -/
theorem bounds_15_17507 : exactInterval 15 17507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17507 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17507) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17507 : oddCount 17507 15 = 8 ∧ acceleratedOrbit 15 17507 = 3509 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17507 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17507) = 3 ^ 8 * m + 3509 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17507.1, data_15_17507.2]

/-- Complete interval computation for depth 15, residue 17508. -/
theorem bounds_15_17508 : exactInterval 15 17508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17508 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17508) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17508 : oddCount 17508 15 = 8 ∧ acceleratedOrbit 15 17508 = 3509 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17508 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17508) = 3 ^ 8 * m + 3509 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17508.1, data_15_17508.2]

/-- Complete interval computation for depth 15, residue 17509. -/
theorem bounds_15_17509 : exactInterval 15 17509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17509 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17509) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17509 : oddCount 17509 15 = 8 ∧ acceleratedOrbit 15 17509 = 3509 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17509 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17509) = 3 ^ 8 * m + 3509 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17509.1, data_15_17509.2]

/-- Complete interval computation for depth 15, residue 17510. -/
theorem bounds_15_17510 : exactInterval 15 17510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17510 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17510) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17510 : oddCount 17510 15 = 8 ∧ acceleratedOrbit 15 17510 = 3509 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17510 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17510) = 3 ^ 8 * m + 3509 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17510.1, data_15_17510.2]

/-- Complete interval computation for depth 15, residue 17511. -/
theorem bounds_15_17511 : exactInterval 15 17511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17511 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17511) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17511 : oddCount 17511 15 = 10 ∧ acceleratedOrbit 15 17511 = 31558 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17511 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17511) = 3 ^ 10 * m + 31558 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17511.1, data_15_17511.2]

/-- Complete interval computation for depth 15, residue 17512. -/
theorem bounds_15_17512 : exactInterval 15 17512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17512 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17512) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17512 : oddCount 17512 15 = 4 ∧ acceleratedOrbit 15 17512 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17512 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17512) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17512.1, data_15_17512.2]

/-- Complete interval computation for depth 15, residue 17513. -/
theorem bounds_15_17513 : exactInterval 15 17513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17513 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17513) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17513 : oddCount 17513 15 = 7 ∧ acceleratedOrbit 15 17513 = 1169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17513 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17513) = 3 ^ 7 * m + 1169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17513.1, data_15_17513.2]

/-- Complete interval computation for depth 15, residue 17514. -/
theorem bounds_15_17514 : exactInterval 15 17514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17514 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17514) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17514 : oddCount 17514 15 = 4 ∧ acceleratedOrbit 15 17514 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17514 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17514) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17514.1, data_15_17514.2]

/-- Complete interval computation for depth 15, residue 17515. -/
theorem bounds_15_17515 : exactInterval 15 17515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17515 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17515) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17515 : oddCount 17515 15 = 9 ∧ acceleratedOrbit 15 17515 = 10523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17515 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17515) = 3 ^ 9 * m + 10523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17515.1, data_15_17515.2]

/-- Complete interval computation for depth 15, residue 17516. -/
theorem bounds_15_17516 : exactInterval 15 17516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17516 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17516) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17516 : oddCount 17516 15 = 9 ∧ acceleratedOrbit 15 17516 = 10525 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17516 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17516) = 3 ^ 9 * m + 10525 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17516.1, data_15_17516.2]

/-- Complete interval computation for depth 15, residue 17517. -/
theorem bounds_15_17517 : exactInterval 15 17517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17517 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17517) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17517 : oddCount 17517 15 = 9 ∧ acceleratedOrbit 15 17517 = 10525 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17517 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17517) = 3 ^ 9 * m + 10525 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17517.1, data_15_17517.2]

/-- Complete interval computation for depth 15, residue 17518. -/
theorem bounds_15_17518 : exactInterval 15 17518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17518 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17518) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17518 : oddCount 17518 15 = 9 ∧ acceleratedOrbit 15 17518 = 10525 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17518 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17518) = 3 ^ 9 * m + 10525 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17518.1, data_15_17518.2]

/-- Complete interval computation for depth 15, residue 17519. -/
theorem bounds_15_17519 : exactInterval 15 17519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17519 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17519) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17519 : oddCount 17519 15 = 8 ∧ acceleratedOrbit 15 17519 = 3508 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17519 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17519) = 3 ^ 8 * m + 3508 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17519.1, data_15_17519.2]

/-- Complete interval computation for depth 15, residue 17520. -/
theorem bounds_15_17520 : exactInterval 15 17520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17520 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17520) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17520 : oddCount 17520 15 = 7 ∧ acceleratedOrbit 15 17520 = 1171 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17520 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17520) = 3 ^ 7 * m + 1171 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17520.1, data_15_17520.2]

/-- Complete interval computation for depth 15, residue 17521. -/
theorem bounds_15_17521 : exactInterval 15 17521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17521 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17521) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17521 : oddCount 17521 15 = 4 ∧ acceleratedOrbit 15 17521 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17521 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17521) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17521.1, data_15_17521.2]

/-- Complete interval computation for depth 15, residue 17522. -/
theorem bounds_15_17522 : exactInterval 15 17522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17522 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17522) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17522 : oddCount 17522 15 = 10 ∧ acceleratedOrbit 15 17522 = 31589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17522 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17522) = 3 ^ 10 * m + 31589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17522.1, data_15_17522.2]

/-- Complete interval computation for depth 15, residue 17523. -/
theorem bounds_15_17523 : exactInterval 15 17523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17523 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17523) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17523 : oddCount 17523 15 = 10 ∧ acceleratedOrbit 15 17523 = 31589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17523 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17523) = 3 ^ 10 * m + 31589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17523.1, data_15_17523.2]

/-- Complete interval computation for depth 15, residue 17524. -/
theorem bounds_15_17524 : exactInterval 15 17524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17524 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17524) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17524 : oddCount 17524 15 = 7 ∧ acceleratedOrbit 15 17524 = 1171 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17524 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17524) = 3 ^ 7 * m + 1171 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17524.1, data_15_17524.2]

/-- Complete interval computation for depth 15, residue 17525. -/
theorem bounds_15_17525 : exactInterval 15 17525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17525 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17525) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17525 : oddCount 17525 15 = 7 ∧ acceleratedOrbit 15 17525 = 1171 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17525 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17525) = 3 ^ 7 * m + 1171 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17525.1, data_15_17525.2]

/-- Complete interval computation for depth 15, residue 17526. -/
theorem bounds_15_17526 : exactInterval 15 17526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17526 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17526) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17526 : oddCount 17526 15 = 5 ∧ acceleratedOrbit 15 17526 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17526 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17526) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17526.1, data_15_17526.2]

/-- Complete interval computation for depth 15, residue 17527. -/
theorem bounds_15_17527 : exactInterval 15 17527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17527 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17527) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17527 : oddCount 17527 15 = 5 ∧ acceleratedOrbit 15 17527 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17527 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17527) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17527.1, data_15_17527.2]

/-- Complete interval computation for depth 15, residue 17528. -/
theorem bounds_15_17528 : exactInterval 15 17528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17528 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17528) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17528 : oddCount 17528 15 = 7 ∧ acceleratedOrbit 15 17528 = 1171 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17528 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17528) = 3 ^ 7 * m + 1171 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17528.1, data_15_17528.2]

/-- Complete interval computation for depth 15, residue 17529. -/
theorem bounds_15_17529 : exactInterval 15 17529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17529 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17529) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17529 : oddCount 17529 15 = 9 ∧ acceleratedOrbit 15 17529 = 10531 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17529 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17529) = 3 ^ 9 * m + 10531 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17529.1, data_15_17529.2]

end Collatz.Research.PassageAtlas.Batch0535
