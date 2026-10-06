import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0352

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 11501. -/
theorem bounds_15_11501 : exactInterval 15 11501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11501 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11501) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11501 : oddCount 11501 15 = 7 ∧ acceleratedOrbit 15 11501 = 769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11501 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11501) = 3 ^ 7 * m + 769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11501.1, data_15_11501.2]

/-- Complete interval computation for depth 15, residue 11502. -/
theorem bounds_15_11502 : exactInterval 15 11502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11502 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11502) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11502 : oddCount 11502 15 = 7 ∧ acceleratedOrbit 15 11502 = 769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11502 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11502) = 3 ^ 7 * m + 769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11502.1, data_15_11502.2]

/-- Complete interval computation for depth 15, residue 11503. -/
theorem bounds_15_11503 : exactInterval 15 11503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11503 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11503) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11503 : oddCount 11503 15 = 13 ∧ acceleratedOrbit 15 11503 = 559736 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11503 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11503) = 3 ^ 13 * m + 559736 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11503.1, data_15_11503.2]

/-- Complete interval computation for depth 15, residue 11504. -/
theorem bounds_15_11504 : exactInterval 15 11504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11504 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11504) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11504 : oddCount 11504 15 = 8 ∧ acceleratedOrbit 15 11504 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11504 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11504) = 3 ^ 8 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11504.1, data_15_11504.2]

/-- Complete interval computation for depth 15, residue 11505. -/
theorem bounds_15_11505 : exactInterval 15 11505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11505 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11505) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11505 : oddCount 11505 15 = 8 ∧ acceleratedOrbit 15 11505 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11505 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11505) = 3 ^ 8 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11505.1, data_15_11505.2]

/-- Complete interval computation for depth 15, residue 11506. -/
theorem bounds_15_11506 : exactInterval 15 11506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11506 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11506) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11506 : oddCount 11506 15 = 8 ∧ acceleratedOrbit 15 11506 = 2305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11506 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11506) = 3 ^ 8 * m + 2305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11506.1, data_15_11506.2]

/-- Complete interval computation for depth 15, residue 11507. -/
theorem bounds_15_11507 : exactInterval 15 11507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11507 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11507) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11507 : oddCount 11507 15 = 8 ∧ acceleratedOrbit 15 11507 = 2305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11507 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11507) = 3 ^ 8 * m + 2305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11507.1, data_15_11507.2]

/-- Complete interval computation for depth 15, residue 11508. -/
theorem bounds_15_11508 : exactInterval 15 11508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11508 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11508) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11508 : oddCount 11508 15 = 8 ∧ acceleratedOrbit 15 11508 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11508 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11508) = 3 ^ 8 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11508.1, data_15_11508.2]

/-- Complete interval computation for depth 15, residue 11509. -/
theorem bounds_15_11509 : exactInterval 15 11509 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11509 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11509) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11509 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11509 : oddCount 11509 15 = 8 ∧ acceleratedOrbit 15 11509 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11509 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11509) = 3 ^ 8 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11509.1, data_15_11509.2]

/-- Complete interval computation for depth 15, residue 11510. -/
theorem bounds_15_11510 : exactInterval 15 11510 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11510 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11510) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11510 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11510 : oddCount 11510 15 = 7 ∧ acceleratedOrbit 15 11510 = 769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11510 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11510) = 3 ^ 7 * m + 769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11510.1, data_15_11510.2]

/-- Complete interval computation for depth 15, residue 11511. -/
theorem bounds_15_11511 : exactInterval 15 11511 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11511 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11511) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11511 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11511 : oddCount 11511 15 = 7 ∧ acceleratedOrbit 15 11511 = 769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11511 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11511) = 3 ^ 7 * m + 769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11511.1, data_15_11511.2]

/-- Complete interval computation for depth 15, residue 11512. -/
theorem bounds_15_11512 : exactInterval 15 11512 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11512 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11512) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11512 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11512 : oddCount 11512 15 = 10 ∧ acceleratedOrbit 15 11512 = 20762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11512 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11512) = 3 ^ 10 * m + 20762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11512.1, data_15_11512.2]

/-- Complete interval computation for depth 15, residue 11513. -/
theorem bounds_15_11513 : exactInterval 15 11513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11513 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11513) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11513 : oddCount 11513 15 = 8 ∧ acceleratedOrbit 15 11513 = 2306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11513 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11513) = 3 ^ 8 * m + 2306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11513.1, data_15_11513.2]

/-- Complete interval computation for depth 15, residue 11514. -/
theorem bounds_15_11514 : exactInterval 15 11514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11514 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11514) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11514 : oddCount 11514 15 = 10 ∧ acceleratedOrbit 15 11514 = 20762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11514 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11514) = 3 ^ 10 * m + 20762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11514.1, data_15_11514.2]

/-- Complete interval computation for depth 15, residue 11515. -/
theorem bounds_15_11515 : exactInterval 15 11515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11515 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11515) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11515 : oddCount 11515 15 = 12 ∧ acceleratedOrbit 15 11515 = 186785 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11515 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11515) = 3 ^ 12 * m + 186785 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11515.1, data_15_11515.2]

/-- Complete interval computation for depth 15, residue 11516. -/
theorem bounds_15_11516 : exactInterval 15 11516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11516 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11516) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11516 : oddCount 11516 15 = 10 ∧ acceleratedOrbit 15 11516 = 20762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11516 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11516) = 3 ^ 10 * m + 20762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11516.1, data_15_11516.2]

/-- Complete interval computation for depth 15, residue 11517. -/
theorem bounds_15_11517 : exactInterval 15 11517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11517 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11517) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11517 : oddCount 11517 15 = 10 ∧ acceleratedOrbit 15 11517 = 20762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11517 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11517) = 3 ^ 10 * m + 20762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11517.1, data_15_11517.2]

/-- Complete interval computation for depth 15, residue 11518. -/
theorem bounds_15_11518 : exactInterval 15 11518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11518 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11518) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11518 : oddCount 11518 15 = 11 ∧ acceleratedOrbit 15 11518 = 62279 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11518 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11518) = 3 ^ 11 * m + 62279 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11518.1, data_15_11518.2]

/-- Complete interval computation for depth 15, residue 11519. -/
theorem bounds_15_11519 : exactInterval 15 11519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11519 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11519) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11519 : oddCount 11519 15 = 11 ∧ acceleratedOrbit 15 11519 = 62279 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11519 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11519) = 3 ^ 11 * m + 62279 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11519.1, data_15_11519.2]

/-- Complete interval computation for depth 15, residue 11520. -/
theorem bounds_15_11520 : exactInterval 15 11520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11520 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11520) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11520 : oddCount 11520 15 = 3 ∧ acceleratedOrbit 15 11520 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11520 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11520) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11520.1, data_15_11520.2]

/-- Complete interval computation for depth 15, residue 11521. -/
theorem bounds_15_11521 : exactInterval 15 11521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11521 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11521) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11521 : oddCount 11521 15 = 9 ∧ acceleratedOrbit 15 11521 = 6925 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11521 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11521) = 3 ^ 9 * m + 6925 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11521.1, data_15_11521.2]

/-- Complete interval computation for depth 15, residue 11522. -/
theorem bounds_15_11522 : exactInterval 15 11522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11522 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11522) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11522 : oddCount 11522 15 = 10 ∧ acceleratedOrbit 15 11522 = 20776 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11522 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11522) = 3 ^ 10 * m + 20776 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11522.1, data_15_11522.2]

/-- Complete interval computation for depth 15, residue 11523. -/
theorem bounds_15_11523 : exactInterval 15 11523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11523 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11523) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11523 : oddCount 11523 15 = 10 ∧ acceleratedOrbit 15 11523 = 20776 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11523 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11523) = 3 ^ 10 * m + 20776 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11523.1, data_15_11523.2]

/-- Complete interval computation for depth 15, residue 11524. -/
theorem bounds_15_11524 : exactInterval 15 11524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11524 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11524) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11524 : oddCount 11524 15 = 4 ∧ acceleratedOrbit 15 11524 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11524 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11524) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11524.1, data_15_11524.2]

/-- Complete interval computation for depth 15, residue 11525. -/
theorem bounds_15_11525 : exactInterval 15 11525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11525 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11525) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11525 : oddCount 11525 15 = 4 ∧ acceleratedOrbit 15 11525 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11525 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11525) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11525.1, data_15_11525.2]

/-- Complete interval computation for depth 15, residue 11526. -/
theorem bounds_15_11526 : exactInterval 15 11526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11526 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11526) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11526 : oddCount 11526 15 = 4 ∧ acceleratedOrbit 15 11526 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11526 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11526) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11526.1, data_15_11526.2]

/-- Complete interval computation for depth 15, residue 11527. -/
theorem bounds_15_11527 : exactInterval 15 11527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11527 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11527) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11527 : oddCount 11527 15 = 11 ∧ acceleratedOrbit 15 11527 = 62329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11527 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11527) = 3 ^ 11 * m + 62329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11527.1, data_15_11527.2]

/-- Complete interval computation for depth 15, residue 11528. -/
theorem bounds_15_11528 : exactInterval 15 11528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11528 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11528) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11528 : oddCount 11528 15 = 6 ∧ acceleratedOrbit 15 11528 = 257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11528 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11528) = 3 ^ 6 * m + 257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11528.1, data_15_11528.2]

/-- Complete interval computation for depth 15, residue 11529. -/
theorem bounds_15_11529 : exactInterval 15 11529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11529 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11529) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11529 : oddCount 11529 15 = 8 ∧ acceleratedOrbit 15 11529 = 2309 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11529 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11529) = 3 ^ 8 * m + 2309 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11529.1, data_15_11529.2]

/-- Complete interval computation for depth 15, residue 11530. -/
theorem bounds_15_11530 : exactInterval 15 11530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11530 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11530) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11530 : oddCount 11530 15 = 6 ∧ acceleratedOrbit 15 11530 = 257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11530 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11530) = 3 ^ 6 * m + 257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11530.1, data_15_11530.2]

/-- Complete interval computation for depth 15, residue 11531. -/
theorem bounds_15_11531 : exactInterval 15 11531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11531 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11531) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11531 : oddCount 11531 15 = 7 ∧ acceleratedOrbit 15 11531 = 770 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11531 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11531) = 3 ^ 7 * m + 770 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11531.1, data_15_11531.2]

/-- Complete interval computation for depth 15, residue 11532. -/
theorem bounds_15_11532 : exactInterval 15 11532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11532 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11532) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11532 : oddCount 11532 15 = 6 ∧ acceleratedOrbit 15 11532 = 257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11532 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11532) = 3 ^ 6 * m + 257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11532.1, data_15_11532.2]

/-- Complete interval computation for depth 15, residue 11533. -/
theorem bounds_15_11533 : exactInterval 15 11533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11533 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11533) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11533 : oddCount 11533 15 = 6 ∧ acceleratedOrbit 15 11533 = 257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11533 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11533) = 3 ^ 6 * m + 257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11533.1, data_15_11533.2]

end Collatz.Research.PassageAtlas.Batch0352
