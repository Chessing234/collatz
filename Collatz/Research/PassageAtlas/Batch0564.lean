import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0564

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 18448. -/
theorem bounds_15_18448 : exactInterval 15 18448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18448 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18448) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18448 : oddCount 18448 15 = 7 ∧ acceleratedOrbit 15 18448 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18448 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18448) = 3 ^ 7 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18448.1, data_15_18448.2]

/-- Complete interval computation for depth 15, residue 18449. -/
theorem bounds_15_18449 : exactInterval 15 18449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18449 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18449) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18449 : oddCount 18449 15 = 5 ∧ acceleratedOrbit 15 18449 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18449 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18449) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18449.1, data_15_18449.2]

/-- Complete interval computation for depth 15, residue 18450. -/
theorem bounds_15_18450 : exactInterval 15 18450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18450 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18450) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18450 : oddCount 18450 15 = 9 ∧ acceleratedOrbit 15 18450 = 11087 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18450 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18450) = 3 ^ 9 * m + 11087 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18450.1, data_15_18450.2]

/-- Complete interval computation for depth 15, residue 18451. -/
theorem bounds_15_18451 : exactInterval 15 18451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18451 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18451) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18451 : oddCount 18451 15 = 9 ∧ acceleratedOrbit 15 18451 = 11087 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18451 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18451) = 3 ^ 9 * m + 11087 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18451.1, data_15_18451.2]

/-- Complete interval computation for depth 15, residue 18452. -/
theorem bounds_15_18452 : exactInterval 15 18452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18452 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18452) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18452 : oddCount 18452 15 = 7 ∧ acceleratedOrbit 15 18452 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18452 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18452) = 3 ^ 7 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18452.1, data_15_18452.2]

/-- Complete interval computation for depth 15, residue 18453. -/
theorem bounds_15_18453 : exactInterval 15 18453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18453 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18453) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18453 : oddCount 18453 15 = 7 ∧ acceleratedOrbit 15 18453 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18453 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18453) = 3 ^ 7 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18453.1, data_15_18453.2]

/-- Complete interval computation for depth 15, residue 18454. -/
theorem bounds_15_18454 : exactInterval 15 18454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18454 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18454) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18454 : oddCount 18454 15 = 5 ∧ acceleratedOrbit 15 18454 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18454 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18454) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18454.1, data_15_18454.2]

/-- Complete interval computation for depth 15, residue 18455. -/
theorem bounds_15_18455 : exactInterval 15 18455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18455 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18455) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18455 : oddCount 18455 15 = 5 ∧ acceleratedOrbit 15 18455 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18455 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18455) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18455.1, data_15_18455.2]

/-- Complete interval computation for depth 15, residue 18456. -/
theorem bounds_15_18456 : exactInterval 15 18456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18456 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18456) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18456 : oddCount 18456 15 = 7 ∧ acceleratedOrbit 15 18456 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18456 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18456) = 3 ^ 7 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18456.1, data_15_18456.2]

/-- Complete interval computation for depth 15, residue 18457. -/
theorem bounds_15_18457 : exactInterval 15 18457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18457 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18457) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18457 : oddCount 18457 15 = 9 ∧ acceleratedOrbit 15 18457 = 11090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18457 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18457) = 3 ^ 9 * m + 11090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18457.1, data_15_18457.2]

/-- Complete interval computation for depth 15, residue 18458. -/
theorem bounds_15_18458 : exactInterval 15 18458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18458 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18458) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18458 : oddCount 18458 15 = 7 ∧ acceleratedOrbit 15 18458 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18458 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18458) = 3 ^ 7 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18458.1, data_15_18458.2]

/-- Complete interval computation for depth 15, residue 18459. -/
theorem bounds_15_18459 : exactInterval 15 18459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18459 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18459) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18459 : oddCount 18459 15 = 9 ∧ acceleratedOrbit 15 18459 = 11089 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18459 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18459) = 3 ^ 9 * m + 11089 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18459.1, data_15_18459.2]

/-- Complete interval computation for depth 15, residue 18460. -/
theorem bounds_15_18460 : exactInterval 15 18460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18460 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18460) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18460 : oddCount 18460 15 = 9 ∧ acceleratedOrbit 15 18460 = 11096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18460 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18460) = 3 ^ 9 * m + 11096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18460.1, data_15_18460.2]

/-- Complete interval computation for depth 15, residue 18461. -/
theorem bounds_15_18461 : exactInterval 15 18461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18461 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18461) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18461 : oddCount 18461 15 = 9 ∧ acceleratedOrbit 15 18461 = 11096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18461 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18461) = 3 ^ 9 * m + 11096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18461.1, data_15_18461.2]

/-- Complete interval computation for depth 15, residue 18462. -/
theorem bounds_15_18462 : exactInterval 15 18462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18462 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18462) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18462 : oddCount 18462 15 = 9 ∧ acceleratedOrbit 15 18462 = 11096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18462 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18462) = 3 ^ 9 * m + 11096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18462.1, data_15_18462.2]

/-- Complete interval computation for depth 15, residue 18463. -/
theorem bounds_15_18463 : exactInterval 15 18463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18463 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18463) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18463 : oddCount 18463 15 = 8 ∧ acceleratedOrbit 15 18463 = 3697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18463 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18463) = 3 ^ 8 * m + 3697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18463.1, data_15_18463.2]

/-- Complete interval computation for depth 15, residue 18464. -/
theorem bounds_15_18464 : exactInterval 15 18464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18464 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18464) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18464 : oddCount 18464 15 = 4 ∧ acceleratedOrbit 15 18464 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18464 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18464) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18464.1, data_15_18464.2]

/-- Complete interval computation for depth 15, residue 18465. -/
theorem bounds_15_18465 : exactInterval 15 18465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18465 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18465) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18465 : oddCount 18465 15 = 9 ∧ acceleratedOrbit 15 18465 = 11096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18465 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18465) = 3 ^ 9 * m + 11096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18465.1, data_15_18465.2]

/-- Complete interval computation for depth 15, residue 18466. -/
theorem bounds_15_18466 : exactInterval 15 18466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18466 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18466) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18466 : oddCount 18466 15 = 7 ∧ acceleratedOrbit 15 18466 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18466 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18466) = 3 ^ 7 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18466.1, data_15_18466.2]

/-- Complete interval computation for depth 15, residue 18467. -/
theorem bounds_15_18467 : exactInterval 15 18467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18467 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18467) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18467 : oddCount 18467 15 = 7 ∧ acceleratedOrbit 15 18467 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18467 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18467) = 3 ^ 7 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18467.1, data_15_18467.2]

/-- Complete interval computation for depth 15, residue 18468. -/
theorem bounds_15_18468 : exactInterval 15 18468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18468 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18468) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18468 : oddCount 18468 15 = 5 ∧ acceleratedOrbit 15 18468 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18468 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18468) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18468.1, data_15_18468.2]

/-- Complete interval computation for depth 15, residue 18469. -/
theorem bounds_15_18469 : exactInterval 15 18469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18469 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18469) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18469 : oddCount 18469 15 = 5 ∧ acceleratedOrbit 15 18469 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18469 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18469) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18469.1, data_15_18469.2]

/-- Complete interval computation for depth 15, residue 18470. -/
theorem bounds_15_18470 : exactInterval 15 18470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18470 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18470) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18470 : oddCount 18470 15 = 5 ∧ acceleratedOrbit 15 18470 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18470 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18470) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18470.1, data_15_18470.2]

/-- Complete interval computation for depth 15, residue 18471. -/
theorem bounds_15_18471 : exactInterval 15 18471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18471 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18471) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18471 : oddCount 18471 15 = 11 ∧ acceleratedOrbit 15 18471 = 99872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18471 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18471) = 3 ^ 11 * m + 99872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18471.1, data_15_18471.2]

/-- Complete interval computation for depth 15, residue 18472. -/
theorem bounds_15_18472 : exactInterval 15 18472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18472 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18472) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18472 : oddCount 18472 15 = 4 ∧ acceleratedOrbit 15 18472 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18472 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18472) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18472.1, data_15_18472.2]

/-- Complete interval computation for depth 15, residue 18473. -/
theorem bounds_15_18473 : exactInterval 15 18473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18473 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18473) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18473 : oddCount 18473 15 = 10 ∧ acceleratedOrbit 15 18473 = 33293 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18473 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18473) = 3 ^ 10 * m + 33293 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18473.1, data_15_18473.2]

/-- Complete interval computation for depth 15, residue 18474. -/
theorem bounds_15_18474 : exactInterval 15 18474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18474 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18474) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18474 : oddCount 18474 15 = 4 ∧ acceleratedOrbit 15 18474 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18474 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18474) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18474.1, data_15_18474.2]

/-- Complete interval computation for depth 15, residue 18475. -/
theorem bounds_15_18475 : exactInterval 15 18475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18475 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18475) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18475 : oddCount 18475 15 = 8 ∧ acceleratedOrbit 15 18475 = 3701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18475 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18475) = 3 ^ 8 * m + 3701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18475.1, data_15_18475.2]

/-- Complete interval computation for depth 15, residue 18476. -/
theorem bounds_15_18476 : exactInterval 15 18476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18476 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18476) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18476 : oddCount 18476 15 = 7 ∧ acceleratedOrbit 15 18476 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18476 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18476) = 3 ^ 7 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18476.1, data_15_18476.2]

/-- Complete interval computation for depth 15, residue 18477. -/
theorem bounds_15_18477 : exactInterval 15 18477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18477 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18477) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18477 : oddCount 18477 15 = 7 ∧ acceleratedOrbit 15 18477 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18477 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18477) = 3 ^ 7 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18477.1, data_15_18477.2]

/-- Complete interval computation for depth 15, residue 18478. -/
theorem bounds_15_18478 : exactInterval 15 18478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18478 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18478) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18478 : oddCount 18478 15 = 7 ∧ acceleratedOrbit 15 18478 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18478 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18478) = 3 ^ 7 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18478.1, data_15_18478.2]

/-- Complete interval computation for depth 15, residue 18479. -/
theorem bounds_15_18479 : exactInterval 15 18479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18479 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18479) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18479 : oddCount 18479 15 = 9 ∧ acceleratedOrbit 15 18479 = 11101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18479 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18479) = 3 ^ 9 * m + 11101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18479.1, data_15_18479.2]

/-- Complete interval computation for depth 15, residue 18480. -/
theorem bounds_15_18480 : exactInterval 15 18480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18480 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18480) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18480 : oddCount 18480 15 = 4 ∧ acceleratedOrbit 15 18480 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18480 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18480) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18480.1, data_15_18480.2]

end Collatz.Research.PassageAtlas.Batch0564
