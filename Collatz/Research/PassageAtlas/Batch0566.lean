import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0566

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 18513. -/
theorem bounds_15_18513 : exactInterval 15 18513 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18513 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18513) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18513 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18513 : oddCount 18513 15 = 6 ∧ acceleratedOrbit 15 18513 = 412 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18513 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18513) = 3 ^ 6 * m + 412 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18513.1, data_15_18513.2]

/-- Complete interval computation for depth 15, residue 18514. -/
theorem bounds_15_18514 : exactInterval 15 18514 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18514 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18514) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18514 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18514 : oddCount 18514 15 = 10 ∧ acceleratedOrbit 15 18514 = 33371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18514 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18514) = 3 ^ 10 * m + 33371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18514.1, data_15_18514.2]

/-- Complete interval computation for depth 15, residue 18515. -/
theorem bounds_15_18515 : exactInterval 15 18515 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18515 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18515) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18515 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18515 : oddCount 18515 15 = 10 ∧ acceleratedOrbit 15 18515 = 33371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18515 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18515) = 3 ^ 10 * m + 33371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18515.1, data_15_18515.2]

/-- Complete interval computation for depth 15, residue 18516. -/
theorem bounds_15_18516 : exactInterval 15 18516 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18516 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18516) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18516 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18516 : oddCount 18516 15 = 4 ∧ acceleratedOrbit 15 18516 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18516 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18516) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18516.1, data_15_18516.2]

/-- Complete interval computation for depth 15, residue 18517. -/
theorem bounds_15_18517 : exactInterval 15 18517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18517 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18517) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18517 : oddCount 18517 15 = 4 ∧ acceleratedOrbit 15 18517 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18517 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18517) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18517.1, data_15_18517.2]

/-- Complete interval computation for depth 15, residue 18518. -/
theorem bounds_15_18518 : exactInterval 15 18518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18518 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18518) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18518 : oddCount 18518 15 = 7 ∧ acceleratedOrbit 15 18518 = 1237 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18518 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18518) = 3 ^ 7 * m + 1237 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18518.1, data_15_18518.2]

/-- Complete interval computation for depth 15, residue 18519. -/
theorem bounds_15_18519 : exactInterval 15 18519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18519 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18519) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18519 : oddCount 18519 15 = 7 ∧ acceleratedOrbit 15 18519 = 1237 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18519 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18519) = 3 ^ 7 * m + 1237 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18519.1, data_15_18519.2]

/-- Complete interval computation for depth 15, residue 18520. -/
theorem bounds_15_18520 : exactInterval 15 18520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18520 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18520) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18520 : oddCount 18520 15 = 6 ∧ acceleratedOrbit 15 18520 = 413 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18520 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18520) = 3 ^ 6 * m + 413 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18520.1, data_15_18520.2]

/-- Complete interval computation for depth 15, residue 18521. -/
theorem bounds_15_18521 : exactInterval 15 18521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18521 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18521) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18521 : oddCount 18521 15 = 7 ∧ acceleratedOrbit 15 18521 = 1237 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18521 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18521) = 3 ^ 7 * m + 1237 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18521.1, data_15_18521.2]

/-- Complete interval computation for depth 15, residue 18522. -/
theorem bounds_15_18522 : exactInterval 15 18522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18522 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18522) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18522 : oddCount 18522 15 = 6 ∧ acceleratedOrbit 15 18522 = 413 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18522 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18522) = 3 ^ 6 * m + 413 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18522.1, data_15_18522.2]

/-- Complete interval computation for depth 15, residue 18523. -/
theorem bounds_15_18523 : exactInterval 15 18523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18523 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18523) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18523 : oddCount 18523 15 = 10 ∧ acceleratedOrbit 15 18523 = 33382 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18523 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18523) = 3 ^ 10 * m + 33382 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18523.1, data_15_18523.2]

/-- Complete interval computation for depth 15, residue 18524. -/
theorem bounds_15_18524 : exactInterval 15 18524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18524 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18524) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18524 : oddCount 18524 15 = 6 ∧ acceleratedOrbit 15 18524 = 413 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18524 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18524) = 3 ^ 6 * m + 413 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18524.1, data_15_18524.2]

/-- Complete interval computation for depth 15, residue 18525. -/
theorem bounds_15_18525 : exactInterval 15 18525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18525 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18525) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18525 : oddCount 18525 15 = 6 ∧ acceleratedOrbit 15 18525 = 413 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18525 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18525) = 3 ^ 6 * m + 413 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18525.1, data_15_18525.2]

/-- Complete interval computation for depth 15, residue 18526. -/
theorem bounds_15_18526 : exactInterval 15 18526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18526 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18526) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18526 : oddCount 18526 15 = 8 ∧ acceleratedOrbit 15 18526 = 3710 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18526 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18526) = 3 ^ 8 * m + 3710 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18526.1, data_15_18526.2]

/-- Complete interval computation for depth 15, residue 18527. -/
theorem bounds_15_18527 : exactInterval 15 18527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18527 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18527) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18527 : oddCount 18527 15 = 8 ∧ acceleratedOrbit 15 18527 = 3710 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18527 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18527) = 3 ^ 8 * m + 3710 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18527.1, data_15_18527.2]

/-- Complete interval computation for depth 15, residue 18528. -/
theorem bounds_15_18528 : exactInterval 15 18528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18528 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18528) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18528 : oddCount 18528 15 = 4 ∧ acceleratedOrbit 15 18528 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18528 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18528) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18528.1, data_15_18528.2]

/-- Complete interval computation for depth 15, residue 18529. -/
theorem bounds_15_18529 : exactInterval 15 18529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18529 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18529) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18529 : oddCount 18529 15 = 10 ∧ acceleratedOrbit 15 18529 = 33398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18529 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18529) = 3 ^ 10 * m + 33398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18529.1, data_15_18529.2]

/-- Complete interval computation for depth 15, residue 18530. -/
theorem bounds_15_18530 : exactInterval 15 18530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18530 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18530) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18530 : oddCount 18530 15 = 6 ∧ acceleratedOrbit 15 18530 = 413 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18530 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18530) = 3 ^ 6 * m + 413 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18530.1, data_15_18530.2]

/-- Complete interval computation for depth 15, residue 18531. -/
theorem bounds_15_18531 : exactInterval 15 18531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18531 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18531) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18531 : oddCount 18531 15 = 6 ∧ acceleratedOrbit 15 18531 = 413 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18531 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18531) = 3 ^ 6 * m + 413 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18531.1, data_15_18531.2]

/-- Complete interval computation for depth 15, residue 18532. -/
theorem bounds_15_18532 : exactInterval 15 18532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18532 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18532) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18532 : oddCount 18532 15 = 6 ∧ acceleratedOrbit 15 18532 = 413 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18532 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18532) = 3 ^ 6 * m + 413 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18532.1, data_15_18532.2]

/-- Complete interval computation for depth 15, residue 18533. -/
theorem bounds_15_18533 : exactInterval 15 18533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18533 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18533) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18533 : oddCount 18533 15 = 6 ∧ acceleratedOrbit 15 18533 = 413 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18533 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18533) = 3 ^ 6 * m + 413 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18533.1, data_15_18533.2]

/-- Complete interval computation for depth 15, residue 18534. -/
theorem bounds_15_18534 : exactInterval 15 18534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18534 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18534) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18534 : oddCount 18534 15 = 6 ∧ acceleratedOrbit 15 18534 = 413 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18534 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18534) = 3 ^ 6 * m + 413 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18534.1, data_15_18534.2]

/-- Complete interval computation for depth 15, residue 18535. -/
theorem bounds_15_18535 : exactInterval 15 18535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18535 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18535) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18535 : oddCount 18535 15 = 11 ∧ acceleratedOrbit 15 18535 = 100210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18535 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18535) = 3 ^ 11 * m + 100210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18535.1, data_15_18535.2]

/-- Complete interval computation for depth 15, residue 18536. -/
theorem bounds_15_18536 : exactInterval 15 18536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18536 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18536) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18536 : oddCount 18536 15 = 4 ∧ acceleratedOrbit 15 18536 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18536 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18536) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18536.1, data_15_18536.2]

/-- Complete interval computation for depth 15, residue 18537. -/
theorem bounds_15_18537 : exactInterval 15 18537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18537 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18537) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18537 : oddCount 18537 15 = 9 ∧ acceleratedOrbit 15 18537 = 11137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18537 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18537) = 3 ^ 9 * m + 11137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18537.1, data_15_18537.2]

/-- Complete interval computation for depth 15, residue 18538. -/
theorem bounds_15_18538 : exactInterval 15 18538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18538 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18538) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18538 : oddCount 18538 15 = 4 ∧ acceleratedOrbit 15 18538 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18538 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18538) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18538.1, data_15_18538.2]

/-- Complete interval computation for depth 15, residue 18539. -/
theorem bounds_15_18539 : exactInterval 15 18539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18539 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18539) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18539 : oddCount 18539 15 = 11 ∧ acceleratedOrbit 15 18539 = 100237 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18539 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18539) = 3 ^ 11 * m + 100237 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18539.1, data_15_18539.2]

/-- Complete interval computation for depth 15, residue 18540. -/
theorem bounds_15_18540 : exactInterval 15 18540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18540 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18540) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18540 : oddCount 18540 15 = 9 ∧ acceleratedOrbit 15 18540 = 11141 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18540 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18540) = 3 ^ 9 * m + 11141 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18540.1, data_15_18540.2]

/-- Complete interval computation for depth 15, residue 18541. -/
theorem bounds_15_18541 : exactInterval 15 18541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18541 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18541) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18541 : oddCount 18541 15 = 9 ∧ acceleratedOrbit 15 18541 = 11141 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18541 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18541) = 3 ^ 9 * m + 11141 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18541.1, data_15_18541.2]

/-- Complete interval computation for depth 15, residue 18542. -/
theorem bounds_15_18542 : exactInterval 15 18542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18542 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18542) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18542 : oddCount 18542 15 = 9 ∧ acceleratedOrbit 15 18542 = 11141 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18542 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18542) = 3 ^ 9 * m + 11141 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18542.1, data_15_18542.2]

/-- Complete interval computation for depth 15, residue 18543. -/
theorem bounds_15_18543 : exactInterval 15 18543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18543 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18543) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18543 : oddCount 18543 15 = 11 ∧ acceleratedOrbit 15 18543 = 100253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18543 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18543) = 3 ^ 11 * m + 100253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18543.1, data_15_18543.2]

/-- Complete interval computation for depth 15, residue 18544. -/
theorem bounds_15_18544 : exactInterval 15 18544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18544 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18544) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18544 : oddCount 18544 15 = 7 ∧ acceleratedOrbit 15 18544 = 1241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18544 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18544) = 3 ^ 7 * m + 1241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18544.1, data_15_18544.2]

/-- Complete interval computation for depth 15, residue 18545. -/
theorem bounds_15_18545 : exactInterval 15 18545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18545 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18545) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18545 : oddCount 18545 15 = 4 ∧ acceleratedOrbit 15 18545 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18545 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18545) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18545.1, data_15_18545.2]

end Collatz.Research.PassageAtlas.Batch0566
