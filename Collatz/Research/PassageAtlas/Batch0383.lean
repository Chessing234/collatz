import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0383

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 12517. -/
theorem bounds_15_12517 : exactInterval 15 12517 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12517 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12517) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12517 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12517 : oddCount 12517 15 = 8 ∧ acceleratedOrbit 15 12517 = 2510 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12517 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12517) = 3 ^ 8 * m + 2510 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12517.1, data_15_12517.2]

/-- Complete interval computation for depth 15, residue 12518. -/
theorem bounds_15_12518 : exactInterval 15 12518 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12518 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12518) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12518 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12518 : oddCount 12518 15 = 8 ∧ acceleratedOrbit 15 12518 = 2510 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12518 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12518) = 3 ^ 8 * m + 2510 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12518.1, data_15_12518.2]

/-- Complete interval computation for depth 15, residue 12519. -/
theorem bounds_15_12519 : exactInterval 15 12519 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12519 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12519) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12519 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12519 : oddCount 12519 15 = 8 ∧ acceleratedOrbit 15 12519 = 2507 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12519 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12519) = 3 ^ 8 * m + 2507 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12519.1, data_15_12519.2]

/-- Complete interval computation for depth 15, residue 12520. -/
theorem bounds_15_12520 : exactInterval 15 12520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12520 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12520) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12520 : oddCount 12520 15 = 4 ∧ acceleratedOrbit 15 12520 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12520 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12520) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12520.1, data_15_12520.2]

/-- Complete interval computation for depth 15, residue 12521. -/
theorem bounds_15_12521 : exactInterval 15 12521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12521 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12521) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12521 : oddCount 12521 15 = 9 ∧ acceleratedOrbit 15 12521 = 7523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12521 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12521) = 3 ^ 9 * m + 7523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12521.1, data_15_12521.2]

/-- Complete interval computation for depth 15, residue 12522. -/
theorem bounds_15_12522 : exactInterval 15 12522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12522 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12522) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12522 : oddCount 12522 15 = 4 ∧ acceleratedOrbit 15 12522 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12522 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12522) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12522.1, data_15_12522.2]

/-- Complete interval computation for depth 15, residue 12523. -/
theorem bounds_15_12523 : exactInterval 15 12523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12523 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12523) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12523 : oddCount 12523 15 = 11 ∧ acceleratedOrbit 15 12523 = 67715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12523 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12523) = 3 ^ 11 * m + 67715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12523.1, data_15_12523.2]

/-- Complete interval computation for depth 15, residue 12524. -/
theorem bounds_15_12524 : exactInterval 15 12524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12524 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12524) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12524 : oddCount 12524 15 = 9 ∧ acceleratedOrbit 15 12524 = 7532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12524 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12524) = 3 ^ 9 * m + 7532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12524.1, data_15_12524.2]

/-- Complete interval computation for depth 15, residue 12525. -/
theorem bounds_15_12525 : exactInterval 15 12525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12525 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12525) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12525 : oddCount 12525 15 = 9 ∧ acceleratedOrbit 15 12525 = 7532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12525 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12525) = 3 ^ 9 * m + 7532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12525.1, data_15_12525.2]

/-- Complete interval computation for depth 15, residue 12526. -/
theorem bounds_15_12526 : exactInterval 15 12526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12526 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12526) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12526 : oddCount 12526 15 = 9 ∧ acceleratedOrbit 15 12526 = 7532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12526 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12526) = 3 ^ 9 * m + 7532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12526.1, data_15_12526.2]

/-- Complete interval computation for depth 15, residue 12527. -/
theorem bounds_15_12527 : exactInterval 15 12527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12527 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12527) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12527 : oddCount 12527 15 = 11 ∧ acceleratedOrbit 15 12527 = 67729 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12527 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12527) = 3 ^ 11 * m + 67729 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12527.1, data_15_12527.2]

/-- Complete interval computation for depth 15, residue 12528. -/
theorem bounds_15_12528 : exactInterval 15 12528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12528 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12528) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12528 : oddCount 12528 15 = 4 ∧ acceleratedOrbit 15 12528 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12528 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12528) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12528.1, data_15_12528.2]

/-- Complete interval computation for depth 15, residue 12529. -/
theorem bounds_15_12529 : exactInterval 15 12529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12529 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12529) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12529 : oddCount 12529 15 = 4 ∧ acceleratedOrbit 15 12529 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12529 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12529) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12529.1, data_15_12529.2]

/-- Complete interval computation for depth 15, residue 12530. -/
theorem bounds_15_12530 : exactInterval 15 12530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12530 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12530) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12530 : oddCount 12530 15 = 10 ∧ acceleratedOrbit 15 12530 = 22589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12530 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12530) = 3 ^ 10 * m + 22589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12530.1, data_15_12530.2]

/-- Complete interval computation for depth 15, residue 12531. -/
theorem bounds_15_12531 : exactInterval 15 12531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12531 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12531) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12531 : oddCount 12531 15 = 10 ∧ acceleratedOrbit 15 12531 = 22589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12531 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12531) = 3 ^ 10 * m + 22589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12531.1, data_15_12531.2]

/-- Complete interval computation for depth 15, residue 12532. -/
theorem bounds_15_12532 : exactInterval 15 12532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12532 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12532) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12532 : oddCount 12532 15 = 4 ∧ acceleratedOrbit 15 12532 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12532 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12532) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12532.1, data_15_12532.2]

/-- Complete interval computation for depth 15, residue 12533. -/
theorem bounds_15_12533 : exactInterval 15 12533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12533 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12533) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12533 : oddCount 12533 15 = 4 ∧ acceleratedOrbit 15 12533 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12533 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12533) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12533.1, data_15_12533.2]

/-- Complete interval computation for depth 15, residue 12534. -/
theorem bounds_15_12534 : exactInterval 15 12534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12534 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12534) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12534 : oddCount 12534 15 = 10 ∧ acceleratedOrbit 15 12534 = 22598 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12534 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12534) = 3 ^ 10 * m + 22598 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12534.1, data_15_12534.2]

/-- Complete interval computation for depth 15, residue 12535. -/
theorem bounds_15_12535 : exactInterval 15 12535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12535 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12535) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12535 : oddCount 12535 15 = 10 ∧ acceleratedOrbit 15 12535 = 22598 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12535 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12535) = 3 ^ 10 * m + 22598 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12535.1, data_15_12535.2]

/-- Complete interval computation for depth 15, residue 12536. -/
theorem bounds_15_12536 : exactInterval 15 12536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12536 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12536) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12536 : oddCount 12536 15 = 8 ∧ acceleratedOrbit 15 12536 = 2512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12536 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12536) = 3 ^ 8 * m + 2512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12536.1, data_15_12536.2]

/-- Complete interval computation for depth 15, residue 12537. -/
theorem bounds_15_12537 : exactInterval 15 12537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12537 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12537) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12537 : oddCount 12537 15 = 11 ∧ acceleratedOrbit 15 12537 = 67796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12537 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12537) = 3 ^ 11 * m + 67796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12537.1, data_15_12537.2]

/-- Complete interval computation for depth 15, residue 12538. -/
theorem bounds_15_12538 : exactInterval 15 12538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12538 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12538) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12538 : oddCount 12538 15 = 8 ∧ acceleratedOrbit 15 12538 = 2512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12538 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12538) = 3 ^ 8 * m + 2512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12538.1, data_15_12538.2]

/-- Complete interval computation for depth 15, residue 12539. -/
theorem bounds_15_12539 : exactInterval 15 12539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12539 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12539) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12539 : oddCount 12539 15 = 13 ∧ acceleratedOrbit 15 12539 = 610172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12539 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12539) = 3 ^ 13 * m + 610172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12539.1, data_15_12539.2]

/-- Complete interval computation for depth 15, residue 12540. -/
theorem bounds_15_12540 : exactInterval 15 12540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12540 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12540) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12540 : oddCount 12540 15 = 8 ∧ acceleratedOrbit 15 12540 = 2512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12540 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12540) = 3 ^ 8 * m + 2512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12540.1, data_15_12540.2]

/-- Complete interval computation for depth 15, residue 12541. -/
theorem bounds_15_12541 : exactInterval 15 12541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12541 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12541) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12541 : oddCount 12541 15 = 8 ∧ acceleratedOrbit 15 12541 = 2512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12541 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12541) = 3 ^ 8 * m + 2512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12541.1, data_15_12541.2]

/-- Complete interval computation for depth 15, residue 12542. -/
theorem bounds_15_12542 : exactInterval 15 12542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12542 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12542) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12542 : oddCount 12542 15 = 9 ∧ acceleratedOrbit 15 12542 = 7535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12542 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12542) = 3 ^ 9 * m + 7535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12542.1, data_15_12542.2]

/-- Complete interval computation for depth 15, residue 12543. -/
theorem bounds_15_12543 : exactInterval 15 12543 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12543 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12543) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12543 : oddCount 12543 15 = 9 ∧ acceleratedOrbit 15 12543 = 7535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12543 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12543) = 3 ^ 9 * m + 7535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12543.1, data_15_12543.2]

/-- Complete interval computation for depth 15, residue 12544. -/
theorem bounds_15_12544 : exactInterval 15 12544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12544 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12544) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12544 : oddCount 12544 15 = 3 ∧ acceleratedOrbit 15 12544 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12544 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12544) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12544.1, data_15_12544.2]

/-- Complete interval computation for depth 15, residue 12545. -/
theorem bounds_15_12545 : exactInterval 15 12545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12545 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12545) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12545 : oddCount 12545 15 = 7 ∧ acceleratedOrbit 15 12545 = 838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12545 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12545) = 3 ^ 7 * m + 838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12545.1, data_15_12545.2]

/-- Complete interval computation for depth 15, residue 12546. -/
theorem bounds_15_12546 : exactInterval 15 12546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12546 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12546) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12546 : oddCount 12546 15 = 7 ∧ acceleratedOrbit 15 12546 = 838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12546 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12546) = 3 ^ 7 * m + 838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12546.1, data_15_12546.2]

/-- Complete interval computation for depth 15, residue 12547. -/
theorem bounds_15_12547 : exactInterval 15 12547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12547 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12547) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12547 : oddCount 12547 15 = 7 ∧ acceleratedOrbit 15 12547 = 838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12547 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12547) = 3 ^ 7 * m + 838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12547.1, data_15_12547.2]

/-- Complete interval computation for depth 15, residue 12548. -/
theorem bounds_15_12548 : exactInterval 15 12548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12548 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12548) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12548 : oddCount 12548 15 = 6 ∧ acceleratedOrbit 15 12548 = 280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12548 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12548) = 3 ^ 6 * m + 280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12548.1, data_15_12548.2]

/-- Complete interval computation for depth 15, residue 12549. -/
theorem bounds_15_12549 : exactInterval 15 12549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12549 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12549) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12549 : oddCount 12549 15 = 6 ∧ acceleratedOrbit 15 12549 = 280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12549 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12549) = 3 ^ 6 * m + 280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12549.1, data_15_12549.2]

end Collatz.Research.PassageAtlas.Batch0383
