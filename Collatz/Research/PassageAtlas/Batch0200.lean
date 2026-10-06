import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0200

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 6520. -/
theorem bounds_15_6520 : exactInterval 15 6520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6520 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6520) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6520 : oddCount 6520 15 = 7 ∧ acceleratedOrbit 15 6520 = 436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6520 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6520) = 3 ^ 7 * m + 436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6520.1, data_15_6520.2]

/-- Complete interval computation for depth 15, residue 6521. -/
theorem bounds_15_6521 : exactInterval 15 6521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6521 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6521) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6521 : oddCount 6521 15 = 10 ∧ acceleratedOrbit 15 6521 = 11755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6521 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6521) = 3 ^ 10 * m + 11755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6521.1, data_15_6521.2]

/-- Complete interval computation for depth 15, residue 6522. -/
theorem bounds_15_6522 : exactInterval 15 6522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6522 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6522) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6522 : oddCount 6522 15 = 7 ∧ acceleratedOrbit 15 6522 = 436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6522 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6522) = 3 ^ 7 * m + 436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6522.1, data_15_6522.2]

/-- Complete interval computation for depth 15, residue 6523. -/
theorem bounds_15_6523 : exactInterval 15 6523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6523 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6523) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6523 : oddCount 6523 15 = 8 ∧ acceleratedOrbit 15 6523 = 1307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6523 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6523) = 3 ^ 8 * m + 1307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6523.1, data_15_6523.2]

/-- Complete interval computation for depth 15, residue 6524. -/
theorem bounds_15_6524 : exactInterval 15 6524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6524 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6524) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6524 : oddCount 6524 15 = 7 ∧ acceleratedOrbit 15 6524 = 436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6524 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6524) = 3 ^ 7 * m + 436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6524.1, data_15_6524.2]

/-- Complete interval computation for depth 15, residue 6525. -/
theorem bounds_15_6525 : exactInterval 15 6525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6525 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6525) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6525 : oddCount 6525 15 = 7 ∧ acceleratedOrbit 15 6525 = 436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6525 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6525) = 3 ^ 7 * m + 436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6525.1, data_15_6525.2]

/-- Complete interval computation for depth 15, residue 6526. -/
theorem bounds_15_6526 : exactInterval 15 6526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6526 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6526) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6526 : oddCount 6526 15 = 10 ∧ acceleratedOrbit 15 6526 = 11765 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6526 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6526) = 3 ^ 10 * m + 11765 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6526.1, data_15_6526.2]

/-- Complete interval computation for depth 15, residue 6527. -/
theorem bounds_15_6527 : exactInterval 15 6527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6527 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6527) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6527 : oddCount 6527 15 = 10 ∧ acceleratedOrbit 15 6527 = 11765 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6527 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6527) = 3 ^ 10 * m + 11765 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6527.1, data_15_6527.2]

/-- Complete interval computation for depth 15, residue 6528. -/
theorem bounds_15_6528 : exactInterval 15 6528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6528 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6528) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6528 : oddCount 6528 15 = 4 ∧ acceleratedOrbit 15 6528 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6528 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6528) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6528.1, data_15_6528.2]

/-- Complete interval computation for depth 15, residue 6529. -/
theorem bounds_15_6529 : exactInterval 15 6529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6529 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6529) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6529 : oddCount 6529 15 = 8 ∧ acceleratedOrbit 15 6529 = 1309 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6529 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6529) = 3 ^ 8 * m + 1309 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6529.1, data_15_6529.2]

/-- Complete interval computation for depth 15, residue 6530. -/
theorem bounds_15_6530 : exactInterval 15 6530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6530 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6530) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6530 : oddCount 6530 15 = 6 ∧ acceleratedOrbit 15 6530 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6530 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6530) = 3 ^ 6 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6530.1, data_15_6530.2]

/-- Complete interval computation for depth 15, residue 6531. -/
theorem bounds_15_6531 : exactInterval 15 6531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6531 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6531) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6531 : oddCount 6531 15 = 6 ∧ acceleratedOrbit 15 6531 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6531 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6531) = 3 ^ 6 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6531.1, data_15_6531.2]

/-- Complete interval computation for depth 15, residue 6532. -/
theorem bounds_15_6532 : exactInterval 15 6532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6532 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6532) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6532 : oddCount 6532 15 = 6 ∧ acceleratedOrbit 15 6532 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6532 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6532) = 3 ^ 6 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6532.1, data_15_6532.2]

/-- Complete interval computation for depth 15, residue 6533. -/
theorem bounds_15_6533 : exactInterval 15 6533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6533 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6533) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6533 : oddCount 6533 15 = 6 ∧ acceleratedOrbit 15 6533 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6533 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6533) = 3 ^ 6 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6533.1, data_15_6533.2]

/-- Complete interval computation for depth 15, residue 6534. -/
theorem bounds_15_6534 : exactInterval 15 6534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6534 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6534) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6534 : oddCount 6534 15 = 6 ∧ acceleratedOrbit 15 6534 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6534 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6534) = 3 ^ 6 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6534.1, data_15_6534.2]

/-- Complete interval computation for depth 15, residue 6535. -/
theorem bounds_15_6535 : exactInterval 15 6535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6535 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6535) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6535 : oddCount 6535 15 = 6 ∧ acceleratedOrbit 15 6535 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6535 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6535) = 3 ^ 6 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6535.1, data_15_6535.2]

/-- Complete interval computation for depth 15, residue 6536. -/
theorem bounds_15_6536 : exactInterval 15 6536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6536 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6536) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6536 : oddCount 6536 15 = 5 ∧ acceleratedOrbit 15 6536 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6536 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6536) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6536.1, data_15_6536.2]

/-- Complete interval computation for depth 15, residue 6537. -/
theorem bounds_15_6537 : exactInterval 15 6537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6537 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6537) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6537 : oddCount 6537 15 = 10 ∧ acceleratedOrbit 15 6537 = 11785 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6537 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6537) = 3 ^ 10 * m + 11785 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6537.1, data_15_6537.2]

/-- Complete interval computation for depth 15, residue 6538. -/
theorem bounds_15_6538 : exactInterval 15 6538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6538 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6538) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6538 : oddCount 6538 15 = 5 ∧ acceleratedOrbit 15 6538 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6538 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6538) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6538.1, data_15_6538.2]

/-- Complete interval computation for depth 15, residue 6539. -/
theorem bounds_15_6539 : exactInterval 15 6539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6539 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6539) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6539 : oddCount 6539 15 = 8 ∧ acceleratedOrbit 15 6539 = 1310 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6539 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6539) = 3 ^ 8 * m + 1310 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6539.1, data_15_6539.2]

/-- Complete interval computation for depth 15, residue 6540. -/
theorem bounds_15_6540 : exactInterval 15 6540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6540 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6540) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6540 : oddCount 6540 15 = 5 ∧ acceleratedOrbit 15 6540 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6540 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6540) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6540.1, data_15_6540.2]

/-- Complete interval computation for depth 15, residue 6541. -/
theorem bounds_15_6541 : exactInterval 15 6541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6541 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6541) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6541 : oddCount 6541 15 = 5 ∧ acceleratedOrbit 15 6541 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6541 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6541) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6541.1, data_15_6541.2]

/-- Complete interval computation for depth 15, residue 6542. -/
theorem bounds_15_6542 : exactInterval 15 6542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6542 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6542) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6542 : oddCount 6542 15 = 7 ∧ acceleratedOrbit 15 6542 = 437 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6542 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6542) = 3 ^ 7 * m + 437 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6542.1, data_15_6542.2]

/-- Complete interval computation for depth 15, residue 6543. -/
theorem bounds_15_6543 : exactInterval 15 6543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6543 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6543) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6543 : oddCount 6543 15 = 7 ∧ acceleratedOrbit 15 6543 = 437 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6543 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6543) = 3 ^ 7 * m + 437 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6543.1, data_15_6543.2]

/-- Complete interval computation for depth 15, residue 6544. -/
theorem bounds_15_6544 : exactInterval 15 6544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6544 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6544) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6544 : oddCount 6544 15 = 5 ∧ acceleratedOrbit 15 6544 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6544 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6544) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6544.1, data_15_6544.2]

/-- Complete interval computation for depth 15, residue 6545. -/
theorem bounds_15_6545 : exactInterval 15 6545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6545 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6545) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6545 : oddCount 6545 15 = 6 ∧ acceleratedOrbit 15 6545 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6545 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6545) = 3 ^ 6 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6545.1, data_15_6545.2]

/-- Complete interval computation for depth 15, residue 6546. -/
theorem bounds_15_6546 : exactInterval 15 6546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6546 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6546) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6546 : oddCount 6546 15 = 6 ∧ acceleratedOrbit 15 6546 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6546 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6546) = 3 ^ 6 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6546.1, data_15_6546.2]

/-- Complete interval computation for depth 15, residue 6547. -/
theorem bounds_15_6547 : exactInterval 15 6547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6547 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6547) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6547 : oddCount 6547 15 = 6 ∧ acceleratedOrbit 15 6547 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6547 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6547) = 3 ^ 6 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6547.1, data_15_6547.2]

/-- Complete interval computation for depth 15, residue 6548. -/
theorem bounds_15_6548 : exactInterval 15 6548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6548 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6548) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6548 : oddCount 6548 15 = 5 ∧ acceleratedOrbit 15 6548 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6548 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6548) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6548.1, data_15_6548.2]

/-- Complete interval computation for depth 15, residue 6549. -/
theorem bounds_15_6549 : exactInterval 15 6549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6549 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6549) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6549 : oddCount 6549 15 = 5 ∧ acceleratedOrbit 15 6549 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6549 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6549) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6549.1, data_15_6549.2]

/-- Complete interval computation for depth 15, residue 6550. -/
theorem bounds_15_6550 : exactInterval 15 6550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6550 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6550) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6550 : oddCount 6550 15 = 6 ∧ acceleratedOrbit 15 6550 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6550 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6550) = 3 ^ 6 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6550.1, data_15_6550.2]

/-- Complete interval computation for depth 15, residue 6551. -/
theorem bounds_15_6551 : exactInterval 15 6551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6551 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6551) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6551 : oddCount 6551 15 = 6 ∧ acceleratedOrbit 15 6551 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6551 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6551) = 3 ^ 6 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6551.1, data_15_6551.2]

/-- Complete interval computation for depth 15, residue 6552. -/
theorem bounds_15_6552 : exactInterval 15 6552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6552 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6552) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6552 : oddCount 6552 15 = 5 ∧ acceleratedOrbit 15 6552 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6552 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6552) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6552.1, data_15_6552.2]

end Collatz.Research.PassageAtlas.Batch0200
