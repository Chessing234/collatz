import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0902

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 29523. -/
theorem bounds_15_29523 : exactInterval 15 29523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29523 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29523) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29523 : oddCount 29523 15 = 10 ∧ acceleratedOrbit 15 29523 = 53207 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29523 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29523) = 3 ^ 10 * m + 53207 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29523.1, data_15_29523.2]

/-- Complete interval computation for depth 15, residue 29524. -/
theorem bounds_15_29524 : exactInterval 15 29524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29524 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29524) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29524 : oddCount 29524 15 = 4 ∧ acceleratedOrbit 15 29524 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29524 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29524) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29524.1, data_15_29524.2]

/-- Complete interval computation for depth 15, residue 29525. -/
theorem bounds_15_29525 : exactInterval 15 29525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29525 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29525) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29525 : oddCount 29525 15 = 4 ∧ acceleratedOrbit 15 29525 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29525 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29525) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29525.1, data_15_29525.2]

/-- Complete interval computation for depth 15, residue 29526. -/
theorem bounds_15_29526 : exactInterval 15 29526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29526 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29526) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29526 : oddCount 29526 15 = 11 ∧ acceleratedOrbit 15 29526 = 159650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29526 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29526) = 3 ^ 11 * m + 159650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29526.1, data_15_29526.2]

/-- Complete interval computation for depth 15, residue 29527. -/
theorem bounds_15_29527 : exactInterval 15 29527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29527 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29527) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29527 : oddCount 29527 15 = 11 ∧ acceleratedOrbit 15 29527 = 159650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29527 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29527) = 3 ^ 11 * m + 159650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29527.1, data_15_29527.2]

/-- Complete interval computation for depth 15, residue 29528. -/
theorem bounds_15_29528 : exactInterval 15 29528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29528 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29528) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29528 : oddCount 29528 15 = 7 ∧ acceleratedOrbit 15 29528 = 1972 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29528 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29528) = 3 ^ 7 * m + 1972 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29528.1, data_15_29528.2]

/-- Complete interval computation for depth 15, residue 29529. -/
theorem bounds_15_29529 : exactInterval 15 29529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29529 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29529) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29529 : oddCount 29529 15 = 4 ∧ acceleratedOrbit 15 29529 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29529 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29529) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29529.1, data_15_29529.2]

/-- Complete interval computation for depth 15, residue 29530. -/
theorem bounds_15_29530 : exactInterval 15 29530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29530 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29530) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29530 : oddCount 29530 15 = 7 ∧ acceleratedOrbit 15 29530 = 1972 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29530 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29530) = 3 ^ 7 * m + 1972 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29530.1, data_15_29530.2]

/-- Complete interval computation for depth 15, residue 29531. -/
theorem bounds_15_29531 : exactInterval 15 29531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29531 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29531) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29531 : oddCount 29531 15 = 9 ∧ acceleratedOrbit 15 29531 = 17740 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29531 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29531) = 3 ^ 9 * m + 17740 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29531.1, data_15_29531.2]

/-- Complete interval computation for depth 15, residue 29532. -/
theorem bounds_15_29532 : exactInterval 15 29532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29532 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29532) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29532 : oddCount 29532 15 = 7 ∧ acceleratedOrbit 15 29532 = 1972 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29532 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29532) = 3 ^ 7 * m + 1972 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29532.1, data_15_29532.2]

/-- Complete interval computation for depth 15, residue 29533. -/
theorem bounds_15_29533 : exactInterval 15 29533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29533 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29533) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29533 : oddCount 29533 15 = 7 ∧ acceleratedOrbit 15 29533 = 1972 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29533 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29533) = 3 ^ 7 * m + 1972 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29533.1, data_15_29533.2]

/-- Complete interval computation for depth 15, residue 29534. -/
theorem bounds_15_29534 : exactInterval 15 29534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29534 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29534) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29534 : oddCount 29534 15 = 8 ∧ acceleratedOrbit 15 29534 = 5915 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29534 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29534) = 3 ^ 8 * m + 5915 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29534.1, data_15_29534.2]

/-- Complete interval computation for depth 15, residue 29535. -/
theorem bounds_15_29535 : exactInterval 15 29535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29535 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29535) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29535 : oddCount 29535 15 = 8 ∧ acceleratedOrbit 15 29535 = 5915 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29535 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29535) = 3 ^ 8 * m + 5915 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29535.1, data_15_29535.2]

/-- Complete interval computation for depth 15, residue 29536. -/
theorem bounds_15_29536 : exactInterval 15 29536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29536 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29536) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29536 : oddCount 29536 15 = 6 ∧ acceleratedOrbit 15 29536 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29536 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29536) = 3 ^ 6 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29536.1, data_15_29536.2]

/-- Complete interval computation for depth 15, residue 29537. -/
theorem bounds_15_29537 : exactInterval 15 29537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29537 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29537) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29537 : oddCount 29537 15 = 9 ∧ acceleratedOrbit 15 29537 = 17744 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29537 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29537) = 3 ^ 9 * m + 17744 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29537.1, data_15_29537.2]

/-- Complete interval computation for depth 15, residue 29538. -/
theorem bounds_15_29538 : exactInterval 15 29538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29538 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29538) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29538 : oddCount 29538 15 = 6 ∧ acceleratedOrbit 15 29538 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29538 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29538) = 3 ^ 6 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29538.1, data_15_29538.2]

/-- Complete interval computation for depth 15, residue 29539. -/
theorem bounds_15_29539 : exactInterval 15 29539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29539 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29539) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29539 : oddCount 29539 15 = 6 ∧ acceleratedOrbit 15 29539 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29539 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29539) = 3 ^ 6 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29539.1, data_15_29539.2]

/-- Complete interval computation for depth 15, residue 29540. -/
theorem bounds_15_29540 : exactInterval 15 29540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29540 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29540) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29540 : oddCount 29540 15 = 6 ∧ acceleratedOrbit 15 29540 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29540 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29540) = 3 ^ 6 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29540.1, data_15_29540.2]

/-- Complete interval computation for depth 15, residue 29541. -/
theorem bounds_15_29541 : exactInterval 15 29541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29541 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29541) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29541 : oddCount 29541 15 = 6 ∧ acceleratedOrbit 15 29541 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29541 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29541) = 3 ^ 6 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29541.1, data_15_29541.2]

/-- Complete interval computation for depth 15, residue 29542. -/
theorem bounds_15_29542 : exactInterval 15 29542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29542 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29542) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29542 : oddCount 29542 15 = 6 ∧ acceleratedOrbit 15 29542 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29542 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29542) = 3 ^ 6 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29542.1, data_15_29542.2]

/-- Complete interval computation for depth 15, residue 29543. -/
theorem bounds_15_29543 : exactInterval 15 29543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29543 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29543) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29543 : oddCount 29543 15 = 12 ∧ acceleratedOrbit 15 29543 = 479159 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29543 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29543) = 3 ^ 12 * m + 479159 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29543.1, data_15_29543.2]

/-- Complete interval computation for depth 15, residue 29544. -/
theorem bounds_15_29544 : exactInterval 15 29544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29544 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29544) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29544 : oddCount 29544 15 = 6 ∧ acceleratedOrbit 15 29544 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29544 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29544) = 3 ^ 6 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29544.1, data_15_29544.2]

/-- Complete interval computation for depth 15, residue 29545. -/
theorem bounds_15_29545 : exactInterval 15 29545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29545 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29545) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29545 : oddCount 29545 15 = 9 ∧ acceleratedOrbit 15 29545 = 17749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29545 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29545) = 3 ^ 9 * m + 17749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29545.1, data_15_29545.2]

/-- Complete interval computation for depth 15, residue 29546. -/
theorem bounds_15_29546 : exactInterval 15 29546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29546 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29546) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29546 : oddCount 29546 15 = 6 ∧ acceleratedOrbit 15 29546 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29546 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29546) = 3 ^ 6 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29546.1, data_15_29546.2]

/-- Complete interval computation for depth 15, residue 29547. -/
theorem bounds_15_29547 : exactInterval 15 29547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29547 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29547) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29547 : oddCount 29547 15 = 7 ∧ acceleratedOrbit 15 29547 = 1973 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29547 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29547) = 3 ^ 7 * m + 1973 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29547.1, data_15_29547.2]

/-- Complete interval computation for depth 15, residue 29548. -/
theorem bounds_15_29548 : exactInterval 15 29548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29548 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29548) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29548 : oddCount 29548 15 = 7 ∧ acceleratedOrbit 15 29548 = 1973 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29548 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29548) = 3 ^ 7 * m + 1973 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29548.1, data_15_29548.2]

/-- Complete interval computation for depth 15, residue 29549. -/
theorem bounds_15_29549 : exactInterval 15 29549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29549 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29549) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29549 : oddCount 29549 15 = 7 ∧ acceleratedOrbit 15 29549 = 1973 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29549 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29549) = 3 ^ 7 * m + 1973 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29549.1, data_15_29549.2]

/-- Complete interval computation for depth 15, residue 29550. -/
theorem bounds_15_29550 : exactInterval 15 29550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29550 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29550) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29550 : oddCount 29550 15 = 7 ∧ acceleratedOrbit 15 29550 = 1973 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29550 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29550) = 3 ^ 7 * m + 1973 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29550.1, data_15_29550.2]

/-- Complete interval computation for depth 15, residue 29551. -/
theorem bounds_15_29551 : exactInterval 15 29551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29551 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29551) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29551 : oddCount 29551 15 = 9 ∧ acceleratedOrbit 15 29551 = 17752 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29551 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29551) = 3 ^ 9 * m + 17752 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29551.1, data_15_29551.2]

/-- Complete interval computation for depth 15, residue 29552. -/
theorem bounds_15_29552 : exactInterval 15 29552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29552 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29552) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29552 : oddCount 29552 15 = 6 ∧ acceleratedOrbit 15 29552 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29552 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29552) = 3 ^ 6 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29552.1, data_15_29552.2]

/-- Complete interval computation for depth 15, residue 29553. -/
theorem bounds_15_29553 : exactInterval 15 29553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29553 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29553) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29553 : oddCount 29553 15 = 6 ∧ acceleratedOrbit 15 29553 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29553 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29553) = 3 ^ 6 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29553.1, data_15_29553.2]

/-- Complete interval computation for depth 15, residue 29554. -/
theorem bounds_15_29554 : exactInterval 15 29554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29554 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29554) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29554 : oddCount 29554 15 = 6 ∧ acceleratedOrbit 15 29554 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29554 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29554) = 3 ^ 6 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29554.1, data_15_29554.2]

/-- Complete interval computation for depth 15, residue 29555. -/
theorem bounds_15_29555 : exactInterval 15 29555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29555 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29555) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29555 : oddCount 29555 15 = 6 ∧ acceleratedOrbit 15 29555 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29555 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29555) = 3 ^ 6 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29555.1, data_15_29555.2]

end Collatz.Research.PassageAtlas.Batch0902
