import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0502

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 527. -/
theorem bounds_13_527 : exactInterval 13 527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_527 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 527) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_527 : oddCount 527 13 = 8 ∧ acceleratedOrbit 13 527 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_527 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 527) = 3 ^ 8 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_527.1, data_13_527.2]

/-- Complete interval computation for depth 13, residue 528. -/
theorem bounds_13_528 : exactInterval 13 528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_528 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 528) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_528 : oddCount 528 13 = 5 ∧ acceleratedOrbit 13 528 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_528 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 528) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_528.1, data_13_528.2]

/-- Complete interval computation for depth 13, residue 529. -/
theorem bounds_13_529 : exactInterval 13 529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_529 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 529) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_529 : oddCount 529 13 = 5 ∧ acceleratedOrbit 13 529 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_529 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 529) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_529.1, data_13_529.2]

/-- Complete interval computation for depth 13, residue 530. -/
theorem bounds_13_530 : exactInterval 13 530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_530 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 530) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_530 : oddCount 530 13 = 7 ∧ acceleratedOrbit 13 530 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_530 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 530) = 3 ^ 7 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_530.1, data_13_530.2]

/-- Complete interval computation for depth 13, residue 531. -/
theorem bounds_13_531 : exactInterval 13 531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_531 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 531) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_531 : oddCount 531 13 = 7 ∧ acceleratedOrbit 13 531 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_531 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 531) = 3 ^ 7 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_531.1, data_13_531.2]

/-- Complete interval computation for depth 13, residue 532. -/
theorem bounds_13_532 : exactInterval 13 532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_532 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 532) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_532 : oddCount 532 13 = 5 ∧ acceleratedOrbit 13 532 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_532 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 532) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_532.1, data_13_532.2]

/-- Complete interval computation for depth 13, residue 533. -/
theorem bounds_13_533 : exactInterval 13 533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_533 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 533) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_533 : oddCount 533 13 = 5 ∧ acceleratedOrbit 13 533 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_533 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 533) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_533.1, data_13_533.2]

/-- Complete interval computation for depth 13, residue 534. -/
theorem bounds_13_534 : exactInterval 13 534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_534 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 534) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_534 : oddCount 534 13 = 5 ∧ acceleratedOrbit 13 534 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_534 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 534) = 3 ^ 5 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_534.1, data_13_534.2]

/-- Complete interval computation for depth 13, residue 535. -/
theorem bounds_13_535 : exactInterval 13 535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_535 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 535) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_535 : oddCount 535 13 = 5 ∧ acceleratedOrbit 13 535 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_535 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 535) = 3 ^ 5 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_535.1, data_13_535.2]

/-- Complete interval computation for depth 13, residue 536. -/
theorem bounds_13_536 : exactInterval 13 536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_536 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 536) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_536 : oddCount 536 13 = 5 ∧ acceleratedOrbit 13 536 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_536 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 536) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_536.1, data_13_536.2]

/-- Complete interval computation for depth 13, residue 537. -/
theorem bounds_13_537 : exactInterval 13 537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_537 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 537) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_537 : oddCount 537 13 = 5 ∧ acceleratedOrbit 13 537 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_537 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 537) = 3 ^ 5 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_537.1, data_13_537.2]

/-- Complete interval computation for depth 13, residue 538. -/
theorem bounds_13_538 : exactInterval 13 538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_538 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 538) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_538 : oddCount 538 13 = 5 ∧ acceleratedOrbit 13 538 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_538 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 538) = 3 ^ 5 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_538.1, data_13_538.2]

/-- Complete interval computation for depth 13, residue 539. -/
theorem bounds_13_539 : exactInterval 13 539 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_539 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 539) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_539 : oddCount 539 13 = 8 ∧ acceleratedOrbit 13 539 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_539 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 539) = 3 ^ 8 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_539.1, data_13_539.2]

/-- Complete interval computation for depth 13, residue 540. -/
theorem bounds_13_540 : exactInterval 13 540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_540 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 540) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_540 : oddCount 540 13 = 6 ∧ acceleratedOrbit 13 540 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_540 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 540) = 3 ^ 6 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_540.1, data_13_540.2]

/-- Complete interval computation for depth 13, residue 541. -/
theorem bounds_13_541 : exactInterval 13 541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_541 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 541) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_541 : oddCount 541 13 = 6 ∧ acceleratedOrbit 13 541 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_541 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 541) = 3 ^ 6 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_541.1, data_13_541.2]

end Collatz.Research.StoppingAtlas.Batch0502
