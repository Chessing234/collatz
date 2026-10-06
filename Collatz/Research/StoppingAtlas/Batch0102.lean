import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0102

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 527. -/
theorem bounds_11_527 : exactInterval 11 527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_527 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 527) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_527 : oddCount 527 11 = 7 ∧ acceleratedOrbit 11 527 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_527 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 527) = 3 ^ 7 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_527.1, data_11_527.2]

/-- Complete interval computation for depth 11, residue 528. -/
theorem bounds_11_528 : exactInterval 11 528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_528 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 528) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_528 : oddCount 528 11 = 4 ∧ acceleratedOrbit 11 528 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_528 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 528) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_528.1, data_11_528.2]

/-- Complete interval computation for depth 11, residue 529. -/
theorem bounds_11_529 : exactInterval 11 529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_529 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 529) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_529 : oddCount 529 11 = 3 ∧ acceleratedOrbit 11 529 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_529 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 529) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_529.1, data_11_529.2]

/-- Complete interval computation for depth 11, residue 530. -/
theorem bounds_11_530 : exactInterval 11 530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_530 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 530) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_530 : oddCount 530 11 = 6 ∧ acceleratedOrbit 11 530 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_530 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 530) = 3 ^ 6 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_530.1, data_11_530.2]

/-- Complete interval computation for depth 11, residue 531. -/
theorem bounds_11_531 : exactInterval 11 531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_531 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 531) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_531 : oddCount 531 11 = 6 ∧ acceleratedOrbit 11 531 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_531 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 531) = 3 ^ 6 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_531.1, data_11_531.2]

/-- Complete interval computation for depth 11, residue 532. -/
theorem bounds_11_532 : exactInterval 11 532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_532 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 532) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_532 : oddCount 532 11 = 4 ∧ acceleratedOrbit 11 532 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_532 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 532) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_532.1, data_11_532.2]

/-- Complete interval computation for depth 11, residue 533. -/
theorem bounds_11_533 : exactInterval 11 533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_533 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 533) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_533 : oddCount 533 11 = 4 ∧ acceleratedOrbit 11 533 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_533 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 533) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_533.1, data_11_533.2]

/-- Complete interval computation for depth 11, residue 534. -/
theorem bounds_11_534 : exactInterval 11 534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_534 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 534) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_534 : oddCount 534 11 = 5 ∧ acceleratedOrbit 11 534 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_534 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 534) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_534.1, data_11_534.2]

/-- Complete interval computation for depth 11, residue 535. -/
theorem bounds_11_535 : exactInterval 11 535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_535 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 535) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_535 : oddCount 535 11 = 5 ∧ acceleratedOrbit 11 535 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_535 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 535) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_535.1, data_11_535.2]

/-- Complete interval computation for depth 11, residue 536. -/
theorem bounds_11_536 : exactInterval 11 536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_536 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 536) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_536 : oddCount 536 11 = 4 ∧ acceleratedOrbit 11 536 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_536 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 536) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_536.1, data_11_536.2]

/-- Complete interval computation for depth 11, residue 537. -/
theorem bounds_11_537 : exactInterval 11 537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_537 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 537) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_537 : oddCount 537 11 = 5 ∧ acceleratedOrbit 11 537 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_537 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 537) = 3 ^ 5 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_537.1, data_11_537.2]

/-- Complete interval computation for depth 11, residue 538. -/
theorem bounds_11_538 : exactInterval 11 538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_538 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 538) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_538 : oddCount 538 11 = 4 ∧ acceleratedOrbit 11 538 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_538 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 538) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_538.1, data_11_538.2]

/-- Complete interval computation for depth 11, residue 539. -/
theorem bounds_11_539 : exactInterval 11 539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_539 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 539) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_539 : oddCount 539 11 = 7 ∧ acceleratedOrbit 11 539 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_539 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 539) = 3 ^ 7 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_539.1, data_11_539.2]

/-- Complete interval computation for depth 11, residue 540. -/
theorem bounds_11_540 : exactInterval 11 540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_540 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 540) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_540 : oddCount 540 11 = 5 ∧ acceleratedOrbit 11 540 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_540 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 540) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_540.1, data_11_540.2]

/-- Complete interval computation for depth 11, residue 541. -/
theorem bounds_11_541 : exactInterval 11 541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_541 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 541) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_541 : oddCount 541 11 = 5 ∧ acceleratedOrbit 11 541 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_541 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 541) = 3 ^ 5 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_541.1, data_11_541.2]

end Collatz.Research.StoppingAtlas.Batch0102
