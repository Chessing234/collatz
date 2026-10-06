import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0017

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 524. -/
theorem bounds_15_524 : exactInterval 15 524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_524 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 524) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_524 : oddCount 524 15 = 6 ∧ acceleratedOrbit 15 524 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_524 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 524) = 3 ^ 6 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_524.1, data_15_524.2]

/-- Complete interval computation for depth 15, residue 525. -/
theorem bounds_15_525 : exactInterval 15 525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_525 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 525) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_525 : oddCount 525 15 = 6 ∧ acceleratedOrbit 15 525 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_525 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 525) = 3 ^ 6 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_525.1, data_15_525.2]

/-- Complete interval computation for depth 15, residue 526. -/
theorem bounds_15_526 : exactInterval 15 526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_526 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 526) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_526 : oddCount 526 15 = 9 ∧ acceleratedOrbit 15 526 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_526 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 526) = 3 ^ 9 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_526.1, data_15_526.2]

/-- Complete interval computation for depth 15, residue 527. -/
theorem bounds_15_527 : exactInterval 15 527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_527 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 527) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_527 : oddCount 527 15 = 9 ∧ acceleratedOrbit 15 527 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_527 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 527) = 3 ^ 9 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_527.1, data_15_527.2]

/-- Complete interval computation for depth 15, residue 528. -/
theorem bounds_15_528 : exactInterval 15 528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_528 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 528) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_528 : oddCount 528 15 = 6 ∧ acceleratedOrbit 15 528 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_528 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 528) = 3 ^ 6 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_528.1, data_15_528.2]

/-- Complete interval computation for depth 15, residue 529. -/
theorem bounds_15_529 : exactInterval 15 529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_529 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 529) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_529 : oddCount 529 15 = 6 ∧ acceleratedOrbit 15 529 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_529 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 529) = 3 ^ 6 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_529.1, data_15_529.2]

/-- Complete interval computation for depth 15, residue 530. -/
theorem bounds_15_530 : exactInterval 15 530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_530 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 530) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_530 : oddCount 530 15 = 9 ∧ acceleratedOrbit 15 530 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_530 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 530) = 3 ^ 9 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_530.1, data_15_530.2]

/-- Complete interval computation for depth 15, residue 531. -/
theorem bounds_15_531 : exactInterval 15 531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_531 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 531) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_531 : oddCount 531 15 = 9 ∧ acceleratedOrbit 15 531 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_531 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 531) = 3 ^ 9 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_531.1, data_15_531.2]

/-- Complete interval computation for depth 15, residue 532. -/
theorem bounds_15_532 : exactInterval 15 532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_532 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 532) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_532 : oddCount 532 15 = 6 ∧ acceleratedOrbit 15 532 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_532 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 532) = 3 ^ 6 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_532.1, data_15_532.2]

/-- Complete interval computation for depth 15, residue 533. -/
theorem bounds_15_533 : exactInterval 15 533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_533 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 533) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_533 : oddCount 533 15 = 6 ∧ acceleratedOrbit 15 533 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_533 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 533) = 3 ^ 6 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_533.1, data_15_533.2]

/-- Complete interval computation for depth 15, residue 534. -/
theorem bounds_15_534 : exactInterval 15 534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_534 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 534) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_534 : oddCount 534 15 = 5 ∧ acceleratedOrbit 15 534 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_534 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 534) = 3 ^ 5 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_534.1, data_15_534.2]

/-- Complete interval computation for depth 15, residue 535. -/
theorem bounds_15_535 : exactInterval 15 535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_535 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 535) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_535 : oddCount 535 15 = 5 ∧ acceleratedOrbit 15 535 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_535 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 535) = 3 ^ 5 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_535.1, data_15_535.2]

/-- Complete interval computation for depth 15, residue 536. -/
theorem bounds_15_536 : exactInterval 15 536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_536 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 536) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_536 : oddCount 536 15 = 6 ∧ acceleratedOrbit 15 536 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_536 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 536) = 3 ^ 6 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_536.1, data_15_536.2]

/-- Complete interval computation for depth 15, residue 537. -/
theorem bounds_15_537 : exactInterval 15 537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_537 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 537) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_537 : oddCount 537 15 = 5 ∧ acceleratedOrbit 15 537 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_537 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 537) = 3 ^ 5 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_537.1, data_15_537.2]

/-- Complete interval computation for depth 15, residue 538. -/
theorem bounds_15_538 : exactInterval 15 538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_538 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 538) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_538 : oddCount 538 15 = 6 ∧ acceleratedOrbit 15 538 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_538 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 538) = 3 ^ 6 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_538.1, data_15_538.2]

/-- Complete interval computation for depth 15, residue 539. -/
theorem bounds_15_539 : exactInterval 15 539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_539 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 539) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_539 : oddCount 539 15 = 9 ∧ acceleratedOrbit 15 539 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_539 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 539) = 3 ^ 9 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_539.1, data_15_539.2]

/-- Complete interval computation for depth 15, residue 540. -/
theorem bounds_15_540 : exactInterval 15 540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_540 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 540) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_540 : oddCount 540 15 = 7 ∧ acceleratedOrbit 15 540 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_540 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 540) = 3 ^ 7 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_540.1, data_15_540.2]

/-- Complete interval computation for depth 15, residue 541. -/
theorem bounds_15_541 : exactInterval 15 541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_541 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 541) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_541 : oddCount 541 15 = 7 ∧ acceleratedOrbit 15 541 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_541 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 541) = 3 ^ 7 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_541.1, data_15_541.2]

/-- Complete interval computation for depth 15, residue 542. -/
theorem bounds_15_542 : exactInterval 15 542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_542 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 542) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_542 : oddCount 542 15 = 7 ∧ acceleratedOrbit 15 542 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_542 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 542) = 3 ^ 7 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_542.1, data_15_542.2]

/-- Complete interval computation for depth 15, residue 543. -/
theorem bounds_15_543 : exactInterval 15 543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_543 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 543) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_543 : oddCount 543 15 = 8 ∧ acceleratedOrbit 15 543 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_543 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 543) = 3 ^ 8 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_543.1, data_15_543.2]

/-- Complete interval computation for depth 15, residue 544. -/
theorem bounds_15_544 : exactInterval 15 544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_544 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 544) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_544 : oddCount 544 15 = 4 ∧ acceleratedOrbit 15 544 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_544 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 544) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_544.1, data_15_544.2]

/-- Complete interval computation for depth 15, residue 545. -/
theorem bounds_15_545 : exactInterval 15 545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_545 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 545) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_545 : oddCount 545 15 = 7 ∧ acceleratedOrbit 15 545 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_545 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 545) = 3 ^ 7 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_545.1, data_15_545.2]

/-- Complete interval computation for depth 15, residue 546. -/
theorem bounds_15_546 : exactInterval 15 546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_546 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 546) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_546 : oddCount 546 15 = 6 ∧ acceleratedOrbit 15 546 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_546 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 546) = 3 ^ 6 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_546.1, data_15_546.2]

/-- Complete interval computation for depth 15, residue 547. -/
theorem bounds_15_547 : exactInterval 15 547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_547 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 547) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_547 : oddCount 547 15 = 6 ∧ acceleratedOrbit 15 547 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_547 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 547) = 3 ^ 6 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_547.1, data_15_547.2]

/-- Complete interval computation for depth 15, residue 548. -/
theorem bounds_15_548 : exactInterval 15 548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_548 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 548) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_548 : oddCount 548 15 = 9 ∧ acceleratedOrbit 15 548 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_548 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 548) = 3 ^ 9 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_548.1, data_15_548.2]

/-- Complete interval computation for depth 15, residue 549. -/
theorem bounds_15_549 : exactInterval 15 549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_549 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 549) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_549 : oddCount 549 15 = 9 ∧ acceleratedOrbit 15 549 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_549 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 549) = 3 ^ 9 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_549.1, data_15_549.2]

/-- Complete interval computation for depth 15, residue 550. -/
theorem bounds_15_550 : exactInterval 15 550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_550 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 550) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_550 : oddCount 550 15 = 9 ∧ acceleratedOrbit 15 550 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_550 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 550) = 3 ^ 9 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_550.1, data_15_550.2]

/-- Complete interval computation for depth 15, residue 551. -/
theorem bounds_15_551 : exactInterval 15 551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_551 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 551) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_551 : oddCount 551 15 = 7 ∧ acceleratedOrbit 15 551 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_551 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 551) = 3 ^ 7 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_551.1, data_15_551.2]

/-- Complete interval computation for depth 15, residue 552. -/
theorem bounds_15_552 : exactInterval 15 552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_552 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 552) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_552 : oddCount 552 15 = 4 ∧ acceleratedOrbit 15 552 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_552 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 552) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_552.1, data_15_552.2]

/-- Complete interval computation for depth 15, residue 553. -/
theorem bounds_15_553 : exactInterval 15 553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_553 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 553) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_553 : oddCount 553 15 = 10 ∧ acceleratedOrbit 15 553 = 1000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_553 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 553) = 3 ^ 10 * m + 1000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_553.1, data_15_553.2]

/-- Complete interval computation for depth 15, residue 554. -/
theorem bounds_15_554 : exactInterval 15 554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_554 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 554) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_554 : oddCount 554 15 = 4 ∧ acceleratedOrbit 15 554 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_554 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 554) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_554.1, data_15_554.2]

/-- Complete interval computation for depth 15, residue 555. -/
theorem bounds_15_555 : exactInterval 15 555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_555 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 555) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_555 : oddCount 555 15 = 6 ∧ acceleratedOrbit 15 555 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_555 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 555) = 3 ^ 6 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_555.1, data_15_555.2]

/-- Complete interval computation for depth 15, residue 556. -/
theorem bounds_15_556 : exactInterval 15 556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_556 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 556) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_556 : oddCount 556 15 = 7 ∧ acceleratedOrbit 15 556 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_556 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 556) = 3 ^ 7 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_556.1, data_15_556.2]

end Collatz.Research.PassageAtlas.Batch0017
