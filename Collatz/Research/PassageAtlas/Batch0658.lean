import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0658

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 21528. -/
theorem bounds_15_21528 : exactInterval 15 21528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21528 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21528) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21528 : oddCount 21528 15 = 5 ∧ acceleratedOrbit 15 21528 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21528 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21528) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21528.1, data_15_21528.2]

/-- Complete interval computation for depth 15, residue 21529. -/
theorem bounds_15_21529 : exactInterval 15 21529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21529 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21529) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21529 : oddCount 21529 15 = 9 ∧ acceleratedOrbit 15 21529 = 12935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21529 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21529) = 3 ^ 9 * m + 12935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21529.1, data_15_21529.2]

/-- Complete interval computation for depth 15, residue 21530. -/
theorem bounds_15_21530 : exactInterval 15 21530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21530 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21530) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21530 : oddCount 21530 15 = 5 ∧ acceleratedOrbit 15 21530 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21530 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21530) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21530.1, data_15_21530.2]

/-- Complete interval computation for depth 15, residue 21531. -/
theorem bounds_15_21531 : exactInterval 15 21531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21531 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21531) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21531 : oddCount 21531 15 = 11 ∧ acceleratedOrbit 15 21531 = 116407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21531 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21531) = 3 ^ 11 * m + 116407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21531.1, data_15_21531.2]

/-- Complete interval computation for depth 15, residue 21532. -/
theorem bounds_15_21532 : exactInterval 15 21532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21532 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21532) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21532 : oddCount 21532 15 = 8 ∧ acceleratedOrbit 15 21532 = 4313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21532 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21532) = 3 ^ 8 * m + 4313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21532.1, data_15_21532.2]

/-- Complete interval computation for depth 15, residue 21533. -/
theorem bounds_15_21533 : exactInterval 15 21533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21533 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21533) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21533 : oddCount 21533 15 = 8 ∧ acceleratedOrbit 15 21533 = 4313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21533 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21533) = 3 ^ 8 * m + 4313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21533.1, data_15_21533.2]

/-- Complete interval computation for depth 15, residue 21534. -/
theorem bounds_15_21534 : exactInterval 15 21534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21534 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21534) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21534 : oddCount 21534 15 = 8 ∧ acceleratedOrbit 15 21534 = 4313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21534 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21534) = 3 ^ 8 * m + 4313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21534.1, data_15_21534.2]

/-- Complete interval computation for depth 15, residue 21535. -/
theorem bounds_15_21535 : exactInterval 15 21535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21535 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21535) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21535 : oddCount 21535 15 = 10 ∧ acceleratedOrbit 15 21535 = 38809 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21535 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21535) = 3 ^ 10 * m + 38809 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21535.1, data_15_21535.2]

/-- Complete interval computation for depth 15, residue 21536. -/
theorem bounds_15_21536 : exactInterval 15 21536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21536 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21536) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21536 : oddCount 21536 15 = 6 ∧ acceleratedOrbit 15 21536 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21536 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21536) = 3 ^ 6 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21536.1, data_15_21536.2]

/-- Complete interval computation for depth 15, residue 21537. -/
theorem bounds_15_21537 : exactInterval 15 21537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21537 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21537) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21537 : oddCount 21537 15 = 10 ∧ acceleratedOrbit 15 21537 = 38819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21537 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21537) = 3 ^ 10 * m + 38819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21537.1, data_15_21537.2]

/-- Complete interval computation for depth 15, residue 21538. -/
theorem bounds_15_21538 : exactInterval 15 21538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21538 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21538) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21538 : oddCount 21538 15 = 5 ∧ acceleratedOrbit 15 21538 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21538 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21538) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21538.1, data_15_21538.2]

/-- Complete interval computation for depth 15, residue 21539. -/
theorem bounds_15_21539 : exactInterval 15 21539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21539 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21539) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21539 : oddCount 21539 15 = 5 ∧ acceleratedOrbit 15 21539 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21539 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21539) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21539.1, data_15_21539.2]

/-- Complete interval computation for depth 15, residue 21540. -/
theorem bounds_15_21540 : exactInterval 15 21540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21540 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21540) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21540 : oddCount 21540 15 = 8 ∧ acceleratedOrbit 15 21540 = 4315 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21540 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21540) = 3 ^ 8 * m + 4315 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21540.1, data_15_21540.2]

/-- Complete interval computation for depth 15, residue 21541. -/
theorem bounds_15_21541 : exactInterval 15 21541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21541 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21541) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21541 : oddCount 21541 15 = 8 ∧ acceleratedOrbit 15 21541 = 4315 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21541 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21541) = 3 ^ 8 * m + 4315 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21541.1, data_15_21541.2]

/-- Complete interval computation for depth 15, residue 21542. -/
theorem bounds_15_21542 : exactInterval 15 21542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21542 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21542) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21542 : oddCount 21542 15 = 8 ∧ acceleratedOrbit 15 21542 = 4315 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21542 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21542) = 3 ^ 8 * m + 4315 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21542.1, data_15_21542.2]

/-- Complete interval computation for depth 15, residue 21543. -/
theorem bounds_15_21543 : exactInterval 15 21543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21543 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21543) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21543 : oddCount 21543 15 = 7 ∧ acceleratedOrbit 15 21543 = 1438 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21543 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21543) = 3 ^ 7 * m + 1438 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21543.1, data_15_21543.2]

/-- Complete interval computation for depth 15, residue 21544. -/
theorem bounds_15_21544 : exactInterval 15 21544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21544 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21544) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21544 : oddCount 21544 15 = 6 ∧ acceleratedOrbit 15 21544 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21544 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21544) = 3 ^ 6 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21544.1, data_15_21544.2]

/-- Complete interval computation for depth 15, residue 21545. -/
theorem bounds_15_21545 : exactInterval 15 21545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21545 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21545) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21545 : oddCount 21545 15 = 9 ∧ acceleratedOrbit 15 21545 = 12943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21545 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21545) = 3 ^ 9 * m + 12943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21545.1, data_15_21545.2]

/-- Complete interval computation for depth 15, residue 21546. -/
theorem bounds_15_21546 : exactInterval 15 21546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21546 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21546) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21546 : oddCount 21546 15 = 6 ∧ acceleratedOrbit 15 21546 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21546 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21546) = 3 ^ 6 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21546.1, data_15_21546.2]

/-- Complete interval computation for depth 15, residue 21547. -/
theorem bounds_15_21547 : exactInterval 15 21547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21547 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21547) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21547 : oddCount 21547 15 = 7 ∧ acceleratedOrbit 15 21547 = 1439 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21547 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21547) = 3 ^ 7 * m + 1439 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21547.1, data_15_21547.2]

/-- Complete interval computation for depth 15, residue 21548. -/
theorem bounds_15_21548 : exactInterval 15 21548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21548 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21548) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21548 : oddCount 21548 15 = 8 ∧ acceleratedOrbit 15 21548 = 4319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21548 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21548) = 3 ^ 8 * m + 4319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21548.1, data_15_21548.2]

/-- Complete interval computation for depth 15, residue 21549. -/
theorem bounds_15_21549 : exactInterval 15 21549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21549 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21549) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21549 : oddCount 21549 15 = 8 ∧ acceleratedOrbit 15 21549 = 4319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21549 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21549) = 3 ^ 8 * m + 4319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21549.1, data_15_21549.2]

/-- Complete interval computation for depth 15, residue 21550. -/
theorem bounds_15_21550 : exactInterval 15 21550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21550 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21550) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21550 : oddCount 21550 15 = 8 ∧ acceleratedOrbit 15 21550 = 4319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21550 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21550) = 3 ^ 8 * m + 4319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21550.1, data_15_21550.2]

/-- Complete interval computation for depth 15, residue 21551. -/
theorem bounds_15_21551 : exactInterval 15 21551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21551 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21551) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21551 : oddCount 21551 15 = 10 ∧ acceleratedOrbit 15 21551 = 38839 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21551 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21551) = 3 ^ 10 * m + 38839 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21551.1, data_15_21551.2]

/-- Complete interval computation for depth 15, residue 21552. -/
theorem bounds_15_21552 : exactInterval 15 21552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21552 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21552) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21552 : oddCount 21552 15 = 6 ∧ acceleratedOrbit 15 21552 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21552 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21552) = 3 ^ 6 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21552.1, data_15_21552.2]

/-- Complete interval computation for depth 15, residue 21553. -/
theorem bounds_15_21553 : exactInterval 15 21553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21553 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21553) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21553 : oddCount 21553 15 = 8 ∧ acceleratedOrbit 15 21553 = 4319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21553 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21553) = 3 ^ 8 * m + 4319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21553.1, data_15_21553.2]

/-- Complete interval computation for depth 15, residue 21554. -/
theorem bounds_15_21554 : exactInterval 15 21554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21554 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21554) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21554 : oddCount 21554 15 = 8 ∧ acceleratedOrbit 15 21554 = 4319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21554 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21554) = 3 ^ 8 * m + 4319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21554.1, data_15_21554.2]

/-- Complete interval computation for depth 15, residue 21555. -/
theorem bounds_15_21555 : exactInterval 15 21555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21555 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21555) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21555 : oddCount 21555 15 = 8 ∧ acceleratedOrbit 15 21555 = 4319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21555 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21555) = 3 ^ 8 * m + 4319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21555.1, data_15_21555.2]

/-- Complete interval computation for depth 15, residue 21556. -/
theorem bounds_15_21556 : exactInterval 15 21556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21556 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21556) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21556 : oddCount 21556 15 = 6 ∧ acceleratedOrbit 15 21556 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21556 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21556) = 3 ^ 6 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21556.1, data_15_21556.2]

/-- Complete interval computation for depth 15, residue 21557. -/
theorem bounds_15_21557 : exactInterval 15 21557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21557 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21557) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21557 : oddCount 21557 15 = 6 ∧ acceleratedOrbit 15 21557 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21557 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21557) = 3 ^ 6 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21557.1, data_15_21557.2]

/-- Complete interval computation for depth 15, residue 21558. -/
theorem bounds_15_21558 : exactInterval 15 21558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21558 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21558) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21558 : oddCount 21558 15 = 7 ∧ acceleratedOrbit 15 21558 = 1439 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21558 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21558) = 3 ^ 7 * m + 1439 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21558.1, data_15_21558.2]

/-- Complete interval computation for depth 15, residue 21559. -/
theorem bounds_15_21559 : exactInterval 15 21559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21559 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21559) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21559 : oddCount 21559 15 = 7 ∧ acceleratedOrbit 15 21559 = 1439 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21559 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21559) = 3 ^ 7 * m + 1439 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21559.1, data_15_21559.2]

/-- Complete interval computation for depth 15, residue 21560. -/
theorem bounds_15_21560 : exactInterval 15 21560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21560 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21560) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21560 : oddCount 21560 15 = 5 ∧ acceleratedOrbit 15 21560 = 160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21560 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21560) = 3 ^ 5 * m + 160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21560.1, data_15_21560.2]

end Collatz.Research.PassageAtlas.Batch0658
