import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0597

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 19529. -/
theorem bounds_15_19529 : exactInterval 15 19529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19529 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19529) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19529 : oddCount 19529 15 = 10 ∧ acceleratedOrbit 15 19529 = 35198 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19529 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19529) = 3 ^ 10 * m + 35198 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19529.1, data_15_19529.2]

/-- Complete interval computation for depth 15, residue 19530. -/
theorem bounds_15_19530 : exactInterval 15 19530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19530 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19530) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19530 : oddCount 19530 15 = 8 ∧ acceleratedOrbit 15 19530 = 3914 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19530 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19530) = 3 ^ 8 * m + 3914 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19530.1, data_15_19530.2]

/-- Complete interval computation for depth 15, residue 19531. -/
theorem bounds_15_19531 : exactInterval 15 19531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19531 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19531) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19531 : oddCount 19531 15 = 5 ∧ acceleratedOrbit 15 19531 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19531 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19531) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19531.1, data_15_19531.2]

/-- Complete interval computation for depth 15, residue 19532. -/
theorem bounds_15_19532 : exactInterval 15 19532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19532 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19532) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19532 : oddCount 19532 15 = 8 ∧ acceleratedOrbit 15 19532 = 3914 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19532 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19532) = 3 ^ 8 * m + 3914 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19532.1, data_15_19532.2]

/-- Complete interval computation for depth 15, residue 19533. -/
theorem bounds_15_19533 : exactInterval 15 19533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19533 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19533) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19533 : oddCount 19533 15 = 8 ∧ acceleratedOrbit 15 19533 = 3914 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19533 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19533) = 3 ^ 8 * m + 3914 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19533.1, data_15_19533.2]

/-- Complete interval computation for depth 15, residue 19534. -/
theorem bounds_15_19534 : exactInterval 15 19534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19534 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19534) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19534 : oddCount 19534 15 = 8 ∧ acceleratedOrbit 15 19534 = 3914 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19534 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19534) = 3 ^ 8 * m + 3914 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19534.1, data_15_19534.2]

/-- Complete interval computation for depth 15, residue 19535. -/
theorem bounds_15_19535 : exactInterval 15 19535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19535 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19535) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19535 : oddCount 19535 15 = 8 ∧ acceleratedOrbit 15 19535 = 3914 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19535 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19535) = 3 ^ 8 * m + 3914 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19535.1, data_15_19535.2]

/-- Complete interval computation for depth 15, residue 19536. -/
theorem bounds_15_19536 : exactInterval 15 19536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19536 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19536) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19536 : oddCount 19536 15 = 4 ∧ acceleratedOrbit 15 19536 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19536 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19536) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19536.1, data_15_19536.2]

/-- Complete interval computation for depth 15, residue 19537. -/
theorem bounds_15_19537 : exactInterval 15 19537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19537 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19537) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19537 : oddCount 19537 15 = 8 ∧ acceleratedOrbit 15 19537 = 3914 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19537 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19537) = 3 ^ 8 * m + 3914 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19537.1, data_15_19537.2]

/-- Complete interval computation for depth 15, residue 19538. -/
theorem bounds_15_19538 : exactInterval 15 19538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19538 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19538) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19538 : oddCount 19538 15 = 11 ∧ acceleratedOrbit 15 19538 = 105644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19538 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19538) = 3 ^ 11 * m + 105644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19538.1, data_15_19538.2]

/-- Complete interval computation for depth 15, residue 19539. -/
theorem bounds_15_19539 : exactInterval 15 19539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19539 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19539) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19539 : oddCount 19539 15 = 11 ∧ acceleratedOrbit 15 19539 = 105644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19539 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19539) = 3 ^ 11 * m + 105644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19539.1, data_15_19539.2]

/-- Complete interval computation for depth 15, residue 19540. -/
theorem bounds_15_19540 : exactInterval 15 19540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19540 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19540) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19540 : oddCount 19540 15 = 4 ∧ acceleratedOrbit 15 19540 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19540 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19540) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19540.1, data_15_19540.2]

/-- Complete interval computation for depth 15, residue 19541. -/
theorem bounds_15_19541 : exactInterval 15 19541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19541 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19541) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19541 : oddCount 19541 15 = 4 ∧ acceleratedOrbit 15 19541 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19541 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19541) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19541.1, data_15_19541.2]

/-- Complete interval computation for depth 15, residue 19542. -/
theorem bounds_15_19542 : exactInterval 15 19542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19542 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19542) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19542 : oddCount 19542 15 = 5 ∧ acceleratedOrbit 15 19542 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19542 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19542) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19542.1, data_15_19542.2]

/-- Complete interval computation for depth 15, residue 19543. -/
theorem bounds_15_19543 : exactInterval 15 19543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19543 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19543) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19543 : oddCount 19543 15 = 5 ∧ acceleratedOrbit 15 19543 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19543 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19543) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19543.1, data_15_19543.2]

/-- Complete interval computation for depth 15, residue 19544. -/
theorem bounds_15_19544 : exactInterval 15 19544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19544 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19544) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19544 : oddCount 19544 15 = 7 ∧ acceleratedOrbit 15 19544 = 1306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19544 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19544) = 3 ^ 7 * m + 1306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19544.1, data_15_19544.2]

/-- Complete interval computation for depth 15, residue 19545. -/
theorem bounds_15_19545 : exactInterval 15 19545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19545 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19545) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19545 : oddCount 19545 15 = 10 ∧ acceleratedOrbit 15 19545 = 35234 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19545 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19545) = 3 ^ 10 * m + 35234 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19545.1, data_15_19545.2]

/-- Complete interval computation for depth 15, residue 19546. -/
theorem bounds_15_19546 : exactInterval 15 19546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19546 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19546) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19546 : oddCount 19546 15 = 7 ∧ acceleratedOrbit 15 19546 = 1306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19546 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19546) = 3 ^ 7 * m + 1306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19546.1, data_15_19546.2]

/-- Complete interval computation for depth 15, residue 19547. -/
theorem bounds_15_19547 : exactInterval 15 19547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19547 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19547) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19547 : oddCount 19547 15 = 10 ∧ acceleratedOrbit 15 19547 = 35228 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19547 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19547) = 3 ^ 10 * m + 35228 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19547.1, data_15_19547.2]

/-- Complete interval computation for depth 15, residue 19548. -/
theorem bounds_15_19548 : exactInterval 15 19548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19548 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19548) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19548 : oddCount 19548 15 = 7 ∧ acceleratedOrbit 15 19548 = 1306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19548 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19548) = 3 ^ 7 * m + 1306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19548.1, data_15_19548.2]

/-- Complete interval computation for depth 15, residue 19549. -/
theorem bounds_15_19549 : exactInterval 15 19549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19549 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19549) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19549 : oddCount 19549 15 = 7 ∧ acceleratedOrbit 15 19549 = 1306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19549 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19549) = 3 ^ 7 * m + 1306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19549.1, data_15_19549.2]

/-- Complete interval computation for depth 15, residue 19550. -/
theorem bounds_15_19550 : exactInterval 15 19550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19550 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19550) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19550 : oddCount 19550 15 = 12 ∧ acceleratedOrbit 15 19550 = 317114 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19550 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19550) = 3 ^ 12 * m + 317114 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19550.1, data_15_19550.2]

/-- Complete interval computation for depth 15, residue 19551. -/
theorem bounds_15_19551 : exactInterval 15 19551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19551 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19551) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19551 : oddCount 19551 15 = 12 ∧ acceleratedOrbit 15 19551 = 317114 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19551 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19551) = 3 ^ 12 * m + 317114 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19551.1, data_15_19551.2]

/-- Complete interval computation for depth 15, residue 19552. -/
theorem bounds_15_19552 : exactInterval 15 19552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19552 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19552) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19552 : oddCount 19552 15 = 4 ∧ acceleratedOrbit 15 19552 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19552 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19552) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19552.1, data_15_19552.2]

/-- Complete interval computation for depth 15, residue 19553. -/
theorem bounds_15_19553 : exactInterval 15 19553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19553 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19553) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19553 : oddCount 19553 15 = 8 ∧ acceleratedOrbit 15 19553 = 3916 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19553 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19553) = 3 ^ 8 * m + 3916 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19553.1, data_15_19553.2]

/-- Complete interval computation for depth 15, residue 19554. -/
theorem bounds_15_19554 : exactInterval 15 19554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19554 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19554) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19554 : oddCount 19554 15 = 7 ∧ acceleratedOrbit 15 19554 = 1306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19554 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19554) = 3 ^ 7 * m + 1306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19554.1, data_15_19554.2]

/-- Complete interval computation for depth 15, residue 19555. -/
theorem bounds_15_19555 : exactInterval 15 19555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19555 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19555) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19555 : oddCount 19555 15 = 7 ∧ acceleratedOrbit 15 19555 = 1306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19555 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19555) = 3 ^ 7 * m + 1306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19555.1, data_15_19555.2]

/-- Complete interval computation for depth 15, residue 19556. -/
theorem bounds_15_19556 : exactInterval 15 19556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19556 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19556) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19556 : oddCount 19556 15 = 7 ∧ acceleratedOrbit 15 19556 = 1306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19556 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19556) = 3 ^ 7 * m + 1306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19556.1, data_15_19556.2]

/-- Complete interval computation for depth 15, residue 19557. -/
theorem bounds_15_19557 : exactInterval 15 19557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19557 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19557) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19557 : oddCount 19557 15 = 7 ∧ acceleratedOrbit 15 19557 = 1306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19557 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19557) = 3 ^ 7 * m + 1306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19557.1, data_15_19557.2]

/-- Complete interval computation for depth 15, residue 19558. -/
theorem bounds_15_19558 : exactInterval 15 19558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19558 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19558) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19558 : oddCount 19558 15 = 7 ∧ acceleratedOrbit 15 19558 = 1306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19558 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19558) = 3 ^ 7 * m + 1306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19558.1, data_15_19558.2]

/-- Complete interval computation for depth 15, residue 19559. -/
theorem bounds_15_19559 : exactInterval 15 19559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19559 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19559) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19559 : oddCount 19559 15 = 12 ∧ acceleratedOrbit 15 19559 = 317236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19559 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19559) = 3 ^ 12 * m + 317236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19559.1, data_15_19559.2]

/-- Complete interval computation for depth 15, residue 19560. -/
theorem bounds_15_19560 : exactInterval 15 19560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19560 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19560) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19560 : oddCount 19560 15 = 4 ∧ acceleratedOrbit 15 19560 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19560 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19560) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19560.1, data_15_19560.2]

/-- Complete interval computation for depth 15, residue 19561. -/
theorem bounds_15_19561 : exactInterval 15 19561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19561 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19561) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19561 : oddCount 19561 15 = 10 ∧ acceleratedOrbit 15 19561 = 35255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19561 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19561) = 3 ^ 10 * m + 35255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19561.1, data_15_19561.2]

end Collatz.Research.PassageAtlas.Batch0597
