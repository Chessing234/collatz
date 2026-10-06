import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0536

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 17530. -/
theorem bounds_15_17530 : exactInterval 15 17530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17530 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17530) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17530 : oddCount 17530 15 = 7 ∧ acceleratedOrbit 15 17530 = 1171 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17530 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17530) = 3 ^ 7 * m + 1171 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17530.1, data_15_17530.2]

/-- Complete interval computation for depth 15, residue 17531. -/
theorem bounds_15_17531 : exactInterval 15 17531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17531 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17531) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17531 : oddCount 17531 15 = 8 ∧ acceleratedOrbit 15 17531 = 3511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17531 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17531) = 3 ^ 8 * m + 3511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17531.1, data_15_17531.2]

/-- Complete interval computation for depth 15, residue 17532. -/
theorem bounds_15_17532 : exactInterval 15 17532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17532 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17532) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17532 : oddCount 17532 15 = 8 ∧ acceleratedOrbit 15 17532 = 3512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17532 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17532) = 3 ^ 8 * m + 3512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17532.1, data_15_17532.2]

/-- Complete interval computation for depth 15, residue 17533. -/
theorem bounds_15_17533 : exactInterval 15 17533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17533 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17533) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17533 : oddCount 17533 15 = 8 ∧ acceleratedOrbit 15 17533 = 3512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17533 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17533) = 3 ^ 8 * m + 3512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17533.1, data_15_17533.2]

/-- Complete interval computation for depth 15, residue 17534. -/
theorem bounds_15_17534 : exactInterval 15 17534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17534 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17534) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17534 : oddCount 17534 15 = 8 ∧ acceleratedOrbit 15 17534 = 3512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17534 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17534) = 3 ^ 8 * m + 3512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17534.1, data_15_17534.2]

/-- Complete interval computation for depth 15, residue 17535. -/
theorem bounds_15_17535 : exactInterval 15 17535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17535 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17535) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17535 : oddCount 17535 15 = 10 ∧ acceleratedOrbit 15 17535 = 31601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17535 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17535) = 3 ^ 10 * m + 31601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17535.1, data_15_17535.2]

/-- Complete interval computation for depth 15, residue 17536. -/
theorem bounds_15_17536 : exactInterval 15 17536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17536 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17536) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17536 : oddCount 17536 15 = 6 ∧ acceleratedOrbit 15 17536 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17536 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17536) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17536.1, data_15_17536.2]

/-- Complete interval computation for depth 15, residue 17537. -/
theorem bounds_15_17537 : exactInterval 15 17537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17537 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17537) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17537 : oddCount 17537 15 = 10 ∧ acceleratedOrbit 15 17537 = 31610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17537 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17537) = 3 ^ 10 * m + 31610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17537.1, data_15_17537.2]

/-- Complete interval computation for depth 15, residue 17538. -/
theorem bounds_15_17538 : exactInterval 15 17538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17538 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17538) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17538 : oddCount 17538 15 = 6 ∧ acceleratedOrbit 15 17538 = 391 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17538 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17538) = 3 ^ 6 * m + 391 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17538.1, data_15_17538.2]

/-- Complete interval computation for depth 15, residue 17539. -/
theorem bounds_15_17539 : exactInterval 15 17539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17539 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17539) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17539 : oddCount 17539 15 = 6 ∧ acceleratedOrbit 15 17539 = 391 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17539 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17539) = 3 ^ 6 * m + 391 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17539.1, data_15_17539.2]

/-- Complete interval computation for depth 15, residue 17540. -/
theorem bounds_15_17540 : exactInterval 15 17540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17540 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17540) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17540 : oddCount 17540 15 = 6 ∧ acceleratedOrbit 15 17540 = 391 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17540 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17540) = 3 ^ 6 * m + 391 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17540.1, data_15_17540.2]

/-- Complete interval computation for depth 15, residue 17541. -/
theorem bounds_15_17541 : exactInterval 15 17541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17541 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17541) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17541 : oddCount 17541 15 = 6 ∧ acceleratedOrbit 15 17541 = 391 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17541 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17541) = 3 ^ 6 * m + 391 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17541.1, data_15_17541.2]

/-- Complete interval computation for depth 15, residue 17542. -/
theorem bounds_15_17542 : exactInterval 15 17542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17542 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17542) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17542 : oddCount 17542 15 = 6 ∧ acceleratedOrbit 15 17542 = 391 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17542 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17542) = 3 ^ 6 * m + 391 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17542.1, data_15_17542.2]

/-- Complete interval computation for depth 15, residue 17543. -/
theorem bounds_15_17543 : exactInterval 15 17543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17543 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17543) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17543 : oddCount 17543 15 = 9 ∧ acceleratedOrbit 15 17543 = 10540 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17543 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17543) = 3 ^ 9 * m + 10540 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17543.1, data_15_17543.2]

/-- Complete interval computation for depth 15, residue 17544. -/
theorem bounds_15_17544 : exactInterval 15 17544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17544 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17544) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17544 : oddCount 17544 15 = 7 ∧ acceleratedOrbit 15 17544 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17544 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17544) = 3 ^ 7 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17544.1, data_15_17544.2]

/-- Complete interval computation for depth 15, residue 17545. -/
theorem bounds_15_17545 : exactInterval 15 17545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17545 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17545) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17545 : oddCount 17545 15 = 11 ∧ acceleratedOrbit 15 17545 = 94861 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17545 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17545) = 3 ^ 11 * m + 94861 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17545.1, data_15_17545.2]

/-- Complete interval computation for depth 15, residue 17546. -/
theorem bounds_15_17546 : exactInterval 15 17546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17546 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17546) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17546 : oddCount 17546 15 = 7 ∧ acceleratedOrbit 15 17546 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17546 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17546) = 3 ^ 7 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17546.1, data_15_17546.2]

/-- Complete interval computation for depth 15, residue 17547. -/
theorem bounds_15_17547 : exactInterval 15 17547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17547 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17547) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17547 : oddCount 17547 15 = 9 ∧ acceleratedOrbit 15 17547 = 10543 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17547 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17547) = 3 ^ 9 * m + 10543 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17547.1, data_15_17547.2]

/-- Complete interval computation for depth 15, residue 17548. -/
theorem bounds_15_17548 : exactInterval 15 17548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17548 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17548) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17548 : oddCount 17548 15 = 7 ∧ acceleratedOrbit 15 17548 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17548 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17548) = 3 ^ 7 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17548.1, data_15_17548.2]

/-- Complete interval computation for depth 15, residue 17549. -/
theorem bounds_15_17549 : exactInterval 15 17549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17549 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17549) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17549 : oddCount 17549 15 = 7 ∧ acceleratedOrbit 15 17549 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17549 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17549) = 3 ^ 7 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17549.1, data_15_17549.2]

/-- Complete interval computation for depth 15, residue 17550. -/
theorem bounds_15_17550 : exactInterval 15 17550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17550 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17550) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17550 : oddCount 17550 15 = 7 ∧ acceleratedOrbit 15 17550 = 1172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17550 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17550) = 3 ^ 7 * m + 1172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17550.1, data_15_17550.2]

/-- Complete interval computation for depth 15, residue 17551. -/
theorem bounds_15_17551 : exactInterval 15 17551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17551 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17551) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17551 : oddCount 17551 15 = 7 ∧ acceleratedOrbit 15 17551 = 1172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17551 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17551) = 3 ^ 7 * m + 1172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17551.1, data_15_17551.2]

/-- Complete interval computation for depth 15, residue 17552. -/
theorem bounds_15_17552 : exactInterval 15 17552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17552 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17552) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17552 : oddCount 17552 15 = 7 ∧ acceleratedOrbit 15 17552 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17552 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17552) = 3 ^ 7 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17552.1, data_15_17552.2]

/-- Complete interval computation for depth 15, residue 17553. -/
theorem bounds_15_17553 : exactInterval 15 17553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17553 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17553) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17553 : oddCount 17553 15 = 7 ∧ acceleratedOrbit 15 17553 = 1172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17553 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17553) = 3 ^ 7 * m + 1172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17553.1, data_15_17553.2]

/-- Complete interval computation for depth 15, residue 17554. -/
theorem bounds_15_17554 : exactInterval 15 17554 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17554 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17554) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17554 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17554 : oddCount 17554 15 = 7 ∧ acceleratedOrbit 15 17554 = 1172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17554 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17554) = 3 ^ 7 * m + 1172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17554.1, data_15_17554.2]

/-- Complete interval computation for depth 15, residue 17555. -/
theorem bounds_15_17555 : exactInterval 15 17555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17555 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17555) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17555 : oddCount 17555 15 = 7 ∧ acceleratedOrbit 15 17555 = 1172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17555 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17555) = 3 ^ 7 * m + 1172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17555.1, data_15_17555.2]

/-- Complete interval computation for depth 15, residue 17556. -/
theorem bounds_15_17556 : exactInterval 15 17556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17556 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17556) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17556 : oddCount 17556 15 = 7 ∧ acceleratedOrbit 15 17556 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17556 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17556) = 3 ^ 7 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17556.1, data_15_17556.2]

/-- Complete interval computation for depth 15, residue 17557. -/
theorem bounds_15_17557 : exactInterval 15 17557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17557 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17557) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17557 : oddCount 17557 15 = 7 ∧ acceleratedOrbit 15 17557 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17557 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17557) = 3 ^ 7 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17557.1, data_15_17557.2]

/-- Complete interval computation for depth 15, residue 17558. -/
theorem bounds_15_17558 : exactInterval 15 17558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17558 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17558) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17558 : oddCount 17558 15 = 7 ∧ acceleratedOrbit 15 17558 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17558 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17558) = 3 ^ 7 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17558.1, data_15_17558.2]

/-- Complete interval computation for depth 15, residue 17559. -/
theorem bounds_15_17559 : exactInterval 15 17559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17559 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17559) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17559 : oddCount 17559 15 = 7 ∧ acceleratedOrbit 15 17559 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17559 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17559) = 3 ^ 7 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17559.1, data_15_17559.2]

/-- Complete interval computation for depth 15, residue 17560. -/
theorem bounds_15_17560 : exactInterval 15 17560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17560 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17560) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17560 : oddCount 17560 15 = 7 ∧ acceleratedOrbit 15 17560 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17560 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17560) = 3 ^ 7 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17560.1, data_15_17560.2]

/-- Complete interval computation for depth 15, residue 17561. -/
theorem bounds_15_17561 : exactInterval 15 17561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17561 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17561) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17561 : oddCount 17561 15 = 6 ∧ acceleratedOrbit 15 17561 = 391 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17561 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17561) = 3 ^ 6 * m + 391 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17561.1, data_15_17561.2]

/-- Complete interval computation for depth 15, residue 17562. -/
theorem bounds_15_17562 : exactInterval 15 17562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17562 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17562) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17562 : oddCount 17562 15 = 7 ∧ acceleratedOrbit 15 17562 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17562 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17562) = 3 ^ 7 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17562.1, data_15_17562.2]

end Collatz.Research.PassageAtlas.Batch0536
