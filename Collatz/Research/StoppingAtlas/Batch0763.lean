import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0763

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4536. -/
theorem bounds_13_4536 : exactInterval 13 4536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4536 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4536) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4536 : oddCount 4536 13 = 8 ∧ acceleratedOrbit 13 4536 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4536 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4536) = 3 ^ 8 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4536.1, data_13_4536.2]

/-- Complete interval computation for depth 13, residue 4537. -/
theorem bounds_13_4537 : exactInterval 13 4537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4537 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4537) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4537 : oddCount 4537 13 = 7 ∧ acceleratedOrbit 13 4537 = 1214 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4537 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4537) = 3 ^ 7 * m + 1214 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4537.1, data_13_4537.2]

/-- Complete interval computation for depth 13, residue 4538. -/
theorem bounds_13_4538 : exactInterval 13 4538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4538 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4538) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4538 : oddCount 4538 13 = 8 ∧ acceleratedOrbit 13 4538 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4538 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4538) = 3 ^ 8 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4538.1, data_13_4538.2]

/-- Complete interval computation for depth 13, residue 4539. -/
theorem bounds_13_4539 : exactInterval 13 4539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4539 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4539) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4539 : oddCount 4539 13 = 8 ∧ acceleratedOrbit 13 4539 = 3638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4539 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4539) = 3 ^ 8 * m + 3638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4539.1, data_13_4539.2]

/-- Complete interval computation for depth 13, residue 4540. -/
theorem bounds_13_4540 : exactInterval 13 4540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4540 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4540) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4540 : oddCount 4540 13 = 8 ∧ acceleratedOrbit 13 4540 = 3640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4540 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4540) = 3 ^ 8 * m + 3640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4540.1, data_13_4540.2]

/-- Complete interval computation for depth 13, residue 4541. -/
theorem bounds_13_4541 : exactInterval 13 4541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4541 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4541) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4541 : oddCount 4541 13 = 8 ∧ acceleratedOrbit 13 4541 = 3640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4541 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4541) = 3 ^ 8 * m + 3640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4541.1, data_13_4541.2]

/-- Complete interval computation for depth 13, residue 4542. -/
theorem bounds_13_4542 : exactInterval 13 4542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4542 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4542) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4542 : oddCount 4542 13 = 8 ∧ acceleratedOrbit 13 4542 = 3640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4542 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4542) = 3 ^ 8 * m + 3640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4542.1, data_13_4542.2]

/-- Complete interval computation for depth 13, residue 4543. -/
theorem bounds_13_4543 : exactInterval 13 4543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4543 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4543) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4543 : oddCount 4543 13 = 9 ∧ acceleratedOrbit 13 4543 = 10918 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4543 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4543) = 3 ^ 9 * m + 10918 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4543.1, data_13_4543.2]

/-- Complete interval computation for depth 13, residue 4544. -/
theorem bounds_13_4544 : exactInterval 13 4544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4544 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4544) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4544 : oddCount 4544 13 = 5 ∧ acceleratedOrbit 13 4544 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4544 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4544) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4544.1, data_13_4544.2]

/-- Complete interval computation for depth 13, residue 4545. -/
theorem bounds_13_4545 : exactInterval 13 4545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4545 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4545) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4545 : oddCount 4545 13 = 9 ∧ acceleratedOrbit 13 4545 = 10934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4545 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4545) = 3 ^ 9 * m + 10934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4545.1, data_13_4545.2]

/-- Complete interval computation for depth 13, residue 4546. -/
theorem bounds_13_4546 : exactInterval 13 4546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4546 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4546) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4546 : oddCount 4546 13 = 10 ∧ acceleratedOrbit 13 4546 = 32804 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4546 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4546) = 3 ^ 10 * m + 32804 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4546.1, data_13_4546.2]

/-- Complete interval computation for depth 13, residue 4547. -/
theorem bounds_13_4547 : exactInterval 13 4547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4547 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4547) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4547 : oddCount 4547 13 = 10 ∧ acceleratedOrbit 13 4547 = 32804 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4547 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4547) = 3 ^ 10 * m + 32804 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4547.1, data_13_4547.2]

/-- Complete interval computation for depth 13, residue 4548. -/
theorem bounds_13_4548 : exactInterval 13 4548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4548 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4548) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4548 : oddCount 4548 13 = 2 ∧ acceleratedOrbit 13 4548 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4548 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4548) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4548.1, data_13_4548.2]

/-- Complete interval computation for depth 13, residue 4549. -/
theorem bounds_13_4549 : exactInterval 13 4549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4549 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4549) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4549 : oddCount 4549 13 = 2 ∧ acceleratedOrbit 13 4549 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4549 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4549) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4549.1, data_13_4549.2]

/-- Complete interval computation for depth 13, residue 4550. -/
theorem bounds_13_4550 : exactInterval 13 4550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4550 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4550) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4550 : oddCount 4550 13 = 2 ∧ acceleratedOrbit 13 4550 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4550 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4550) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4550.1, data_13_4550.2]

end Collatz.Research.StoppingAtlas.Batch0763
