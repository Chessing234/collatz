import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0139

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 4521. -/
theorem bounds_15_4521 : exactInterval 15 4521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4521 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4521) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4521 : oddCount 4521 15 = 11 ∧ acceleratedOrbit 15 4521 = 24452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4521 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4521) = 3 ^ 11 * m + 24452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4521.1, data_15_4521.2]

/-- Complete interval computation for depth 15, residue 4522. -/
theorem bounds_15_4522 : exactInterval 15 4522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4522 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4522) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4522 : oddCount 4522 15 = 3 ∧ acceleratedOrbit 15 4522 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4522 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4522) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4522.1, data_15_4522.2]

/-- Complete interval computation for depth 15, residue 4523. -/
theorem bounds_15_4523 : exactInterval 15 4523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4523 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4523) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4523 : oddCount 4523 15 = 10 ∧ acceleratedOrbit 15 4523 = 8156 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4523 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4523) = 3 ^ 10 * m + 8156 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4523.1, data_15_4523.2]

/-- Complete interval computation for depth 15, residue 4524. -/
theorem bounds_15_4524 : exactInterval 15 4524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4524 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4524) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4524 : oddCount 4524 15 = 8 ∧ acceleratedOrbit 15 4524 = 908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4524 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4524) = 3 ^ 8 * m + 908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4524.1, data_15_4524.2]

/-- Complete interval computation for depth 15, residue 4525. -/
theorem bounds_15_4525 : exactInterval 15 4525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4525 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4525) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4525 : oddCount 4525 15 = 8 ∧ acceleratedOrbit 15 4525 = 908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4525 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4525) = 3 ^ 8 * m + 908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4525.1, data_15_4525.2]

/-- Complete interval computation for depth 15, residue 4526. -/
theorem bounds_15_4526 : exactInterval 15 4526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4526 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4526) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4526 : oddCount 4526 15 = 8 ∧ acceleratedOrbit 15 4526 = 908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4526 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4526) = 3 ^ 8 * m + 908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4526.1, data_15_4526.2]

/-- Complete interval computation for depth 15, residue 4527. -/
theorem bounds_15_4527 : exactInterval 15 4527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4527 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4527) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4527 : oddCount 4527 15 = 8 ∧ acceleratedOrbit 15 4527 = 908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4527 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4527) = 3 ^ 8 * m + 908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4527.1, data_15_4527.2]

/-- Complete interval computation for depth 15, residue 4528. -/
theorem bounds_15_4528 : exactInterval 15 4528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4528 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4528) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4528 : oddCount 4528 15 = 8 ∧ acceleratedOrbit 15 4528 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4528 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4528) = 3 ^ 8 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4528.1, data_15_4528.2]

/-- Complete interval computation for depth 15, residue 4529. -/
theorem bounds_15_4529 : exactInterval 15 4529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4529 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4529) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4529 : oddCount 4529 15 = 8 ∧ acceleratedOrbit 15 4529 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4529 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4529) = 3 ^ 8 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4529.1, data_15_4529.2]

/-- Complete interval computation for depth 15, residue 4530. -/
theorem bounds_15_4530 : exactInterval 15 4530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4530 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4530) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4530 : oddCount 4530 15 = 8 ∧ acceleratedOrbit 15 4530 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4530 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4530) = 3 ^ 8 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4530.1, data_15_4530.2]

/-- Complete interval computation for depth 15, residue 4531. -/
theorem bounds_15_4531 : exactInterval 15 4531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4531 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4531) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4531 : oddCount 4531 15 = 8 ∧ acceleratedOrbit 15 4531 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4531 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4531) = 3 ^ 8 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4531.1, data_15_4531.2]

/-- Complete interval computation for depth 15, residue 4532. -/
theorem bounds_15_4532 : exactInterval 15 4532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4532 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4532) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4532 : oddCount 4532 15 = 8 ∧ acceleratedOrbit 15 4532 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4532 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4532) = 3 ^ 8 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4532.1, data_15_4532.2]

/-- Complete interval computation for depth 15, residue 4533. -/
theorem bounds_15_4533 : exactInterval 15 4533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4533 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4533) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4533 : oddCount 4533 15 = 8 ∧ acceleratedOrbit 15 4533 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4533 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4533) = 3 ^ 8 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4533.1, data_15_4533.2]

/-- Complete interval computation for depth 15, residue 4534. -/
theorem bounds_15_4534 : exactInterval 15 4534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4534 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4534) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4534 : oddCount 4534 15 = 10 ∧ acceleratedOrbit 15 4534 = 8180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4534 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4534) = 3 ^ 10 * m + 8180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4534.1, data_15_4534.2]

/-- Complete interval computation for depth 15, residue 4535. -/
theorem bounds_15_4535 : exactInterval 15 4535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4535 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4535) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4535 : oddCount 4535 15 = 10 ∧ acceleratedOrbit 15 4535 = 8180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4535 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4535) = 3 ^ 10 * m + 8180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4535.1, data_15_4535.2]

/-- Complete interval computation for depth 15, residue 4536. -/
theorem bounds_15_4536 : exactInterval 15 4536 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4536 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4536) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4536 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4536 : oddCount 4536 15 = 8 ∧ acceleratedOrbit 15 4536 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4536 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4536) = 3 ^ 8 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4536.1, data_15_4536.2]

/-- Complete interval computation for depth 15, residue 4537. -/
theorem bounds_15_4537 : exactInterval 15 4537 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4537 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4537) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4537 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4537 : oddCount 4537 15 = 8 ∧ acceleratedOrbit 15 4537 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4537 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4537) = 3 ^ 8 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4537.1, data_15_4537.2]

/-- Complete interval computation for depth 15, residue 4538. -/
theorem bounds_15_4538 : exactInterval 15 4538 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4538 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4538) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4538 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4538 : oddCount 4538 15 = 8 ∧ acceleratedOrbit 15 4538 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4538 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4538) = 3 ^ 8 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4538.1, data_15_4538.2]

/-- Complete interval computation for depth 15, residue 4539. -/
theorem bounds_15_4539 : exactInterval 15 4539 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4539 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4539) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4539 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4539 : oddCount 4539 15 = 9 ∧ acceleratedOrbit 15 4539 = 2729 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4539 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4539) = 3 ^ 9 * m + 2729 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4539.1, data_15_4539.2]

/-- Complete interval computation for depth 15, residue 4540. -/
theorem bounds_15_4540 : exactInterval 15 4540 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4540 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4540) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4540 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4540 : oddCount 4540 15 = 8 ∧ acceleratedOrbit 15 4540 = 910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4540 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4540) = 3 ^ 8 * m + 910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4540.1, data_15_4540.2]

/-- Complete interval computation for depth 15, residue 4541. -/
theorem bounds_15_4541 : exactInterval 15 4541 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4541 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4541) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4541 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4541 : oddCount 4541 15 = 8 ∧ acceleratedOrbit 15 4541 = 910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4541 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4541) = 3 ^ 8 * m + 910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4541.1, data_15_4541.2]

/-- Complete interval computation for depth 15, residue 4542. -/
theorem bounds_15_4542 : exactInterval 15 4542 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4542 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4542) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4542 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4542 : oddCount 4542 15 = 8 ∧ acceleratedOrbit 15 4542 = 910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4542 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4542) = 3 ^ 8 * m + 910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4542.1, data_15_4542.2]

/-- Complete interval computation for depth 15, residue 4543. -/
theorem bounds_15_4543 : exactInterval 15 4543 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4543 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4543) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4543 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4543 : oddCount 4543 15 = 10 ∧ acceleratedOrbit 15 4543 = 8189 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4543 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4543) = 3 ^ 10 * m + 8189 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4543.1, data_15_4543.2]

/-- Complete interval computation for depth 15, residue 4544. -/
theorem bounds_15_4544 : exactInterval 15 4544 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4544 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4544) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4544 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4544 : oddCount 4544 15 = 6 ∧ acceleratedOrbit 15 4544 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4544 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4544) = 3 ^ 6 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4544.1, data_15_4544.2]

/-- Complete interval computation for depth 15, residue 4545. -/
theorem bounds_15_4545 : exactInterval 15 4545 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4545 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4545) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4545 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4545 : oddCount 4545 15 = 10 ∧ acceleratedOrbit 15 4545 = 8201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4545 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4545) = 3 ^ 10 * m + 8201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4545.1, data_15_4545.2]

/-- Complete interval computation for depth 15, residue 4546. -/
theorem bounds_15_4546 : exactInterval 15 4546 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4546 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4546) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4546 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4546 : oddCount 4546 15 = 10 ∧ acceleratedOrbit 15 4546 = 8201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4546 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4546) = 3 ^ 10 * m + 8201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4546.1, data_15_4546.2]

/-- Complete interval computation for depth 15, residue 4547. -/
theorem bounds_15_4547 : exactInterval 15 4547 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4547 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4547) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4547 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4547 : oddCount 4547 15 = 10 ∧ acceleratedOrbit 15 4547 = 8201 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4547 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4547) = 3 ^ 10 * m + 8201 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4547.1, data_15_4547.2]

/-- Complete interval computation for depth 15, residue 4548. -/
theorem bounds_15_4548 : exactInterval 15 4548 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4548 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4548) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4548 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4548 : oddCount 4548 15 = 3 ∧ acceleratedOrbit 15 4548 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4548 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4548) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4548.1, data_15_4548.2]

/-- Complete interval computation for depth 15, residue 4549. -/
theorem bounds_15_4549 : exactInterval 15 4549 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4549 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4549) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4549 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4549 : oddCount 4549 15 = 3 ∧ acceleratedOrbit 15 4549 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4549 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4549) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4549.1, data_15_4549.2]

/-- Complete interval computation for depth 15, residue 4550. -/
theorem bounds_15_4550 : exactInterval 15 4550 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4550 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4550) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4550 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4550 : oddCount 4550 15 = 3 ∧ acceleratedOrbit 15 4550 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4550 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4550) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4550.1, data_15_4550.2]

/-- Complete interval computation for depth 15, residue 4551. -/
theorem bounds_15_4551 : exactInterval 15 4551 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4551 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4551) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4551 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4551 : oddCount 4551 15 = 10 ∧ acceleratedOrbit 15 4551 = 8207 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4551 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4551) = 3 ^ 10 * m + 8207 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4551.1, data_15_4551.2]

/-- Complete interval computation for depth 15, residue 4552. -/
theorem bounds_15_4552 : exactInterval 15 4552 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4552 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4552) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4552 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4552 : oddCount 4552 15 = 8 ∧ acceleratedOrbit 15 4552 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4552 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4552) = 3 ^ 8 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4552.1, data_15_4552.2]

/-- Complete interval computation for depth 15, residue 4553. -/
theorem bounds_15_4553 : exactInterval 15 4553 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4553 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4553) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4553 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4553 : oddCount 4553 15 = 8 ∧ acceleratedOrbit 15 4553 = 913 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4553 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4553) = 3 ^ 8 * m + 913 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4553.1, data_15_4553.2]

end Collatz.Research.PassageAtlas.Batch0139
