import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0762

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4520. -/
theorem bounds_13_4520 : exactInterval 13 4520 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4520 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4520) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4520 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4520 : oddCount 4520 13 = 2 ∧ acceleratedOrbit 13 4520 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4520 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4520) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4520.1, data_13_4520.2]

/-- Complete interval computation for depth 13, residue 4521. -/
theorem bounds_13_4521 : exactInterval 13 4521 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4521 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4521) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4521 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4521 : oddCount 4521 13 = 9 ∧ acceleratedOrbit 13 4521 = 10867 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4521 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4521) = 3 ^ 9 * m + 10867 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4521.1, data_13_4521.2]

/-- Complete interval computation for depth 13, residue 4522. -/
theorem bounds_13_4522 : exactInterval 13 4522 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4522 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4522) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4522 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4522 : oddCount 4522 13 = 2 ∧ acceleratedOrbit 13 4522 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4522 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4522) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4522.1, data_13_4522.2]

/-- Complete interval computation for depth 13, residue 4523. -/
theorem bounds_13_4523 : exactInterval 13 4523 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4523 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4523) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4523 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4523 : oddCount 4523 13 = 9 ∧ acceleratedOrbit 13 4523 = 10874 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4523 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4523) = 3 ^ 9 * m + 10874 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4523.1, data_13_4523.2]

/-- Complete interval computation for depth 13, residue 4524. -/
theorem bounds_13_4524 : exactInterval 13 4524 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4524 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4524) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4524 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4524 : oddCount 4524 13 = 7 ∧ acceleratedOrbit 13 4524 = 1210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4524 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4524) = 3 ^ 7 * m + 1210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4524.1, data_13_4524.2]

/-- Complete interval computation for depth 13, residue 4525. -/
theorem bounds_13_4525 : exactInterval 13 4525 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4525 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4525) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4525 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4525 : oddCount 4525 13 = 7 ∧ acceleratedOrbit 13 4525 = 1210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4525 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4525) = 3 ^ 7 * m + 1210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4525.1, data_13_4525.2]

/-- Complete interval computation for depth 13, residue 4526. -/
theorem bounds_13_4526 : exactInterval 13 4526 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4526 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4526) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4526 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4526 : oddCount 4526 13 = 7 ∧ acceleratedOrbit 13 4526 = 1210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4526 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4526) = 3 ^ 7 * m + 1210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4526.1, data_13_4526.2]

/-- Complete interval computation for depth 13, residue 4527. -/
theorem bounds_13_4527 : exactInterval 13 4527 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4527 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4527) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4527 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4527 : oddCount 4527 13 = 6 ∧ acceleratedOrbit 13 4527 = 403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4527 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4527) = 3 ^ 6 * m + 403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4527.1, data_13_4527.2]

/-- Complete interval computation for depth 13, residue 4528. -/
theorem bounds_13_4528 : exactInterval 13 4528 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4528 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4528) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4528 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4528 : oddCount 4528 13 = 8 ∧ acceleratedOrbit 13 4528 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4528 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4528) = 3 ^ 8 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4528.1, data_13_4528.2]

/-- Complete interval computation for depth 13, residue 4529. -/
theorem bounds_13_4529 : exactInterval 13 4529 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4529 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4529) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4529 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4529 : oddCount 4529 13 = 7 ∧ acceleratedOrbit 13 4529 = 1214 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4529 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4529) = 3 ^ 7 * m + 1214 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4529.1, data_13_4529.2]

/-- Complete interval computation for depth 13, residue 4530. -/
theorem bounds_13_4530 : exactInterval 13 4530 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4530 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4530) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4530 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4530 : oddCount 4530 13 = 7 ∧ acceleratedOrbit 13 4530 = 1214 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4530 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4530) = 3 ^ 7 * m + 1214 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4530.1, data_13_4530.2]

/-- Complete interval computation for depth 13, residue 4531. -/
theorem bounds_13_4531 : exactInterval 13 4531 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4531 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4531) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4531 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4531 : oddCount 4531 13 = 7 ∧ acceleratedOrbit 13 4531 = 1214 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4531 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4531) = 3 ^ 7 * m + 1214 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4531.1, data_13_4531.2]

/-- Complete interval computation for depth 13, residue 4532. -/
theorem bounds_13_4532 : exactInterval 13 4532 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4532 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4532) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4532 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4532 : oddCount 4532 13 = 8 ∧ acceleratedOrbit 13 4532 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4532 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4532) = 3 ^ 8 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4532.1, data_13_4532.2]

/-- Complete interval computation for depth 13, residue 4533. -/
theorem bounds_13_4533 : exactInterval 13 4533 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4533 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4533) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4533 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4533 : oddCount 4533 13 = 8 ∧ acceleratedOrbit 13 4533 = 3644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4533 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4533) = 3 ^ 8 * m + 3644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4533.1, data_13_4533.2]

/-- Complete interval computation for depth 13, residue 4534. -/
theorem bounds_13_4534 : exactInterval 13 4534 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4534 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4534) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4534 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4534 : oddCount 4534 13 = 8 ∧ acceleratedOrbit 13 4534 = 3635 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4534 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4534) = 3 ^ 8 * m + 3635 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4534.1, data_13_4534.2]

/-- Complete interval computation for depth 13, residue 4535. -/
theorem bounds_13_4535 : exactInterval 13 4535 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4535 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4535) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4535 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4535 : oddCount 4535 13 = 8 ∧ acceleratedOrbit 13 4535 = 3635 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4535 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4535) = 3 ^ 8 * m + 3635 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4535.1, data_13_4535.2]

end Collatz.Research.StoppingAtlas.Batch0762
