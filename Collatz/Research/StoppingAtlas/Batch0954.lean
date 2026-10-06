import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0954

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7470. -/
theorem bounds_13_7470 : exactInterval 13 7470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7470 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7470) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7470 : oddCount 7470 13 = 4 ∧ acceleratedOrbit 13 7470 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7470 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7470) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7470.1, data_13_7470.2]

/-- Complete interval computation for depth 13, residue 7471. -/
theorem bounds_13_7471 : exactInterval 13 7471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7471 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7471) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7471 : oddCount 7471 13 = 10 ∧ acceleratedOrbit 13 7471 = 53864 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7471 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7471) = 3 ^ 10 * m + 53864 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7471.1, data_13_7471.2]

/-- Complete interval computation for depth 13, residue 7472. -/
theorem bounds_13_7472 : exactInterval 13 7472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7472 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7472) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7472 : oddCount 7472 13 = 6 ∧ acceleratedOrbit 13 7472 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7472 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7472) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7472.1, data_13_7472.2]

/-- Complete interval computation for depth 13, residue 7473. -/
theorem bounds_13_7473 : exactInterval 13 7473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7473 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7473) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7473 : oddCount 7473 13 = 8 ∧ acceleratedOrbit 13 7473 = 5993 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7473 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7473) = 3 ^ 8 * m + 5993 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7473.1, data_13_7473.2]

/-- Complete interval computation for depth 13, residue 7474. -/
theorem bounds_13_7474 : exactInterval 13 7474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7474 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7474) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7474 : oddCount 7474 13 = 8 ∧ acceleratedOrbit 13 7474 = 5993 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7474 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7474) = 3 ^ 8 * m + 5993 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7474.1, data_13_7474.2]

/-- Complete interval computation for depth 13, residue 7475. -/
theorem bounds_13_7475 : exactInterval 13 7475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7475 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7475) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7475 : oddCount 7475 13 = 8 ∧ acceleratedOrbit 13 7475 = 5993 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7475 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7475) = 3 ^ 8 * m + 5993 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7475.1, data_13_7475.2]

/-- Complete interval computation for depth 13, residue 7476. -/
theorem bounds_13_7476 : exactInterval 13 7476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7476 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7476) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7476 : oddCount 7476 13 = 6 ∧ acceleratedOrbit 13 7476 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7476 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7476) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7476.1, data_13_7476.2]

/-- Complete interval computation for depth 13, residue 7477. -/
theorem bounds_13_7477 : exactInterval 13 7477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7477 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7477) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7477 : oddCount 7477 13 = 6 ∧ acceleratedOrbit 13 7477 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7477 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7477) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7477.1, data_13_7477.2]

/-- Complete interval computation for depth 13, residue 7478. -/
theorem bounds_13_7478 : exactInterval 13 7478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7478 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7478) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7478 : oddCount 7478 13 = 9 ∧ acceleratedOrbit 13 7478 = 17975 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7478 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7478) = 3 ^ 9 * m + 17975 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7478.1, data_13_7478.2]

/-- Complete interval computation for depth 13, residue 7479. -/
theorem bounds_13_7479 : exactInterval 13 7479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7479 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7479) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7479 : oddCount 7479 13 = 9 ∧ acceleratedOrbit 13 7479 = 17975 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7479 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7479) = 3 ^ 9 * m + 17975 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7479.1, data_13_7479.2]

/-- Complete interval computation for depth 13, residue 7480. -/
theorem bounds_13_7480 : exactInterval 13 7480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7480 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7480) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7480 : oddCount 7480 13 = 7 ∧ acceleratedOrbit 13 7480 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7480 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7480) = 3 ^ 7 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7480.1, data_13_7480.2]

/-- Complete interval computation for depth 13, residue 7481. -/
theorem bounds_13_7481 : exactInterval 13 7481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7481 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7481) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7481 : oddCount 7481 13 = 10 ∧ acceleratedOrbit 13 7481 = 53945 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7481 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7481) = 3 ^ 10 * m + 53945 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7481.1, data_13_7481.2]

/-- Complete interval computation for depth 13, residue 7482. -/
theorem bounds_13_7482 : exactInterval 13 7482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7482 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7482) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7482 : oddCount 7482 13 = 7 ∧ acceleratedOrbit 13 7482 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7482 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7482) = 3 ^ 7 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7482.1, data_13_7482.2]

/-- Complete interval computation for depth 13, residue 7483. -/
theorem bounds_13_7483 : exactInterval 13 7483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7483 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7483) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7483 : oddCount 7483 13 = 4 ∧ acceleratedOrbit 13 7483 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7483 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7483) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7483.1, data_13_7483.2]

/-- Complete interval computation for depth 13, residue 7484. -/
theorem bounds_13_7484 : exactInterval 13 7484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7484 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7484) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7484 : oddCount 7484 13 = 7 ∧ acceleratedOrbit 13 7484 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7484 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7484) = 3 ^ 7 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7484.1, data_13_7484.2]

end Collatz.Research.StoppingAtlas.Batch0954
