import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0694

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3476. -/
theorem bounds_13_3476 : exactInterval 13 3476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3476 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3476) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3476 : oddCount 3476 13 = 4 ∧ acceleratedOrbit 13 3476 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3476 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3476) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3476.1, data_13_3476.2]

/-- Complete interval computation for depth 13, residue 3477. -/
theorem bounds_13_3477 : exactInterval 13 3477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3477 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3477) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3477 : oddCount 3477 13 = 4 ∧ acceleratedOrbit 13 3477 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3477 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3477) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3477.1, data_13_3477.2]

/-- Complete interval computation for depth 13, residue 3478. -/
theorem bounds_13_3478 : exactInterval 13 3478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3478 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3478) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3478 : oddCount 3478 13 = 7 ∧ acceleratedOrbit 13 3478 = 931 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3478 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3478) = 3 ^ 7 * m + 931 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3478.1, data_13_3478.2]

/-- Complete interval computation for depth 13, residue 3479. -/
theorem bounds_13_3479 : exactInterval 13 3479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3479 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3479) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3479 : oddCount 3479 13 = 7 ∧ acceleratedOrbit 13 3479 = 931 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3479 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3479) = 3 ^ 7 * m + 931 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3479.1, data_13_3479.2]

/-- Complete interval computation for depth 13, residue 3480. -/
theorem bounds_13_3480 : exactInterval 13 3480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3480 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3480) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3480 : oddCount 3480 13 = 4 ∧ acceleratedOrbit 13 3480 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3480 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3480) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3480.1, data_13_3480.2]

/-- Complete interval computation for depth 13, residue 3481. -/
theorem bounds_13_3481 : exactInterval 13 3481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3481 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3481) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3481 : oddCount 3481 13 = 7 ∧ acceleratedOrbit 13 3481 = 931 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3481 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3481) = 3 ^ 7 * m + 931 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3481.1, data_13_3481.2]

/-- Complete interval computation for depth 13, residue 3482. -/
theorem bounds_13_3482 : exactInterval 13 3482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3482 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3482) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3482 : oddCount 3482 13 = 4 ∧ acceleratedOrbit 13 3482 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3482 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3482) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3482.1, data_13_3482.2]

/-- Complete interval computation for depth 13, residue 3483. -/
theorem bounds_13_3483 : exactInterval 13 3483 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3483 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3483) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3483 : oddCount 3483 13 = 8 ∧ acceleratedOrbit 13 3483 = 2791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3483 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3483) = 3 ^ 8 * m + 2791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3483.1, data_13_3483.2]

/-- Complete interval computation for depth 13, residue 3484. -/
theorem bounds_13_3484 : exactInterval 13 3484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3484 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3484) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3484 : oddCount 3484 13 = 9 ∧ acceleratedOrbit 13 3484 = 8383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3484 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3484) = 3 ^ 9 * m + 8383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3484.1, data_13_3484.2]

/-- Complete interval computation for depth 13, residue 3485. -/
theorem bounds_13_3485 : exactInterval 13 3485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3485 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3485) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3485 : oddCount 3485 13 = 9 ∧ acceleratedOrbit 13 3485 = 8383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3485 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3485) = 3 ^ 9 * m + 8383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3485.1, data_13_3485.2]

/-- Complete interval computation for depth 13, residue 3486. -/
theorem bounds_13_3486 : exactInterval 13 3486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3486 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3486) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3486 : oddCount 3486 13 = 9 ∧ acceleratedOrbit 13 3486 = 8383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3486 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3486) = 3 ^ 9 * m + 8383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3486.1, data_13_3486.2]

/-- Complete interval computation for depth 13, residue 3487. -/
theorem bounds_13_3487 : exactInterval 13 3487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3487 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3487) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3487 : oddCount 3487 13 = 9 ∧ acceleratedOrbit 13 3487 = 8381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3487 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3487) = 3 ^ 9 * m + 8381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3487.1, data_13_3487.2]

/-- Complete interval computation for depth 13, residue 3488. -/
theorem bounds_13_3488 : exactInterval 13 3488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3488 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3488) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3488 : oddCount 3488 13 = 5 ∧ acceleratedOrbit 13 3488 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3488 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3488) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3488.1, data_13_3488.2]

/-- Complete interval computation for depth 13, residue 3489. -/
theorem bounds_13_3489 : exactInterval 13 3489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3489 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3489) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3489 : oddCount 3489 13 = 8 ∧ acceleratedOrbit 13 3489 = 2798 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3489 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3489) = 3 ^ 8 * m + 2798 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3489.1, data_13_3489.2]

/-- Complete interval computation for depth 13, residue 3490. -/
theorem bounds_13_3490 : exactInterval 13 3490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3490 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3490) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3490 : oddCount 3490 13 = 7 ∧ acceleratedOrbit 13 3490 = 935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3490 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3490) = 3 ^ 7 * m + 935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3490.1, data_13_3490.2]

end Collatz.Research.StoppingAtlas.Batch0694
