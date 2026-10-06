import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0496

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 435. -/
theorem bounds_13_435 : exactInterval 13 435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_435 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 435) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_435 : oddCount 435 13 = 6 ∧ acceleratedOrbit 13 435 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_435 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 435) = 3 ^ 6 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_435.1, data_13_435.2]

/-- Complete interval computation for depth 13, residue 436. -/
theorem bounds_13_436 : exactInterval 13 436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_436 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 436) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_436 : oddCount 436 13 = 7 ∧ acceleratedOrbit 13 436 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_436 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 436) = 3 ^ 7 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_436.1, data_13_436.2]

/-- Complete interval computation for depth 13, residue 437. -/
theorem bounds_13_437 : exactInterval 13 437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_437 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 437) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_437 : oddCount 437 13 = 7 ∧ acceleratedOrbit 13 437 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_437 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 437) = 3 ^ 7 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_437.1, data_13_437.2]

/-- Complete interval computation for depth 13, residue 438. -/
theorem bounds_13_438 : exactInterval 13 438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_438 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 438) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_438 : oddCount 438 13 = 7 ∧ acceleratedOrbit 13 438 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_438 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 438) = 3 ^ 7 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_438.1, data_13_438.2]

/-- Complete interval computation for depth 13, residue 439. -/
theorem bounds_13_439 : exactInterval 13 439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_439 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 439) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_439 : oddCount 439 13 = 7 ∧ acceleratedOrbit 13 439 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_439 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 439) = 3 ^ 7 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_439.1, data_13_439.2]

/-- Complete interval computation for depth 13, residue 440. -/
theorem bounds_13_440 : exactInterval 13 440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_440 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 440) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_440 : oddCount 440 13 = 7 ∧ acceleratedOrbit 13 440 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_440 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 440) = 3 ^ 7 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_440.1, data_13_440.2]

/-- Complete interval computation for depth 13, residue 441. -/
theorem bounds_13_441 : exactInterval 13 441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_441 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 441) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_441 : oddCount 441 13 = 6 ∧ acceleratedOrbit 13 441 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_441 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 441) = 3 ^ 6 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_441.1, data_13_441.2]

/-- Complete interval computation for depth 13, residue 442. -/
theorem bounds_13_442 : exactInterval 13 442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_442 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 442) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_442 : oddCount 442 13 = 7 ∧ acceleratedOrbit 13 442 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_442 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 442) = 3 ^ 7 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_442.1, data_13_442.2]

/-- Complete interval computation for depth 13, residue 443. -/
theorem bounds_13_443 : exactInterval 13 443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_443 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 443) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_443 : oddCount 443 13 = 7 ∧ acceleratedOrbit 13 443 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_443 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 443) = 3 ^ 7 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_443.1, data_13_443.2]

/-- Complete interval computation for depth 13, residue 444. -/
theorem bounds_13_444 : exactInterval 13 444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_444 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 444) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_444 : oddCount 444 13 = 9 ∧ acceleratedOrbit 13 444 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_444 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 444) = 3 ^ 9 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_444.1, data_13_444.2]

/-- Complete interval computation for depth 13, residue 445. -/
theorem bounds_13_445 : exactInterval 13 445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_445 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 445) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_445 : oddCount 445 13 = 9 ∧ acceleratedOrbit 13 445 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_445 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 445) = 3 ^ 9 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_445.1, data_13_445.2]

/-- Complete interval computation for depth 13, residue 446. -/
theorem bounds_13_446 : exactInterval 13 446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_446 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 446) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_446 : oddCount 446 13 = 9 ∧ acceleratedOrbit 13 446 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_446 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 446) = 3 ^ 9 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_446.1, data_13_446.2]

/-- Complete interval computation for depth 13, residue 447. -/
theorem bounds_13_447 : exactInterval 13 447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_447 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 447) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_447 : oddCount 447 13 = 10 ∧ acceleratedOrbit 13 447 = 3230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_447 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 447) = 3 ^ 10 * m + 3230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_447.1, data_13_447.2]

/-- Complete interval computation for depth 13, residue 448. -/
theorem bounds_13_448 : exactInterval 13 448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_448 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 448) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_448 : oddCount 448 13 = 4 ∧ acceleratedOrbit 13 448 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_448 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 448) = 3 ^ 4 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_448.1, data_13_448.2]

/-- Complete interval computation for depth 13, residue 449. -/
theorem bounds_13_449 : exactInterval 13 449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_449 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 449) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_449 : oddCount 449 13 = 8 ∧ acceleratedOrbit 13 449 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_449 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 449) = 3 ^ 8 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_449.1, data_13_449.2]

end Collatz.Research.StoppingAtlas.Batch0496
