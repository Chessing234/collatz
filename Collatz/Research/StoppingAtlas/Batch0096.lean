import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0096

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 435. -/
theorem bounds_11_435 : exactInterval 11 435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_435 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 435) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_435 : oddCount 435 11 = 5 ∧ acceleratedOrbit 11 435 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_435 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 435) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_435.1, data_11_435.2]

/-- Complete interval computation for depth 11, residue 436. -/
theorem bounds_11_436 : exactInterval 11 436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_436 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 436) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_436 : oddCount 436 11 = 6 ∧ acceleratedOrbit 11 436 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_436 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 436) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_436.1, data_11_436.2]

/-- Complete interval computation for depth 11, residue 437. -/
theorem bounds_11_437 : exactInterval 11 437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_437 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 437) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_437 : oddCount 437 11 = 6 ∧ acceleratedOrbit 11 437 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_437 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 437) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_437.1, data_11_437.2]

/-- Complete interval computation for depth 11, residue 438. -/
theorem bounds_11_438 : exactInterval 11 438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_438 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 438) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_438 : oddCount 438 11 = 6 ∧ acceleratedOrbit 11 438 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_438 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 438) = 3 ^ 6 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_438.1, data_11_438.2]

/-- Complete interval computation for depth 11, residue 439. -/
theorem bounds_11_439 : exactInterval 11 439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_439 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 439) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_439 : oddCount 439 11 = 6 ∧ acceleratedOrbit 11 439 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_439 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 439) = 3 ^ 6 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_439.1, data_11_439.2]

/-- Complete interval computation for depth 11, residue 440. -/
theorem bounds_11_440 : exactInterval 11 440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_440 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 440) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_440 : oddCount 440 11 = 6 ∧ acceleratedOrbit 11 440 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_440 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 440) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_440.1, data_11_440.2]

/-- Complete interval computation for depth 11, residue 441. -/
theorem bounds_11_441 : exactInterval 11 441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_441 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 441) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_441 : oddCount 441 11 = 5 ∧ acceleratedOrbit 11 441 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_441 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 441) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_441.1, data_11_441.2]

/-- Complete interval computation for depth 11, residue 442. -/
theorem bounds_11_442 : exactInterval 11 442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_442 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 442) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_442 : oddCount 442 11 = 6 ∧ acceleratedOrbit 11 442 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_442 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 442) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_442.1, data_11_442.2]

/-- Complete interval computation for depth 11, residue 443. -/
theorem bounds_11_443 : exactInterval 11 443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_443 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 443) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_443 : oddCount 443 11 = 7 ∧ acceleratedOrbit 11 443 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_443 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 443) = 3 ^ 7 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_443.1, data_11_443.2]

/-- Complete interval computation for depth 11, residue 444. -/
theorem bounds_11_444 : exactInterval 11 444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_444 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 444) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_444 : oddCount 444 11 = 7 ∧ acceleratedOrbit 11 444 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_444 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 444) = 3 ^ 7 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_444.1, data_11_444.2]

/-- Complete interval computation for depth 11, residue 445. -/
theorem bounds_11_445 : exactInterval 11 445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_445 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 445) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_445 : oddCount 445 11 = 7 ∧ acceleratedOrbit 11 445 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_445 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 445) = 3 ^ 7 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_445.1, data_11_445.2]

/-- Complete interval computation for depth 11, residue 446. -/
theorem bounds_11_446 : exactInterval 11 446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_446 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 446) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_446 : oddCount 446 11 = 7 ∧ acceleratedOrbit 11 446 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_446 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 446) = 3 ^ 7 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_446.1, data_11_446.2]

/-- Complete interval computation for depth 11, residue 447. -/
theorem bounds_11_447 : exactInterval 11 447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_447 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 447) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_447 : oddCount 447 11 = 9 ∧ acceleratedOrbit 11 447 = 4306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_447 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 447) = 3 ^ 9 * m + 4306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_447.1, data_11_447.2]

/-- Complete interval computation for depth 11, residue 448. -/
theorem bounds_11_448 : exactInterval 11 448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_448 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 448) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_448 : oddCount 448 11 = 4 ∧ acceleratedOrbit 11 448 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_448 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 448) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_448.1, data_11_448.2]

/-- Complete interval computation for depth 11, residue 449. -/
theorem bounds_11_449 : exactInterval 11 449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_449 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 449) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_449 : oddCount 449 11 = 7 ∧ acceleratedOrbit 11 449 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_449 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 449) = 3 ^ 7 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_449.1, data_11_449.2]

end Collatz.Research.StoppingAtlas.Batch0096
