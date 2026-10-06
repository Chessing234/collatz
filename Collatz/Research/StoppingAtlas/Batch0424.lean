import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0424

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3425. -/
theorem bounds_12_3425 : exactInterval 12 3425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3425 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3425) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3425 : oddCount 3425 12 = 6 ∧ acceleratedOrbit 12 3425 = 610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3425 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3425) = 3 ^ 6 * m + 610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3425.1, data_12_3425.2]

/-- Complete interval computation for depth 12, residue 3426. -/
theorem bounds_12_3426 : exactInterval 12 3426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3426 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3426) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3426 : oddCount 3426 12 = 4 ∧ acceleratedOrbit 12 3426 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3426 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3426) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3426.1, data_12_3426.2]

/-- Complete interval computation for depth 12, residue 3427. -/
theorem bounds_12_3427 : exactInterval 12 3427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3427 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3427) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3427 : oddCount 3427 12 = 4 ∧ acceleratedOrbit 12 3427 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3427 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3427) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3427.1, data_12_3427.2]

/-- Complete interval computation for depth 12, residue 3428. -/
theorem bounds_12_3428 : exactInterval 12 3428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3428 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3428) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3428 : oddCount 3428 12 = 4 ∧ acceleratedOrbit 12 3428 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3428 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3428) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3428.1, data_12_3428.2]

/-- Complete interval computation for depth 12, residue 3429. -/
theorem bounds_12_3429 : exactInterval 12 3429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3429 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3429) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3429 : oddCount 3429 12 = 4 ∧ acceleratedOrbit 12 3429 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3429 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3429) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3429.1, data_12_3429.2]

/-- Complete interval computation for depth 12, residue 3430. -/
theorem bounds_12_3430 : exactInterval 12 3430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3430 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3430) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3430 : oddCount 3430 12 = 4 ∧ acceleratedOrbit 12 3430 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3430 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3430) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3430.1, data_12_3430.2]

/-- Complete interval computation for depth 12, residue 3431. -/
theorem bounds_12_3431 : exactInterval 12 3431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3431 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3431) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3431 : oddCount 3431 12 = 10 ∧ acceleratedOrbit 12 3431 = 49481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3431 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3431) = 3 ^ 10 * m + 49481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3431.1, data_12_3431.2]

/-- Complete interval computation for depth 12, residue 3432. -/
theorem bounds_12_3432 : exactInterval 12 3432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3432 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3432) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3432 : oddCount 3432 12 = 5 ∧ acceleratedOrbit 12 3432 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3432 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3432) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3432.1, data_12_3432.2]

/-- Complete interval computation for depth 12, residue 3433. -/
theorem bounds_12_3433 : exactInterval 12 3433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3433 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3433) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3433 : oddCount 3433 12 = 7 ∧ acceleratedOrbit 12 3433 = 1835 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3433 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3433) = 3 ^ 7 * m + 1835 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3433.1, data_12_3433.2]

/-- Complete interval computation for depth 12, residue 3434. -/
theorem bounds_12_3434 : exactInterval 12 3434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3434 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3434) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3434 : oddCount 3434 12 = 5 ∧ acceleratedOrbit 12 3434 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3434 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3434) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3434.1, data_12_3434.2]

/-- Complete interval computation for depth 12, residue 3435. -/
theorem bounds_12_3435 : exactInterval 12 3435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3435 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3435) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3435 : oddCount 3435 12 = 8 ∧ acceleratedOrbit 12 3435 = 5507 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3435 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3435) = 3 ^ 8 * m + 5507 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3435.1, data_12_3435.2]

/-- Complete interval computation for depth 12, residue 3436. -/
theorem bounds_12_3436 : exactInterval 12 3436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3436 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3436) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3436 : oddCount 3436 12 = 7 ∧ acceleratedOrbit 12 3436 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3436 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3436) = 3 ^ 7 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3436.1, data_12_3436.2]

/-- Complete interval computation for depth 12, residue 3437. -/
theorem bounds_12_3437 : exactInterval 12 3437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3437 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3437) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3437 : oddCount 3437 12 = 7 ∧ acceleratedOrbit 12 3437 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3437 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3437) = 3 ^ 7 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3437.1, data_12_3437.2]

/-- Complete interval computation for depth 12, residue 3438. -/
theorem bounds_12_3438 : exactInterval 12 3438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3438 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3438) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3438 : oddCount 3438 12 = 7 ∧ acceleratedOrbit 12 3438 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3438 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3438) = 3 ^ 7 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3438.1, data_12_3438.2]

/-- Complete interval computation for depth 12, residue 3439. -/
theorem bounds_12_3439 : exactInterval 12 3439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3439 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3439) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3439 : oddCount 3439 12 = 7 ∧ acceleratedOrbit 12 3439 = 1837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3439 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3439) = 3 ^ 7 * m + 1837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3439.1, data_12_3439.2]

end Collatz.Research.StoppingAtlas.Batch0424
