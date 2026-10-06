import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch092

/-- Complete interval computation for depth 9, residue 420. -/
theorem bounds_9_420 : exactInterval 9 420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_420 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 420) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_420 : oddCount 420 9 = 5 ∧ acceleratedOrbit 9 420 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_420 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 420) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_420.1, data_9_420.2]

/-- Complete interval computation for depth 9, residue 421. -/
theorem bounds_9_421 : exactInterval 9 421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_421 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 421) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_421 : oddCount 421 9 = 5 ∧ acceleratedOrbit 9 421 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_421 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 421) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_421.1, data_9_421.2]

/-- Complete interval computation for depth 9, residue 422. -/
theorem bounds_9_422 : exactInterval 9 422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_422 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 422) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_422 : oddCount 422 9 = 5 ∧ acceleratedOrbit 9 422 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_422 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 422) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_422.1, data_9_422.2]

/-- Complete interval computation for depth 9, residue 423. -/
theorem bounds_9_423 : exactInterval 9 423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_423 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 423) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_423 : oddCount 423 9 = 6 ∧ acceleratedOrbit 9 423 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_423 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 423) = 3 ^ 6 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_423.1, data_9_423.2]

/-- Complete interval computation for depth 9, residue 424. -/
theorem bounds_9_424 : exactInterval 9 424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_424 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 424) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_424 : oddCount 424 9 = 2 ∧ acceleratedOrbit 9 424 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_424 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 424) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_424.1, data_9_424.2]

/-- Complete interval computation for depth 9, residue 425. -/
theorem bounds_9_425 : exactInterval 9 425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_425 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 425) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_425 : oddCount 425 9 = 7 ∧ acceleratedOrbit 9 425 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_425 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 425) = 3 ^ 7 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_425.1, data_9_425.2]

/-- Complete interval computation for depth 9, residue 426. -/
theorem bounds_9_426 : exactInterval 9 426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_426 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 426) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_426 : oddCount 426 9 = 2 ∧ acceleratedOrbit 9 426 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_426 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 426) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_426.1, data_9_426.2]

/-- Complete interval computation for depth 9, residue 427. -/
theorem bounds_9_427 : exactInterval 9 427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_427 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 427) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_427 : oddCount 427 9 = 6 ∧ acceleratedOrbit 9 427 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_427 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 427) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_427.1, data_9_427.2]

/-- Complete interval computation for depth 9, residue 428. -/
theorem bounds_9_428 : exactInterval 9 428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_428 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 428) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_428 : oddCount 428 9 = 5 ∧ acceleratedOrbit 9 428 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_428 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 428) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_428.1, data_9_428.2]

/-- Complete interval computation for depth 9, residue 429. -/
theorem bounds_9_429 : exactInterval 9 429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_429 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 429) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_429 : oddCount 429 9 = 5 ∧ acceleratedOrbit 9 429 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_429 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 429) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_429.1, data_9_429.2]

end Collatz.Research.DescentIntervals.Batch092
