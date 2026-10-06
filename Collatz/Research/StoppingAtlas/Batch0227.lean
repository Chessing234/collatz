import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0227

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 399. -/
theorem bounds_12_399 : exactInterval 12 399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_399 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 399) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_399 : oddCount 399 12 = 7 ∧ acceleratedOrbit 12 399 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_399 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 399) = 3 ^ 7 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_399.1, data_12_399.2]

/-- Complete interval computation for depth 12, residue 400. -/
theorem bounds_12_400 : exactInterval 12 400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_400 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 400) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_400 : oddCount 400 12 = 5 ∧ acceleratedOrbit 12 400 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_400 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 400) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_400.1, data_12_400.2]

/-- Complete interval computation for depth 12, residue 401. -/
theorem bounds_12_401 : exactInterval 12 401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_401 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 401) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_401 : oddCount 401 12 = 4 ∧ acceleratedOrbit 12 401 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_401 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 401) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_401.1, data_12_401.2]

/-- Complete interval computation for depth 12, residue 402. -/
theorem bounds_12_402 : exactInterval 12 402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_402 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 402) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_402 : oddCount 402 12 = 4 ∧ acceleratedOrbit 12 402 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_402 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 402) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_402.1, data_12_402.2]

/-- Complete interval computation for depth 12, residue 403. -/
theorem bounds_12_403 : exactInterval 12 403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_403 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 403) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_403 : oddCount 403 12 = 4 ∧ acceleratedOrbit 12 403 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_403 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 403) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_403.1, data_12_403.2]

/-- Complete interval computation for depth 12, residue 404. -/
theorem bounds_12_404 : exactInterval 12 404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_404 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 404) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_404 : oddCount 404 12 = 5 ∧ acceleratedOrbit 12 404 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_404 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 404) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_404.1, data_12_404.2]

/-- Complete interval computation for depth 12, residue 405. -/
theorem bounds_12_405 : exactInterval 12 405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_405 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 405) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_405 : oddCount 405 12 = 5 ∧ acceleratedOrbit 12 405 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_405 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 405) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_405.1, data_12_405.2]

/-- Complete interval computation for depth 12, residue 406. -/
theorem bounds_12_406 : exactInterval 12 406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_406 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 406) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_406 : oddCount 406 12 = 6 ∧ acceleratedOrbit 12 406 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_406 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 406) = 3 ^ 6 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_406.1, data_12_406.2]

/-- Complete interval computation for depth 12, residue 407. -/
theorem bounds_12_407 : exactInterval 12 407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_407 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 407) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_407 : oddCount 407 12 = 6 ∧ acceleratedOrbit 12 407 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_407 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 407) = 3 ^ 6 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_407.1, data_12_407.2]

/-- Complete interval computation for depth 12, residue 408. -/
theorem bounds_12_408 : exactInterval 12 408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_408 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 408) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_408 : oddCount 408 12 = 5 ∧ acceleratedOrbit 12 408 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_408 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 408) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_408.1, data_12_408.2]

/-- Complete interval computation for depth 12, residue 409. -/
theorem bounds_12_409 : exactInterval 12 409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_409 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 409) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_409 : oddCount 409 12 = 6 ∧ acceleratedOrbit 12 409 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_409 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 409) = 3 ^ 6 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_409.1, data_12_409.2]

/-- Complete interval computation for depth 12, residue 410. -/
theorem bounds_12_410 : exactInterval 12 410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_410 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 410) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_410 : oddCount 410 12 = 5 ∧ acceleratedOrbit 12 410 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_410 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 410) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_410.1, data_12_410.2]

/-- Complete interval computation for depth 12, residue 411. -/
theorem bounds_12_411 : exactInterval 12 411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_411 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 411) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_411 : oddCount 411 12 = 8 ∧ acceleratedOrbit 12 411 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_411 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 411) = 3 ^ 8 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_411.1, data_12_411.2]

/-- Complete interval computation for depth 12, residue 412. -/
theorem bounds_12_412 : exactInterval 12 412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_412 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 412) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_412 : oddCount 412 12 = 8 ∧ acceleratedOrbit 12 412 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_412 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 412) = 3 ^ 8 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_412.1, data_12_412.2]

/-- Complete interval computation for depth 12, residue 413. -/
theorem bounds_12_413 : exactInterval 12 413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_413 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 413) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_413 : oddCount 413 12 = 8 ∧ acceleratedOrbit 12 413 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_413 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 413) = 3 ^ 8 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_413.1, data_12_413.2]

end Collatz.Research.StoppingAtlas.Batch0227
