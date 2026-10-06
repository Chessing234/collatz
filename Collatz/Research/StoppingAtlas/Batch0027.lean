import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0027

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 399. -/
theorem bounds_10_399 : exactInterval 10 399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_399 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 399) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_399 : oddCount 399 10 = 5 ∧ acceleratedOrbit 10 399 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_399 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 399) = 3 ^ 5 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_399.1, data_10_399.2]

/-- Complete interval computation for depth 10, residue 400. -/
theorem bounds_10_400 : exactInterval 10 400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_400 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 400) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_400 : oddCount 400 10 = 3 ∧ acceleratedOrbit 10 400 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_400 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 400) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_400.1, data_10_400.2]

/-- Complete interval computation for depth 10, residue 401. -/
theorem bounds_10_401 : exactInterval 10 401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_401 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 401) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_401 : oddCount 401 10 = 4 ∧ acceleratedOrbit 10 401 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_401 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 401) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_401.1, data_10_401.2]

/-- Complete interval computation for depth 10, residue 402. -/
theorem bounds_10_402 : exactInterval 10 402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_402 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 402) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_402 : oddCount 402 10 = 4 ∧ acceleratedOrbit 10 402 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_402 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 402) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_402.1, data_10_402.2]

/-- Complete interval computation for depth 10, residue 403. -/
theorem bounds_10_403 : exactInterval 10 403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_403 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 403) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_403 : oddCount 403 10 = 4 ∧ acceleratedOrbit 10 403 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_403 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 403) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_403.1, data_10_403.2]

/-- Complete interval computation for depth 10, residue 404. -/
theorem bounds_10_404 : exactInterval 10 404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_404 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 404) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_404 : oddCount 404 10 = 3 ∧ acceleratedOrbit 10 404 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_404 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 404) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_404.1, data_10_404.2]

/-- Complete interval computation for depth 10, residue 405. -/
theorem bounds_10_405 : exactInterval 10 405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_405 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 405) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_405 : oddCount 405 10 = 3 ∧ acceleratedOrbit 10 405 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_405 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 405) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_405.1, data_10_405.2]

/-- Complete interval computation for depth 10, residue 406. -/
theorem bounds_10_406 : exactInterval 10 406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_406 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 406) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_406 : oddCount 406 10 = 5 ∧ acceleratedOrbit 10 406 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_406 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 406) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_406.1, data_10_406.2]

/-- Complete interval computation for depth 10, residue 407. -/
theorem bounds_10_407 : exactInterval 10 407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_407 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 407) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_407 : oddCount 407 10 = 5 ∧ acceleratedOrbit 10 407 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_407 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 407) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_407.1, data_10_407.2]

/-- Complete interval computation for depth 10, residue 408. -/
theorem bounds_10_408 : exactInterval 10 408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_408 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 408) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_408 : oddCount 408 10 = 3 ∧ acceleratedOrbit 10 408 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_408 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 408) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_408.1, data_10_408.2]

/-- Complete interval computation for depth 10, residue 409. -/
theorem bounds_10_409 : exactInterval 10 409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_409 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 409) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_409 : oddCount 409 10 = 5 ∧ acceleratedOrbit 10 409 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_409 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 409) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_409.1, data_10_409.2]

/-- Complete interval computation for depth 10, residue 410. -/
theorem bounds_10_410 : exactInterval 10 410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_410 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 410) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_410 : oddCount 410 10 = 3 ∧ acceleratedOrbit 10 410 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_410 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 410) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_410.1, data_10_410.2]

/-- Complete interval computation for depth 10, residue 411. -/
theorem bounds_10_411 : exactInterval 10 411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_411 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 411) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_411 : oddCount 411 10 = 7 ∧ acceleratedOrbit 10 411 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_411 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 411) = 3 ^ 7 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_411.1, data_10_411.2]

/-- Complete interval computation for depth 10, residue 412. -/
theorem bounds_10_412 : exactInterval 10 412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_412 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 412) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_412 : oddCount 412 10 = 7 ∧ acceleratedOrbit 10 412 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_412 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 412) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_412.1, data_10_412.2]

/-- Complete interval computation for depth 10, residue 413. -/
theorem bounds_10_413 : exactInterval 10 413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_413 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 413) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_413 : oddCount 413 10 = 7 ∧ acceleratedOrbit 10 413 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_413 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 413) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_413.1, data_10_413.2]

end Collatz.Research.StoppingAtlas.Batch0027
