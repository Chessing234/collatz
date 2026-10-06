import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0819

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5396. -/
theorem bounds_13_5396 : exactInterval 13 5396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5396 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5396) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5396 : oddCount 5396 13 = 6 ∧ acceleratedOrbit 13 5396 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5396 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5396) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5396.1, data_13_5396.2]

/-- Complete interval computation for depth 13, residue 5397. -/
theorem bounds_13_5397 : exactInterval 13 5397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5397 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5397) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5397 : oddCount 5397 13 = 6 ∧ acceleratedOrbit 13 5397 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5397 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5397) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5397.1, data_13_5397.2]

/-- Complete interval computation for depth 13, residue 5398. -/
theorem bounds_13_5398 : exactInterval 13 5398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5398 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5398) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5398 : oddCount 5398 13 = 6 ∧ acceleratedOrbit 13 5398 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5398 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5398) = 3 ^ 6 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5398.1, data_13_5398.2]

/-- Complete interval computation for depth 13, residue 5399. -/
theorem bounds_13_5399 : exactInterval 13 5399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5399 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5399) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5399 : oddCount 5399 13 = 6 ∧ acceleratedOrbit 13 5399 = 481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5399 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5399) = 3 ^ 6 * m + 481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5399.1, data_13_5399.2]

/-- Complete interval computation for depth 13, residue 5400. -/
theorem bounds_13_5400 : exactInterval 13 5400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5400 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5400) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5400 : oddCount 5400 13 = 6 ∧ acceleratedOrbit 13 5400 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5400 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5400) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5400.1, data_13_5400.2]

/-- Complete interval computation for depth 13, residue 5401. -/
theorem bounds_13_5401 : exactInterval 13 5401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5401 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5401) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5401 : oddCount 5401 13 = 9 ∧ acceleratedOrbit 13 5401 = 12986 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5401 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5401) = 3 ^ 9 * m + 12986 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5401.1, data_13_5401.2]

/-- Complete interval computation for depth 13, residue 5402. -/
theorem bounds_13_5402 : exactInterval 13 5402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5402 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5402) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5402 : oddCount 5402 13 = 6 ∧ acceleratedOrbit 13 5402 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5402 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5402) = 3 ^ 6 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5402.1, data_13_5402.2]

/-- Complete interval computation for depth 13, residue 5403. -/
theorem bounds_13_5403 : exactInterval 13 5403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5403 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5403) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5403 : oddCount 5403 13 = 10 ∧ acceleratedOrbit 13 5403 = 38956 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5403 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5403) = 3 ^ 10 * m + 38956 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5403.1, data_13_5403.2]

/-- Complete interval computation for depth 13, residue 5404. -/
theorem bounds_13_5404 : exactInterval 13 5404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5404 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5404) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5404 : oddCount 5404 13 = 8 ∧ acceleratedOrbit 13 5404 = 4333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5404 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5404) = 3 ^ 8 * m + 4333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5404.1, data_13_5404.2]

/-- Complete interval computation for depth 13, residue 5405. -/
theorem bounds_13_5405 : exactInterval 13 5405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5405 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5405) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5405 : oddCount 5405 13 = 8 ∧ acceleratedOrbit 13 5405 = 4333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5405 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5405) = 3 ^ 8 * m + 4333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5405.1, data_13_5405.2]

/-- Complete interval computation for depth 13, residue 5406. -/
theorem bounds_13_5406 : exactInterval 13 5406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5406 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5406) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5406 : oddCount 5406 13 = 8 ∧ acceleratedOrbit 13 5406 = 4333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5406 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5406) = 3 ^ 8 * m + 4333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5406.1, data_13_5406.2]

/-- Complete interval computation for depth 13, residue 5407. -/
theorem bounds_13_5407 : exactInterval 13 5407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5407 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5407) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5407 : oddCount 5407 13 = 7 ∧ acceleratedOrbit 13 5407 = 1444 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5407 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5407) = 3 ^ 7 * m + 1444 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5407.1, data_13_5407.2]

/-- Complete interval computation for depth 13, residue 5408. -/
theorem bounds_13_5408 : exactInterval 13 5408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5408 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5408) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5408 : oddCount 5408 13 = 7 ∧ acceleratedOrbit 13 5408 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5408 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5408) = 3 ^ 7 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5408.1, data_13_5408.2]

/-- Complete interval computation for depth 13, residue 5409. -/
theorem bounds_13_5409 : exactInterval 13 5409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5409 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5409) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5409 : oddCount 5409 13 = 5 ∧ acceleratedOrbit 13 5409 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5409 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5409) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5409.1, data_13_5409.2]

/-- Complete interval computation for depth 13, residue 5410. -/
theorem bounds_13_5410 : exactInterval 13 5410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5410 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5410) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5410 : oddCount 5410 13 = 7 ∧ acceleratedOrbit 13 5410 = 1448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5410 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5410) = 3 ^ 7 * m + 1448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5410.1, data_13_5410.2]

end Collatz.Research.StoppingAtlas.Batch0819
