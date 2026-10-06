import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0885

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6410. -/
theorem bounds_13_6410 : exactInterval 13 6410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6410 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6410) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6410 : oddCount 6410 13 = 5 ∧ acceleratedOrbit 13 6410 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6410 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6410) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6410.1, data_13_6410.2]

/-- Complete interval computation for depth 13, residue 6411. -/
theorem bounds_13_6411 : exactInterval 13 6411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6411 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6411) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6411 : oddCount 6411 13 = 6 ∧ acceleratedOrbit 13 6411 = 571 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6411 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6411) = 3 ^ 6 * m + 571 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6411.1, data_13_6411.2]

/-- Complete interval computation for depth 13, residue 6412. -/
theorem bounds_13_6412 : exactInterval 13 6412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6412 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6412) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6412 : oddCount 6412 13 = 5 ∧ acceleratedOrbit 13 6412 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6412 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6412) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6412.1, data_13_6412.2]

/-- Complete interval computation for depth 13, residue 6413. -/
theorem bounds_13_6413 : exactInterval 13 6413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6413 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6413) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6413 : oddCount 6413 13 = 5 ∧ acceleratedOrbit 13 6413 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6413 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6413) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6413.1, data_13_6413.2]

/-- Complete interval computation for depth 13, residue 6414. -/
theorem bounds_13_6414 : exactInterval 13 6414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6414 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6414) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6414 : oddCount 6414 13 = 7 ∧ acceleratedOrbit 13 6414 = 1714 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6414 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6414) = 3 ^ 7 * m + 1714 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6414.1, data_13_6414.2]

/-- Complete interval computation for depth 13, residue 6415. -/
theorem bounds_13_6415 : exactInterval 13 6415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6415 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6415) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6415 : oddCount 6415 13 = 7 ∧ acceleratedOrbit 13 6415 = 1714 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6415 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6415) = 3 ^ 7 * m + 1714 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6415.1, data_13_6415.2]

/-- Complete interval computation for depth 13, residue 6416. -/
theorem bounds_13_6416 : exactInterval 13 6416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6416 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6416) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6416 : oddCount 6416 13 = 4 ∧ acceleratedOrbit 13 6416 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6416 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6416) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6416.1, data_13_6416.2]

/-- Complete interval computation for depth 13, residue 6417. -/
theorem bounds_13_6417 : exactInterval 13 6417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6417 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6417) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6417 : oddCount 6417 13 = 5 ∧ acceleratedOrbit 13 6417 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6417 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6417) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6417.1, data_13_6417.2]

/-- Complete interval computation for depth 13, residue 6418. -/
theorem bounds_13_6418 : exactInterval 13 6418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6418 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6418) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6418 : oddCount 6418 13 = 9 ∧ acceleratedOrbit 13 6418 = 15430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6418 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6418) = 3 ^ 9 * m + 15430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6418.1, data_13_6418.2]

/-- Complete interval computation for depth 13, residue 6419. -/
theorem bounds_13_6419 : exactInterval 13 6419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6419 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6419) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6419 : oddCount 6419 13 = 9 ∧ acceleratedOrbit 13 6419 = 15430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6419 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6419) = 3 ^ 9 * m + 15430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6419.1, data_13_6419.2]

/-- Complete interval computation for depth 13, residue 6420. -/
theorem bounds_13_6420 : exactInterval 13 6420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6420 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6420) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6420 : oddCount 6420 13 = 4 ∧ acceleratedOrbit 13 6420 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6420 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6420) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6420.1, data_13_6420.2]

/-- Complete interval computation for depth 13, residue 6421. -/
theorem bounds_13_6421 : exactInterval 13 6421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6421 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6421) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6421 : oddCount 6421 13 = 4 ∧ acceleratedOrbit 13 6421 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6421 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6421) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6421.1, data_13_6421.2]

/-- Complete interval computation for depth 13, residue 6422. -/
theorem bounds_13_6422 : exactInterval 13 6422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6422 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6422) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6422 : oddCount 6422 13 = 6 ∧ acceleratedOrbit 13 6422 = 572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6422 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6422) = 3 ^ 6 * m + 572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6422.1, data_13_6422.2]

/-- Complete interval computation for depth 13, residue 6423. -/
theorem bounds_13_6423 : exactInterval 13 6423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6423 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6423) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6423 : oddCount 6423 13 = 6 ∧ acceleratedOrbit 13 6423 = 572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6423 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6423) = 3 ^ 6 * m + 572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6423.1, data_13_6423.2]

/-- Complete interval computation for depth 13, residue 6424. -/
theorem bounds_13_6424 : exactInterval 13 6424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6424 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6424) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6424 : oddCount 6424 13 = 4 ∧ acceleratedOrbit 13 6424 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6424 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6424) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6424.1, data_13_6424.2]

end Collatz.Research.StoppingAtlas.Batch0885
