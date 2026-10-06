import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0358

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2411. -/
theorem bounds_12_2411 : exactInterval 12 2411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2411 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2411) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2411 : oddCount 2411 12 = 7 ∧ acceleratedOrbit 12 2411 = 1289 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2411 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2411) = 3 ^ 7 * m + 1289 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2411.1, data_12_2411.2]

/-- Complete interval computation for depth 12, residue 2412. -/
theorem bounds_12_2412 : exactInterval 12 2412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2412 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2412) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2412 : oddCount 2412 12 = 7 ∧ acceleratedOrbit 12 2412 = 1291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2412 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2412) = 3 ^ 7 * m + 1291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2412.1, data_12_2412.2]

/-- Complete interval computation for depth 12, residue 2413. -/
theorem bounds_12_2413 : exactInterval 12 2413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2413 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2413) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2413 : oddCount 2413 12 = 7 ∧ acceleratedOrbit 12 2413 = 1291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2413 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2413) = 3 ^ 7 * m + 1291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2413.1, data_12_2413.2]

/-- Complete interval computation for depth 12, residue 2414. -/
theorem bounds_12_2414 : exactInterval 12 2414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2414 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2414) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2414 : oddCount 2414 12 = 7 ∧ acceleratedOrbit 12 2414 = 1291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2414 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2414) = 3 ^ 7 * m + 1291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2414.1, data_12_2414.2]

/-- Complete interval computation for depth 12, residue 2415. -/
theorem bounds_12_2415 : exactInterval 12 2415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2415 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2415) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2415 : oddCount 2415 12 = 6 ∧ acceleratedOrbit 12 2415 = 430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2415 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2415) = 3 ^ 6 * m + 430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2415.1, data_12_2415.2]

/-- Complete interval computation for depth 12, residue 2416. -/
theorem bounds_12_2416 : exactInterval 12 2416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2416 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2416) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2416 : oddCount 2416 12 = 3 ∧ acceleratedOrbit 12 2416 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2416 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2416) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2416.1, data_12_2416.2]

/-- Complete interval computation for depth 12, residue 2417. -/
theorem bounds_12_2417 : exactInterval 12 2417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2417 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2417) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2417 : oddCount 2417 12 = 3 ∧ acceleratedOrbit 12 2417 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2417 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2417) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2417.1, data_12_2417.2]

/-- Complete interval computation for depth 12, residue 2418. -/
theorem bounds_12_2418 : exactInterval 12 2418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2418 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2418) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2418 : oddCount 2418 12 = 7 ∧ acceleratedOrbit 12 2418 = 1295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2418 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2418) = 3 ^ 7 * m + 1295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2418.1, data_12_2418.2]

/-- Complete interval computation for depth 12, residue 2419. -/
theorem bounds_12_2419 : exactInterval 12 2419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2419 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2419) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2419 : oddCount 2419 12 = 7 ∧ acceleratedOrbit 12 2419 = 1295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2419 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2419) = 3 ^ 7 * m + 1295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2419.1, data_12_2419.2]

/-- Complete interval computation for depth 12, residue 2420. -/
theorem bounds_12_2420 : exactInterval 12 2420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2420 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2420) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2420 : oddCount 2420 12 = 3 ∧ acceleratedOrbit 12 2420 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2420 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2420) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2420.1, data_12_2420.2]

/-- Complete interval computation for depth 12, residue 2421. -/
theorem bounds_12_2421 : exactInterval 12 2421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2421 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2421) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2421 : oddCount 2421 12 = 3 ∧ acceleratedOrbit 12 2421 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2421 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2421) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2421.1, data_12_2421.2]

/-- Complete interval computation for depth 12, residue 2422. -/
theorem bounds_12_2422 : exactInterval 12 2422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2422 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2422) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2422 : oddCount 2422 12 = 8 ∧ acceleratedOrbit 12 2422 = 3887 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2422 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2422) = 3 ^ 8 * m + 3887 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2422.1, data_12_2422.2]

/-- Complete interval computation for depth 12, residue 2423. -/
theorem bounds_12_2423 : exactInterval 12 2423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2423 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2423) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2423 : oddCount 2423 12 = 8 ∧ acceleratedOrbit 12 2423 = 3887 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2423 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2423) = 3 ^ 8 * m + 3887 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2423.1, data_12_2423.2]

/-- Complete interval computation for depth 12, residue 2424. -/
theorem bounds_12_2424 : exactInterval 12 2424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2424 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2424) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2424 : oddCount 2424 12 = 6 ∧ acceleratedOrbit 12 2424 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2424 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2424) = 3 ^ 6 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2424.1, data_12_2424.2]

/-- Complete interval computation for depth 12, residue 2425. -/
theorem bounds_12_2425 : exactInterval 12 2425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2425 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2425) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2425 : oddCount 2425 12 = 10 ∧ acceleratedOrbit 12 2425 = 34991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2425 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2425) = 3 ^ 10 * m + 34991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2425.1, data_12_2425.2]

end Collatz.Research.StoppingAtlas.Batch0358
