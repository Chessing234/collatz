import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0929

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 30408. -/
theorem bounds_15_30408 : exactInterval 15 30408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30408 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30408) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30408 : oddCount 30408 15 = 5 ∧ acceleratedOrbit 15 30408 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30408 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30408) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30408.1, data_15_30408.2]

/-- Complete interval computation for depth 15, residue 30409. -/
theorem bounds_15_30409 : exactInterval 15 30409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30409 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30409) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30409 : oddCount 30409 15 = 7 ∧ acceleratedOrbit 15 30409 = 2030 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30409 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30409) = 3 ^ 7 * m + 2030 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30409.1, data_15_30409.2]

/-- Complete interval computation for depth 15, residue 30410. -/
theorem bounds_15_30410 : exactInterval 15 30410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30410 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30410) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30410 : oddCount 30410 15 = 5 ∧ acceleratedOrbit 15 30410 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30410 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30410) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30410.1, data_15_30410.2]

/-- Complete interval computation for depth 15, residue 30411. -/
theorem bounds_15_30411 : exactInterval 15 30411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30411 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30411) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30411 : oddCount 30411 15 = 7 ∧ acceleratedOrbit 15 30411 = 2030 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30411 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30411) = 3 ^ 7 * m + 2030 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30411.1, data_15_30411.2]

/-- Complete interval computation for depth 15, residue 30412. -/
theorem bounds_15_30412 : exactInterval 15 30412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30412 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30412) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30412 : oddCount 30412 15 = 5 ∧ acceleratedOrbit 15 30412 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30412 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30412) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30412.1, data_15_30412.2]

/-- Complete interval computation for depth 15, residue 30413. -/
theorem bounds_15_30413 : exactInterval 15 30413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30413 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30413) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30413 : oddCount 30413 15 = 5 ∧ acceleratedOrbit 15 30413 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30413 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30413) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30413.1, data_15_30413.2]

/-- Complete interval computation for depth 15, residue 30414. -/
theorem bounds_15_30414 : exactInterval 15 30414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30414 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30414) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30414 : oddCount 30414 15 = 10 ∧ acceleratedOrbit 15 30414 = 54812 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30414 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30414) = 3 ^ 10 * m + 54812 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30414.1, data_15_30414.2]

/-- Complete interval computation for depth 15, residue 30415. -/
theorem bounds_15_30415 : exactInterval 15 30415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30415 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30415) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30415 : oddCount 30415 15 = 10 ∧ acceleratedOrbit 15 30415 = 54812 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30415 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30415) = 3 ^ 10 * m + 54812 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30415.1, data_15_30415.2]

/-- Complete interval computation for depth 15, residue 30416. -/
theorem bounds_15_30416 : exactInterval 15 30416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30416 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30416) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30416 : oddCount 30416 15 = 5 ∧ acceleratedOrbit 15 30416 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30416 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30416) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30416.1, data_15_30416.2]

/-- Complete interval computation for depth 15, residue 30417. -/
theorem bounds_15_30417 : exactInterval 15 30417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30417 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30417) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30417 : oddCount 30417 15 = 8 ∧ acceleratedOrbit 15 30417 = 6092 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30417 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30417) = 3 ^ 8 * m + 6092 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30417.1, data_15_30417.2]

/-- Complete interval computation for depth 15, residue 30418. -/
theorem bounds_15_30418 : exactInterval 15 30418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30418 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30418) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30418 : oddCount 30418 15 = 8 ∧ acceleratedOrbit 15 30418 = 6092 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30418 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30418) = 3 ^ 8 * m + 6092 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30418.1, data_15_30418.2]

/-- Complete interval computation for depth 15, residue 30419. -/
theorem bounds_15_30419 : exactInterval 15 30419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30419 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30419) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30419 : oddCount 30419 15 = 8 ∧ acceleratedOrbit 15 30419 = 6092 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30419 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30419) = 3 ^ 8 * m + 6092 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30419.1, data_15_30419.2]

/-- Complete interval computation for depth 15, residue 30420. -/
theorem bounds_15_30420 : exactInterval 15 30420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30420 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30420) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30420 : oddCount 30420 15 = 5 ∧ acceleratedOrbit 15 30420 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30420 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30420) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30420.1, data_15_30420.2]

/-- Complete interval computation for depth 15, residue 30421. -/
theorem bounds_15_30421 : exactInterval 15 30421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30421 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30421) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30421 : oddCount 30421 15 = 5 ∧ acceleratedOrbit 15 30421 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30421 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30421) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30421.1, data_15_30421.2]

/-- Complete interval computation for depth 15, residue 30422. -/
theorem bounds_15_30422 : exactInterval 15 30422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30422 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30422) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30422 : oddCount 30422 15 = 6 ∧ acceleratedOrbit 15 30422 = 677 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30422 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30422) = 3 ^ 6 * m + 677 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30422.1, data_15_30422.2]

/-- Complete interval computation for depth 15, residue 30423. -/
theorem bounds_15_30423 : exactInterval 15 30423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30423 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30423) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30423 : oddCount 30423 15 = 6 ∧ acceleratedOrbit 15 30423 = 677 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30423 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30423) = 3 ^ 6 * m + 677 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30423.1, data_15_30423.2]

/-- Complete interval computation for depth 15, residue 30424. -/
theorem bounds_15_30424 : exactInterval 15 30424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30424 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30424) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30424 : oddCount 30424 15 = 8 ∧ acceleratedOrbit 15 30424 = 6095 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30424 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30424) = 3 ^ 8 * m + 6095 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30424.1, data_15_30424.2]

/-- Complete interval computation for depth 15, residue 30425. -/
theorem bounds_15_30425 : exactInterval 15 30425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30425 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30425) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30425 : oddCount 30425 15 = 8 ∧ acceleratedOrbit 15 30425 = 6095 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30425 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30425) = 3 ^ 8 * m + 6095 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30425.1, data_15_30425.2]

/-- Complete interval computation for depth 15, residue 30426. -/
theorem bounds_15_30426 : exactInterval 15 30426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30426 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30426) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30426 : oddCount 30426 15 = 8 ∧ acceleratedOrbit 15 30426 = 6095 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30426 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30426) = 3 ^ 8 * m + 6095 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30426.1, data_15_30426.2]

/-- Complete interval computation for depth 15, residue 30427. -/
theorem bounds_15_30427 : exactInterval 15 30427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30427 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30427) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30427 : oddCount 30427 15 = 10 ∧ acceleratedOrbit 15 30427 = 54836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30427 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30427) = 3 ^ 10 * m + 54836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30427.1, data_15_30427.2]

/-- Complete interval computation for depth 15, residue 30428. -/
theorem bounds_15_30428 : exactInterval 15 30428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30428 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30428) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30428 : oddCount 30428 15 = 8 ∧ acceleratedOrbit 15 30428 = 6095 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30428 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30428) = 3 ^ 8 * m + 6095 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30428.1, data_15_30428.2]

/-- Complete interval computation for depth 15, residue 30429. -/
theorem bounds_15_30429 : exactInterval 15 30429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30429 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30429) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30429 : oddCount 30429 15 = 8 ∧ acceleratedOrbit 15 30429 = 6095 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30429 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30429) = 3 ^ 8 * m + 6095 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30429.1, data_15_30429.2]

/-- Complete interval computation for depth 15, residue 30430. -/
theorem bounds_15_30430 : exactInterval 15 30430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30430 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30430) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30430 : oddCount 30430 15 = 9 ∧ acceleratedOrbit 15 30430 = 18281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30430 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30430) = 3 ^ 9 * m + 18281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30430.1, data_15_30430.2]

/-- Complete interval computation for depth 15, residue 30431. -/
theorem bounds_15_30431 : exactInterval 15 30431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30431 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30431) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30431 : oddCount 30431 15 = 9 ∧ acceleratedOrbit 15 30431 = 18281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30431 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30431) = 3 ^ 9 * m + 18281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30431.1, data_15_30431.2]

/-- Complete interval computation for depth 15, residue 30432. -/
theorem bounds_15_30432 : exactInterval 15 30432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30432 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30432) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30432 : oddCount 30432 15 = 5 ∧ acceleratedOrbit 15 30432 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30432 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30432) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30432.1, data_15_30432.2]

/-- Complete interval computation for depth 15, residue 30433. -/
theorem bounds_15_30433 : exactInterval 15 30433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30433 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30433) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30433 : oddCount 30433 15 = 8 ∧ acceleratedOrbit 15 30433 = 6094 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30433 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30433) = 3 ^ 8 * m + 6094 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30433.1, data_15_30433.2]

/-- Complete interval computation for depth 15, residue 30434. -/
theorem bounds_15_30434 : exactInterval 15 30434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30434 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30434) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30434 : oddCount 30434 15 = 5 ∧ acceleratedOrbit 15 30434 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30434 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30434) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30434.1, data_15_30434.2]

/-- Complete interval computation for depth 15, residue 30435. -/
theorem bounds_15_30435 : exactInterval 15 30435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30435 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30435) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30435 : oddCount 30435 15 = 5 ∧ acceleratedOrbit 15 30435 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30435 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30435) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30435.1, data_15_30435.2]

/-- Complete interval computation for depth 15, residue 30436. -/
theorem bounds_15_30436 : exactInterval 15 30436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30436 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30436) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30436 : oddCount 30436 15 = 5 ∧ acceleratedOrbit 15 30436 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30436 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30436) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30436.1, data_15_30436.2]

/-- Complete interval computation for depth 15, residue 30437. -/
theorem bounds_15_30437 : exactInterval 15 30437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30437 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30437) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30437 : oddCount 30437 15 = 5 ∧ acceleratedOrbit 15 30437 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30437 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30437) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30437.1, data_15_30437.2]

/-- Complete interval computation for depth 15, residue 30438. -/
theorem bounds_15_30438 : exactInterval 15 30438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30438 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30438) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30438 : oddCount 30438 15 = 5 ∧ acceleratedOrbit 15 30438 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30438 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30438) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30438.1, data_15_30438.2]

/-- Complete interval computation for depth 15, residue 30439. -/
theorem bounds_15_30439 : exactInterval 15 30439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30439 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30439) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30439 : oddCount 30439 15 = 12 ∧ acceleratedOrbit 15 30439 = 493694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30439 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30439) = 3 ^ 12 * m + 493694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30439.1, data_15_30439.2]

/-- Complete interval computation for depth 15, residue 30440. -/
theorem bounds_15_30440 : exactInterval 15 30440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30440 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30440) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30440 : oddCount 30440 15 = 5 ∧ acceleratedOrbit 15 30440 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30440 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30440) = 3 ^ 5 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30440.1, data_15_30440.2]

end Collatz.Research.PassageAtlas.Batch0929
