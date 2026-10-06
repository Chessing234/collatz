import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0868

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 28409. -/
theorem bounds_15_28409 : exactInterval 15 28409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28409 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28409) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28409 : oddCount 28409 15 = 8 ∧ acceleratedOrbit 15 28409 = 5690 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28409 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28409) = 3 ^ 8 * m + 5690 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28409.1, data_15_28409.2]

/-- Complete interval computation for depth 15, residue 28410. -/
theorem bounds_15_28410 : exactInterval 15 28410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28410 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28410) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28410 : oddCount 28410 15 = 8 ∧ acceleratedOrbit 15 28410 = 5690 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28410 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28410) = 3 ^ 8 * m + 5690 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28410.1, data_15_28410.2]

/-- Complete interval computation for depth 15, residue 28411. -/
theorem bounds_15_28411 : exactInterval 15 28411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28411 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28411) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28411 : oddCount 28411 15 = 8 ∧ acceleratedOrbit 15 28411 = 5689 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28411 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28411) = 3 ^ 8 * m + 5689 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28411.1, data_15_28411.2]

/-- Complete interval computation for depth 15, residue 28412. -/
theorem bounds_15_28412 : exactInterval 15 28412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28412 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28412) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28412 : oddCount 28412 15 = 9 ∧ acceleratedOrbit 15 28412 = 17069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28412 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28412) = 3 ^ 9 * m + 17069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28412.1, data_15_28412.2]

/-- Complete interval computation for depth 15, residue 28413. -/
theorem bounds_15_28413 : exactInterval 15 28413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28413 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28413) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28413 : oddCount 28413 15 = 9 ∧ acceleratedOrbit 15 28413 = 17069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28413 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28413) = 3 ^ 9 * m + 17069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28413.1, data_15_28413.2]

/-- Complete interval computation for depth 15, residue 28414. -/
theorem bounds_15_28414 : exactInterval 15 28414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28414 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28414) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28414 : oddCount 28414 15 = 9 ∧ acceleratedOrbit 15 28414 = 17069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28414 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28414) = 3 ^ 9 * m + 17069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28414.1, data_15_28414.2]

/-- Complete interval computation for depth 15, residue 28415. -/
theorem bounds_15_28415 : exactInterval 15 28415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28415 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28415) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28415 : oddCount 28415 15 = 13 ∧ acceleratedOrbit 15 28415 = 1382579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28415 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28415) = 3 ^ 13 * m + 1382579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28415.1, data_15_28415.2]

/-- Complete interval computation for depth 15, residue 28416. -/
theorem bounds_15_28416 : exactInterval 15 28416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28416 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28416) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28416 : oddCount 28416 15 = 6 ∧ acceleratedOrbit 15 28416 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28416 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28416) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28416.1, data_15_28416.2]

/-- Complete interval computation for depth 15, residue 28417. -/
theorem bounds_15_28417 : exactInterval 15 28417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28417 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28417) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28417 : oddCount 28417 15 = 5 ∧ acceleratedOrbit 15 28417 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28417 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28417) = 3 ^ 5 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28417.1, data_15_28417.2]

/-- Complete interval computation for depth 15, residue 28418. -/
theorem bounds_15_28418 : exactInterval 15 28418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28418 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28418) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28418 : oddCount 28418 15 = 8 ∧ acceleratedOrbit 15 28418 = 5692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28418 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28418) = 3 ^ 8 * m + 5692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28418.1, data_15_28418.2]

/-- Complete interval computation for depth 15, residue 28419. -/
theorem bounds_15_28419 : exactInterval 15 28419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28419 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28419) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28419 : oddCount 28419 15 = 8 ∧ acceleratedOrbit 15 28419 = 5692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28419 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28419) = 3 ^ 8 * m + 5692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28419.1, data_15_28419.2]

/-- Complete interval computation for depth 15, residue 28420. -/
theorem bounds_15_28420 : exactInterval 15 28420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28420 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28420) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28420 : oddCount 28420 15 = 8 ∧ acceleratedOrbit 15 28420 = 5696 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28420 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28420) = 3 ^ 8 * m + 5696 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28420.1, data_15_28420.2]

/-- Complete interval computation for depth 15, residue 28421. -/
theorem bounds_15_28421 : exactInterval 15 28421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28421 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28421) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28421 : oddCount 28421 15 = 8 ∧ acceleratedOrbit 15 28421 = 5696 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28421 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28421) = 3 ^ 8 * m + 5696 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28421.1, data_15_28421.2]

/-- Complete interval computation for depth 15, residue 28422. -/
theorem bounds_15_28422 : exactInterval 15 28422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28422 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28422) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28422 : oddCount 28422 15 = 8 ∧ acceleratedOrbit 15 28422 = 5696 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28422 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28422) = 3 ^ 8 * m + 5696 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28422.1, data_15_28422.2]

/-- Complete interval computation for depth 15, residue 28423. -/
theorem bounds_15_28423 : exactInterval 15 28423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28423 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28423) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28423 : oddCount 28423 15 = 8 ∧ acceleratedOrbit 15 28423 = 5692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28423 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28423) = 3 ^ 8 * m + 5692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28423.1, data_15_28423.2]

/-- Complete interval computation for depth 15, residue 28424. -/
theorem bounds_15_28424 : exactInterval 15 28424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28424 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28424) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28424 : oddCount 28424 15 = 8 ∧ acceleratedOrbit 15 28424 = 5696 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28424 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28424) = 3 ^ 8 * m + 5696 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28424.1, data_15_28424.2]

/-- Complete interval computation for depth 15, residue 28425. -/
theorem bounds_15_28425 : exactInterval 15 28425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28425 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28425) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28425 : oddCount 28425 15 = 11 ∧ acceleratedOrbit 15 28425 = 153683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28425 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28425) = 3 ^ 11 * m + 153683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28425.1, data_15_28425.2]

/-- Complete interval computation for depth 15, residue 28426. -/
theorem bounds_15_28426 : exactInterval 15 28426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28426 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28426) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28426 : oddCount 28426 15 = 8 ∧ acceleratedOrbit 15 28426 = 5696 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28426 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28426) = 3 ^ 8 * m + 5696 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28426.1, data_15_28426.2]

/-- Complete interval computation for depth 15, residue 28427. -/
theorem bounds_15_28427 : exactInterval 15 28427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28427 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28427) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28427 : oddCount 28427 15 = 7 ∧ acceleratedOrbit 15 28427 = 1898 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28427 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28427) = 3 ^ 7 * m + 1898 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28427.1, data_15_28427.2]

/-- Complete interval computation for depth 15, residue 28428. -/
theorem bounds_15_28428 : exactInterval 15 28428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28428 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28428) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28428 : oddCount 28428 15 = 8 ∧ acceleratedOrbit 15 28428 = 5696 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28428 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28428) = 3 ^ 8 * m + 5696 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28428.1, data_15_28428.2]

/-- Complete interval computation for depth 15, residue 28429. -/
theorem bounds_15_28429 : exactInterval 15 28429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28429 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28429) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28429 : oddCount 28429 15 = 8 ∧ acceleratedOrbit 15 28429 = 5696 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28429 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28429) = 3 ^ 8 * m + 5696 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28429.1, data_15_28429.2]

/-- Complete interval computation for depth 15, residue 28430. -/
theorem bounds_15_28430 : exactInterval 15 28430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28430 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28430) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28430 : oddCount 28430 15 = 8 ∧ acceleratedOrbit 15 28430 = 5696 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28430 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28430) = 3 ^ 8 * m + 5696 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28430.1, data_15_28430.2]

/-- Complete interval computation for depth 15, residue 28431. -/
theorem bounds_15_28431 : exactInterval 15 28431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28431 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28431) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28431 : oddCount 28431 15 = 8 ∧ acceleratedOrbit 15 28431 = 5696 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28431 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28431) = 3 ^ 8 * m + 5696 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28431.1, data_15_28431.2]

/-- Complete interval computation for depth 15, residue 28432. -/
theorem bounds_15_28432 : exactInterval 15 28432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28432 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28432) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28432 : oddCount 28432 15 = 4 ∧ acceleratedOrbit 15 28432 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28432 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28432) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28432.1, data_15_28432.2]

/-- Complete interval computation for depth 15, residue 28433. -/
theorem bounds_15_28433 : exactInterval 15 28433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28433 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28433) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28433 : oddCount 28433 15 = 8 ∧ acceleratedOrbit 15 28433 = 5696 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28433 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28433) = 3 ^ 8 * m + 5696 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28433.1, data_15_28433.2]

/-- Complete interval computation for depth 15, residue 28434. -/
theorem bounds_15_28434 : exactInterval 15 28434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28434 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28434) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28434 : oddCount 28434 15 = 7 ∧ acceleratedOrbit 15 28434 = 1898 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28434 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28434) = 3 ^ 7 * m + 1898 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28434.1, data_15_28434.2]

/-- Complete interval computation for depth 15, residue 28435. -/
theorem bounds_15_28435 : exactInterval 15 28435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28435 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28435) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28435 : oddCount 28435 15 = 7 ∧ acceleratedOrbit 15 28435 = 1898 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28435 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28435) = 3 ^ 7 * m + 1898 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28435.1, data_15_28435.2]

/-- Complete interval computation for depth 15, residue 28436. -/
theorem bounds_15_28436 : exactInterval 15 28436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28436 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28436) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28436 : oddCount 28436 15 = 4 ∧ acceleratedOrbit 15 28436 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28436 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28436) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28436.1, data_15_28436.2]

/-- Complete interval computation for depth 15, residue 28437. -/
theorem bounds_15_28437 : exactInterval 15 28437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28437 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28437) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28437 : oddCount 28437 15 = 4 ∧ acceleratedOrbit 15 28437 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28437 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28437) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28437.1, data_15_28437.2]

/-- Complete interval computation for depth 15, residue 28438. -/
theorem bounds_15_28438 : exactInterval 15 28438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28438 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28438) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28438 : oddCount 28438 15 = 9 ∧ acceleratedOrbit 15 28438 = 17086 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28438 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28438) = 3 ^ 9 * m + 17086 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28438.1, data_15_28438.2]

/-- Complete interval computation for depth 15, residue 28439. -/
theorem bounds_15_28439 : exactInterval 15 28439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28439 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28439) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28439 : oddCount 28439 15 = 9 ∧ acceleratedOrbit 15 28439 = 17086 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28439 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28439) = 3 ^ 9 * m + 17086 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28439.1, data_15_28439.2]

/-- Complete interval computation for depth 15, residue 28440. -/
theorem bounds_15_28440 : exactInterval 15 28440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28440 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28440) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28440 : oddCount 28440 15 = 4 ∧ acceleratedOrbit 15 28440 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28440 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28440) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28440.1, data_15_28440.2]

/-- Complete interval computation for depth 15, residue 28441. -/
theorem bounds_15_28441 : exactInterval 15 28441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28441 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28441) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28441 : oddCount 28441 15 = 9 ∧ acceleratedOrbit 15 28441 = 17086 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28441 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28441) = 3 ^ 9 * m + 17086 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28441.1, data_15_28441.2]

end Collatz.Research.PassageAtlas.Batch0868
