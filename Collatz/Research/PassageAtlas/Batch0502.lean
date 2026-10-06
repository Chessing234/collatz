import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0502

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 16416. -/
theorem bounds_15_16416 : exactInterval 15 16416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16416 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16416) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16416 : oddCount 16416 15 = 6 ∧ acceleratedOrbit 15 16416 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16416 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16416) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16416.1, data_15_16416.2]

/-- Complete interval computation for depth 15, residue 16417. -/
theorem bounds_15_16417 : exactInterval 15 16417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16417 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16417) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16417 : oddCount 16417 15 = 7 ∧ acceleratedOrbit 15 16417 = 1096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16417 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16417) = 3 ^ 7 * m + 1096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16417.1, data_15_16417.2]

/-- Complete interval computation for depth 15, residue 16418. -/
theorem bounds_15_16418 : exactInterval 15 16418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16418 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16418) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16418 : oddCount 16418 15 = 5 ∧ acceleratedOrbit 15 16418 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16418 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16418) = 3 ^ 5 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16418.1, data_15_16418.2]

/-- Complete interval computation for depth 15, residue 16419. -/
theorem bounds_15_16419 : exactInterval 15 16419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16419 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16419) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16419 : oddCount 16419 15 = 5 ∧ acceleratedOrbit 15 16419 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16419 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16419) = 3 ^ 5 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16419.1, data_15_16419.2]

/-- Complete interval computation for depth 15, residue 16420. -/
theorem bounds_15_16420 : exactInterval 15 16420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16420 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16420) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16420 : oddCount 16420 15 = 7 ∧ acceleratedOrbit 15 16420 = 1097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16420 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16420) = 3 ^ 7 * m + 1097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16420.1, data_15_16420.2]

/-- Complete interval computation for depth 15, residue 16421. -/
theorem bounds_15_16421 : exactInterval 15 16421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16421 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16421) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16421 : oddCount 16421 15 = 7 ∧ acceleratedOrbit 15 16421 = 1097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16421 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16421) = 3 ^ 7 * m + 1097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16421.1, data_15_16421.2]

/-- Complete interval computation for depth 15, residue 16422. -/
theorem bounds_15_16422 : exactInterval 15 16422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16422 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16422) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16422 : oddCount 16422 15 = 7 ∧ acceleratedOrbit 15 16422 = 1097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16422 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16422) = 3 ^ 7 * m + 1097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16422.1, data_15_16422.2]

/-- Complete interval computation for depth 15, residue 16423. -/
theorem bounds_15_16423 : exactInterval 15 16423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16423 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16423) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16423 : oddCount 16423 15 = 8 ∧ acceleratedOrbit 15 16423 = 3289 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16423 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16423) = 3 ^ 8 * m + 3289 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16423.1, data_15_16423.2]

/-- Complete interval computation for depth 15, residue 16424. -/
theorem bounds_15_16424 : exactInterval 15 16424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16424 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16424) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16424 : oddCount 16424 15 = 6 ∧ acceleratedOrbit 15 16424 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16424 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16424) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16424.1, data_15_16424.2]

/-- Complete interval computation for depth 15, residue 16425. -/
theorem bounds_15_16425 : exactInterval 15 16425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16425 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16425) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16425 : oddCount 16425 15 = 10 ∧ acceleratedOrbit 15 16425 = 29602 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16425 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16425) = 3 ^ 10 * m + 29602 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16425.1, data_15_16425.2]

/-- Complete interval computation for depth 15, residue 16426. -/
theorem bounds_15_16426 : exactInterval 15 16426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16426 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16426) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16426 : oddCount 16426 15 = 6 ∧ acceleratedOrbit 15 16426 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16426 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16426) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16426.1, data_15_16426.2]

/-- Complete interval computation for depth 15, residue 16427. -/
theorem bounds_15_16427 : exactInterval 15 16427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16427 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16427) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16427 : oddCount 16427 15 = 9 ∧ acceleratedOrbit 15 16427 = 9872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16427 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16427) = 3 ^ 9 * m + 9872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16427.1, data_15_16427.2]

/-- Complete interval computation for depth 15, residue 16428. -/
theorem bounds_15_16428 : exactInterval 15 16428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16428 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16428) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16428 : oddCount 16428 15 = 5 ∧ acceleratedOrbit 15 16428 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16428 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16428) = 3 ^ 5 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16428.1, data_15_16428.2]

/-- Complete interval computation for depth 15, residue 16429. -/
theorem bounds_15_16429 : exactInterval 15 16429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16429 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16429) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16429 : oddCount 16429 15 = 5 ∧ acceleratedOrbit 15 16429 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16429 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16429) = 3 ^ 5 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16429.1, data_15_16429.2]

/-- Complete interval computation for depth 15, residue 16430. -/
theorem bounds_15_16430 : exactInterval 15 16430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16430 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16430) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16430 : oddCount 16430 15 = 5 ∧ acceleratedOrbit 15 16430 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16430 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16430) = 3 ^ 5 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16430.1, data_15_16430.2]

/-- Complete interval computation for depth 15, residue 16431. -/
theorem bounds_15_16431 : exactInterval 15 16431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16431 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16431) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16431 : oddCount 16431 15 = 10 ∧ acceleratedOrbit 15 16431 = 29612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16431 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16431) = 3 ^ 10 * m + 29612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16431.1, data_15_16431.2]

/-- Complete interval computation for depth 15, residue 16432. -/
theorem bounds_15_16432 : exactInterval 15 16432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16432 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16432) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16432 : oddCount 16432 15 = 6 ∧ acceleratedOrbit 15 16432 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16432 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16432) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16432.1, data_15_16432.2]

/-- Complete interval computation for depth 15, residue 16433. -/
theorem bounds_15_16433 : exactInterval 15 16433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16433 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16433) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16433 : oddCount 16433 15 = 8 ∧ acceleratedOrbit 15 16433 = 3293 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16433 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16433) = 3 ^ 8 * m + 3293 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16433.1, data_15_16433.2]

/-- Complete interval computation for depth 15, residue 16434. -/
theorem bounds_15_16434 : exactInterval 15 16434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16434 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16434) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16434 : oddCount 16434 15 = 8 ∧ acceleratedOrbit 15 16434 = 3293 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16434 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16434) = 3 ^ 8 * m + 3293 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16434.1, data_15_16434.2]

/-- Complete interval computation for depth 15, residue 16435. -/
theorem bounds_15_16435 : exactInterval 15 16435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16435 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16435) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16435 : oddCount 16435 15 = 8 ∧ acceleratedOrbit 15 16435 = 3293 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16435 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16435) = 3 ^ 8 * m + 3293 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16435.1, data_15_16435.2]

/-- Complete interval computation for depth 15, residue 16436. -/
theorem bounds_15_16436 : exactInterval 15 16436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16436 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16436) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16436 : oddCount 16436 15 = 6 ∧ acceleratedOrbit 15 16436 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16436 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16436) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16436.1, data_15_16436.2]

/-- Complete interval computation for depth 15, residue 16437. -/
theorem bounds_15_16437 : exactInterval 15 16437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16437 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16437) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16437 : oddCount 16437 15 = 6 ∧ acceleratedOrbit 15 16437 = 368 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16437 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16437) = 3 ^ 6 * m + 368 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16437.1, data_15_16437.2]

/-- Complete interval computation for depth 15, residue 16438. -/
theorem bounds_15_16438 : exactInterval 15 16438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16438 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16438) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16438 : oddCount 16438 15 = 11 ∧ acceleratedOrbit 15 16438 = 88883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16438 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16438) = 3 ^ 11 * m + 88883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16438.1, data_15_16438.2]

/-- Complete interval computation for depth 15, residue 16439. -/
theorem bounds_15_16439 : exactInterval 15 16439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16439 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16439) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16439 : oddCount 16439 15 = 11 ∧ acceleratedOrbit 15 16439 = 88883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16439 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16439) = 3 ^ 11 * m + 88883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16439.1, data_15_16439.2]

/-- Complete interval computation for depth 15, residue 16440. -/
theorem bounds_15_16440 : exactInterval 15 16440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16440 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16440) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16440 : oddCount 16440 15 = 5 ∧ acceleratedOrbit 15 16440 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16440 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16440) = 3 ^ 5 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16440.1, data_15_16440.2]

/-- Complete interval computation for depth 15, residue 16441. -/
theorem bounds_15_16441 : exactInterval 15 16441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16441 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16441) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16441 : oddCount 16441 15 = 9 ∧ acceleratedOrbit 15 16441 = 9881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16441 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16441) = 3 ^ 9 * m + 9881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16441.1, data_15_16441.2]

/-- Complete interval computation for depth 15, residue 16442. -/
theorem bounds_15_16442 : exactInterval 15 16442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16442 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16442) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16442 : oddCount 16442 15 = 5 ∧ acceleratedOrbit 15 16442 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16442 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16442) = 3 ^ 5 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16442.1, data_15_16442.2]

/-- Complete interval computation for depth 15, residue 16443. -/
theorem bounds_15_16443 : exactInterval 15 16443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16443 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16443) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16443 : oddCount 16443 15 = 9 ∧ acceleratedOrbit 15 16443 = 9881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16443 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16443) = 3 ^ 9 * m + 9881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16443.1, data_15_16443.2]

/-- Complete interval computation for depth 15, residue 16444. -/
theorem bounds_15_16444 : exactInterval 15 16444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16444 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16444) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16444 : oddCount 16444 15 = 5 ∧ acceleratedOrbit 15 16444 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16444 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16444) = 3 ^ 5 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16444.1, data_15_16444.2]

/-- Complete interval computation for depth 15, residue 16445. -/
theorem bounds_15_16445 : exactInterval 15 16445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16445 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16445) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16445 : oddCount 16445 15 = 5 ∧ acceleratedOrbit 15 16445 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16445 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16445) = 3 ^ 5 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16445.1, data_15_16445.2]

/-- Complete interval computation for depth 15, residue 16446. -/
theorem bounds_15_16446 : exactInterval 15 16446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16446 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16446) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16446 : oddCount 16446 15 = 10 ∧ acceleratedOrbit 15 16446 = 29641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16446 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16446) = 3 ^ 10 * m + 29641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16446.1, data_15_16446.2]

/-- Complete interval computation for depth 15, residue 16447. -/
theorem bounds_15_16447 : exactInterval 15 16447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16447 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16447) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16447 : oddCount 16447 15 = 10 ∧ acceleratedOrbit 15 16447 = 29641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16447 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16447) = 3 ^ 10 * m + 29641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16447.1, data_15_16447.2]

/-- Complete interval computation for depth 15, residue 16448. -/
theorem bounds_15_16448 : exactInterval 15 16448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16448 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16448) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16448 : oddCount 16448 15 = 4 ∧ acceleratedOrbit 15 16448 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16448 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16448) = 3 ^ 4 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16448.1, data_15_16448.2]

end Collatz.Research.PassageAtlas.Batch0502
