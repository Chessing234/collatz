import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0563

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 18415. -/
theorem bounds_15_18415 : exactInterval 15 18415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18415 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18415) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18415 : oddCount 18415 15 = 9 ∧ acceleratedOrbit 15 18415 = 11063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18415 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18415) = 3 ^ 9 * m + 11063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18415.1, data_15_18415.2]

/-- Complete interval computation for depth 15, residue 18416. -/
theorem bounds_15_18416 : exactInterval 15 18416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18416 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18416) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18416 : oddCount 18416 15 = 9 ∧ acceleratedOrbit 15 18416 = 11072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18416 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18416) = 3 ^ 9 * m + 11072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18416.1, data_15_18416.2]

/-- Complete interval computation for depth 15, residue 18417. -/
theorem bounds_15_18417 : exactInterval 15 18417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18417 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18417) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18417 : oddCount 18417 15 = 6 ∧ acceleratedOrbit 15 18417 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18417 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18417) = 3 ^ 6 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18417.1, data_15_18417.2]

/-- Complete interval computation for depth 15, residue 18418. -/
theorem bounds_15_18418 : exactInterval 15 18418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18418 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18418) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18418 : oddCount 18418 15 = 10 ∧ acceleratedOrbit 15 18418 = 33200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18418 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18418) = 3 ^ 10 * m + 33200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18418.1, data_15_18418.2]

/-- Complete interval computation for depth 15, residue 18419. -/
theorem bounds_15_18419 : exactInterval 15 18419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18419 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18419) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18419 : oddCount 18419 15 = 10 ∧ acceleratedOrbit 15 18419 = 33200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18419 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18419) = 3 ^ 10 * m + 33200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18419.1, data_15_18419.2]

/-- Complete interval computation for depth 15, residue 18420. -/
theorem bounds_15_18420 : exactInterval 15 18420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18420 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18420) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18420 : oddCount 18420 15 = 9 ∧ acceleratedOrbit 15 18420 = 11072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18420 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18420) = 3 ^ 9 * m + 11072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18420.1, data_15_18420.2]

/-- Complete interval computation for depth 15, residue 18421. -/
theorem bounds_15_18421 : exactInterval 15 18421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18421 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18421) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18421 : oddCount 18421 15 = 9 ∧ acceleratedOrbit 15 18421 = 11072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18421 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18421) = 3 ^ 9 * m + 11072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18421.1, data_15_18421.2]

/-- Complete interval computation for depth 15, residue 18422. -/
theorem bounds_15_18422 : exactInterval 15 18422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18422 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18422) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18422 : oddCount 18422 15 = 9 ∧ acceleratedOrbit 15 18422 = 11069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18422 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18422) = 3 ^ 9 * m + 11069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18422.1, data_15_18422.2]

/-- Complete interval computation for depth 15, residue 18423. -/
theorem bounds_15_18423 : exactInterval 15 18423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18423 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18423) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18423 : oddCount 18423 15 = 9 ∧ acceleratedOrbit 15 18423 = 11069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18423 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18423) = 3 ^ 9 * m + 11069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18423.1, data_15_18423.2]

/-- Complete interval computation for depth 15, residue 18424. -/
theorem bounds_15_18424 : exactInterval 15 18424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18424 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18424) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18424 : oddCount 18424 15 = 9 ∧ acceleratedOrbit 15 18424 = 11072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18424 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18424) = 3 ^ 9 * m + 11072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18424.1, data_15_18424.2]

/-- Complete interval computation for depth 15, residue 18425. -/
theorem bounds_15_18425 : exactInterval 15 18425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18425 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18425) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18425 : oddCount 18425 15 = 10 ∧ acceleratedOrbit 15 18425 = 33209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18425 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18425) = 3 ^ 10 * m + 33209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18425.1, data_15_18425.2]

/-- Complete interval computation for depth 15, residue 18426. -/
theorem bounds_15_18426 : exactInterval 15 18426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18426 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18426) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18426 : oddCount 18426 15 = 9 ∧ acceleratedOrbit 15 18426 = 11072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18426 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18426) = 3 ^ 9 * m + 11072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18426.1, data_15_18426.2]

/-- Complete interval computation for depth 15, residue 18427. -/
theorem bounds_15_18427 : exactInterval 15 18427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18427 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18427) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18427 : oddCount 18427 15 = 12 ∧ acceleratedOrbit 15 18427 = 298889 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18427 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18427) = 3 ^ 12 * m + 298889 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18427.1, data_15_18427.2]

/-- Complete interval computation for depth 15, residue 18428. -/
theorem bounds_15_18428 : exactInterval 15 18428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18428 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18428) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18428 : oddCount 18428 15 = 10 ∧ acceleratedOrbit 15 18428 = 33215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18428 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18428) = 3 ^ 10 * m + 33215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18428.1, data_15_18428.2]

/-- Complete interval computation for depth 15, residue 18429. -/
theorem bounds_15_18429 : exactInterval 15 18429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18429 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18429) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18429 : oddCount 18429 15 = 10 ∧ acceleratedOrbit 15 18429 = 33215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18429 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18429) = 3 ^ 10 * m + 33215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18429.1, data_15_18429.2]

/-- Complete interval computation for depth 15, residue 18430. -/
theorem bounds_15_18430 : exactInterval 15 18430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18430 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18430) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18430 : oddCount 18430 15 = 10 ∧ acceleratedOrbit 15 18430 = 33215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18430 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18430) = 3 ^ 10 * m + 33215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18430.1, data_15_18430.2]

/-- Complete interval computation for depth 15, residue 18431. -/
theorem bounds_15_18431 : exactInterval 15 18431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18431 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18431) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18431 : oddCount 18431 15 = 13 ∧ acceleratedOrbit 15 18431 = 896807 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18431 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18431) = 3 ^ 13 * m + 896807 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18431.1, data_15_18431.2]

/-- Complete interval computation for depth 15, residue 18432. -/
theorem bounds_15_18432 : exactInterval 15 18432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18432 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18432) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18432 : oddCount 18432 15 = 3 ∧ acceleratedOrbit 15 18432 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18432 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18432) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18432.1, data_15_18432.2]

/-- Complete interval computation for depth 15, residue 18433. -/
theorem bounds_15_18433 : exactInterval 15 18433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18433 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18433) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18433 : oddCount 18433 15 = 8 ∧ acceleratedOrbit 15 18433 = 3692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18433 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18433) = 3 ^ 8 * m + 3692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18433.1, data_15_18433.2]

/-- Complete interval computation for depth 15, residue 18434. -/
theorem bounds_15_18434 : exactInterval 15 18434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18434 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18434) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18434 : oddCount 18434 15 = 7 ∧ acceleratedOrbit 15 18434 = 1232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18434 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18434) = 3 ^ 7 * m + 1232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18434.1, data_15_18434.2]

/-- Complete interval computation for depth 15, residue 18435. -/
theorem bounds_15_18435 : exactInterval 15 18435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18435 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18435) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18435 : oddCount 18435 15 = 7 ∧ acceleratedOrbit 15 18435 = 1232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18435 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18435) = 3 ^ 7 * m + 1232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18435.1, data_15_18435.2]

/-- Complete interval computation for depth 15, residue 18436. -/
theorem bounds_15_18436 : exactInterval 15 18436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18436 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18436) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18436 : oddCount 18436 15 = 7 ∧ acceleratedOrbit 15 18436 = 1232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18436 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18436) = 3 ^ 7 * m + 1232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18436.1, data_15_18436.2]

/-- Complete interval computation for depth 15, residue 18437. -/
theorem bounds_15_18437 : exactInterval 15 18437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18437 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18437) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18437 : oddCount 18437 15 = 7 ∧ acceleratedOrbit 15 18437 = 1232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18437 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18437) = 3 ^ 7 * m + 1232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18437.1, data_15_18437.2]

/-- Complete interval computation for depth 15, residue 18438. -/
theorem bounds_15_18438 : exactInterval 15 18438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18438 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18438) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18438 : oddCount 18438 15 = 7 ∧ acceleratedOrbit 15 18438 = 1232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18438 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18438) = 3 ^ 7 * m + 1232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18438.1, data_15_18438.2]

/-- Complete interval computation for depth 15, residue 18439. -/
theorem bounds_15_18439 : exactInterval 15 18439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18439 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18439) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18439 : oddCount 18439 15 = 7 ∧ acceleratedOrbit 15 18439 = 1232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18439 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18439) = 3 ^ 7 * m + 1232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18439.1, data_15_18439.2]

/-- Complete interval computation for depth 15, residue 18440. -/
theorem bounds_15_18440 : exactInterval 15 18440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18440 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18440) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18440 : oddCount 18440 15 = 5 ∧ acceleratedOrbit 15 18440 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18440 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18440) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18440.1, data_15_18440.2]

/-- Complete interval computation for depth 15, residue 18441. -/
theorem bounds_15_18441 : exactInterval 15 18441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18441 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18441) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18441 : oddCount 18441 15 = 7 ∧ acceleratedOrbit 15 18441 = 1231 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18441 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18441) = 3 ^ 7 * m + 1231 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18441.1, data_15_18441.2]

/-- Complete interval computation for depth 15, residue 18442. -/
theorem bounds_15_18442 : exactInterval 15 18442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18442 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18442) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18442 : oddCount 18442 15 = 5 ∧ acceleratedOrbit 15 18442 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18442 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18442) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18442.1, data_15_18442.2]

/-- Complete interval computation for depth 15, residue 18443. -/
theorem bounds_15_18443 : exactInterval 15 18443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18443 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18443) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18443 : oddCount 18443 15 = 7 ∧ acceleratedOrbit 15 18443 = 1232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18443 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18443) = 3 ^ 7 * m + 1232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18443.1, data_15_18443.2]

/-- Complete interval computation for depth 15, residue 18444. -/
theorem bounds_15_18444 : exactInterval 15 18444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18444 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18444) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18444 : oddCount 18444 15 = 5 ∧ acceleratedOrbit 15 18444 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18444 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18444) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18444.1, data_15_18444.2]

/-- Complete interval computation for depth 15, residue 18445. -/
theorem bounds_15_18445 : exactInterval 15 18445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18445 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18445) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18445 : oddCount 18445 15 = 5 ∧ acceleratedOrbit 15 18445 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18445 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18445) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18445.1, data_15_18445.2]

/-- Complete interval computation for depth 15, residue 18446. -/
theorem bounds_15_18446 : exactInterval 15 18446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18446 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18446) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18446 : oddCount 18446 15 = 7 ∧ acceleratedOrbit 15 18446 = 1232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18446 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18446) = 3 ^ 7 * m + 1232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18446.1, data_15_18446.2]

/-- Complete interval computation for depth 15, residue 18447. -/
theorem bounds_15_18447 : exactInterval 15 18447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18447 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18447) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18447 : oddCount 18447 15 = 7 ∧ acceleratedOrbit 15 18447 = 1232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18447 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18447) = 3 ^ 7 * m + 1232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18447.1, data_15_18447.2]

end Collatz.Research.PassageAtlas.Batch0563
