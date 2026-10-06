import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0624

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 20414. -/
theorem bounds_15_20414 : exactInterval 15 20414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20414 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20414) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20414 : oddCount 20414 15 = 8 ∧ acceleratedOrbit 15 20414 = 4088 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20414 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20414) = 3 ^ 8 * m + 4088 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20414.1, data_15_20414.2]

/-- Complete interval computation for depth 15, residue 20415. -/
theorem bounds_15_20415 : exactInterval 15 20415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20415 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20415) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20415 : oddCount 20415 15 = 10 ∧ acceleratedOrbit 15 20415 = 36791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20415 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20415) = 3 ^ 10 * m + 36791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20415.1, data_15_20415.2]

/-- Complete interval computation for depth 15, residue 20416. -/
theorem bounds_15_20416 : exactInterval 15 20416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20416 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20416) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20416 : oddCount 20416 15 = 7 ∧ acceleratedOrbit 15 20416 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20416 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20416) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20416.1, data_15_20416.2]

/-- Complete interval computation for depth 15, residue 20417. -/
theorem bounds_15_20417 : exactInterval 15 20417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20417 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20417) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20417 : oddCount 20417 15 = 8 ∧ acceleratedOrbit 15 20417 = 4090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20417 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20417) = 3 ^ 8 * m + 4090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20417.1, data_15_20417.2]

/-- Complete interval computation for depth 15, residue 20418. -/
theorem bounds_15_20418 : exactInterval 15 20418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20418 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20418) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20418 : oddCount 20418 15 = 9 ∧ acceleratedOrbit 15 20418 = 12268 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20418 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20418) = 3 ^ 9 * m + 12268 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20418.1, data_15_20418.2]

/-- Complete interval computation for depth 15, residue 20419. -/
theorem bounds_15_20419 : exactInterval 15 20419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20419 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20419) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20419 : oddCount 20419 15 = 9 ∧ acceleratedOrbit 15 20419 = 12268 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20419 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20419) = 3 ^ 9 * m + 12268 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20419.1, data_15_20419.2]

/-- Complete interval computation for depth 15, residue 20420. -/
theorem bounds_15_20420 : exactInterval 15 20420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20420 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20420) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20420 : oddCount 20420 15 = 7 ∧ acceleratedOrbit 15 20420 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20420 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20420) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20420.1, data_15_20420.2]

/-- Complete interval computation for depth 15, residue 20421. -/
theorem bounds_15_20421 : exactInterval 15 20421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20421 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20421) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20421 : oddCount 20421 15 = 7 ∧ acceleratedOrbit 15 20421 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20421 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20421) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20421.1, data_15_20421.2]

/-- Complete interval computation for depth 15, residue 20422. -/
theorem bounds_15_20422 : exactInterval 15 20422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20422 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20422) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20422 : oddCount 20422 15 = 7 ∧ acceleratedOrbit 15 20422 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20422 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20422) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20422.1, data_15_20422.2]

/-- Complete interval computation for depth 15, residue 20423. -/
theorem bounds_15_20423 : exactInterval 15 20423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20423 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20423) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20423 : oddCount 20423 15 = 9 ∧ acceleratedOrbit 15 20423 = 12269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20423 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20423) = 3 ^ 9 * m + 12269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20423.1, data_15_20423.2]

/-- Complete interval computation for depth 15, residue 20424. -/
theorem bounds_15_20424 : exactInterval 15 20424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20424 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20424) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20424 : oddCount 20424 15 = 8 ∧ acceleratedOrbit 15 20424 = 4094 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20424 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20424) = 3 ^ 8 * m + 4094 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20424.1, data_15_20424.2]

/-- Complete interval computation for depth 15, residue 20425. -/
theorem bounds_15_20425 : exactInterval 15 20425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20425 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20425) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20425 : oddCount 20425 15 = 10 ∧ acceleratedOrbit 15 20425 = 36814 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20425 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20425) = 3 ^ 10 * m + 36814 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20425.1, data_15_20425.2]

/-- Complete interval computation for depth 15, residue 20426. -/
theorem bounds_15_20426 : exactInterval 15 20426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20426 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20426) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20426 : oddCount 20426 15 = 8 ∧ acceleratedOrbit 15 20426 = 4094 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20426 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20426) = 3 ^ 8 * m + 4094 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20426.1, data_15_20426.2]

/-- Complete interval computation for depth 15, residue 20427. -/
theorem bounds_15_20427 : exactInterval 15 20427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20427 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20427) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20427 : oddCount 20427 15 = 5 ∧ acceleratedOrbit 15 20427 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20427 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20427) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20427.1, data_15_20427.2]

/-- Complete interval computation for depth 15, residue 20428. -/
theorem bounds_15_20428 : exactInterval 15 20428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20428 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20428) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20428 : oddCount 20428 15 = 8 ∧ acceleratedOrbit 15 20428 = 4094 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20428 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20428) = 3 ^ 8 * m + 4094 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20428.1, data_15_20428.2]

/-- Complete interval computation for depth 15, residue 20429. -/
theorem bounds_15_20429 : exactInterval 15 20429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20429 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20429) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20429 : oddCount 20429 15 = 8 ∧ acceleratedOrbit 15 20429 = 4094 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20429 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20429) = 3 ^ 8 * m + 4094 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20429.1, data_15_20429.2]

/-- Complete interval computation for depth 15, residue 20430. -/
theorem bounds_15_20430 : exactInterval 15 20430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20430 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20430) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20430 : oddCount 20430 15 = 9 ∧ acceleratedOrbit 15 20430 = 12275 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20430 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20430) = 3 ^ 9 * m + 12275 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20430.1, data_15_20430.2]

/-- Complete interval computation for depth 15, residue 20431. -/
theorem bounds_15_20431 : exactInterval 15 20431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20431 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20431) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20431 : oddCount 20431 15 = 9 ∧ acceleratedOrbit 15 20431 = 12275 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20431 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20431) = 3 ^ 9 * m + 12275 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20431.1, data_15_20431.2]

/-- Complete interval computation for depth 15, residue 20432. -/
theorem bounds_15_20432 : exactInterval 15 20432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20432 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20432) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20432 : oddCount 20432 15 = 7 ∧ acceleratedOrbit 15 20432 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20432 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20432) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20432.1, data_15_20432.2]

/-- Complete interval computation for depth 15, residue 20433. -/
theorem bounds_15_20433 : exactInterval 15 20433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20433 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20433) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20433 : oddCount 20433 15 = 8 ∧ acceleratedOrbit 15 20433 = 4094 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20433 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20433) = 3 ^ 8 * m + 4094 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20433.1, data_15_20433.2]

/-- Complete interval computation for depth 15, residue 20434. -/
theorem bounds_15_20434 : exactInterval 15 20434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20434 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20434) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20434 : oddCount 20434 15 = 10 ∧ acceleratedOrbit 15 20434 = 36830 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20434 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20434) = 3 ^ 10 * m + 36830 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20434.1, data_15_20434.2]

/-- Complete interval computation for depth 15, residue 20435. -/
theorem bounds_15_20435 : exactInterval 15 20435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20435 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20435) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20435 : oddCount 20435 15 = 10 ∧ acceleratedOrbit 15 20435 = 36830 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20435 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20435) = 3 ^ 10 * m + 36830 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20435.1, data_15_20435.2]

/-- Complete interval computation for depth 15, residue 20436. -/
theorem bounds_15_20436 : exactInterval 15 20436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20436 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20436) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20436 : oddCount 20436 15 = 7 ∧ acceleratedOrbit 15 20436 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20436 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20436) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20436.1, data_15_20436.2]

/-- Complete interval computation for depth 15, residue 20437. -/
theorem bounds_15_20437 : exactInterval 15 20437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20437 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20437) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20437 : oddCount 20437 15 = 7 ∧ acceleratedOrbit 15 20437 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20437 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20437) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20437.1, data_15_20437.2]

/-- Complete interval computation for depth 15, residue 20438. -/
theorem bounds_15_20438 : exactInterval 15 20438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20438 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20438) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20438 : oddCount 20438 15 = 8 ∧ acceleratedOrbit 15 20438 = 4093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20438 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20438) = 3 ^ 8 * m + 4093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20438.1, data_15_20438.2]

/-- Complete interval computation for depth 15, residue 20439. -/
theorem bounds_15_20439 : exactInterval 15 20439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20439 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20439) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20439 : oddCount 20439 15 = 8 ∧ acceleratedOrbit 15 20439 = 4093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20439 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20439) = 3 ^ 8 * m + 4093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20439.1, data_15_20439.2]

/-- Complete interval computation for depth 15, residue 20440. -/
theorem bounds_15_20440 : exactInterval 15 20440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20440 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20440) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20440 : oddCount 20440 15 = 6 ∧ acceleratedOrbit 15 20440 = 455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20440 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20440) = 3 ^ 6 * m + 455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20440.1, data_15_20440.2]

/-- Complete interval computation for depth 15, residue 20441. -/
theorem bounds_15_20441 : exactInterval 15 20441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20441 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20441) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20441 : oddCount 20441 15 = 7 ∧ acceleratedOrbit 15 20441 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20441 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20441) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20441.1, data_15_20441.2]

/-- Complete interval computation for depth 15, residue 20442. -/
theorem bounds_15_20442 : exactInterval 15 20442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20442 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20442) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20442 : oddCount 20442 15 = 6 ∧ acceleratedOrbit 15 20442 = 455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20442 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20442) = 3 ^ 6 * m + 455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20442.1, data_15_20442.2]

/-- Complete interval computation for depth 15, residue 20443. -/
theorem bounds_15_20443 : exactInterval 15 20443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20443 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20443) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20443 : oddCount 20443 15 = 10 ∧ acceleratedOrbit 15 20443 = 36845 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20443 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20443) = 3 ^ 10 * m + 36845 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20443.1, data_15_20443.2]

/-- Complete interval computation for depth 15, residue 20444. -/
theorem bounds_15_20444 : exactInterval 15 20444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20444 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20444) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20444 : oddCount 20444 15 = 6 ∧ acceleratedOrbit 15 20444 = 455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20444 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20444) = 3 ^ 6 * m + 455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20444.1, data_15_20444.2]

/-- Complete interval computation for depth 15, residue 20445. -/
theorem bounds_15_20445 : exactInterval 15 20445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20445 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20445) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20445 : oddCount 20445 15 = 6 ∧ acceleratedOrbit 15 20445 = 455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20445 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20445) = 3 ^ 6 * m + 455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20445.1, data_15_20445.2]

/-- Complete interval computation for depth 15, residue 20446. -/
theorem bounds_15_20446 : exactInterval 15 20446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20446 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20446) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20446 : oddCount 20446 15 = 9 ∧ acceleratedOrbit 15 20446 = 12284 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20446 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20446) = 3 ^ 9 * m + 12284 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20446.1, data_15_20446.2]

end Collatz.Research.PassageAtlas.Batch0624
