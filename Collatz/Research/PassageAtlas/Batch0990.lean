import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0990

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 32407. -/
theorem bounds_15_32407 : exactInterval 15 32407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32407 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32407) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32407 : oddCount 32407 15 = 6 ∧ acceleratedOrbit 15 32407 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32407 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32407) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32407.1, data_15_32407.2]

/-- Complete interval computation for depth 15, residue 32408. -/
theorem bounds_15_32408 : exactInterval 15 32408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32408 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32408) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32408 : oddCount 32408 15 = 8 ∧ acceleratedOrbit 15 32408 = 6493 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32408 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32408) = 3 ^ 8 * m + 6493 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32408.1, data_15_32408.2]

/-- Complete interval computation for depth 15, residue 32409. -/
theorem bounds_15_32409 : exactInterval 15 32409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32409 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32409) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32409 : oddCount 32409 15 = 8 ∧ acceleratedOrbit 15 32409 = 6490 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32409 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32409) = 3 ^ 8 * m + 6490 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32409.1, data_15_32409.2]

/-- Complete interval computation for depth 15, residue 32410. -/
theorem bounds_15_32410 : exactInterval 15 32410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32410 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32410) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32410 : oddCount 32410 15 = 8 ∧ acceleratedOrbit 15 32410 = 6493 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32410 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32410) = 3 ^ 8 * m + 6493 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32410.1, data_15_32410.2]

/-- Complete interval computation for depth 15, residue 32411. -/
theorem bounds_15_32411 : exactInterval 15 32411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32411 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32411) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32411 : oddCount 32411 15 = 10 ∧ acceleratedOrbit 15 32411 = 58409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32411 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32411) = 3 ^ 10 * m + 58409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32411.1, data_15_32411.2]

/-- Complete interval computation for depth 15, residue 32412. -/
theorem bounds_15_32412 : exactInterval 15 32412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32412 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32412) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32412 : oddCount 32412 15 = 8 ∧ acceleratedOrbit 15 32412 = 6491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32412 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32412) = 3 ^ 8 * m + 6491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32412.1, data_15_32412.2]

/-- Complete interval computation for depth 15, residue 32413. -/
theorem bounds_15_32413 : exactInterval 15 32413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32413 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32413) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32413 : oddCount 32413 15 = 8 ∧ acceleratedOrbit 15 32413 = 6491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32413 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32413) = 3 ^ 8 * m + 6491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32413.1, data_15_32413.2]

/-- Complete interval computation for depth 15, residue 32414. -/
theorem bounds_15_32414 : exactInterval 15 32414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32414 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32414) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32414 : oddCount 32414 15 = 8 ∧ acceleratedOrbit 15 32414 = 6491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32414 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32414) = 3 ^ 8 * m + 6491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32414.1, data_15_32414.2]

/-- Complete interval computation for depth 15, residue 32415. -/
theorem bounds_15_32415 : exactInterval 15 32415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32415 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32415) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32415 : oddCount 32415 15 = 10 ∧ acceleratedOrbit 15 32415 = 58415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32415 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32415) = 3 ^ 10 * m + 58415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32415.1, data_15_32415.2]

/-- Complete interval computation for depth 15, residue 32416. -/
theorem bounds_15_32416 : exactInterval 15 32416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32416 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32416) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32416 : oddCount 32416 15 = 6 ∧ acceleratedOrbit 15 32416 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32416 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32416) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32416.1, data_15_32416.2]

/-- Complete interval computation for depth 15, residue 32417. -/
theorem bounds_15_32417 : exactInterval 15 32417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32417 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32417) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32417 : oddCount 32417 15 = 7 ∧ acceleratedOrbit 15 32417 = 2164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32417 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32417) = 3 ^ 7 * m + 2164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32417.1, data_15_32417.2]

/-- Complete interval computation for depth 15, residue 32418. -/
theorem bounds_15_32418 : exactInterval 15 32418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32418 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32418) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32418 : oddCount 32418 15 = 8 ∧ acceleratedOrbit 15 32418 = 6493 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32418 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32418) = 3 ^ 8 * m + 6493 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32418.1, data_15_32418.2]

/-- Complete interval computation for depth 15, residue 32419. -/
theorem bounds_15_32419 : exactInterval 15 32419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32419 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32419) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32419 : oddCount 32419 15 = 8 ∧ acceleratedOrbit 15 32419 = 6493 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32419 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32419) = 3 ^ 8 * m + 6493 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32419.1, data_15_32419.2]

/-- Complete interval computation for depth 15, residue 32420. -/
theorem bounds_15_32420 : exactInterval 15 32420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32420 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32420) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32420 : oddCount 32420 15 = 9 ∧ acceleratedOrbit 15 32420 = 19478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32420 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32420) = 3 ^ 9 * m + 19478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32420.1, data_15_32420.2]

/-- Complete interval computation for depth 15, residue 32421. -/
theorem bounds_15_32421 : exactInterval 15 32421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32421 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32421) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32421 : oddCount 32421 15 = 9 ∧ acceleratedOrbit 15 32421 = 19478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32421 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32421) = 3 ^ 9 * m + 19478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32421.1, data_15_32421.2]

/-- Complete interval computation for depth 15, residue 32422. -/
theorem bounds_15_32422 : exactInterval 15 32422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32422 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32422) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32422 : oddCount 32422 15 = 9 ∧ acceleratedOrbit 15 32422 = 19478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32422 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32422) = 3 ^ 9 * m + 19478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32422.1, data_15_32422.2]

/-- Complete interval computation for depth 15, residue 32423. -/
theorem bounds_15_32423 : exactInterval 15 32423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32423 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32423) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32423 : oddCount 32423 15 = 9 ∧ acceleratedOrbit 15 32423 = 19477 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32423 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32423) = 3 ^ 9 * m + 19477 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32423.1, data_15_32423.2]

/-- Complete interval computation for depth 15, residue 32424. -/
theorem bounds_15_32424 : exactInterval 15 32424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32424 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32424) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32424 : oddCount 32424 15 = 6 ∧ acceleratedOrbit 15 32424 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32424 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32424) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32424.1, data_15_32424.2]

/-- Complete interval computation for depth 15, residue 32425. -/
theorem bounds_15_32425 : exactInterval 15 32425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32425 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32425) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32425 : oddCount 32425 15 = 13 ∧ acceleratedOrbit 15 32425 = 1577717 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32425 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32425) = 3 ^ 13 * m + 1577717 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32425.1, data_15_32425.2]

/-- Complete interval computation for depth 15, residue 32426. -/
theorem bounds_15_32426 : exactInterval 15 32426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32426 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32426) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32426 : oddCount 32426 15 = 6 ∧ acceleratedOrbit 15 32426 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32426 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32426) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32426.1, data_15_32426.2]

/-- Complete interval computation for depth 15, residue 32427. -/
theorem bounds_15_32427 : exactInterval 15 32427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32427 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32427) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32427 : oddCount 32427 15 = 10 ∧ acceleratedOrbit 15 32427 = 58441 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32427 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32427) = 3 ^ 10 * m + 58441 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32427.1, data_15_32427.2]

/-- Complete interval computation for depth 15, residue 32428. -/
theorem bounds_15_32428 : exactInterval 15 32428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32428 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32428) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32428 : oddCount 32428 15 = 7 ∧ acceleratedOrbit 15 32428 = 2165 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32428 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32428) = 3 ^ 7 * m + 2165 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32428.1, data_15_32428.2]

/-- Complete interval computation for depth 15, residue 32429. -/
theorem bounds_15_32429 : exactInterval 15 32429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32429 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32429) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32429 : oddCount 32429 15 = 7 ∧ acceleratedOrbit 15 32429 = 2165 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32429 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32429) = 3 ^ 7 * m + 2165 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32429.1, data_15_32429.2]

/-- Complete interval computation for depth 15, residue 32430. -/
theorem bounds_15_32430 : exactInterval 15 32430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32430 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32430) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32430 : oddCount 32430 15 = 7 ∧ acceleratedOrbit 15 32430 = 2165 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32430 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32430) = 3 ^ 7 * m + 2165 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32430.1, data_15_32430.2]

/-- Complete interval computation for depth 15, residue 32431. -/
theorem bounds_15_32431 : exactInterval 15 32431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32431 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32431) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32431 : oddCount 32431 15 = 8 ∧ acceleratedOrbit 15 32431 = 6494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32431 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32431) = 3 ^ 8 * m + 6494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32431.1, data_15_32431.2]

/-- Complete interval computation for depth 15, residue 32432. -/
theorem bounds_15_32432 : exactInterval 15 32432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32432 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32432) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32432 : oddCount 32432 15 = 8 ∧ acceleratedOrbit 15 32432 = 6500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32432 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32432) = 3 ^ 8 * m + 6500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32432.1, data_15_32432.2]

/-- Complete interval computation for depth 15, residue 32433. -/
theorem bounds_15_32433 : exactInterval 15 32433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32433 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32433) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32433 : oddCount 32433 15 = 6 ∧ acceleratedOrbit 15 32433 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32433 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32433) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32433.1, data_15_32433.2]

/-- Complete interval computation for depth 15, residue 32434. -/
theorem bounds_15_32434 : exactInterval 15 32434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32434 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32434) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32434 : oddCount 32434 15 = 6 ∧ acceleratedOrbit 15 32434 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32434 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32434) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32434.1, data_15_32434.2]

/-- Complete interval computation for depth 15, residue 32435. -/
theorem bounds_15_32435 : exactInterval 15 32435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32435 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32435) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32435 : oddCount 32435 15 = 6 ∧ acceleratedOrbit 15 32435 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32435 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32435) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32435.1, data_15_32435.2]

/-- Complete interval computation for depth 15, residue 32436. -/
theorem bounds_15_32436 : exactInterval 15 32436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32436 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32436) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32436 : oddCount 32436 15 = 8 ∧ acceleratedOrbit 15 32436 = 6500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32436 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32436) = 3 ^ 8 * m + 6500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32436.1, data_15_32436.2]

/-- Complete interval computation for depth 15, residue 32437. -/
theorem bounds_15_32437 : exactInterval 15 32437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32437 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32437) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32437 : oddCount 32437 15 = 8 ∧ acceleratedOrbit 15 32437 = 6500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32437 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32437) = 3 ^ 8 * m + 6500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32437.1, data_15_32437.2]

/-- Complete interval computation for depth 15, residue 32438. -/
theorem bounds_15_32438 : exactInterval 15 32438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32438 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32438) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32438 : oddCount 32438 15 = 9 ∧ acceleratedOrbit 15 32438 = 19487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32438 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32438) = 3 ^ 9 * m + 19487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32438.1, data_15_32438.2]

/-- Complete interval computation for depth 15, residue 32439. -/
theorem bounds_15_32439 : exactInterval 15 32439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32439 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32439) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32439 : oddCount 32439 15 = 9 ∧ acceleratedOrbit 15 32439 = 19487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32439 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32439) = 3 ^ 9 * m + 19487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32439.1, data_15_32439.2]

end Collatz.Research.PassageAtlas.Batch0990
