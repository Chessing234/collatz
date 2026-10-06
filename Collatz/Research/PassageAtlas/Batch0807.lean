import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0807

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 26411. -/
theorem bounds_15_26411 : exactInterval 15 26411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26411 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26411) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26411 : oddCount 26411 15 = 8 ∧ acceleratedOrbit 15 26411 = 5291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26411 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26411) = 3 ^ 8 * m + 5291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26411.1, data_15_26411.2]

/-- Complete interval computation for depth 15, residue 26412. -/
theorem bounds_15_26412 : exactInterval 15 26412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26412 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26412) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26412 : oddCount 26412 15 = 5 ∧ acceleratedOrbit 15 26412 = 196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26412 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26412) = 3 ^ 5 * m + 196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26412.1, data_15_26412.2]

/-- Complete interval computation for depth 15, residue 26413. -/
theorem bounds_15_26413 : exactInterval 15 26413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26413 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26413) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26413 : oddCount 26413 15 = 5 ∧ acceleratedOrbit 15 26413 = 196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26413 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26413) = 3 ^ 5 * m + 196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26413.1, data_15_26413.2]

/-- Complete interval computation for depth 15, residue 26414. -/
theorem bounds_15_26414 : exactInterval 15 26414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26414 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26414) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26414 : oddCount 26414 15 = 5 ∧ acceleratedOrbit 15 26414 = 196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26414 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26414) = 3 ^ 5 * m + 196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26414.1, data_15_26414.2]

/-- Complete interval computation for depth 15, residue 26415. -/
theorem bounds_15_26415 : exactInterval 15 26415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26415 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26415) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26415 : oddCount 26415 15 = 9 ∧ acceleratedOrbit 15 26415 = 15869 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26415 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26415) = 3 ^ 9 * m + 15869 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26415.1, data_15_26415.2]

/-- Complete interval computation for depth 15, residue 26416. -/
theorem bounds_15_26416 : exactInterval 15 26416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26416 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26416) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26416 : oddCount 26416 15 = 6 ∧ acceleratedOrbit 15 26416 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26416 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26416) = 3 ^ 6 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26416.1, data_15_26416.2]

/-- Complete interval computation for depth 15, residue 26417. -/
theorem bounds_15_26417 : exactInterval 15 26417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26417 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26417) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26417 : oddCount 26417 15 = 5 ∧ acceleratedOrbit 15 26417 = 196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26417 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26417) = 3 ^ 5 * m + 196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26417.1, data_15_26417.2]

/-- Complete interval computation for depth 15, residue 26418. -/
theorem bounds_15_26418 : exactInterval 15 26418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26418 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26418) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26418 : oddCount 26418 15 = 5 ∧ acceleratedOrbit 15 26418 = 196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26418 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26418) = 3 ^ 5 * m + 196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26418.1, data_15_26418.2]

/-- Complete interval computation for depth 15, residue 26419. -/
theorem bounds_15_26419 : exactInterval 15 26419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26419 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26419) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26419 : oddCount 26419 15 = 5 ∧ acceleratedOrbit 15 26419 = 196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26419 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26419) = 3 ^ 5 * m + 196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26419.1, data_15_26419.2]

/-- Complete interval computation for depth 15, residue 26420. -/
theorem bounds_15_26420 : exactInterval 15 26420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26420 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26420) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26420 : oddCount 26420 15 = 6 ∧ acceleratedOrbit 15 26420 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26420 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26420) = 3 ^ 6 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26420.1, data_15_26420.2]

/-- Complete interval computation for depth 15, residue 26421. -/
theorem bounds_15_26421 : exactInterval 15 26421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26421 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26421) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26421 : oddCount 26421 15 = 6 ∧ acceleratedOrbit 15 26421 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26421 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26421) = 3 ^ 6 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26421.1, data_15_26421.2]

/-- Complete interval computation for depth 15, residue 26422. -/
theorem bounds_15_26422 : exactInterval 15 26422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26422 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26422) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26422 : oddCount 26422 15 = 9 ∧ acceleratedOrbit 15 26422 = 15875 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26422 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26422) = 3 ^ 9 * m + 15875 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26422.1, data_15_26422.2]

/-- Complete interval computation for depth 15, residue 26423. -/
theorem bounds_15_26423 : exactInterval 15 26423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26423 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26423) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26423 : oddCount 26423 15 = 9 ∧ acceleratedOrbit 15 26423 = 15875 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26423 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26423) = 3 ^ 9 * m + 15875 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26423.1, data_15_26423.2]

/-- Complete interval computation for depth 15, residue 26424. -/
theorem bounds_15_26424 : exactInterval 15 26424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26424 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26424) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26424 : oddCount 26424 15 = 8 ∧ acceleratedOrbit 15 26424 = 5293 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26424 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26424) = 3 ^ 8 * m + 5293 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26424.1, data_15_26424.2]

/-- Complete interval computation for depth 15, residue 26425. -/
theorem bounds_15_26425 : exactInterval 15 26425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26425 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26425) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26425 : oddCount 26425 15 = 10 ∧ acceleratedOrbit 15 26425 = 47627 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26425 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26425) = 3 ^ 10 * m + 47627 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26425.1, data_15_26425.2]

/-- Complete interval computation for depth 15, residue 26426. -/
theorem bounds_15_26426 : exactInterval 15 26426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26426 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26426) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26426 : oddCount 26426 15 = 8 ∧ acceleratedOrbit 15 26426 = 5293 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26426 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26426) = 3 ^ 8 * m + 5293 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26426.1, data_15_26426.2]

/-- Complete interval computation for depth 15, residue 26427. -/
theorem bounds_15_26427 : exactInterval 15 26427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26427 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26427) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26427 : oddCount 26427 15 = 5 ∧ acceleratedOrbit 15 26427 = 196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26427 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26427) = 3 ^ 5 * m + 196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26427.1, data_15_26427.2]

/-- Complete interval computation for depth 15, residue 26428. -/
theorem bounds_15_26428 : exactInterval 15 26428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26428 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26428) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26428 : oddCount 26428 15 = 8 ∧ acceleratedOrbit 15 26428 = 5293 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26428 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26428) = 3 ^ 8 * m + 5293 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26428.1, data_15_26428.2]

/-- Complete interval computation for depth 15, residue 26429. -/
theorem bounds_15_26429 : exactInterval 15 26429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26429 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26429) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26429 : oddCount 26429 15 = 8 ∧ acceleratedOrbit 15 26429 = 5293 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26429 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26429) = 3 ^ 8 * m + 5293 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26429.1, data_15_26429.2]

/-- Complete interval computation for depth 15, residue 26430. -/
theorem bounds_15_26430 : exactInterval 15 26430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26430 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26430) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26430 : oddCount 26430 15 = 9 ∧ acceleratedOrbit 15 26430 = 15878 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26430 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26430) = 3 ^ 9 * m + 15878 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26430.1, data_15_26430.2]

/-- Complete interval computation for depth 15, residue 26431. -/
theorem bounds_15_26431 : exactInterval 15 26431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26431 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26431) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26431 : oddCount 26431 15 = 9 ∧ acceleratedOrbit 15 26431 = 15878 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26431 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26431) = 3 ^ 9 * m + 15878 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26431.1, data_15_26431.2]

/-- Complete interval computation for depth 15, residue 26432. -/
theorem bounds_15_26432 : exactInterval 15 26432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26432 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26432) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26432 : oddCount 26432 15 = 6 ∧ acceleratedOrbit 15 26432 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26432 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26432) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26432.1, data_15_26432.2]

/-- Complete interval computation for depth 15, residue 26433. -/
theorem bounds_15_26433 : exactInterval 15 26433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26433 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26433) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26433 : oddCount 26433 15 = 6 ∧ acceleratedOrbit 15 26433 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26433 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26433) = 3 ^ 6 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26433.1, data_15_26433.2]

/-- Complete interval computation for depth 15, residue 26434. -/
theorem bounds_15_26434 : exactInterval 15 26434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26434 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26434) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26434 : oddCount 26434 15 = 7 ∧ acceleratedOrbit 15 26434 = 1765 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26434 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26434) = 3 ^ 7 * m + 1765 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26434.1, data_15_26434.2]

/-- Complete interval computation for depth 15, residue 26435. -/
theorem bounds_15_26435 : exactInterval 15 26435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26435 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26435) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26435 : oddCount 26435 15 = 7 ∧ acceleratedOrbit 15 26435 = 1765 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26435 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26435) = 3 ^ 7 * m + 1765 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26435.1, data_15_26435.2]

/-- Complete interval computation for depth 15, residue 26436. -/
theorem bounds_15_26436 : exactInterval 15 26436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26436 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26436) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26436 : oddCount 26436 15 = 6 ∧ acceleratedOrbit 15 26436 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26436 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26436) = 3 ^ 6 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26436.1, data_15_26436.2]

/-- Complete interval computation for depth 15, residue 26437. -/
theorem bounds_15_26437 : exactInterval 15 26437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26437 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26437) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26437 : oddCount 26437 15 = 6 ∧ acceleratedOrbit 15 26437 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26437 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26437) = 3 ^ 6 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26437.1, data_15_26437.2]

/-- Complete interval computation for depth 15, residue 26438. -/
theorem bounds_15_26438 : exactInterval 15 26438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26438 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26438) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26438 : oddCount 26438 15 = 6 ∧ acceleratedOrbit 15 26438 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26438 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26438) = 3 ^ 6 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26438.1, data_15_26438.2]

/-- Complete interval computation for depth 15, residue 26439. -/
theorem bounds_15_26439 : exactInterval 15 26439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26439 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26439) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26439 : oddCount 26439 15 = 10 ∧ acceleratedOrbit 15 26439 = 47648 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26439 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26439) = 3 ^ 10 * m + 47648 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26439.1, data_15_26439.2]

/-- Complete interval computation for depth 15, residue 26440. -/
theorem bounds_15_26440 : exactInterval 15 26440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26440 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26440) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26440 : oddCount 26440 15 = 7 ∧ acceleratedOrbit 15 26440 = 1766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26440 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26440) = 3 ^ 7 * m + 1766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26440.1, data_15_26440.2]

/-- Complete interval computation for depth 15, residue 26441. -/
theorem bounds_15_26441 : exactInterval 15 26441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26441 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26441) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26441 : oddCount 26441 15 = 7 ∧ acceleratedOrbit 15 26441 = 1765 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26441 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26441) = 3 ^ 7 * m + 1765 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26441.1, data_15_26441.2]

/-- Complete interval computation for depth 15, residue 26442. -/
theorem bounds_15_26442 : exactInterval 15 26442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26442 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26442) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26442 : oddCount 26442 15 = 7 ∧ acceleratedOrbit 15 26442 = 1766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26442 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26442) = 3 ^ 7 * m + 1766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26442.1, data_15_26442.2]

end Collatz.Research.PassageAtlas.Batch0807
