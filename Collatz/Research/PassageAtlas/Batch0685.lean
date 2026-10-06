import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0685

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 22413. -/
theorem bounds_15_22413 : exactInterval 15 22413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22413 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22413) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22413 : oddCount 22413 15 = 4 ∧ acceleratedOrbit 15 22413 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22413 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22413) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22413.1, data_15_22413.2]

/-- Complete interval computation for depth 15, residue 22414. -/
theorem bounds_15_22414 : exactInterval 15 22414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22414 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22414) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22414 : oddCount 22414 15 = 9 ∧ acceleratedOrbit 15 22414 = 13466 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22414 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22414) = 3 ^ 9 * m + 13466 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22414.1, data_15_22414.2]

/-- Complete interval computation for depth 15, residue 22415. -/
theorem bounds_15_22415 : exactInterval 15 22415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22415 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22415) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22415 : oddCount 22415 15 = 9 ∧ acceleratedOrbit 15 22415 = 13466 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22415 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22415) = 3 ^ 9 * m + 13466 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22415.1, data_15_22415.2]

/-- Complete interval computation for depth 15, residue 22416. -/
theorem bounds_15_22416 : exactInterval 15 22416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22416 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22416) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22416 : oddCount 22416 15 = 8 ∧ acceleratedOrbit 15 22416 = 4495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22416 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22416) = 3 ^ 8 * m + 4495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22416.1, data_15_22416.2]

/-- Complete interval computation for depth 15, residue 22417. -/
theorem bounds_15_22417 : exactInterval 15 22417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22417 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22417) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22417 : oddCount 22417 15 = 9 ∧ acceleratedOrbit 15 22417 = 13472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22417 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22417) = 3 ^ 9 * m + 13472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22417.1, data_15_22417.2]

/-- Complete interval computation for depth 15, residue 22418. -/
theorem bounds_15_22418 : exactInterval 15 22418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22418 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22418) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22418 : oddCount 22418 15 = 9 ∧ acceleratedOrbit 15 22418 = 13472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22418 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22418) = 3 ^ 9 * m + 13472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22418.1, data_15_22418.2]

/-- Complete interval computation for depth 15, residue 22419. -/
theorem bounds_15_22419 : exactInterval 15 22419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22419 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22419) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22419 : oddCount 22419 15 = 9 ∧ acceleratedOrbit 15 22419 = 13472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22419 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22419) = 3 ^ 9 * m + 13472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22419.1, data_15_22419.2]

/-- Complete interval computation for depth 15, residue 22420. -/
theorem bounds_15_22420 : exactInterval 15 22420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22420 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22420) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22420 : oddCount 22420 15 = 8 ∧ acceleratedOrbit 15 22420 = 4495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22420 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22420) = 3 ^ 8 * m + 4495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22420.1, data_15_22420.2]

/-- Complete interval computation for depth 15, residue 22421. -/
theorem bounds_15_22421 : exactInterval 15 22421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22421 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22421) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22421 : oddCount 22421 15 = 8 ∧ acceleratedOrbit 15 22421 = 4495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22421 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22421) = 3 ^ 8 * m + 4495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22421.1, data_15_22421.2]

/-- Complete interval computation for depth 15, residue 22422. -/
theorem bounds_15_22422 : exactInterval 15 22422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22422 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22422) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22422 : oddCount 22422 15 = 7 ∧ acceleratedOrbit 15 22422 = 1498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22422 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22422) = 3 ^ 7 * m + 1498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22422.1, data_15_22422.2]

/-- Complete interval computation for depth 15, residue 22423. -/
theorem bounds_15_22423 : exactInterval 15 22423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22423 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22423) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22423 : oddCount 22423 15 = 7 ∧ acceleratedOrbit 15 22423 = 1498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22423 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22423) = 3 ^ 7 * m + 1498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22423.1, data_15_22423.2]

/-- Complete interval computation for depth 15, residue 22424. -/
theorem bounds_15_22424 : exactInterval 15 22424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22424 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22424) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22424 : oddCount 22424 15 = 8 ∧ acceleratedOrbit 15 22424 = 4495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22424 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22424) = 3 ^ 8 * m + 4495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22424.1, data_15_22424.2]

/-- Complete interval computation for depth 15, residue 22425. -/
theorem bounds_15_22425 : exactInterval 15 22425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22425 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22425) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22425 : oddCount 22425 15 = 7 ∧ acceleratedOrbit 15 22425 = 1498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22425 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22425) = 3 ^ 7 * m + 1498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22425.1, data_15_22425.2]

/-- Complete interval computation for depth 15, residue 22426. -/
theorem bounds_15_22426 : exactInterval 15 22426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22426 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22426) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22426 : oddCount 22426 15 = 8 ∧ acceleratedOrbit 15 22426 = 4495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22426 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22426) = 3 ^ 8 * m + 4495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22426.1, data_15_22426.2]

/-- Complete interval computation for depth 15, residue 22427. -/
theorem bounds_15_22427 : exactInterval 15 22427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22427 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22427) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22427 : oddCount 22427 15 = 11 ∧ acceleratedOrbit 15 22427 = 121256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22427 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22427) = 3 ^ 11 * m + 121256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22427.1, data_15_22427.2]

/-- Complete interval computation for depth 15, residue 22428. -/
theorem bounds_15_22428 : exactInterval 15 22428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22428 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22428) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22428 : oddCount 22428 15 = 8 ∧ acceleratedOrbit 15 22428 = 4492 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22428 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22428) = 3 ^ 8 * m + 4492 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22428.1, data_15_22428.2]

/-- Complete interval computation for depth 15, residue 22429. -/
theorem bounds_15_22429 : exactInterval 15 22429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22429 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22429) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22429 : oddCount 22429 15 = 8 ∧ acceleratedOrbit 15 22429 = 4492 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22429 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22429) = 3 ^ 8 * m + 4492 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22429.1, data_15_22429.2]

/-- Complete interval computation for depth 15, residue 22430. -/
theorem bounds_15_22430 : exactInterval 15 22430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22430 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22430) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22430 : oddCount 22430 15 = 8 ∧ acceleratedOrbit 15 22430 = 4492 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22430 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22430) = 3 ^ 8 * m + 4492 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22430.1, data_15_22430.2]

/-- Complete interval computation for depth 15, residue 22431. -/
theorem bounds_15_22431 : exactInterval 15 22431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22431 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22431) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22431 : oddCount 22431 15 = 9 ∧ acceleratedOrbit 15 22431 = 13475 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22431 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22431) = 3 ^ 9 * m + 13475 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22431.1, data_15_22431.2]

/-- Complete interval computation for depth 15, residue 22432. -/
theorem bounds_15_22432 : exactInterval 15 22432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22432 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22432) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22432 : oddCount 22432 15 = 5 ∧ acceleratedOrbit 15 22432 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22432 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22432) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22432.1, data_15_22432.2]

/-- Complete interval computation for depth 15, residue 22433. -/
theorem bounds_15_22433 : exactInterval 15 22433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22433 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22433) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22433 : oddCount 22433 15 = 7 ∧ acceleratedOrbit 15 22433 = 1498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22433 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22433) = 3 ^ 7 * m + 1498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22433.1, data_15_22433.2]

/-- Complete interval computation for depth 15, residue 22434. -/
theorem bounds_15_22434 : exactInterval 15 22434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22434 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22434) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22434 : oddCount 22434 15 = 8 ∧ acceleratedOrbit 15 22434 = 4495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22434 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22434) = 3 ^ 8 * m + 4495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22434.1, data_15_22434.2]

/-- Complete interval computation for depth 15, residue 22435. -/
theorem bounds_15_22435 : exactInterval 15 22435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22435 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22435) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22435 : oddCount 22435 15 = 8 ∧ acceleratedOrbit 15 22435 = 4495 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22435 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22435) = 3 ^ 8 * m + 4495 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22435.1, data_15_22435.2]

/-- Complete interval computation for depth 15, residue 22436. -/
theorem bounds_15_22436 : exactInterval 15 22436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22436 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22436) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22436 : oddCount 22436 15 = 10 ∧ acceleratedOrbit 15 22436 = 40445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22436 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22436) = 3 ^ 10 * m + 40445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22436.1, data_15_22436.2]

/-- Complete interval computation for depth 15, residue 22437. -/
theorem bounds_15_22437 : exactInterval 15 22437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22437 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22437) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22437 : oddCount 22437 15 = 10 ∧ acceleratedOrbit 15 22437 = 40445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22437 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22437) = 3 ^ 10 * m + 40445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22437.1, data_15_22437.2]

/-- Complete interval computation for depth 15, residue 22438. -/
theorem bounds_15_22438 : exactInterval 15 22438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22438 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22438) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22438 : oddCount 22438 15 = 10 ∧ acceleratedOrbit 15 22438 = 40445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22438 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22438) = 3 ^ 10 * m + 40445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22438.1, data_15_22438.2]

/-- Complete interval computation for depth 15, residue 22439. -/
theorem bounds_15_22439 : exactInterval 15 22439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22439 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22439) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22439 : oddCount 22439 15 = 10 ∧ acceleratedOrbit 15 22439 = 40439 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22439 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22439) = 3 ^ 10 * m + 40439 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22439.1, data_15_22439.2]

/-- Complete interval computation for depth 15, residue 22440. -/
theorem bounds_15_22440 : exactInterval 15 22440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22440 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22440) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22440 : oddCount 22440 15 = 5 ∧ acceleratedOrbit 15 22440 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22440 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22440) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22440.1, data_15_22440.2]

/-- Complete interval computation for depth 15, residue 22441. -/
theorem bounds_15_22441 : exactInterval 15 22441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22441 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22441) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22441 : oddCount 22441 15 = 11 ∧ acceleratedOrbit 15 22441 = 121328 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22441 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22441) = 3 ^ 11 * m + 121328 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22441.1, data_15_22441.2]

/-- Complete interval computation for depth 15, residue 22442. -/
theorem bounds_15_22442 : exactInterval 15 22442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22442 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22442) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22442 : oddCount 22442 15 = 5 ∧ acceleratedOrbit 15 22442 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22442 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22442) = 3 ^ 5 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22442.1, data_15_22442.2]

/-- Complete interval computation for depth 15, residue 22443. -/
theorem bounds_15_22443 : exactInterval 15 22443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22443 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22443) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22443 : oddCount 22443 15 = 9 ∧ acceleratedOrbit 15 22443 = 13483 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22443 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22443) = 3 ^ 9 * m + 13483 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22443.1, data_15_22443.2]

/-- Complete interval computation for depth 15, residue 22444. -/
theorem bounds_15_22444 : exactInterval 15 22444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22444 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22444) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22444 : oddCount 22444 15 = 10 ∧ acceleratedOrbit 15 22444 = 40459 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22444 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22444) = 3 ^ 10 * m + 40459 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22444.1, data_15_22444.2]

/-- Complete interval computation for depth 15, residue 22445. -/
theorem bounds_15_22445 : exactInterval 15 22445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22445 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22445) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22445 : oddCount 22445 15 = 10 ∧ acceleratedOrbit 15 22445 = 40459 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22445 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22445) = 3 ^ 10 * m + 40459 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22445.1, data_15_22445.2]

end Collatz.Research.PassageAtlas.Batch0685
