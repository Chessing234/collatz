import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0746

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 24412. -/
theorem bounds_15_24412 : exactInterval 15 24412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24412 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24412) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24412 : oddCount 24412 15 = 7 ∧ acceleratedOrbit 15 24412 = 1630 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24412 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24412) = 3 ^ 7 * m + 1630 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24412.1, data_15_24412.2]

/-- Complete interval computation for depth 15, residue 24413. -/
theorem bounds_15_24413 : exactInterval 15 24413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24413 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24413) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24413 : oddCount 24413 15 = 7 ∧ acceleratedOrbit 15 24413 = 1630 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24413 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24413) = 3 ^ 7 * m + 1630 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24413.1, data_15_24413.2]

/-- Complete interval computation for depth 15, residue 24414. -/
theorem bounds_15_24414 : exactInterval 15 24414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24414 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24414) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24414 : oddCount 24414 15 = 7 ∧ acceleratedOrbit 15 24414 = 1630 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24414 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24414) = 3 ^ 7 * m + 1630 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24414.1, data_15_24414.2]

/-- Complete interval computation for depth 15, residue 24415. -/
theorem bounds_15_24415 : exactInterval 15 24415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24415 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24415) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24415 : oddCount 24415 15 = 7 ∧ acceleratedOrbit 15 24415 = 1630 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24415 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24415) = 3 ^ 7 * m + 1630 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24415.1, data_15_24415.2]

/-- Complete interval computation for depth 15, residue 24416. -/
theorem bounds_15_24416 : exactInterval 15 24416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24416 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24416) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24416 : oddCount 24416 15 = 7 ∧ acceleratedOrbit 15 24416 = 1633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24416 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24416) = 3 ^ 7 * m + 1633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24416.1, data_15_24416.2]

/-- Complete interval computation for depth 15, residue 24417. -/
theorem bounds_15_24417 : exactInterval 15 24417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24417 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24417) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24417 : oddCount 24417 15 = 9 ∧ acceleratedOrbit 15 24417 = 14669 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24417 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24417) = 3 ^ 9 * m + 14669 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24417.1, data_15_24417.2]

/-- Complete interval computation for depth 15, residue 24418. -/
theorem bounds_15_24418 : exactInterval 15 24418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24418 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24418) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24418 : oddCount 24418 15 = 5 ∧ acceleratedOrbit 15 24418 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24418 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24418) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24418.1, data_15_24418.2]

/-- Complete interval computation for depth 15, residue 24419. -/
theorem bounds_15_24419 : exactInterval 15 24419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24419 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24419) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24419 : oddCount 24419 15 = 5 ∧ acceleratedOrbit 15 24419 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24419 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24419) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24419.1, data_15_24419.2]

/-- Complete interval computation for depth 15, residue 24420. -/
theorem bounds_15_24420 : exactInterval 15 24420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24420 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24420) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24420 : oddCount 24420 15 = 5 ∧ acceleratedOrbit 15 24420 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24420 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24420) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24420.1, data_15_24420.2]

/-- Complete interval computation for depth 15, residue 24421. -/
theorem bounds_15_24421 : exactInterval 15 24421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24421 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24421) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24421 : oddCount 24421 15 = 5 ∧ acceleratedOrbit 15 24421 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24421 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24421) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24421.1, data_15_24421.2]

/-- Complete interval computation for depth 15, residue 24422. -/
theorem bounds_15_24422 : exactInterval 15 24422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24422 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24422) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24422 : oddCount 24422 15 = 5 ∧ acceleratedOrbit 15 24422 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24422 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24422) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24422.1, data_15_24422.2]

/-- Complete interval computation for depth 15, residue 24423. -/
theorem bounds_15_24423 : exactInterval 15 24423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24423 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24423) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24423 : oddCount 24423 15 = 11 ∧ acceleratedOrbit 15 24423 = 132040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24423 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24423) = 3 ^ 11 * m + 132040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24423.1, data_15_24423.2]

/-- Complete interval computation for depth 15, residue 24424. -/
theorem bounds_15_24424 : exactInterval 15 24424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24424 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24424) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24424 : oddCount 24424 15 = 7 ∧ acceleratedOrbit 15 24424 = 1633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24424 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24424) = 3 ^ 7 * m + 1633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24424.1, data_15_24424.2]

/-- Complete interval computation for depth 15, residue 24425. -/
theorem bounds_15_24425 : exactInterval 15 24425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24425 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24425) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24425 : oddCount 24425 15 = 9 ∧ acceleratedOrbit 15 24425 = 14674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24425 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24425) = 3 ^ 9 * m + 14674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24425.1, data_15_24425.2]

/-- Complete interval computation for depth 15, residue 24426. -/
theorem bounds_15_24426 : exactInterval 15 24426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24426 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24426) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24426 : oddCount 24426 15 = 7 ∧ acceleratedOrbit 15 24426 = 1633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24426 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24426) = 3 ^ 7 * m + 1633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24426.1, data_15_24426.2]

/-- Complete interval computation for depth 15, residue 24427. -/
theorem bounds_15_24427 : exactInterval 15 24427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24427 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24427) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24427 : oddCount 24427 15 = 7 ∧ acceleratedOrbit 15 24427 = 1631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24427 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24427) = 3 ^ 7 * m + 1631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24427.1, data_15_24427.2]

/-- Complete interval computation for depth 15, residue 24428. -/
theorem bounds_15_24428 : exactInterval 15 24428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24428 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24428) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24428 : oddCount 24428 15 = 7 ∧ acceleratedOrbit 15 24428 = 1631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24428 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24428) = 3 ^ 7 * m + 1631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24428.1, data_15_24428.2]

/-- Complete interval computation for depth 15, residue 24429. -/
theorem bounds_15_24429 : exactInterval 15 24429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24429 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24429) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24429 : oddCount 24429 15 = 7 ∧ acceleratedOrbit 15 24429 = 1631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24429 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24429) = 3 ^ 7 * m + 1631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24429.1, data_15_24429.2]

/-- Complete interval computation for depth 15, residue 24430. -/
theorem bounds_15_24430 : exactInterval 15 24430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24430 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24430) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24430 : oddCount 24430 15 = 7 ∧ acceleratedOrbit 15 24430 = 1631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24430 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24430) = 3 ^ 7 * m + 1631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24430.1, data_15_24430.2]

/-- Complete interval computation for depth 15, residue 24431. -/
theorem bounds_15_24431 : exactInterval 15 24431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24431 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24431) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24431 : oddCount 24431 15 = 8 ∧ acceleratedOrbit 15 24431 = 4892 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24431 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24431) = 3 ^ 8 * m + 4892 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24431.1, data_15_24431.2]

/-- Complete interval computation for depth 15, residue 24432. -/
theorem bounds_15_24432 : exactInterval 15 24432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24432 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24432) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24432 : oddCount 24432 15 = 7 ∧ acceleratedOrbit 15 24432 = 1633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24432 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24432) = 3 ^ 7 * m + 1633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24432.1, data_15_24432.2]

/-- Complete interval computation for depth 15, residue 24433. -/
theorem bounds_15_24433 : exactInterval 15 24433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24433 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24433) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24433 : oddCount 24433 15 = 7 ∧ acceleratedOrbit 15 24433 = 1633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24433 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24433) = 3 ^ 7 * m + 1633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24433.1, data_15_24433.2]

/-- Complete interval computation for depth 15, residue 24434. -/
theorem bounds_15_24434 : exactInterval 15 24434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24434 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24434) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24434 : oddCount 24434 15 = 6 ∧ acceleratedOrbit 15 24434 = 544 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24434 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24434) = 3 ^ 6 * m + 544 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24434.1, data_15_24434.2]

/-- Complete interval computation for depth 15, residue 24435. -/
theorem bounds_15_24435 : exactInterval 15 24435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24435 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24435) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24435 : oddCount 24435 15 = 6 ∧ acceleratedOrbit 15 24435 = 544 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24435 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24435) = 3 ^ 6 * m + 544 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24435.1, data_15_24435.2]

/-- Complete interval computation for depth 15, residue 24436. -/
theorem bounds_15_24436 : exactInterval 15 24436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24436 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24436) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24436 : oddCount 24436 15 = 7 ∧ acceleratedOrbit 15 24436 = 1633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24436 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24436) = 3 ^ 7 * m + 1633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24436.1, data_15_24436.2]

/-- Complete interval computation for depth 15, residue 24437. -/
theorem bounds_15_24437 : exactInterval 15 24437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24437 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24437) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24437 : oddCount 24437 15 = 7 ∧ acceleratedOrbit 15 24437 = 1633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24437 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24437) = 3 ^ 7 * m + 1633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24437.1, data_15_24437.2]

/-- Complete interval computation for depth 15, residue 24438. -/
theorem bounds_15_24438 : exactInterval 15 24438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24438 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24438) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24438 : oddCount 24438 15 = 6 ∧ acceleratedOrbit 15 24438 = 544 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24438 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24438) = 3 ^ 6 * m + 544 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24438.1, data_15_24438.2]

/-- Complete interval computation for depth 15, residue 24439. -/
theorem bounds_15_24439 : exactInterval 15 24439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24439 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24439) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24439 : oddCount 24439 15 = 6 ∧ acceleratedOrbit 15 24439 = 544 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24439 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24439) = 3 ^ 6 * m + 544 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24439.1, data_15_24439.2]

/-- Complete interval computation for depth 15, residue 24440. -/
theorem bounds_15_24440 : exactInterval 15 24440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24440 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24440) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24440 : oddCount 24440 15 = 9 ∧ acceleratedOrbit 15 24440 = 14687 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24440 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24440) = 3 ^ 9 * m + 14687 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24440.1, data_15_24440.2]

/-- Complete interval computation for depth 15, residue 24441. -/
theorem bounds_15_24441 : exactInterval 15 24441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24441 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24441) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24441 : oddCount 24441 15 = 9 ∧ acceleratedOrbit 15 24441 = 14683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24441 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24441) = 3 ^ 9 * m + 14683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24441.1, data_15_24441.2]

/-- Complete interval computation for depth 15, residue 24442. -/
theorem bounds_15_24442 : exactInterval 15 24442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24442 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24442) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24442 : oddCount 24442 15 = 9 ∧ acceleratedOrbit 15 24442 = 14687 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24442 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24442) = 3 ^ 9 * m + 14687 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24442.1, data_15_24442.2]

/-- Complete interval computation for depth 15, residue 24443. -/
theorem bounds_15_24443 : exactInterval 15 24443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24443 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24443) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24443 : oddCount 24443 15 = 8 ∧ acceleratedOrbit 15 24443 = 4895 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24443 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24443) = 3 ^ 8 * m + 4895 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24443.1, data_15_24443.2]

end Collatz.Research.PassageAtlas.Batch0746
