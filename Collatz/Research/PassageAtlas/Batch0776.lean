import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0776

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 25395. -/
theorem bounds_15_25395 : exactInterval 15 25395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25395 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25395) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25395 : oddCount 25395 15 = 7 ∧ acceleratedOrbit 15 25395 = 1696 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25395 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25395) = 3 ^ 7 * m + 1696 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25395.1, data_15_25395.2]

/-- Complete interval computation for depth 15, residue 25396. -/
theorem bounds_15_25396 : exactInterval 15 25396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25396 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25396) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25396 : oddCount 25396 15 = 7 ∧ acceleratedOrbit 15 25396 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25396 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25396) = 3 ^ 7 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25396.1, data_15_25396.2]

/-- Complete interval computation for depth 15, residue 25397. -/
theorem bounds_15_25397 : exactInterval 15 25397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25397 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25397) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25397 : oddCount 25397 15 = 7 ∧ acceleratedOrbit 15 25397 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25397 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25397) = 3 ^ 7 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25397.1, data_15_25397.2]

/-- Complete interval computation for depth 15, residue 25398. -/
theorem bounds_15_25398 : exactInterval 15 25398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25398 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25398) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25398 : oddCount 25398 15 = 8 ∧ acceleratedOrbit 15 25398 = 5086 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25398 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25398) = 3 ^ 8 * m + 5086 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25398.1, data_15_25398.2]

/-- Complete interval computation for depth 15, residue 25399. -/
theorem bounds_15_25399 : exactInterval 15 25399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25399 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25399) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25399 : oddCount 25399 15 = 8 ∧ acceleratedOrbit 15 25399 = 5086 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25399 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25399) = 3 ^ 8 * m + 5086 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25399.1, data_15_25399.2]

/-- Complete interval computation for depth 15, residue 25400. -/
theorem bounds_15_25400 : exactInterval 15 25400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25400 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25400) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25400 : oddCount 25400 15 = 10 ∧ acceleratedOrbit 15 25400 = 45791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25400 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25400) = 3 ^ 10 * m + 45791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25400.1, data_15_25400.2]

/-- Complete interval computation for depth 15, residue 25401. -/
theorem bounds_15_25401 : exactInterval 15 25401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25401 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25401) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25401 : oddCount 25401 15 = 8 ∧ acceleratedOrbit 15 25401 = 5087 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25401 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25401) = 3 ^ 8 * m + 5087 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25401.1, data_15_25401.2]

/-- Complete interval computation for depth 15, residue 25402. -/
theorem bounds_15_25402 : exactInterval 15 25402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25402 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25402) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25402 : oddCount 25402 15 = 10 ∧ acceleratedOrbit 15 25402 = 45791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25402 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25402) = 3 ^ 10 * m + 45791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25402.1, data_15_25402.2]

/-- Complete interval computation for depth 15, residue 25403. -/
theorem bounds_15_25403 : exactInterval 15 25403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25403 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25403) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25403 : oddCount 25403 15 = 7 ∧ acceleratedOrbit 15 25403 = 1696 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25403 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25403) = 3 ^ 7 * m + 1696 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25403.1, data_15_25403.2]

/-- Complete interval computation for depth 15, residue 25404. -/
theorem bounds_15_25404 : exactInterval 15 25404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25404 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25404) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25404 : oddCount 25404 15 = 10 ∧ acceleratedOrbit 15 25404 = 45791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25404 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25404) = 3 ^ 10 * m + 45791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25404.1, data_15_25404.2]

/-- Complete interval computation for depth 15, residue 25405. -/
theorem bounds_15_25405 : exactInterval 15 25405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25405 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25405) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25405 : oddCount 25405 15 = 10 ∧ acceleratedOrbit 15 25405 = 45791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25405 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25405) = 3 ^ 10 * m + 45791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25405.1, data_15_25405.2]

/-- Complete interval computation for depth 15, residue 25406. -/
theorem bounds_15_25406 : exactInterval 15 25406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25406 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25406) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25406 : oddCount 25406 15 = 10 ∧ acceleratedOrbit 15 25406 = 45787 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25406 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25406) = 3 ^ 10 * m + 45787 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25406.1, data_15_25406.2]

/-- Complete interval computation for depth 15, residue 25407. -/
theorem bounds_15_25407 : exactInterval 15 25407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25407 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25407) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25407 : oddCount 25407 15 = 10 ∧ acceleratedOrbit 15 25407 = 45787 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25407 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25407) = 3 ^ 10 * m + 45787 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25407.1, data_15_25407.2]

/-- Complete interval computation for depth 15, residue 25408. -/
theorem bounds_15_25408 : exactInterval 15 25408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25408 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25408) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25408 : oddCount 25408 15 = 2 ∧ acceleratedOrbit 15 25408 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25408 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25408) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25408.1, data_15_25408.2]

/-- Complete interval computation for depth 15, residue 25409. -/
theorem bounds_15_25409 : exactInterval 15 25409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25409 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25409) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25409 : oddCount 25409 15 = 7 ∧ acceleratedOrbit 15 25409 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25409 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25409) = 3 ^ 7 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25409.1, data_15_25409.2]

/-- Complete interval computation for depth 15, residue 25410. -/
theorem bounds_15_25410 : exactInterval 15 25410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25410 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25410) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25410 : oddCount 25410 15 = 9 ∧ acceleratedOrbit 15 25410 = 15268 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25410 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25410) = 3 ^ 9 * m + 15268 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25410.1, data_15_25410.2]

/-- Complete interval computation for depth 15, residue 25411. -/
theorem bounds_15_25411 : exactInterval 15 25411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25411 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25411) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25411 : oddCount 25411 15 = 9 ∧ acceleratedOrbit 15 25411 = 15268 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25411 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25411) = 3 ^ 9 * m + 15268 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25411.1, data_15_25411.2]

/-- Complete interval computation for depth 15, residue 25412. -/
theorem bounds_15_25412 : exactInterval 15 25412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25412 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25412) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25412 : oddCount 25412 15 = 8 ∧ acceleratedOrbit 15 25412 = 5093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25412 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25412) = 3 ^ 8 * m + 5093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25412.1, data_15_25412.2]

/-- Complete interval computation for depth 15, residue 25413. -/
theorem bounds_15_25413 : exactInterval 15 25413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25413 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25413) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25413 : oddCount 25413 15 = 8 ∧ acceleratedOrbit 15 25413 = 5093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25413 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25413) = 3 ^ 8 * m + 5093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25413.1, data_15_25413.2]

/-- Complete interval computation for depth 15, residue 25414. -/
theorem bounds_15_25414 : exactInterval 15 25414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25414 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25414) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25414 : oddCount 25414 15 = 8 ∧ acceleratedOrbit 15 25414 = 5093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25414 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25414) = 3 ^ 8 * m + 5093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25414.1, data_15_25414.2]

/-- Complete interval computation for depth 15, residue 25415. -/
theorem bounds_15_25415 : exactInterval 15 25415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25415 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25415) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25415 : oddCount 25415 15 = 10 ∧ acceleratedOrbit 15 25415 = 45802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25415 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25415) = 3 ^ 10 * m + 45802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25415.1, data_15_25415.2]

/-- Complete interval computation for depth 15, residue 25416. -/
theorem bounds_15_25416 : exactInterval 15 25416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25416 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25416) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25416 : oddCount 25416 15 = 8 ∧ acceleratedOrbit 15 25416 = 5093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25416 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25416) = 3 ^ 8 * m + 5093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25416.1, data_15_25416.2]

/-- Complete interval computation for depth 15, residue 25417. -/
theorem bounds_15_25417 : exactInterval 15 25417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25417 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25417) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25417 : oddCount 25417 15 = 6 ∧ acceleratedOrbit 15 25417 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25417 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25417) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25417.1, data_15_25417.2]

/-- Complete interval computation for depth 15, residue 25418. -/
theorem bounds_15_25418 : exactInterval 15 25418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25418 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25418) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25418 : oddCount 25418 15 = 8 ∧ acceleratedOrbit 15 25418 = 5093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25418 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25418) = 3 ^ 8 * m + 5093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25418.1, data_15_25418.2]

/-- Complete interval computation for depth 15, residue 25419. -/
theorem bounds_15_25419 : exactInterval 15 25419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25419 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25419) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25419 : oddCount 25419 15 = 8 ∧ acceleratedOrbit 15 25419 = 5093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25419 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25419) = 3 ^ 8 * m + 5093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25419.1, data_15_25419.2]

/-- Complete interval computation for depth 15, residue 25420. -/
theorem bounds_15_25420 : exactInterval 15 25420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25420 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25420) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25420 : oddCount 25420 15 = 8 ∧ acceleratedOrbit 15 25420 = 5093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25420 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25420) = 3 ^ 8 * m + 5093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25420.1, data_15_25420.2]

/-- Complete interval computation for depth 15, residue 25421. -/
theorem bounds_15_25421 : exactInterval 15 25421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25421 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25421) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25421 : oddCount 25421 15 = 8 ∧ acceleratedOrbit 15 25421 = 5093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25421 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25421) = 3 ^ 8 * m + 5093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25421.1, data_15_25421.2]

/-- Complete interval computation for depth 15, residue 25422. -/
theorem bounds_15_25422 : exactInterval 15 25422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25422 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25422) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25422 : oddCount 25422 15 = 7 ∧ acceleratedOrbit 15 25422 = 1697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25422 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25422) = 3 ^ 7 * m + 1697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25422.1, data_15_25422.2]

/-- Complete interval computation for depth 15, residue 25423. -/
theorem bounds_15_25423 : exactInterval 15 25423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25423 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25423) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25423 : oddCount 25423 15 = 7 ∧ acceleratedOrbit 15 25423 = 1697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25423 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25423) = 3 ^ 7 * m + 1697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25423.1, data_15_25423.2]

/-- Complete interval computation for depth 15, residue 25424. -/
theorem bounds_15_25424 : exactInterval 15 25424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25424 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25424) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25424 : oddCount 25424 15 = 2 ∧ acceleratedOrbit 15 25424 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25424 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25424) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25424.1, data_15_25424.2]

/-- Complete interval computation for depth 15, residue 25425. -/
theorem bounds_15_25425 : exactInterval 15 25425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25425 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25425) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25425 : oddCount 25425 15 = 9 ∧ acceleratedOrbit 15 25425 = 15275 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25425 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25425) = 3 ^ 9 * m + 15275 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25425.1, data_15_25425.2]

/-- Complete interval computation for depth 15, residue 25426. -/
theorem bounds_15_25426 : exactInterval 15 25426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25426 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25426) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25426 : oddCount 25426 15 = 9 ∧ acceleratedOrbit 15 25426 = 15275 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25426 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25426) = 3 ^ 9 * m + 15275 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25426.1, data_15_25426.2]

end Collatz.Research.PassageAtlas.Batch0776
