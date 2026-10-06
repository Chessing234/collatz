import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0715

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 23396. -/
theorem bounds_15_23396 : exactInterval 15 23396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23396 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23396) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23396 : oddCount 23396 15 = 7 ∧ acceleratedOrbit 15 23396 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23396 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23396) = 3 ^ 7 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23396.1, data_15_23396.2]

/-- Complete interval computation for depth 15, residue 23397. -/
theorem bounds_15_23397 : exactInterval 15 23397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23397 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23397) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23397 : oddCount 23397 15 = 7 ∧ acceleratedOrbit 15 23397 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23397 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23397) = 3 ^ 7 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23397.1, data_15_23397.2]

/-- Complete interval computation for depth 15, residue 23398. -/
theorem bounds_15_23398 : exactInterval 15 23398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23398 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23398) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23398 : oddCount 23398 15 = 7 ∧ acceleratedOrbit 15 23398 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23398 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23398) = 3 ^ 7 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23398.1, data_15_23398.2]

/-- Complete interval computation for depth 15, residue 23399. -/
theorem bounds_15_23399 : exactInterval 15 23399 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23399 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23399) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23399 : oddCount 23399 15 = 9 ∧ acceleratedOrbit 15 23399 = 14056 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23399 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23399) = 3 ^ 9 * m + 14056 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23399.1, data_15_23399.2]

/-- Complete interval computation for depth 15, residue 23400. -/
theorem bounds_15_23400 : exactInterval 15 23400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23400 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23400) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23400 : oddCount 23400 15 = 7 ∧ acceleratedOrbit 15 23400 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23400 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23400) = 3 ^ 7 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23400.1, data_15_23400.2]

/-- Complete interval computation for depth 15, residue 23401. -/
theorem bounds_15_23401 : exactInterval 15 23401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23401 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23401) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23401 : oddCount 23401 15 = 7 ∧ acceleratedOrbit 15 23401 = 1562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23401 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23401) = 3 ^ 7 * m + 1562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23401.1, data_15_23401.2]

/-- Complete interval computation for depth 15, residue 23402. -/
theorem bounds_15_23402 : exactInterval 15 23402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23402 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23402) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23402 : oddCount 23402 15 = 7 ∧ acceleratedOrbit 15 23402 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23402 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23402) = 3 ^ 7 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23402.1, data_15_23402.2]

/-- Complete interval computation for depth 15, residue 23403. -/
theorem bounds_15_23403 : exactInterval 15 23403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23403 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23403) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23403 : oddCount 23403 15 = 8 ∧ acceleratedOrbit 15 23403 = 4688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23403 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23403) = 3 ^ 8 * m + 4688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23403.1, data_15_23403.2]

/-- Complete interval computation for depth 15, residue 23404. -/
theorem bounds_15_23404 : exactInterval 15 23404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23404 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23404) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23404 : oddCount 23404 15 = 8 ∧ acceleratedOrbit 15 23404 = 4688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23404 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23404) = 3 ^ 8 * m + 4688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23404.1, data_15_23404.2]

/-- Complete interval computation for depth 15, residue 23405. -/
theorem bounds_15_23405 : exactInterval 15 23405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23405 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23405) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23405 : oddCount 23405 15 = 8 ∧ acceleratedOrbit 15 23405 = 4688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23405 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23405) = 3 ^ 8 * m + 4688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23405.1, data_15_23405.2]

/-- Complete interval computation for depth 15, residue 23406. -/
theorem bounds_15_23406 : exactInterval 15 23406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23406 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23406) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23406 : oddCount 23406 15 = 8 ∧ acceleratedOrbit 15 23406 = 4688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23406 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23406) = 3 ^ 8 * m + 4688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23406.1, data_15_23406.2]

/-- Complete interval computation for depth 15, residue 23407. -/
theorem bounds_15_23407 : exactInterval 15 23407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23407 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23407) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23407 : oddCount 23407 15 = 8 ∧ acceleratedOrbit 15 23407 = 4687 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23407 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23407) = 3 ^ 8 * m + 4687 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23407.1, data_15_23407.2]

/-- Complete interval computation for depth 15, residue 23408. -/
theorem bounds_15_23408 : exactInterval 15 23408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23408 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23408) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23408 : oddCount 23408 15 = 7 ∧ acceleratedOrbit 15 23408 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23408 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23408) = 3 ^ 7 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23408.1, data_15_23408.2]

/-- Complete interval computation for depth 15, residue 23409. -/
theorem bounds_15_23409 : exactInterval 15 23409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23409 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23409) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23409 : oddCount 23409 15 = 7 ∧ acceleratedOrbit 15 23409 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23409 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23409) = 3 ^ 7 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23409.1, data_15_23409.2]

/-- Complete interval computation for depth 15, residue 23410. -/
theorem bounds_15_23410 : exactInterval 15 23410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23410 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23410) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23410 : oddCount 23410 15 = 7 ∧ acceleratedOrbit 15 23410 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23410 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23410) = 3 ^ 7 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23410.1, data_15_23410.2]

/-- Complete interval computation for depth 15, residue 23411. -/
theorem bounds_15_23411 : exactInterval 15 23411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23411 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23411) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23411 : oddCount 23411 15 = 7 ∧ acceleratedOrbit 15 23411 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23411 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23411) = 3 ^ 7 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23411.1, data_15_23411.2]

/-- Complete interval computation for depth 15, residue 23412. -/
theorem bounds_15_23412 : exactInterval 15 23412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23412 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23412) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23412 : oddCount 23412 15 = 7 ∧ acceleratedOrbit 15 23412 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23412 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23412) = 3 ^ 7 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23412.1, data_15_23412.2]

/-- Complete interval computation for depth 15, residue 23413. -/
theorem bounds_15_23413 : exactInterval 15 23413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23413 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23413) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23413 : oddCount 23413 15 = 7 ∧ acceleratedOrbit 15 23413 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23413 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23413) = 3 ^ 7 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23413.1, data_15_23413.2]

/-- Complete interval computation for depth 15, residue 23414. -/
theorem bounds_15_23414 : exactInterval 15 23414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23414 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23414) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23414 : oddCount 23414 15 = 6 ∧ acceleratedOrbit 15 23414 = 521 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23414 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23414) = 3 ^ 6 * m + 521 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23414.1, data_15_23414.2]

/-- Complete interval computation for depth 15, residue 23415. -/
theorem bounds_15_23415 : exactInterval 15 23415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23415 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23415) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23415 : oddCount 23415 15 = 6 ∧ acceleratedOrbit 15 23415 = 521 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23415 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23415) = 3 ^ 6 * m + 521 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23415.1, data_15_23415.2]

/-- Complete interval computation for depth 15, residue 23416. -/
theorem bounds_15_23416 : exactInterval 15 23416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23416 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23416) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23416 : oddCount 23416 15 = 8 ∧ acceleratedOrbit 15 23416 = 4691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23416 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23416) = 3 ^ 8 * m + 4691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23416.1, data_15_23416.2]

/-- Complete interval computation for depth 15, residue 23417. -/
theorem bounds_15_23417 : exactInterval 15 23417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23417 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23417) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23417 : oddCount 23417 15 = 10 ∧ acceleratedOrbit 15 23417 = 42203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23417 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23417) = 3 ^ 10 * m + 42203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23417.1, data_15_23417.2]

/-- Complete interval computation for depth 15, residue 23418. -/
theorem bounds_15_23418 : exactInterval 15 23418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23418 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23418) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23418 : oddCount 23418 15 = 8 ∧ acceleratedOrbit 15 23418 = 4691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23418 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23418) = 3 ^ 8 * m + 4691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23418.1, data_15_23418.2]

/-- Complete interval computation for depth 15, residue 23419. -/
theorem bounds_15_23419 : exactInterval 15 23419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23419 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23419) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23419 : oddCount 23419 15 = 9 ∧ acceleratedOrbit 15 23419 = 14069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23419 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23419) = 3 ^ 9 * m + 14069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23419.1, data_15_23419.2]

/-- Complete interval computation for depth 15, residue 23420. -/
theorem bounds_15_23420 : exactInterval 15 23420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23420 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23420) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23420 : oddCount 23420 15 = 8 ∧ acceleratedOrbit 15 23420 = 4691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23420 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23420) = 3 ^ 8 * m + 4691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23420.1, data_15_23420.2]

/-- Complete interval computation for depth 15, residue 23421. -/
theorem bounds_15_23421 : exactInterval 15 23421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23421 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23421) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23421 : oddCount 23421 15 = 8 ∧ acceleratedOrbit 15 23421 = 4691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23421 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23421) = 3 ^ 8 * m + 4691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23421.1, data_15_23421.2]

/-- Complete interval computation for depth 15, residue 23422. -/
theorem bounds_15_23422 : exactInterval 15 23422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23422 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23422) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23422 : oddCount 23422 15 = 10 ∧ acceleratedOrbit 15 23422 = 42211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23422 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23422) = 3 ^ 10 * m + 42211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23422.1, data_15_23422.2]

/-- Complete interval computation for depth 15, residue 23423. -/
theorem bounds_15_23423 : exactInterval 15 23423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23423 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23423) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23423 : oddCount 23423 15 = 10 ∧ acceleratedOrbit 15 23423 = 42211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23423 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23423) = 3 ^ 10 * m + 42211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23423.1, data_15_23423.2]

/-- Complete interval computation for depth 15, residue 23424. -/
theorem bounds_15_23424 : exactInterval 15 23424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23424 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23424) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23424 : oddCount 23424 15 = 5 ∧ acceleratedOrbit 15 23424 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23424 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23424) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23424.1, data_15_23424.2]

/-- Complete interval computation for depth 15, residue 23425. -/
theorem bounds_15_23425 : exactInterval 15 23425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23425 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23425) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23425 : oddCount 23425 15 = 10 ∧ acceleratedOrbit 15 23425 = 42221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23425 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23425) = 3 ^ 10 * m + 42221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23425.1, data_15_23425.2]

/-- Complete interval computation for depth 15, residue 23426. -/
theorem bounds_15_23426 : exactInterval 15 23426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23426 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23426) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23426 : oddCount 23426 15 = 8 ∧ acceleratedOrbit 15 23426 = 4693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23426 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23426) = 3 ^ 8 * m + 4693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23426.1, data_15_23426.2]

/-- Complete interval computation for depth 15, residue 23427. -/
theorem bounds_15_23427 : exactInterval 15 23427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23427 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23427) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23427 : oddCount 23427 15 = 8 ∧ acceleratedOrbit 15 23427 = 4693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23427 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23427) = 3 ^ 8 * m + 4693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23427.1, data_15_23427.2]

/-- Complete interval computation for depth 15, residue 23428. -/
theorem bounds_15_23428 : exactInterval 15 23428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23428 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23428) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23428 : oddCount 23428 15 = 8 ∧ acceleratedOrbit 15 23428 = 4693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23428 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23428) = 3 ^ 8 * m + 4693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23428.1, data_15_23428.2]

end Collatz.Research.PassageAtlas.Batch0715
