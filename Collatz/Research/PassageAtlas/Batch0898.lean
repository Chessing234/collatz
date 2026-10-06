import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0898

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 29392. -/
theorem bounds_15_29392 : exactInterval 15 29392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29392 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29392) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29392 : oddCount 29392 15 = 4 ∧ acceleratedOrbit 15 29392 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29392 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29392) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29392.1, data_15_29392.2]

/-- Complete interval computation for depth 15, residue 29393. -/
theorem bounds_15_29393 : exactInterval 15 29393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29393 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29393) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29393 : oddCount 29393 15 = 5 ∧ acceleratedOrbit 15 29393 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29393 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29393) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29393.1, data_15_29393.2]

/-- Complete interval computation for depth 15, residue 29394. -/
theorem bounds_15_29394 : exactInterval 15 29394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29394 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29394) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29394 : oddCount 29394 15 = 5 ∧ acceleratedOrbit 15 29394 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29394 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29394) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29394.1, data_15_29394.2]

/-- Complete interval computation for depth 15, residue 29395. -/
theorem bounds_15_29395 : exactInterval 15 29395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29395 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29395) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29395 : oddCount 29395 15 = 5 ∧ acceleratedOrbit 15 29395 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29395 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29395) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29395.1, data_15_29395.2]

/-- Complete interval computation for depth 15, residue 29396. -/
theorem bounds_15_29396 : exactInterval 15 29396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29396 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29396) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29396 : oddCount 29396 15 = 4 ∧ acceleratedOrbit 15 29396 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29396 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29396) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29396.1, data_15_29396.2]

/-- Complete interval computation for depth 15, residue 29397. -/
theorem bounds_15_29397 : exactInterval 15 29397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29397 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29397) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29397 : oddCount 29397 15 = 4 ∧ acceleratedOrbit 15 29397 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29397 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29397) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29397.1, data_15_29397.2]

/-- Complete interval computation for depth 15, residue 29398. -/
theorem bounds_15_29398 : exactInterval 15 29398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29398 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29398) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29398 : oddCount 29398 15 = 8 ∧ acceleratedOrbit 15 29398 = 5888 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29398 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29398) = 3 ^ 8 * m + 5888 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29398.1, data_15_29398.2]

/-- Complete interval computation for depth 15, residue 29399. -/
theorem bounds_15_29399 : exactInterval 15 29399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29399 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29399) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29399 : oddCount 29399 15 = 8 ∧ acceleratedOrbit 15 29399 = 5888 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29399 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29399) = 3 ^ 8 * m + 5888 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29399.1, data_15_29399.2]

/-- Complete interval computation for depth 15, residue 29400. -/
theorem bounds_15_29400 : exactInterval 15 29400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29400 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29400) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29400 : oddCount 29400 15 = 7 ∧ acceleratedOrbit 15 29400 = 1963 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29400 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29400) = 3 ^ 7 * m + 1963 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29400.1, data_15_29400.2]

/-- Complete interval computation for depth 15, residue 29401. -/
theorem bounds_15_29401 : exactInterval 15 29401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29401 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29401) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29401 : oddCount 29401 15 = 7 ∧ acceleratedOrbit 15 29401 = 1964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29401 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29401) = 3 ^ 7 * m + 1964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29401.1, data_15_29401.2]

/-- Complete interval computation for depth 15, residue 29402. -/
theorem bounds_15_29402 : exactInterval 15 29402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29402 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29402) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29402 : oddCount 29402 15 = 7 ∧ acceleratedOrbit 15 29402 = 1963 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29402 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29402) = 3 ^ 7 * m + 1963 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29402.1, data_15_29402.2]

/-- Complete interval computation for depth 15, residue 29403. -/
theorem bounds_15_29403 : exactInterval 15 29403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29403 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29403) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29403 : oddCount 29403 15 = 9 ∧ acceleratedOrbit 15 29403 = 17663 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29403 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29403) = 3 ^ 9 * m + 17663 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29403.1, data_15_29403.2]

/-- Complete interval computation for depth 15, residue 29404. -/
theorem bounds_15_29404 : exactInterval 15 29404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29404 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29404) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29404 : oddCount 29404 15 = 7 ∧ acceleratedOrbit 15 29404 = 1963 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29404 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29404) = 3 ^ 7 * m + 1963 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29404.1, data_15_29404.2]

/-- Complete interval computation for depth 15, residue 29405. -/
theorem bounds_15_29405 : exactInterval 15 29405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29405 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29405) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29405 : oddCount 29405 15 = 7 ∧ acceleratedOrbit 15 29405 = 1963 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29405 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29405) = 3 ^ 7 * m + 1963 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29405.1, data_15_29405.2]

/-- Complete interval computation for depth 15, residue 29406. -/
theorem bounds_15_29406 : exactInterval 15 29406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29406 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29406) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29406 : oddCount 29406 15 = 7 ∧ acceleratedOrbit 15 29406 = 1963 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29406 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29406) = 3 ^ 7 * m + 1963 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29406.1, data_15_29406.2]

/-- Complete interval computation for depth 15, residue 29407. -/
theorem bounds_15_29407 : exactInterval 15 29407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29407 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29407) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29407 : oddCount 29407 15 = 7 ∧ acceleratedOrbit 15 29407 = 1963 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29407 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29407) = 3 ^ 7 * m + 1963 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29407.1, data_15_29407.2]

/-- Complete interval computation for depth 15, residue 29408. -/
theorem bounds_15_29408 : exactInterval 15 29408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29408 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29408) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29408 : oddCount 29408 15 = 4 ∧ acceleratedOrbit 15 29408 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29408 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29408) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29408.1, data_15_29408.2]

/-- Complete interval computation for depth 15, residue 29409. -/
theorem bounds_15_29409 : exactInterval 15 29409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29409 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29409) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29409 : oddCount 29409 15 = 12 ∧ acceleratedOrbit 15 29409 = 477008 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29409 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29409) = 3 ^ 12 * m + 477008 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29409.1, data_15_29409.2]

/-- Complete interval computation for depth 15, residue 29410. -/
theorem bounds_15_29410 : exactInterval 15 29410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29410 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29410) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29410 : oddCount 29410 15 = 4 ∧ acceleratedOrbit 15 29410 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29410 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29410) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29410.1, data_15_29410.2]

/-- Complete interval computation for depth 15, residue 29411. -/
theorem bounds_15_29411 : exactInterval 15 29411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29411 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29411) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29411 : oddCount 29411 15 = 4 ∧ acceleratedOrbit 15 29411 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29411 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29411) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29411.1, data_15_29411.2]

/-- Complete interval computation for depth 15, residue 29412. -/
theorem bounds_15_29412 : exactInterval 15 29412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29412 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29412) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29412 : oddCount 29412 15 = 7 ∧ acceleratedOrbit 15 29412 = 1964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29412 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29412) = 3 ^ 7 * m + 1964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29412.1, data_15_29412.2]

/-- Complete interval computation for depth 15, residue 29413. -/
theorem bounds_15_29413 : exactInterval 15 29413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29413 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29413) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29413 : oddCount 29413 15 = 7 ∧ acceleratedOrbit 15 29413 = 1964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29413 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29413) = 3 ^ 7 * m + 1964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29413.1, data_15_29413.2]

/-- Complete interval computation for depth 15, residue 29414. -/
theorem bounds_15_29414 : exactInterval 15 29414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29414 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29414) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29414 : oddCount 29414 15 = 7 ∧ acceleratedOrbit 15 29414 = 1964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29414 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29414) = 3 ^ 7 * m + 1964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29414.1, data_15_29414.2]

/-- Complete interval computation for depth 15, residue 29415. -/
theorem bounds_15_29415 : exactInterval 15 29415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29415 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29415) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29415 : oddCount 29415 15 = 11 ∧ acceleratedOrbit 15 29415 = 159029 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29415 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29415) = 3 ^ 11 * m + 159029 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29415.1, data_15_29415.2]

/-- Complete interval computation for depth 15, residue 29416. -/
theorem bounds_15_29416 : exactInterval 15 29416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29416 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29416) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29416 : oddCount 29416 15 = 4 ∧ acceleratedOrbit 15 29416 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29416 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29416) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29416.1, data_15_29416.2]

/-- Complete interval computation for depth 15, residue 29417. -/
theorem bounds_15_29417 : exactInterval 15 29417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29417 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29417) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29417 : oddCount 29417 15 = 11 ∧ acceleratedOrbit 15 29417 = 159043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29417 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29417) = 3 ^ 11 * m + 159043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29417.1, data_15_29417.2]

/-- Complete interval computation for depth 15, residue 29418. -/
theorem bounds_15_29418 : exactInterval 15 29418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29418 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29418) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29418 : oddCount 29418 15 = 4 ∧ acceleratedOrbit 15 29418 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29418 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29418) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29418.1, data_15_29418.2]

/-- Complete interval computation for depth 15, residue 29419. -/
theorem bounds_15_29419 : exactInterval 15 29419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29419 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29419) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29419 : oddCount 29419 15 = 8 ∧ acceleratedOrbit 15 29419 = 5891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29419 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29419) = 3 ^ 8 * m + 5891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29419.1, data_15_29419.2]

/-- Complete interval computation for depth 15, residue 29420. -/
theorem bounds_15_29420 : exactInterval 15 29420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29420 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29420) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29420 : oddCount 29420 15 = 9 ∧ acceleratedOrbit 15 29420 = 17678 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29420 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29420) = 3 ^ 9 * m + 17678 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29420.1, data_15_29420.2]

/-- Complete interval computation for depth 15, residue 29421. -/
theorem bounds_15_29421 : exactInterval 15 29421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29421 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29421) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29421 : oddCount 29421 15 = 9 ∧ acceleratedOrbit 15 29421 = 17678 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29421 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29421) = 3 ^ 9 * m + 17678 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29421.1, data_15_29421.2]

/-- Complete interval computation for depth 15, residue 29422. -/
theorem bounds_15_29422 : exactInterval 15 29422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29422 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29422) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29422 : oddCount 29422 15 = 9 ∧ acceleratedOrbit 15 29422 = 17678 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29422 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29422) = 3 ^ 9 * m + 17678 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29422.1, data_15_29422.2]

/-- Complete interval computation for depth 15, residue 29423. -/
theorem bounds_15_29423 : exactInterval 15 29423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29423 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29423) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29423 : oddCount 29423 15 = 12 ∧ acceleratedOrbit 15 29423 = 477211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29423 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29423) = 3 ^ 12 * m + 477211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29423.1, data_15_29423.2]

/-- Complete interval computation for depth 15, residue 29424. -/
theorem bounds_15_29424 : exactInterval 15 29424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29424 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29424) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29424 : oddCount 29424 15 = 6 ∧ acceleratedOrbit 15 29424 = 655 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29424 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29424) = 3 ^ 6 * m + 655 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29424.1, data_15_29424.2]

end Collatz.Research.PassageAtlas.Batch0898
