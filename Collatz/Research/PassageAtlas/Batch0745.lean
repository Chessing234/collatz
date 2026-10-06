import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0745

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 24379. -/
theorem bounds_15_24379 : exactInterval 15 24379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24379 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24379) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24379 : oddCount 24379 15 = 7 ∧ acceleratedOrbit 15 24379 = 1628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24379 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24379) = 3 ^ 7 * m + 1628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24379.1, data_15_24379.2]

/-- Complete interval computation for depth 15, residue 24380. -/
theorem bounds_15_24380 : exactInterval 15 24380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24380 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24380) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24380 : oddCount 24380 15 = 7 ∧ acceleratedOrbit 15 24380 = 1628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24380 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24380) = 3 ^ 7 * m + 1628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24380.1, data_15_24380.2]

/-- Complete interval computation for depth 15, residue 24381. -/
theorem bounds_15_24381 : exactInterval 15 24381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24381 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24381) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24381 : oddCount 24381 15 = 7 ∧ acceleratedOrbit 15 24381 = 1628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24381 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24381) = 3 ^ 7 * m + 1628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24381.1, data_15_24381.2]

/-- Complete interval computation for depth 15, residue 24382. -/
theorem bounds_15_24382 : exactInterval 15 24382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24382 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24382) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24382 : oddCount 24382 15 = 10 ∧ acceleratedOrbit 15 24382 = 43942 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24382 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24382) = 3 ^ 10 * m + 43942 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24382.1, data_15_24382.2]

/-- Complete interval computation for depth 15, residue 24383. -/
theorem bounds_15_24383 : exactInterval 15 24383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24383 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24383) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24383 : oddCount 24383 15 = 10 ∧ acceleratedOrbit 15 24383 = 43942 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24383 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24383) = 3 ^ 10 * m + 43942 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24383.1, data_15_24383.2]

/-- Complete interval computation for depth 15, residue 24384. -/
theorem bounds_15_24384 : exactInterval 15 24384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24384 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24384) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24384 : oddCount 24384 15 = 5 ∧ acceleratedOrbit 15 24384 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24384 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24384) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24384.1, data_15_24384.2]

/-- Complete interval computation for depth 15, residue 24385. -/
theorem bounds_15_24385 : exactInterval 15 24385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24385 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24385) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24385 : oddCount 24385 15 = 5 ∧ acceleratedOrbit 15 24385 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24385 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24385) = 3 ^ 5 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24385.1, data_15_24385.2]

/-- Complete interval computation for depth 15, residue 24386. -/
theorem bounds_15_24386 : exactInterval 15 24386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24386 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24386) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24386 : oddCount 24386 15 = 8 ∧ acceleratedOrbit 15 24386 = 4886 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24386 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24386) = 3 ^ 8 * m + 4886 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24386.1, data_15_24386.2]

/-- Complete interval computation for depth 15, residue 24387. -/
theorem bounds_15_24387 : exactInterval 15 24387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24387 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24387) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24387 : oddCount 24387 15 = 8 ∧ acceleratedOrbit 15 24387 = 4886 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24387 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24387) = 3 ^ 8 * m + 4886 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24387.1, data_15_24387.2]

/-- Complete interval computation for depth 15, residue 24388. -/
theorem bounds_15_24388 : exactInterval 15 24388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24388 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24388) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24388 : oddCount 24388 15 = 5 ∧ acceleratedOrbit 15 24388 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24388 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24388) = 3 ^ 5 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24388.1, data_15_24388.2]

/-- Complete interval computation for depth 15, residue 24389. -/
theorem bounds_15_24389 : exactInterval 15 24389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24389 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24389) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24389 : oddCount 24389 15 = 5 ∧ acceleratedOrbit 15 24389 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24389 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24389) = 3 ^ 5 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24389.1, data_15_24389.2]

/-- Complete interval computation for depth 15, residue 24390. -/
theorem bounds_15_24390 : exactInterval 15 24390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24390 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24390) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24390 : oddCount 24390 15 = 5 ∧ acceleratedOrbit 15 24390 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24390 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24390) = 3 ^ 5 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24390.1, data_15_24390.2]

/-- Complete interval computation for depth 15, residue 24391. -/
theorem bounds_15_24391 : exactInterval 15 24391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24391 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24391) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24391 : oddCount 24391 15 = 7 ∧ acceleratedOrbit 15 24391 = 1628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24391 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24391) = 3 ^ 7 * m + 1628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24391.1, data_15_24391.2]

/-- Complete interval computation for depth 15, residue 24392. -/
theorem bounds_15_24392 : exactInterval 15 24392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24392 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24392) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24392 : oddCount 24392 15 = 10 ∧ acceleratedOrbit 15 24392 = 43982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24392 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24392) = 3 ^ 10 * m + 43982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24392.1, data_15_24392.2]

/-- Complete interval computation for depth 15, residue 24393. -/
theorem bounds_15_24393 : exactInterval 15 24393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24393 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24393) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24393 : oddCount 24393 15 = 8 ∧ acceleratedOrbit 15 24393 = 4886 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24393 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24393) = 3 ^ 8 * m + 4886 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24393.1, data_15_24393.2]

/-- Complete interval computation for depth 15, residue 24394. -/
theorem bounds_15_24394 : exactInterval 15 24394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24394 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24394) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24394 : oddCount 24394 15 = 10 ∧ acceleratedOrbit 15 24394 = 43982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24394 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24394) = 3 ^ 10 * m + 43982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24394.1, data_15_24394.2]

/-- Complete interval computation for depth 15, residue 24395. -/
theorem bounds_15_24395 : exactInterval 15 24395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24395 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24395) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24395 : oddCount 24395 15 = 5 ∧ acceleratedOrbit 15 24395 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24395 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24395) = 3 ^ 5 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24395.1, data_15_24395.2]

/-- Complete interval computation for depth 15, residue 24396. -/
theorem bounds_15_24396 : exactInterval 15 24396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24396 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24396) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24396 : oddCount 24396 15 = 10 ∧ acceleratedOrbit 15 24396 = 43982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24396 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24396) = 3 ^ 10 * m + 43982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24396.1, data_15_24396.2]

/-- Complete interval computation for depth 15, residue 24397. -/
theorem bounds_15_24397 : exactInterval 15 24397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24397 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24397) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24397 : oddCount 24397 15 = 10 ∧ acceleratedOrbit 15 24397 = 43982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24397 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24397) = 3 ^ 10 * m + 43982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24397.1, data_15_24397.2]

/-- Complete interval computation for depth 15, residue 24398. -/
theorem bounds_15_24398 : exactInterval 15 24398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24398 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24398) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24398 : oddCount 24398 15 = 10 ∧ acceleratedOrbit 15 24398 = 43973 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24398 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24398) = 3 ^ 10 * m + 43973 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24398.1, data_15_24398.2]

/-- Complete interval computation for depth 15, residue 24399. -/
theorem bounds_15_24399 : exactInterval 15 24399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24399 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24399) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24399 : oddCount 24399 15 = 10 ∧ acceleratedOrbit 15 24399 = 43973 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24399 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24399) = 3 ^ 10 * m + 43973 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24399.1, data_15_24399.2]

/-- Complete interval computation for depth 15, residue 24400. -/
theorem bounds_15_24400 : exactInterval 15 24400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24400 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24400) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24400 : oddCount 24400 15 = 5 ∧ acceleratedOrbit 15 24400 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24400 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24400) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24400.1, data_15_24400.2]

/-- Complete interval computation for depth 15, residue 24401. -/
theorem bounds_15_24401 : exactInterval 15 24401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24401 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24401) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24401 : oddCount 24401 15 = 10 ∧ acceleratedOrbit 15 24401 = 43982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24401 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24401) = 3 ^ 10 * m + 43982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24401.1, data_15_24401.2]

/-- Complete interval computation for depth 15, residue 24402. -/
theorem bounds_15_24402 : exactInterval 15 24402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24402 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24402) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24402 : oddCount 24402 15 = 11 ∧ acceleratedOrbit 15 24402 = 131939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24402 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24402) = 3 ^ 11 * m + 131939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24402.1, data_15_24402.2]

/-- Complete interval computation for depth 15, residue 24403. -/
theorem bounds_15_24403 : exactInterval 15 24403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24403 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24403) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24403 : oddCount 24403 15 = 11 ∧ acceleratedOrbit 15 24403 = 131939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24403 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24403) = 3 ^ 11 * m + 131939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24403.1, data_15_24403.2]

/-- Complete interval computation for depth 15, residue 24404. -/
theorem bounds_15_24404 : exactInterval 15 24404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24404 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24404) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24404 : oddCount 24404 15 = 5 ∧ acceleratedOrbit 15 24404 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24404 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24404) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24404.1, data_15_24404.2]

/-- Complete interval computation for depth 15, residue 24405. -/
theorem bounds_15_24405 : exactInterval 15 24405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24405 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24405) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24405 : oddCount 24405 15 = 5 ∧ acceleratedOrbit 15 24405 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24405 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24405) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24405.1, data_15_24405.2]

/-- Complete interval computation for depth 15, residue 24406. -/
theorem bounds_15_24406 : exactInterval 15 24406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24406 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24406) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24406 : oddCount 24406 15 = 8 ∧ acceleratedOrbit 15 24406 = 4888 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24406 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24406) = 3 ^ 8 * m + 4888 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24406.1, data_15_24406.2]

/-- Complete interval computation for depth 15, residue 24407. -/
theorem bounds_15_24407 : exactInterval 15 24407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24407 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24407) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24407 : oddCount 24407 15 = 8 ∧ acceleratedOrbit 15 24407 = 4888 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24407 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24407) = 3 ^ 8 * m + 4888 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24407.1, data_15_24407.2]

/-- Complete interval computation for depth 15, residue 24408. -/
theorem bounds_15_24408 : exactInterval 15 24408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24408 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24408) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24408 : oddCount 24408 15 = 7 ∧ acceleratedOrbit 15 24408 = 1630 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24408 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24408) = 3 ^ 7 * m + 1630 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24408.1, data_15_24408.2]

/-- Complete interval computation for depth 15, residue 24409. -/
theorem bounds_15_24409 : exactInterval 15 24409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24409 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24409) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24409 : oddCount 24409 15 = 7 ∧ acceleratedOrbit 15 24409 = 1630 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24409 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24409) = 3 ^ 7 * m + 1630 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24409.1, data_15_24409.2]

/-- Complete interval computation for depth 15, residue 24410. -/
theorem bounds_15_24410 : exactInterval 15 24410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24410 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24410) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24410 : oddCount 24410 15 = 7 ∧ acceleratedOrbit 15 24410 = 1630 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24410 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24410) = 3 ^ 7 * m + 1630 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24410.1, data_15_24410.2]

/-- Complete interval computation for depth 15, residue 24411. -/
theorem bounds_15_24411 : exactInterval 15 24411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24411 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24411) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24411 : oddCount 24411 15 = 10 ∧ acceleratedOrbit 15 24411 = 43993 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24411 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24411) = 3 ^ 10 * m + 43993 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24411.1, data_15_24411.2]

end Collatz.Research.PassageAtlas.Batch0745
