import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0440

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 14385. -/
theorem bounds_15_14385 : exactInterval 15 14385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14385 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14385) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14385 : oddCount 14385 15 = 8 ∧ acceleratedOrbit 15 14385 = 2882 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14385 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14385) = 3 ^ 8 * m + 2882 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14385.1, data_15_14385.2]

/-- Complete interval computation for depth 15, residue 14386. -/
theorem bounds_15_14386 : exactInterval 15 14386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14386 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14386) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14386 : oddCount 14386 15 = 8 ∧ acceleratedOrbit 15 14386 = 2882 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14386 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14386) = 3 ^ 8 * m + 2882 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14386.1, data_15_14386.2]

/-- Complete interval computation for depth 15, residue 14387. -/
theorem bounds_15_14387 : exactInterval 15 14387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14387 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14387) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14387 : oddCount 14387 15 = 8 ∧ acceleratedOrbit 15 14387 = 2882 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14387 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14387) = 3 ^ 8 * m + 2882 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14387.1, data_15_14387.2]

/-- Complete interval computation for depth 15, residue 14388. -/
theorem bounds_15_14388 : exactInterval 15 14388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14388 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14388) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14388 : oddCount 14388 15 = 6 ∧ acceleratedOrbit 15 14388 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14388 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14388) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14388.1, data_15_14388.2]

/-- Complete interval computation for depth 15, residue 14389. -/
theorem bounds_15_14389 : exactInterval 15 14389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14389 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14389) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14389 : oddCount 14389 15 = 6 ∧ acceleratedOrbit 15 14389 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14389 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14389) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14389.1, data_15_14389.2]

/-- Complete interval computation for depth 15, residue 14390. -/
theorem bounds_15_14390 : exactInterval 15 14390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14390 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14390) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14390 : oddCount 14390 15 = 10 ∧ acceleratedOrbit 15 14390 = 25937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14390 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14390) = 3 ^ 10 * m + 25937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14390.1, data_15_14390.2]

/-- Complete interval computation for depth 15, residue 14391. -/
theorem bounds_15_14391 : exactInterval 15 14391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14391 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14391) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14391 : oddCount 14391 15 = 10 ∧ acceleratedOrbit 15 14391 = 25937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14391 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14391) = 3 ^ 10 * m + 25937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14391.1, data_15_14391.2]

/-- Complete interval computation for depth 15, residue 14392. -/
theorem bounds_15_14392 : exactInterval 15 14392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14392 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14392) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14392 : oddCount 14392 15 = 7 ∧ acceleratedOrbit 15 14392 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14392 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14392) = 3 ^ 7 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14392.1, data_15_14392.2]

/-- Complete interval computation for depth 15, residue 14393. -/
theorem bounds_15_14393 : exactInterval 15 14393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14393 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14393) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14393 : oddCount 14393 15 = 7 ∧ acceleratedOrbit 15 14393 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14393 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14393) = 3 ^ 7 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14393.1, data_15_14393.2]

/-- Complete interval computation for depth 15, residue 14394. -/
theorem bounds_15_14394 : exactInterval 15 14394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14394 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14394) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14394 : oddCount 14394 15 = 7 ∧ acceleratedOrbit 15 14394 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14394 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14394) = 3 ^ 7 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14394.1, data_15_14394.2]

/-- Complete interval computation for depth 15, residue 14395. -/
theorem bounds_15_14395 : exactInterval 15 14395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14395 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14395) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14395 : oddCount 14395 15 = 7 ∧ acceleratedOrbit 15 14395 = 961 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14395 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14395) = 3 ^ 7 * m + 961 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14395.1, data_15_14395.2]

/-- Complete interval computation for depth 15, residue 14396. -/
theorem bounds_15_14396 : exactInterval 15 14396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14396 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14396) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14396 : oddCount 14396 15 = 7 ∧ acceleratedOrbit 15 14396 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14396 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14396) = 3 ^ 7 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14396.1, data_15_14396.2]

/-- Complete interval computation for depth 15, residue 14397. -/
theorem bounds_15_14397 : exactInterval 15 14397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14397 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14397) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14397 : oddCount 14397 15 = 7 ∧ acceleratedOrbit 15 14397 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14397 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14397) = 3 ^ 7 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14397.1, data_15_14397.2]

/-- Complete interval computation for depth 15, residue 14398. -/
theorem bounds_15_14398 : exactInterval 15 14398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14398 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14398) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14398 : oddCount 14398 15 = 9 ∧ acceleratedOrbit 15 14398 = 8650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14398 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14398) = 3 ^ 9 * m + 8650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14398.1, data_15_14398.2]

/-- Complete interval computation for depth 15, residue 14399. -/
theorem bounds_15_14399 : exactInterval 15 14399 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14399 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14399) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14399 : oddCount 14399 15 = 9 ∧ acceleratedOrbit 15 14399 = 8650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14399 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14399) = 3 ^ 9 * m + 8650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14399.1, data_15_14399.2]

/-- Complete interval computation for depth 15, residue 14400. -/
theorem bounds_15_14400 : exactInterval 15 14400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14400 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14400) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14400 : oddCount 14400 15 = 7 ∧ acceleratedOrbit 15 14400 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14400 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14400) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14400.1, data_15_14400.2]

/-- Complete interval computation for depth 15, residue 14401. -/
theorem bounds_15_14401 : exactInterval 15 14401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14401 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14401) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14401 : oddCount 14401 15 = 9 ∧ acceleratedOrbit 15 14401 = 8657 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14401 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14401) = 3 ^ 9 * m + 8657 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14401.1, data_15_14401.2]

/-- Complete interval computation for depth 15, residue 14402. -/
theorem bounds_15_14402 : exactInterval 15 14402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14402 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14402) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14402 : oddCount 14402 15 = 9 ∧ acceleratedOrbit 15 14402 = 8657 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14402 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14402) = 3 ^ 9 * m + 8657 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14402.1, data_15_14402.2]

/-- Complete interval computation for depth 15, residue 14403. -/
theorem bounds_15_14403 : exactInterval 15 14403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14403 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14403) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14403 : oddCount 14403 15 = 9 ∧ acceleratedOrbit 15 14403 = 8657 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14403 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14403) = 3 ^ 9 * m + 8657 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14403.1, data_15_14403.2]

/-- Complete interval computation for depth 15, residue 14404. -/
theorem bounds_15_14404 : exactInterval 15 14404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14404 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14404) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14404 : oddCount 14404 15 = 6 ∧ acceleratedOrbit 15 14404 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14404 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14404) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14404.1, data_15_14404.2]

/-- Complete interval computation for depth 15, residue 14405. -/
theorem bounds_15_14405 : exactInterval 15 14405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14405 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14405) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14405 : oddCount 14405 15 = 6 ∧ acceleratedOrbit 15 14405 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14405 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14405) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14405.1, data_15_14405.2]

/-- Complete interval computation for depth 15, residue 14406. -/
theorem bounds_15_14406 : exactInterval 15 14406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14406 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14406) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14406 : oddCount 14406 15 = 6 ∧ acceleratedOrbit 15 14406 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14406 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14406) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14406.1, data_15_14406.2]

/-- Complete interval computation for depth 15, residue 14407. -/
theorem bounds_15_14407 : exactInterval 15 14407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14407 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14407) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14407 : oddCount 14407 15 = 8 ∧ acceleratedOrbit 15 14407 = 2885 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14407 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14407) = 3 ^ 8 * m + 2885 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14407.1, data_15_14407.2]

/-- Complete interval computation for depth 15, residue 14408. -/
theorem bounds_15_14408 : exactInterval 15 14408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14408 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14408) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14408 : oddCount 14408 15 = 9 ∧ acceleratedOrbit 15 14408 = 8666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14408 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14408) = 3 ^ 9 * m + 8666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14408.1, data_15_14408.2]

/-- Complete interval computation for depth 15, residue 14409. -/
theorem bounds_15_14409 : exactInterval 15 14409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14409 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14409) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14409 : oddCount 14409 15 = 11 ∧ acceleratedOrbit 15 14409 = 77912 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14409 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14409) = 3 ^ 11 * m + 77912 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14409.1, data_15_14409.2]

/-- Complete interval computation for depth 15, residue 14410. -/
theorem bounds_15_14410 : exactInterval 15 14410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14410 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14410) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14410 : oddCount 14410 15 = 9 ∧ acceleratedOrbit 15 14410 = 8666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14410 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14410) = 3 ^ 9 * m + 8666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14410.1, data_15_14410.2]

/-- Complete interval computation for depth 15, residue 14411. -/
theorem bounds_15_14411 : exactInterval 15 14411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14411 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14411) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14411 : oddCount 14411 15 = 6 ∧ acceleratedOrbit 15 14411 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14411 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14411) = 3 ^ 6 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14411.1, data_15_14411.2]

/-- Complete interval computation for depth 15, residue 14412. -/
theorem bounds_15_14412 : exactInterval 15 14412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14412 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14412) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14412 : oddCount 14412 15 = 9 ∧ acceleratedOrbit 15 14412 = 8666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14412 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14412) = 3 ^ 9 * m + 8666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14412.1, data_15_14412.2]

/-- Complete interval computation for depth 15, residue 14413. -/
theorem bounds_15_14413 : exactInterval 15 14413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14413 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14413) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14413 : oddCount 14413 15 = 9 ∧ acceleratedOrbit 15 14413 = 8666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14413 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14413) = 3 ^ 9 * m + 8666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14413.1, data_15_14413.2]

/-- Complete interval computation for depth 15, residue 14414. -/
theorem bounds_15_14414 : exactInterval 15 14414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14414 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14414) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14414 : oddCount 14414 15 = 8 ∧ acceleratedOrbit 15 14414 = 2888 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14414 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14414) = 3 ^ 8 * m + 2888 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14414.1, data_15_14414.2]

/-- Complete interval computation for depth 15, residue 14415. -/
theorem bounds_15_14415 : exactInterval 15 14415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14415 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14415) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14415 : oddCount 14415 15 = 8 ∧ acceleratedOrbit 15 14415 = 2888 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14415 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14415) = 3 ^ 8 * m + 2888 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14415.1, data_15_14415.2]

/-- Complete interval computation for depth 15, residue 14416. -/
theorem bounds_15_14416 : exactInterval 15 14416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14416 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14416) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14416 : oddCount 14416 15 = 7 ∧ acceleratedOrbit 15 14416 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14416 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14416) = 3 ^ 7 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14416.1, data_15_14416.2]

end Collatz.Research.PassageAtlas.Batch0440
