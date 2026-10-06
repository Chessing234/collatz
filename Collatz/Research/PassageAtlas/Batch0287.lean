import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0287

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 9371. -/
theorem bounds_15_9371 : exactInterval 15 9371 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9371 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9371) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9371 : oddCount 9371 15 = 9 ∧ acceleratedOrbit 15 9371 = 5630 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9371 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9371) = 3 ^ 9 * m + 5630 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9371.1, data_15_9371.2]

/-- Complete interval computation for depth 15, residue 9372. -/
theorem bounds_15_9372 : exactInterval 15 9372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9372 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9372) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9372 : oddCount 9372 15 = 7 ∧ acceleratedOrbit 15 9372 = 626 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9372 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9372) = 3 ^ 7 * m + 626 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9372.1, data_15_9372.2]

/-- Complete interval computation for depth 15, residue 9373. -/
theorem bounds_15_9373 : exactInterval 15 9373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9373 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9373) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9373 : oddCount 9373 15 = 7 ∧ acceleratedOrbit 15 9373 = 626 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9373 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9373) = 3 ^ 7 * m + 626 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9373.1, data_15_9373.2]

/-- Complete interval computation for depth 15, residue 9374. -/
theorem bounds_15_9374 : exactInterval 15 9374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9374 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9374) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9374 : oddCount 9374 15 = 7 ∧ acceleratedOrbit 15 9374 = 626 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9374 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9374) = 3 ^ 7 * m + 626 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9374.1, data_15_9374.2]

/-- Complete interval computation for depth 15, residue 9375. -/
theorem bounds_15_9375 : exactInterval 15 9375 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9375 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9375) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9375 : oddCount 9375 15 = 9 ∧ acceleratedOrbit 15 9375 = 5632 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9375 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9375) = 3 ^ 9 * m + 5632 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9375.1, data_15_9375.2]

/-- Complete interval computation for depth 15, residue 9376. -/
theorem bounds_15_9376 : exactInterval 15 9376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9376 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9376) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9376 : oddCount 9376 15 = 5 ∧ acceleratedOrbit 15 9376 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9376 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9376) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9376.1, data_15_9376.2]

/-- Complete interval computation for depth 15, residue 9377. -/
theorem bounds_15_9377 : exactInterval 15 9377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9377 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9377) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9377 : oddCount 9377 15 = 10 ∧ acceleratedOrbit 15 9377 = 16904 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9377 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9377) = 3 ^ 10 * m + 16904 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9377.1, data_15_9377.2]

/-- Complete interval computation for depth 15, residue 9378. -/
theorem bounds_15_9378 : exactInterval 15 9378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9378 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9378) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9378 : oddCount 9378 15 = 8 ∧ acceleratedOrbit 15 9378 = 1880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9378 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9378) = 3 ^ 8 * m + 1880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9378.1, data_15_9378.2]

/-- Complete interval computation for depth 15, residue 9379. -/
theorem bounds_15_9379 : exactInterval 15 9379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9379 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9379) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9379 : oddCount 9379 15 = 8 ∧ acceleratedOrbit 15 9379 = 1880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9379 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9379) = 3 ^ 8 * m + 1880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9379.1, data_15_9379.2]

/-- Complete interval computation for depth 15, residue 9380. -/
theorem bounds_15_9380 : exactInterval 15 9380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9380 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9380) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9380 : oddCount 9380 15 = 8 ∧ acceleratedOrbit 15 9380 = 1880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9380 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9380) = 3 ^ 8 * m + 1880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9380.1, data_15_9380.2]

/-- Complete interval computation for depth 15, residue 9381. -/
theorem bounds_15_9381 : exactInterval 15 9381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9381 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9381) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9381 : oddCount 9381 15 = 8 ∧ acceleratedOrbit 15 9381 = 1880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9381 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9381) = 3 ^ 8 * m + 1880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9381.1, data_15_9381.2]

/-- Complete interval computation for depth 15, residue 9382. -/
theorem bounds_15_9382 : exactInterval 15 9382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9382 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9382) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9382 : oddCount 9382 15 = 8 ∧ acceleratedOrbit 15 9382 = 1880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9382 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9382) = 3 ^ 8 * m + 1880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9382.1, data_15_9382.2]

/-- Complete interval computation for depth 15, residue 9383. -/
theorem bounds_15_9383 : exactInterval 15 9383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9383 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9383) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9383 : oddCount 9383 15 = 8 ∧ acceleratedOrbit 15 9383 = 1879 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9383 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9383) = 3 ^ 8 * m + 1879 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9383.1, data_15_9383.2]

/-- Complete interval computation for depth 15, residue 9384. -/
theorem bounds_15_9384 : exactInterval 15 9384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9384 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9384) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9384 : oddCount 9384 15 = 5 ∧ acceleratedOrbit 15 9384 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9384 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9384) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9384.1, data_15_9384.2]

/-- Complete interval computation for depth 15, residue 9385. -/
theorem bounds_15_9385 : exactInterval 15 9385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9385 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9385) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9385 : oddCount 9385 15 = 11 ∧ acceleratedOrbit 15 9385 = 50746 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9385 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9385) = 3 ^ 11 * m + 50746 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9385.1, data_15_9385.2]

/-- Complete interval computation for depth 15, residue 9386. -/
theorem bounds_15_9386 : exactInterval 15 9386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9386 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9386) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9386 : oddCount 9386 15 = 5 ∧ acceleratedOrbit 15 9386 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9386 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9386) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9386.1, data_15_9386.2]

/-- Complete interval computation for depth 15, residue 9387. -/
theorem bounds_15_9387 : exactInterval 15 9387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9387 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9387) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9387 : oddCount 9387 15 = 6 ∧ acceleratedOrbit 15 9387 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9387 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9387) = 3 ^ 6 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9387.1, data_15_9387.2]

/-- Complete interval computation for depth 15, residue 9388. -/
theorem bounds_15_9388 : exactInterval 15 9388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9388 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9388) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9388 : oddCount 9388 15 = 8 ∧ acceleratedOrbit 15 9388 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9388 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9388) = 3 ^ 8 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9388.1, data_15_9388.2]

/-- Complete interval computation for depth 15, residue 9389. -/
theorem bounds_15_9389 : exactInterval 15 9389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9389 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9389) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9389 : oddCount 9389 15 = 8 ∧ acceleratedOrbit 15 9389 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9389 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9389) = 3 ^ 8 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9389.1, data_15_9389.2]

/-- Complete interval computation for depth 15, residue 9390. -/
theorem bounds_15_9390 : exactInterval 15 9390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9390 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9390) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9390 : oddCount 9390 15 = 8 ∧ acceleratedOrbit 15 9390 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9390 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9390) = 3 ^ 8 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9390.1, data_15_9390.2]

/-- Complete interval computation for depth 15, residue 9391. -/
theorem bounds_15_9391 : exactInterval 15 9391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9391 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9391) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9391 : oddCount 9391 15 = 10 ∧ acceleratedOrbit 15 9391 = 16928 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9391 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9391) = 3 ^ 10 * m + 16928 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9391.1, data_15_9391.2]

/-- Complete interval computation for depth 15, residue 9392. -/
theorem bounds_15_9392 : exactInterval 15 9392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9392 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9392) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9392 : oddCount 9392 15 = 5 ∧ acceleratedOrbit 15 9392 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9392 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9392) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9392.1, data_15_9392.2]

/-- Complete interval computation for depth 15, residue 9393. -/
theorem bounds_15_9393 : exactInterval 15 9393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9393 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9393) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9393 : oddCount 9393 15 = 8 ∧ acceleratedOrbit 15 9393 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9393 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9393) = 3 ^ 8 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9393.1, data_15_9393.2]

/-- Complete interval computation for depth 15, residue 9394. -/
theorem bounds_15_9394 : exactInterval 15 9394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9394 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9394) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9394 : oddCount 9394 15 = 8 ∧ acceleratedOrbit 15 9394 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9394 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9394) = 3 ^ 8 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9394.1, data_15_9394.2]

/-- Complete interval computation for depth 15, residue 9395. -/
theorem bounds_15_9395 : exactInterval 15 9395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9395 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9395) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9395 : oddCount 9395 15 = 8 ∧ acceleratedOrbit 15 9395 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9395 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9395) = 3 ^ 8 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9395.1, data_15_9395.2]

/-- Complete interval computation for depth 15, residue 9396. -/
theorem bounds_15_9396 : exactInterval 15 9396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9396 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9396) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9396 : oddCount 9396 15 = 5 ∧ acceleratedOrbit 15 9396 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9396 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9396) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9396.1, data_15_9396.2]

/-- Complete interval computation for depth 15, residue 9397. -/
theorem bounds_15_9397 : exactInterval 15 9397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9397 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9397) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9397 : oddCount 9397 15 = 5 ∧ acceleratedOrbit 15 9397 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9397 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9397) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9397.1, data_15_9397.2]

/-- Complete interval computation for depth 15, residue 9398. -/
theorem bounds_15_9398 : exactInterval 15 9398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9398 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9398) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9398 : oddCount 9398 15 = 10 ∧ acceleratedOrbit 15 9398 = 16942 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9398 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9398) = 3 ^ 10 * m + 16942 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9398.1, data_15_9398.2]

/-- Complete interval computation for depth 15, residue 9399. -/
theorem bounds_15_9399 : exactInterval 15 9399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9399 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9399) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9399 : oddCount 9399 15 = 10 ∧ acceleratedOrbit 15 9399 = 16942 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9399 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9399) = 3 ^ 10 * m + 16942 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9399.1, data_15_9399.2]

/-- Complete interval computation for depth 15, residue 9400. -/
theorem bounds_15_9400 : exactInterval 15 9400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9400 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9400) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9400 : oddCount 9400 15 = 5 ∧ acceleratedOrbit 15 9400 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9400 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9400) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9400.1, data_15_9400.2]

/-- Complete interval computation for depth 15, residue 9401. -/
theorem bounds_15_9401 : exactInterval 15 9401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9401 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9401) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9401 : oddCount 9401 15 = 10 ∧ acceleratedOrbit 15 9401 = 16949 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9401 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9401) = 3 ^ 10 * m + 16949 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9401.1, data_15_9401.2]

/-- Complete interval computation for depth 15, residue 9402. -/
theorem bounds_15_9402 : exactInterval 15 9402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9402 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9402) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9402 : oddCount 9402 15 = 5 ∧ acceleratedOrbit 15 9402 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9402 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9402) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9402.1, data_15_9402.2]

/-- Complete interval computation for depth 15, residue 9403. -/
theorem bounds_15_9403 : exactInterval 15 9403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9403 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9403) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9403 : oddCount 9403 15 = 10 ∧ acceleratedOrbit 15 9403 = 16949 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9403 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9403) = 3 ^ 10 * m + 16949 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9403.1, data_15_9403.2]

end Collatz.Research.PassageAtlas.Batch0287
