import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0688

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3384. -/
theorem bounds_13_3384 : exactInterval 13 3384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3384 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3384) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3384 : oddCount 3384 13 = 6 ∧ acceleratedOrbit 13 3384 = 302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3384 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3384) = 3 ^ 6 * m + 302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3384.1, data_13_3384.2]

/-- Complete interval computation for depth 13, residue 3385. -/
theorem bounds_13_3385 : exactInterval 13 3385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3385 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3385) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3385 : oddCount 3385 13 = 9 ∧ acceleratedOrbit 13 3385 = 8140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3385 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3385) = 3 ^ 9 * m + 8140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3385.1, data_13_3385.2]

/-- Complete interval computation for depth 13, residue 3386. -/
theorem bounds_13_3386 : exactInterval 13 3386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3386 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3386) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3386 : oddCount 3386 13 = 6 ∧ acceleratedOrbit 13 3386 = 302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3386 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3386) = 3 ^ 6 * m + 302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3386.1, data_13_3386.2]

/-- Complete interval computation for depth 13, residue 3387. -/
theorem bounds_13_3387 : exactInterval 13 3387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3387 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3387) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3387 : oddCount 3387 13 = 5 ∧ acceleratedOrbit 13 3387 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3387 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3387) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3387.1, data_13_3387.2]

/-- Complete interval computation for depth 13, residue 3388. -/
theorem bounds_13_3388 : exactInterval 13 3388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3388 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3388) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3388 : oddCount 3388 13 = 6 ∧ acceleratedOrbit 13 3388 = 302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3388 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3388) = 3 ^ 6 * m + 302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3388.1, data_13_3388.2]

/-- Complete interval computation for depth 13, residue 3389. -/
theorem bounds_13_3389 : exactInterval 13 3389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3389 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3389) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3389 : oddCount 3389 13 = 6 ∧ acceleratedOrbit 13 3389 = 302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3389 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3389) = 3 ^ 6 * m + 302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3389.1, data_13_3389.2]

/-- Complete interval computation for depth 13, residue 3390. -/
theorem bounds_13_3390 : exactInterval 13 3390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3390 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3390) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3390 : oddCount 3390 13 = 10 ∧ acceleratedOrbit 13 3390 = 24452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3390 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3390) = 3 ^ 10 * m + 24452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3390.1, data_13_3390.2]

/-- Complete interval computation for depth 13, residue 3391. -/
theorem bounds_13_3391 : exactInterval 13 3391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3391 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3391) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3391 : oddCount 3391 13 = 10 ∧ acceleratedOrbit 13 3391 = 24452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3391 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3391) = 3 ^ 10 * m + 24452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3391.1, data_13_3391.2]

/-- Complete interval computation for depth 13, residue 3392. -/
theorem bounds_13_3392 : exactInterval 13 3392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3392 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3392) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3392 : oddCount 3392 13 = 2 ∧ acceleratedOrbit 13 3392 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3392 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3392) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3392.1, data_13_3392.2]

/-- Complete interval computation for depth 13, residue 3393. -/
theorem bounds_13_3393 : exactInterval 13 3393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3393 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3393) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3393 : oddCount 3393 13 = 5 ∧ acceleratedOrbit 13 3393 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3393 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3393) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3393.1, data_13_3393.2]

/-- Complete interval computation for depth 13, residue 3394. -/
theorem bounds_13_3394 : exactInterval 13 3394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3394 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3394) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3394 : oddCount 3394 13 = 7 ∧ acceleratedOrbit 13 3394 = 908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3394 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3394) = 3 ^ 7 * m + 908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3394.1, data_13_3394.2]

/-- Complete interval computation for depth 13, residue 3395. -/
theorem bounds_13_3395 : exactInterval 13 3395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3395 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3395) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3395 : oddCount 3395 13 = 7 ∧ acceleratedOrbit 13 3395 = 908 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3395 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3395) = 3 ^ 7 * m + 908 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3395.1, data_13_3395.2]

/-- Complete interval computation for depth 13, residue 3396. -/
theorem bounds_13_3396 : exactInterval 13 3396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3396 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3396) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3396 : oddCount 3396 13 = 7 ∧ acceleratedOrbit 13 3396 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3396 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3396) = 3 ^ 7 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3396.1, data_13_3396.2]

/-- Complete interval computation for depth 13, residue 3397. -/
theorem bounds_13_3397 : exactInterval 13 3397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3397 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3397) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3397 : oddCount 3397 13 = 7 ∧ acceleratedOrbit 13 3397 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3397 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3397) = 3 ^ 7 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3397.1, data_13_3397.2]

/-- Complete interval computation for depth 13, residue 3398. -/
theorem bounds_13_3398 : exactInterval 13 3398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3398 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3398) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3398 : oddCount 3398 13 = 7 ∧ acceleratedOrbit 13 3398 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3398 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3398) = 3 ^ 7 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3398.1, data_13_3398.2]

end Collatz.Research.StoppingAtlas.Batch0688
