import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0883

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6379. -/
theorem bounds_13_6379 : exactInterval 13 6379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6379 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6379) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6379 : oddCount 6379 13 = 8 ∧ acceleratedOrbit 13 6379 = 5111 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6379 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6379) = 3 ^ 8 * m + 5111 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6379.1, data_13_6379.2]

/-- Complete interval computation for depth 13, residue 6380. -/
theorem bounds_13_6380 : exactInterval 13 6380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6380 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6380) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6380 : oddCount 6380 13 = 6 ∧ acceleratedOrbit 13 6380 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6380 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6380) = 3 ^ 6 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6380.1, data_13_6380.2]

/-- Complete interval computation for depth 13, residue 6381. -/
theorem bounds_13_6381 : exactInterval 13 6381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6381 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6381) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6381 : oddCount 6381 13 = 6 ∧ acceleratedOrbit 13 6381 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6381 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6381) = 3 ^ 6 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6381.1, data_13_6381.2]

/-- Complete interval computation for depth 13, residue 6382. -/
theorem bounds_13_6382 : exactInterval 13 6382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6382 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6382) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6382 : oddCount 6382 13 = 6 ∧ acceleratedOrbit 13 6382 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6382 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6382) = 3 ^ 6 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6382.1, data_13_6382.2]

/-- Complete interval computation for depth 13, residue 6383. -/
theorem bounds_13_6383 : exactInterval 13 6383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6383 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6383) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6383 : oddCount 6383 13 = 10 ∧ acceleratedOrbit 13 6383 = 46018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6383 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6383) = 3 ^ 10 * m + 46018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6383.1, data_13_6383.2]

/-- Complete interval computation for depth 13, residue 6384. -/
theorem bounds_13_6384 : exactInterval 13 6384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6384 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6384) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6384 : oddCount 6384 13 = 5 ∧ acceleratedOrbit 13 6384 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6384 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6384) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6384.1, data_13_6384.2]

/-- Complete interval computation for depth 13, residue 6385. -/
theorem bounds_13_6385 : exactInterval 13 6385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6385 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6385) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6385 : oddCount 6385 13 = 5 ∧ acceleratedOrbit 13 6385 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6385 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6385) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6385.1, data_13_6385.2]

/-- Complete interval computation for depth 13, residue 6386. -/
theorem bounds_13_6386 : exactInterval 13 6386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6386 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6386) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6386 : oddCount 6386 13 = 7 ∧ acceleratedOrbit 13 6386 = 1706 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6386 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6386) = 3 ^ 7 * m + 1706 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6386.1, data_13_6386.2]

/-- Complete interval computation for depth 13, residue 6387. -/
theorem bounds_13_6387 : exactInterval 13 6387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6387 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6387) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6387 : oddCount 6387 13 = 7 ∧ acceleratedOrbit 13 6387 = 1706 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6387 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6387) = 3 ^ 7 * m + 1706 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6387.1, data_13_6387.2]

/-- Complete interval computation for depth 13, residue 6388. -/
theorem bounds_13_6388 : exactInterval 13 6388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6388 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6388) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6388 : oddCount 6388 13 = 5 ∧ acceleratedOrbit 13 6388 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6388 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6388) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6388.1, data_13_6388.2]

/-- Complete interval computation for depth 13, residue 6389. -/
theorem bounds_13_6389 : exactInterval 13 6389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6389 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6389) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6389 : oddCount 6389 13 = 5 ∧ acceleratedOrbit 13 6389 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6389 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6389) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6389.1, data_13_6389.2]

/-- Complete interval computation for depth 13, residue 6390. -/
theorem bounds_13_6390 : exactInterval 13 6390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6390 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6390) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6390 : oddCount 6390 13 = 6 ∧ acceleratedOrbit 13 6390 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6390 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6390) = 3 ^ 6 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6390.1, data_13_6390.2]

/-- Complete interval computation for depth 13, residue 6391. -/
theorem bounds_13_6391 : exactInterval 13 6391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6391 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6391) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6391 : oddCount 6391 13 = 6 ∧ acceleratedOrbit 13 6391 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6391 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6391) = 3 ^ 6 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6391.1, data_13_6391.2]

/-- Complete interval computation for depth 13, residue 6392. -/
theorem bounds_13_6392 : exactInterval 13 6392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6392 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6392) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6392 : oddCount 6392 13 = 7 ∧ acceleratedOrbit 13 6392 = 1709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6392 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6392) = 3 ^ 7 * m + 1709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6392.1, data_13_6392.2]

/-- Complete interval computation for depth 13, residue 6393. -/
theorem bounds_13_6393 : exactInterval 13 6393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6393 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6393) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6393 : oddCount 6393 13 = 8 ∧ acceleratedOrbit 13 6393 = 5123 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6393 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6393) = 3 ^ 8 * m + 5123 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6393.1, data_13_6393.2]

end Collatz.Research.StoppingAtlas.Batch0883
