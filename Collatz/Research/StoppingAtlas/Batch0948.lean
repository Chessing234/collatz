import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0948

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7377. -/
theorem bounds_13_7377 : exactInterval 13 7377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7377 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7377) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7377 : oddCount 7377 13 = 9 ∧ acceleratedOrbit 13 7377 = 17738 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7377 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7377) = 3 ^ 9 * m + 17738 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7377.1, data_13_7377.2]

/-- Complete interval computation for depth 13, residue 7378. -/
theorem bounds_13_7378 : exactInterval 13 7378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7378 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7378) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7378 : oddCount 7378 13 = 9 ∧ acceleratedOrbit 13 7378 = 17738 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7378 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7378) = 3 ^ 9 * m + 17738 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7378.1, data_13_7378.2]

/-- Complete interval computation for depth 13, residue 7379. -/
theorem bounds_13_7379 : exactInterval 13 7379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7379 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7379) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7379 : oddCount 7379 13 = 9 ∧ acceleratedOrbit 13 7379 = 17738 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7379 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7379) = 3 ^ 9 * m + 17738 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7379.1, data_13_7379.2]

/-- Complete interval computation for depth 13, residue 7380. -/
theorem bounds_13_7380 : exactInterval 13 7380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7380 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7380) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7380 : oddCount 7380 13 = 4 ∧ acceleratedOrbit 13 7380 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7380 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7380) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7380.1, data_13_7380.2]

/-- Complete interval computation for depth 13, residue 7381. -/
theorem bounds_13_7381 : exactInterval 13 7381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7381 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7381) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7381 : oddCount 7381 13 = 4 ∧ acceleratedOrbit 13 7381 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7381 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7381) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7381.1, data_13_7381.2]

/-- Complete interval computation for depth 13, residue 7382. -/
theorem bounds_13_7382 : exactInterval 13 7382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7382 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7382) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7382 : oddCount 7382 13 = 7 ∧ acceleratedOrbit 13 7382 = 1972 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7382 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7382) = 3 ^ 7 * m + 1972 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7382.1, data_13_7382.2]

/-- Complete interval computation for depth 13, residue 7383. -/
theorem bounds_13_7383 : exactInterval 13 7383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7383 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7383) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7383 : oddCount 7383 13 = 7 ∧ acceleratedOrbit 13 7383 = 1972 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7383 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7383) = 3 ^ 7 * m + 1972 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7383.1, data_13_7383.2]

/-- Complete interval computation for depth 13, residue 7384. -/
theorem bounds_13_7384 : exactInterval 13 7384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7384 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7384) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7384 : oddCount 7384 13 = 6 ∧ acceleratedOrbit 13 7384 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7384 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7384) = 3 ^ 6 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7384.1, data_13_7384.2]

/-- Complete interval computation for depth 13, residue 7385. -/
theorem bounds_13_7385 : exactInterval 13 7385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7385 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7385) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7385 : oddCount 7385 13 = 6 ∧ acceleratedOrbit 13 7385 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7385 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7385) = 3 ^ 6 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7385.1, data_13_7385.2]

/-- Complete interval computation for depth 13, residue 7386. -/
theorem bounds_13_7386 : exactInterval 13 7386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7386 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7386) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7386 : oddCount 7386 13 = 6 ∧ acceleratedOrbit 13 7386 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7386 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7386) = 3 ^ 6 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7386.1, data_13_7386.2]

/-- Complete interval computation for depth 13, residue 7387. -/
theorem bounds_13_7387 : exactInterval 13 7387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7387 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7387) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7387 : oddCount 7387 13 = 7 ∧ acceleratedOrbit 13 7387 = 1973 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7387 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7387) = 3 ^ 7 * m + 1973 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7387.1, data_13_7387.2]

/-- Complete interval computation for depth 13, residue 7388. -/
theorem bounds_13_7388 : exactInterval 13 7388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7388 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7388) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7388 : oddCount 7388 13 = 6 ∧ acceleratedOrbit 13 7388 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7388 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7388) = 3 ^ 6 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7388.1, data_13_7388.2]

/-- Complete interval computation for depth 13, residue 7389. -/
theorem bounds_13_7389 : exactInterval 13 7389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7389 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7389) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7389 : oddCount 7389 13 = 6 ∧ acceleratedOrbit 13 7389 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7389 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7389) = 3 ^ 6 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7389.1, data_13_7389.2]

/-- Complete interval computation for depth 13, residue 7390. -/
theorem bounds_13_7390 : exactInterval 13 7390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7390 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7390) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7390 : oddCount 7390 13 = 8 ∧ acceleratedOrbit 13 7390 = 5921 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7390 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7390) = 3 ^ 8 * m + 5921 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7390.1, data_13_7390.2]

/-- Complete interval computation for depth 13, residue 7391. -/
theorem bounds_13_7391 : exactInterval 13 7391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7391 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7391) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7391 : oddCount 7391 13 = 8 ∧ acceleratedOrbit 13 7391 = 5921 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7391 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7391) = 3 ^ 8 * m + 5921 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7391.1, data_13_7391.2]

/-- Complete interval computation for depth 13, residue 7392. -/
theorem bounds_13_7392 : exactInterval 13 7392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7392 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7392) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7392 : oddCount 7392 13 = 6 ∧ acceleratedOrbit 13 7392 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7392 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7392) = 3 ^ 6 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7392.1, data_13_7392.2]

end Collatz.Research.StoppingAtlas.Batch0948
