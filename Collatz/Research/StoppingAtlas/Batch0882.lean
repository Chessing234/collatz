import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0882

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6364. -/
theorem bounds_13_6364 : exactInterval 13 6364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6364 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6364) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6364 : oddCount 6364 13 = 9 ∧ acceleratedOrbit 13 6364 = 15308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6364 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6364) = 3 ^ 9 * m + 15308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6364.1, data_13_6364.2]

/-- Complete interval computation for depth 13, residue 6365. -/
theorem bounds_13_6365 : exactInterval 13 6365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6365 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6365) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6365 : oddCount 6365 13 = 9 ∧ acceleratedOrbit 13 6365 = 15308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6365 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6365) = 3 ^ 9 * m + 15308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6365.1, data_13_6365.2]

/-- Complete interval computation for depth 13, residue 6366. -/
theorem bounds_13_6366 : exactInterval 13 6366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6366 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6366) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6366 : oddCount 6366 13 = 9 ∧ acceleratedOrbit 13 6366 = 15302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6366 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6366) = 3 ^ 9 * m + 15302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6366.1, data_13_6366.2]

/-- Complete interval computation for depth 13, residue 6367. -/
theorem bounds_13_6367 : exactInterval 13 6367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6367 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6367) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6367 : oddCount 6367 13 = 9 ∧ acceleratedOrbit 13 6367 = 15302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6367 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6367) = 3 ^ 9 * m + 15302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6367.1, data_13_6367.2]

/-- Complete interval computation for depth 13, residue 6368. -/
theorem bounds_13_6368 : exactInterval 13 6368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6368 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6368) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6368 : oddCount 6368 13 = 5 ∧ acceleratedOrbit 13 6368 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6368 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6368) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6368.1, data_13_6368.2]

/-- Complete interval computation for depth 13, residue 6369. -/
theorem bounds_13_6369 : exactInterval 13 6369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6369 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6369) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6369 : oddCount 6369 13 = 11 ∧ acceleratedOrbit 13 6369 = 137780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6369 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6369) = 3 ^ 11 * m + 137780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6369.1, data_13_6369.2]

/-- Complete interval computation for depth 13, residue 6370. -/
theorem bounds_13_6370 : exactInterval 13 6370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6370 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6370) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6370 : oddCount 6370 13 = 2 ∧ acceleratedOrbit 13 6370 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6370 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6370) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6370.1, data_13_6370.2]

/-- Complete interval computation for depth 13, residue 6371. -/
theorem bounds_13_6371 : exactInterval 13 6371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6371 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6371) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6371 : oddCount 6371 13 = 2 ∧ acceleratedOrbit 13 6371 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6371 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6371) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6371.1, data_13_6371.2]

/-- Complete interval computation for depth 13, residue 6372. -/
theorem bounds_13_6372 : exactInterval 13 6372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6372 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6372) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6372 : oddCount 6372 13 = 6 ∧ acceleratedOrbit 13 6372 = 568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6372 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6372) = 3 ^ 6 * m + 568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6372.1, data_13_6372.2]

/-- Complete interval computation for depth 13, residue 6373. -/
theorem bounds_13_6373 : exactInterval 13 6373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6373 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6373) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6373 : oddCount 6373 13 = 6 ∧ acceleratedOrbit 13 6373 = 568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6373 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6373) = 3 ^ 6 * m + 568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6373.1, data_13_6373.2]

/-- Complete interval computation for depth 13, residue 6374. -/
theorem bounds_13_6374 : exactInterval 13 6374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6374 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6374) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6374 : oddCount 6374 13 = 6 ∧ acceleratedOrbit 13 6374 = 568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6374 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6374) = 3 ^ 6 * m + 568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6374.1, data_13_6374.2]

/-- Complete interval computation for depth 13, residue 6375. -/
theorem bounds_13_6375 : exactInterval 13 6375 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6375 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6375) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6375 : oddCount 6375 13 = 8 ∧ acceleratedOrbit 13 6375 = 5107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6375 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6375) = 3 ^ 8 * m + 5107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6375.1, data_13_6375.2]

/-- Complete interval computation for depth 13, residue 6376. -/
theorem bounds_13_6376 : exactInterval 13 6376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6376 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6376) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6376 : oddCount 6376 13 = 5 ∧ acceleratedOrbit 13 6376 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6376 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6376) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6376.1, data_13_6376.2]

/-- Complete interval computation for depth 13, residue 6377. -/
theorem bounds_13_6377 : exactInterval 13 6377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6377 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6377) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6377 : oddCount 6377 13 = 7 ∧ acceleratedOrbit 13 6377 = 1703 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6377 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6377) = 3 ^ 7 * m + 1703 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6377.1, data_13_6377.2]

/-- Complete interval computation for depth 13, residue 6378. -/
theorem bounds_13_6378 : exactInterval 13 6378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6378 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6378) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6378 : oddCount 6378 13 = 5 ∧ acceleratedOrbit 13 6378 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6378 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6378) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6378.1, data_13_6378.2]

end Collatz.Research.StoppingAtlas.Batch0882
