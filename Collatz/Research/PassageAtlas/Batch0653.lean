import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0653

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 21364. -/
theorem bounds_15_21364 : exactInterval 15 21364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21364 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21364) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21364 : oddCount 21364 15 = 8 ∧ acceleratedOrbit 15 21364 = 4283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21364 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21364) = 3 ^ 8 * m + 4283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21364.1, data_15_21364.2]

/-- Complete interval computation for depth 15, residue 21365. -/
theorem bounds_15_21365 : exactInterval 15 21365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21365 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21365) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21365 : oddCount 21365 15 = 8 ∧ acceleratedOrbit 15 21365 = 4283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21365 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21365) = 3 ^ 8 * m + 4283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21365.1, data_15_21365.2]

/-- Complete interval computation for depth 15, residue 21366. -/
theorem bounds_15_21366 : exactInterval 15 21366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21366 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21366) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21366 : oddCount 21366 15 = 9 ∧ acceleratedOrbit 15 21366 = 12838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21366 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21366) = 3 ^ 9 * m + 12838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21366.1, data_15_21366.2]

/-- Complete interval computation for depth 15, residue 21367. -/
theorem bounds_15_21367 : exactInterval 15 21367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21367 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21367) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21367 : oddCount 21367 15 = 9 ∧ acceleratedOrbit 15 21367 = 12838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21367 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21367) = 3 ^ 9 * m + 12838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21367.1, data_15_21367.2]

/-- Complete interval computation for depth 15, residue 21368. -/
theorem bounds_15_21368 : exactInterval 15 21368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21368 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21368) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21368 : oddCount 21368 15 = 9 ∧ acceleratedOrbit 15 21368 = 12842 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21368 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21368) = 3 ^ 9 * m + 12842 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21368.1, data_15_21368.2]

/-- Complete interval computation for depth 15, residue 21369. -/
theorem bounds_15_21369 : exactInterval 15 21369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21369 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21369) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21369 : oddCount 21369 15 = 10 ∧ acceleratedOrbit 15 21369 = 38512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21369 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21369) = 3 ^ 10 * m + 38512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21369.1, data_15_21369.2]

/-- Complete interval computation for depth 15, residue 21370. -/
theorem bounds_15_21370 : exactInterval 15 21370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21370 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21370) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21370 : oddCount 21370 15 = 9 ∧ acceleratedOrbit 15 21370 = 12842 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21370 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21370) = 3 ^ 9 * m + 12842 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21370.1, data_15_21370.2]

/-- Complete interval computation for depth 15, residue 21371. -/
theorem bounds_15_21371 : exactInterval 15 21371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21371 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21371) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21371 : oddCount 21371 15 = 11 ∧ acceleratedOrbit 15 21371 = 115546 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21371 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21371) = 3 ^ 11 * m + 115546 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21371.1, data_15_21371.2]

/-- Complete interval computation for depth 15, residue 21372. -/
theorem bounds_15_21372 : exactInterval 15 21372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21372 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21372) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21372 : oddCount 21372 15 = 9 ∧ acceleratedOrbit 15 21372 = 12842 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21372 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21372) = 3 ^ 9 * m + 12842 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21372.1, data_15_21372.2]

/-- Complete interval computation for depth 15, residue 21373. -/
theorem bounds_15_21373 : exactInterval 15 21373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21373 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21373) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21373 : oddCount 21373 15 = 9 ∧ acceleratedOrbit 15 21373 = 12842 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21373 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21373) = 3 ^ 9 * m + 12842 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21373.1, data_15_21373.2]

/-- Complete interval computation for depth 15, residue 21374. -/
theorem bounds_15_21374 : exactInterval 15 21374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21374 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21374) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21374 : oddCount 21374 15 = 11 ∧ acceleratedOrbit 15 21374 = 115562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21374 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21374) = 3 ^ 11 * m + 115562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21374.1, data_15_21374.2]

/-- Complete interval computation for depth 15, residue 21375. -/
theorem bounds_15_21375 : exactInterval 15 21375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21375 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21375) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21375 : oddCount 21375 15 = 11 ∧ acceleratedOrbit 15 21375 = 115562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21375 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21375) = 3 ^ 11 * m + 115562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21375.1, data_15_21375.2]

/-- Complete interval computation for depth 15, residue 21376. -/
theorem bounds_15_21376 : exactInterval 15 21376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21376 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21376) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21376 : oddCount 21376 15 = 6 ∧ acceleratedOrbit 15 21376 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21376 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21376) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21376.1, data_15_21376.2]

/-- Complete interval computation for depth 15, residue 21377. -/
theorem bounds_15_21377 : exactInterval 15 21377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21377 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21377) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21377 : oddCount 21377 15 = 7 ∧ acceleratedOrbit 15 21377 = 1427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21377 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21377) = 3 ^ 7 * m + 1427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21377.1, data_15_21377.2]

/-- Complete interval computation for depth 15, residue 21378. -/
theorem bounds_15_21378 : exactInterval 15 21378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21378 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21378) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21378 : oddCount 21378 15 = 8 ∧ acceleratedOrbit 15 21378 = 4283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21378 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21378) = 3 ^ 8 * m + 4283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21378.1, data_15_21378.2]

/-- Complete interval computation for depth 15, residue 21379. -/
theorem bounds_15_21379 : exactInterval 15 21379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21379 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21379) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21379 : oddCount 21379 15 = 8 ∧ acceleratedOrbit 15 21379 = 4283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21379 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21379) = 3 ^ 8 * m + 4283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21379.1, data_15_21379.2]

/-- Complete interval computation for depth 15, residue 21380. -/
theorem bounds_15_21380 : exactInterval 15 21380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21380 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21380) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21380 : oddCount 21380 15 = 10 ∧ acceleratedOrbit 15 21380 = 38546 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21380 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21380) = 3 ^ 10 * m + 38546 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21380.1, data_15_21380.2]

/-- Complete interval computation for depth 15, residue 21381. -/
theorem bounds_15_21381 : exactInterval 15 21381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21381 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21381) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21381 : oddCount 21381 15 = 10 ∧ acceleratedOrbit 15 21381 = 38546 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21381 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21381) = 3 ^ 10 * m + 38546 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21381.1, data_15_21381.2]

/-- Complete interval computation for depth 15, residue 21382. -/
theorem bounds_15_21382 : exactInterval 15 21382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21382 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21382) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21382 : oddCount 21382 15 = 10 ∧ acceleratedOrbit 15 21382 = 38546 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21382 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21382) = 3 ^ 10 * m + 38546 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21382.1, data_15_21382.2]

/-- Complete interval computation for depth 15, residue 21383. -/
theorem bounds_15_21383 : exactInterval 15 21383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21383 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21383) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21383 : oddCount 21383 15 = 8 ∧ acceleratedOrbit 15 21383 = 4283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21383 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21383) = 3 ^ 8 * m + 4283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21383.1, data_15_21383.2]

/-- Complete interval computation for depth 15, residue 21384. -/
theorem bounds_15_21384 : exactInterval 15 21384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21384 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21384) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21384 : oddCount 21384 15 = 5 ∧ acceleratedOrbit 15 21384 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21384 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21384) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21384.1, data_15_21384.2]

/-- Complete interval computation for depth 15, residue 21385. -/
theorem bounds_15_21385 : exactInterval 15 21385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21385 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21385) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21385 : oddCount 21385 15 = 9 ∧ acceleratedOrbit 15 21385 = 12847 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21385 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21385) = 3 ^ 9 * m + 12847 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21385.1, data_15_21385.2]

/-- Complete interval computation for depth 15, residue 21386. -/
theorem bounds_15_21386 : exactInterval 15 21386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21386 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21386) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21386 : oddCount 21386 15 = 5 ∧ acceleratedOrbit 15 21386 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21386 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21386) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21386.1, data_15_21386.2]

/-- Complete interval computation for depth 15, residue 21387. -/
theorem bounds_15_21387 : exactInterval 15 21387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21387 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21387) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21387 : oddCount 21387 15 = 10 ∧ acceleratedOrbit 15 21387 = 38546 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21387 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21387) = 3 ^ 10 * m + 38546 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21387.1, data_15_21387.2]

/-- Complete interval computation for depth 15, residue 21388. -/
theorem bounds_15_21388 : exactInterval 15 21388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21388 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21388) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21388 : oddCount 21388 15 = 5 ∧ acceleratedOrbit 15 21388 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21388 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21388) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21388.1, data_15_21388.2]

/-- Complete interval computation for depth 15, residue 21389. -/
theorem bounds_15_21389 : exactInterval 15 21389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21389 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21389) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21389 : oddCount 21389 15 = 5 ∧ acceleratedOrbit 15 21389 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21389 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21389) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21389.1, data_15_21389.2]

/-- Complete interval computation for depth 15, residue 21390. -/
theorem bounds_15_21390 : exactInterval 15 21390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21390 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21390) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21390 : oddCount 21390 15 = 10 ∧ acceleratedOrbit 15 21390 = 38555 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21390 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21390) = 3 ^ 10 * m + 38555 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21390.1, data_15_21390.2]

/-- Complete interval computation for depth 15, residue 21391. -/
theorem bounds_15_21391 : exactInterval 15 21391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21391 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21391) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21391 : oddCount 21391 15 = 10 ∧ acceleratedOrbit 15 21391 = 38555 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21391 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21391) = 3 ^ 10 * m + 38555 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21391.1, data_15_21391.2]

/-- Complete interval computation for depth 15, residue 21392. -/
theorem bounds_15_21392 : exactInterval 15 21392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21392 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21392) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21392 : oddCount 21392 15 = 8 ∧ acceleratedOrbit 15 21392 = 4292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21392 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21392) = 3 ^ 8 * m + 4292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21392.1, data_15_21392.2]

/-- Complete interval computation for depth 15, residue 21393. -/
theorem bounds_15_21393 : exactInterval 15 21393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21393 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21393) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21393 : oddCount 21393 15 = 8 ∧ acceleratedOrbit 15 21393 = 4286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21393 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21393) = 3 ^ 8 * m + 4286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21393.1, data_15_21393.2]

/-- Complete interval computation for depth 15, residue 21394. -/
theorem bounds_15_21394 : exactInterval 15 21394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21394 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21394) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21394 : oddCount 21394 15 = 8 ∧ acceleratedOrbit 15 21394 = 4286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21394 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21394) = 3 ^ 8 * m + 4286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21394.1, data_15_21394.2]

/-- Complete interval computation for depth 15, residue 21395. -/
theorem bounds_15_21395 : exactInterval 15 21395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21395 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21395) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21395 : oddCount 21395 15 = 8 ∧ acceleratedOrbit 15 21395 = 4286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21395 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21395) = 3 ^ 8 * m + 4286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21395.1, data_15_21395.2]

/-- Complete interval computation for depth 15, residue 21396. -/
theorem bounds_15_21396 : exactInterval 15 21396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21396 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21396) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21396 : oddCount 21396 15 = 8 ∧ acceleratedOrbit 15 21396 = 4292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21396 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21396) = 3 ^ 8 * m + 4292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21396.1, data_15_21396.2]

end Collatz.Research.PassageAtlas.Batch0653
