import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0621

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 20316. -/
theorem bounds_15_20316 : exactInterval 15 20316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20316 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20316) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20316 : oddCount 20316 15 = 8 ∧ acceleratedOrbit 15 20316 = 4070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20316 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20316) = 3 ^ 8 * m + 4070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20316.1, data_15_20316.2]

/-- Complete interval computation for depth 15, residue 20317. -/
theorem bounds_15_20317 : exactInterval 15 20317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20317 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20317) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20317 : oddCount 20317 15 = 8 ∧ acceleratedOrbit 15 20317 = 4070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20317 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20317) = 3 ^ 8 * m + 4070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20317.1, data_15_20317.2]

/-- Complete interval computation for depth 15, residue 20318. -/
theorem bounds_15_20318 : exactInterval 15 20318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20318 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20318) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20318 : oddCount 20318 15 = 8 ∧ acceleratedOrbit 15 20318 = 4070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20318 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20318) = 3 ^ 8 * m + 4070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20318.1, data_15_20318.2]

/-- Complete interval computation for depth 15, residue 20319. -/
theorem bounds_15_20319 : exactInterval 15 20319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20319 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20319) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20319 : oddCount 20319 15 = 8 ∧ acceleratedOrbit 15 20319 = 4070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20319 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20319) = 3 ^ 8 * m + 4070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20319.1, data_15_20319.2]

/-- Complete interval computation for depth 15, residue 20320. -/
theorem bounds_15_20320 : exactInterval 15 20320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20320 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20320) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20320 : oddCount 20320 15 = 5 ∧ acceleratedOrbit 15 20320 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20320 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20320) = 3 ^ 5 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20320.1, data_15_20320.2]

/-- Complete interval computation for depth 15, residue 20321. -/
theorem bounds_15_20321 : exactInterval 15 20321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20321 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20321) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20321 : oddCount 20321 15 = 10 ∧ acceleratedOrbit 15 20321 = 36625 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20321 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20321) = 3 ^ 10 * m + 36625 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20321.1, data_15_20321.2]

/-- Complete interval computation for depth 15, residue 20322. -/
theorem bounds_15_20322 : exactInterval 15 20322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20322 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20322) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20322 : oddCount 20322 15 = 5 ∧ acceleratedOrbit 15 20322 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20322 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20322) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20322.1, data_15_20322.2]

/-- Complete interval computation for depth 15, residue 20323. -/
theorem bounds_15_20323 : exactInterval 15 20323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20323 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20323) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20323 : oddCount 20323 15 = 5 ∧ acceleratedOrbit 15 20323 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20323 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20323) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20323.1, data_15_20323.2]

/-- Complete interval computation for depth 15, residue 20324. -/
theorem bounds_15_20324 : exactInterval 15 20324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20324 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20324) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20324 : oddCount 20324 15 = 5 ∧ acceleratedOrbit 15 20324 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20324 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20324) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20324.1, data_15_20324.2]

/-- Complete interval computation for depth 15, residue 20325. -/
theorem bounds_15_20325 : exactInterval 15 20325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20325 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20325) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20325 : oddCount 20325 15 = 5 ∧ acceleratedOrbit 15 20325 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20325 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20325) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20325.1, data_15_20325.2]

/-- Complete interval computation for depth 15, residue 20326. -/
theorem bounds_15_20326 : exactInterval 15 20326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20326 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20326) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20326 : oddCount 20326 15 = 5 ∧ acceleratedOrbit 15 20326 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20326 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20326) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20326.1, data_15_20326.2]

/-- Complete interval computation for depth 15, residue 20327. -/
theorem bounds_15_20327 : exactInterval 15 20327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20327 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20327) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20327 : oddCount 20327 15 = 12 ∧ acceleratedOrbit 15 20327 = 329690 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20327 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20327) = 3 ^ 12 * m + 329690 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20327.1, data_15_20327.2]

/-- Complete interval computation for depth 15, residue 20328. -/
theorem bounds_15_20328 : exactInterval 15 20328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20328 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20328) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20328 : oddCount 20328 15 = 5 ∧ acceleratedOrbit 15 20328 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20328 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20328) = 3 ^ 5 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20328.1, data_15_20328.2]

/-- Complete interval computation for depth 15, residue 20329. -/
theorem bounds_15_20329 : exactInterval 15 20329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20329 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20329) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20329 : oddCount 20329 15 = 7 ∧ acceleratedOrbit 15 20329 = 1357 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20329 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20329) = 3 ^ 7 * m + 1357 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20329.1, data_15_20329.2]

/-- Complete interval computation for depth 15, residue 20330. -/
theorem bounds_15_20330 : exactInterval 15 20330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20330 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20330) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20330 : oddCount 20330 15 = 5 ∧ acceleratedOrbit 15 20330 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20330 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20330) = 3 ^ 5 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20330.1, data_15_20330.2]

/-- Complete interval computation for depth 15, residue 20331. -/
theorem bounds_15_20331 : exactInterval 15 20331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20331 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20331) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20331 : oddCount 20331 15 = 8 ∧ acceleratedOrbit 15 20331 = 4072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20331 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20331) = 3 ^ 8 * m + 4072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20331.1, data_15_20331.2]

/-- Complete interval computation for depth 15, residue 20332. -/
theorem bounds_15_20332 : exactInterval 15 20332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20332 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20332) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20332 : oddCount 20332 15 = 7 ∧ acceleratedOrbit 15 20332 = 1358 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20332 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20332) = 3 ^ 7 * m + 1358 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20332.1, data_15_20332.2]

/-- Complete interval computation for depth 15, residue 20333. -/
theorem bounds_15_20333 : exactInterval 15 20333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20333 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20333) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20333 : oddCount 20333 15 = 7 ∧ acceleratedOrbit 15 20333 = 1358 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20333 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20333) = 3 ^ 7 * m + 1358 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20333.1, data_15_20333.2]

/-- Complete interval computation for depth 15, residue 20334. -/
theorem bounds_15_20334 : exactInterval 15 20334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20334 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20334) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20334 : oddCount 20334 15 = 7 ∧ acceleratedOrbit 15 20334 = 1358 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20334 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20334) = 3 ^ 7 * m + 1358 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20334.1, data_15_20334.2]

/-- Complete interval computation for depth 15, residue 20335. -/
theorem bounds_15_20335 : exactInterval 15 20335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20335 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20335) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20335 : oddCount 20335 15 = 11 ∧ acceleratedOrbit 15 20335 = 109943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20335 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20335) = 3 ^ 11 * m + 109943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20335.1, data_15_20335.2]

/-- Complete interval computation for depth 15, residue 20336. -/
theorem bounds_15_20336 : exactInterval 15 20336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20336 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20336) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20336 : oddCount 20336 15 = 5 ∧ acceleratedOrbit 15 20336 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20336 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20336) = 3 ^ 5 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20336.1, data_15_20336.2]

/-- Complete interval computation for depth 15, residue 20337. -/
theorem bounds_15_20337 : exactInterval 15 20337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20337 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20337) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20337 : oddCount 20337 15 = 5 ∧ acceleratedOrbit 15 20337 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20337 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20337) = 3 ^ 5 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20337.1, data_15_20337.2]

/-- Complete interval computation for depth 15, residue 20338. -/
theorem bounds_15_20338 : exactInterval 15 20338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20338 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20338) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20338 : oddCount 20338 15 = 8 ∧ acceleratedOrbit 15 20338 = 4076 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20338 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20338) = 3 ^ 8 * m + 4076 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20338.1, data_15_20338.2]

/-- Complete interval computation for depth 15, residue 20339. -/
theorem bounds_15_20339 : exactInterval 15 20339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20339 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20339) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20339 : oddCount 20339 15 = 8 ∧ acceleratedOrbit 15 20339 = 4076 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20339 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20339) = 3 ^ 8 * m + 4076 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20339.1, data_15_20339.2]

/-- Complete interval computation for depth 15, residue 20340. -/
theorem bounds_15_20340 : exactInterval 15 20340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20340 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20340) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20340 : oddCount 20340 15 = 5 ∧ acceleratedOrbit 15 20340 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20340 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20340) = 3 ^ 5 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20340.1, data_15_20340.2]

/-- Complete interval computation for depth 15, residue 20341. -/
theorem bounds_15_20341 : exactInterval 15 20341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20341 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20341) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20341 : oddCount 20341 15 = 5 ∧ acceleratedOrbit 15 20341 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20341 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20341) = 3 ^ 5 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20341.1, data_15_20341.2]

/-- Complete interval computation for depth 15, residue 20342. -/
theorem bounds_15_20342 : exactInterval 15 20342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20342 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20342) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20342 : oddCount 20342 15 = 8 ∧ acceleratedOrbit 15 20342 = 4076 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20342 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20342) = 3 ^ 8 * m + 4076 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20342.1, data_15_20342.2]

/-- Complete interval computation for depth 15, residue 20343. -/
theorem bounds_15_20343 : exactInterval 15 20343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20343 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20343) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20343 : oddCount 20343 15 = 8 ∧ acceleratedOrbit 15 20343 = 4076 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20343 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20343) = 3 ^ 8 * m + 4076 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20343.1, data_15_20343.2]

/-- Complete interval computation for depth 15, residue 20344. -/
theorem bounds_15_20344 : exactInterval 15 20344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20344 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20344) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20344 : oddCount 20344 15 = 9 ∧ acceleratedOrbit 15 20344 = 12226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20344 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20344) = 3 ^ 9 * m + 12226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20344.1, data_15_20344.2]

/-- Complete interval computation for depth 15, residue 20345. -/
theorem bounds_15_20345 : exactInterval 15 20345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20345 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20345) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20345 : oddCount 20345 15 = 7 ∧ acceleratedOrbit 15 20345 = 1358 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20345 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20345) = 3 ^ 7 * m + 1358 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20345.1, data_15_20345.2]

/-- Complete interval computation for depth 15, residue 20346. -/
theorem bounds_15_20346 : exactInterval 15 20346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20346 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20346) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20346 : oddCount 20346 15 = 9 ∧ acceleratedOrbit 15 20346 = 12226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20346 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20346) = 3 ^ 9 * m + 12226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20346.1, data_15_20346.2]

/-- Complete interval computation for depth 15, residue 20347. -/
theorem bounds_15_20347 : exactInterval 15 20347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20347 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20347) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20347 : oddCount 20347 15 = 9 ∧ acceleratedOrbit 15 20347 = 12224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20347 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20347) = 3 ^ 9 * m + 12224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20347.1, data_15_20347.2]

end Collatz.Research.PassageAtlas.Batch0621
