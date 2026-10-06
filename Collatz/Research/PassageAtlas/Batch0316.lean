import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0316

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 10321. -/
theorem bounds_15_10321 : exactInterval 15 10321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10321 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10321) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10321 : oddCount 10321 15 = 8 ∧ acceleratedOrbit 15 10321 = 2069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10321 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10321) = 3 ^ 8 * m + 2069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10321.1, data_15_10321.2]

/-- Complete interval computation for depth 15, residue 10322. -/
theorem bounds_15_10322 : exactInterval 15 10322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10322 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10322) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10322 : oddCount 10322 15 = 9 ∧ acceleratedOrbit 15 10322 = 6203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10322 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10322) = 3 ^ 9 * m + 6203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10322.1, data_15_10322.2]

/-- Complete interval computation for depth 15, residue 10323. -/
theorem bounds_15_10323 : exactInterval 15 10323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10323 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10323) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10323 : oddCount 10323 15 = 9 ∧ acceleratedOrbit 15 10323 = 6203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10323 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10323) = 3 ^ 9 * m + 6203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10323.1, data_15_10323.2]

/-- Complete interval computation for depth 15, residue 10324. -/
theorem bounds_15_10324 : exactInterval 15 10324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10324 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10324) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10324 : oddCount 10324 15 = 6 ∧ acceleratedOrbit 15 10324 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10324 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10324) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10324.1, data_15_10324.2]

/-- Complete interval computation for depth 15, residue 10325. -/
theorem bounds_15_10325 : exactInterval 15 10325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10325 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10325) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10325 : oddCount 10325 15 = 6 ∧ acceleratedOrbit 15 10325 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10325 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10325) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10325.1, data_15_10325.2]

/-- Complete interval computation for depth 15, residue 10326. -/
theorem bounds_15_10326 : exactInterval 15 10326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10326 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10326) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10326 : oddCount 10326 15 = 6 ∧ acceleratedOrbit 15 10326 = 230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10326 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10326) = 3 ^ 6 * m + 230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10326.1, data_15_10326.2]

/-- Complete interval computation for depth 15, residue 10327. -/
theorem bounds_15_10327 : exactInterval 15 10327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10327 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10327) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10327 : oddCount 10327 15 = 6 ∧ acceleratedOrbit 15 10327 = 230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10327 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10327) = 3 ^ 6 * m + 230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10327.1, data_15_10327.2]

/-- Complete interval computation for depth 15, residue 10328. -/
theorem bounds_15_10328 : exactInterval 15 10328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10328 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10328) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10328 : oddCount 10328 15 = 7 ∧ acceleratedOrbit 15 10328 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10328 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10328) = 3 ^ 7 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10328.1, data_15_10328.2]

/-- Complete interval computation for depth 15, residue 10329. -/
theorem bounds_15_10329 : exactInterval 15 10329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10329 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10329) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10329 : oddCount 10329 15 = 6 ∧ acceleratedOrbit 15 10329 = 230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10329 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10329) = 3 ^ 6 * m + 230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10329.1, data_15_10329.2]

/-- Complete interval computation for depth 15, residue 10330. -/
theorem bounds_15_10330 : exactInterval 15 10330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10330 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10330) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10330 : oddCount 10330 15 = 7 ∧ acceleratedOrbit 15 10330 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10330 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10330) = 3 ^ 7 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10330.1, data_15_10330.2]

/-- Complete interval computation for depth 15, residue 10331. -/
theorem bounds_15_10331 : exactInterval 15 10331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10331 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10331) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10331 : oddCount 10331 15 = 12 ∧ acceleratedOrbit 15 10331 = 167579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10331 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10331) = 3 ^ 12 * m + 167579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10331.1, data_15_10331.2]

/-- Complete interval computation for depth 15, residue 10332. -/
theorem bounds_15_10332 : exactInterval 15 10332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10332 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10332) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10332 : oddCount 10332 15 = 7 ∧ acceleratedOrbit 15 10332 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10332 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10332) = 3 ^ 7 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10332.1, data_15_10332.2]

/-- Complete interval computation for depth 15, residue 10333. -/
theorem bounds_15_10333 : exactInterval 15 10333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10333 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10333) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10333 : oddCount 10333 15 = 7 ∧ acceleratedOrbit 15 10333 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10333 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10333) = 3 ^ 7 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10333.1, data_15_10333.2]

/-- Complete interval computation for depth 15, residue 10334. -/
theorem bounds_15_10334 : exactInterval 15 10334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10334 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10334) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10334 : oddCount 10334 15 = 10 ∧ acceleratedOrbit 15 10334 = 18629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10334 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10334) = 3 ^ 10 * m + 18629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10334.1, data_15_10334.2]

/-- Complete interval computation for depth 15, residue 10335. -/
theorem bounds_15_10335 : exactInterval 15 10335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10335 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10335) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10335 : oddCount 10335 15 = 10 ∧ acceleratedOrbit 15 10335 = 18629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10335 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10335) = 3 ^ 10 * m + 18629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10335.1, data_15_10335.2]

/-- Complete interval computation for depth 15, residue 10336. -/
theorem bounds_15_10336 : exactInterval 15 10336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10336 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10336) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10336 : oddCount 10336 15 = 6 ∧ acceleratedOrbit 15 10336 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10336 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10336) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10336.1, data_15_10336.2]

/-- Complete interval computation for depth 15, residue 10337. -/
theorem bounds_15_10337 : exactInterval 15 10337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10337 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10337) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10337 : oddCount 10337 15 = 9 ∧ acceleratedOrbit 15 10337 = 6212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10337 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10337) = 3 ^ 9 * m + 6212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10337.1, data_15_10337.2]

/-- Complete interval computation for depth 15, residue 10338. -/
theorem bounds_15_10338 : exactInterval 15 10338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10338 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10338) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10338 : oddCount 10338 15 = 7 ∧ acceleratedOrbit 15 10338 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10338 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10338) = 3 ^ 7 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10338.1, data_15_10338.2]

/-- Complete interval computation for depth 15, residue 10339. -/
theorem bounds_15_10339 : exactInterval 15 10339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10339 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10339) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10339 : oddCount 10339 15 = 7 ∧ acceleratedOrbit 15 10339 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10339 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10339) = 3 ^ 7 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10339.1, data_15_10339.2]

/-- Complete interval computation for depth 15, residue 10340. -/
theorem bounds_15_10340 : exactInterval 15 10340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10340 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10340) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10340 : oddCount 10340 15 = 7 ∧ acceleratedOrbit 15 10340 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10340 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10340) = 3 ^ 7 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10340.1, data_15_10340.2]

/-- Complete interval computation for depth 15, residue 10341. -/
theorem bounds_15_10341 : exactInterval 15 10341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10341 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10341) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10341 : oddCount 10341 15 = 7 ∧ acceleratedOrbit 15 10341 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10341 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10341) = 3 ^ 7 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10341.1, data_15_10341.2]

/-- Complete interval computation for depth 15, residue 10342. -/
theorem bounds_15_10342 : exactInterval 15 10342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10342 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10342) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10342 : oddCount 10342 15 = 7 ∧ acceleratedOrbit 15 10342 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10342 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10342) = 3 ^ 7 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10342.1, data_15_10342.2]

/-- Complete interval computation for depth 15, residue 10343. -/
theorem bounds_15_10343 : exactInterval 15 10343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10343 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10343) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10343 : oddCount 10343 15 = 10 ∧ acceleratedOrbit 15 10343 = 18641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10343 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10343) = 3 ^ 10 * m + 18641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10343.1, data_15_10343.2]

/-- Complete interval computation for depth 15, residue 10344. -/
theorem bounds_15_10344 : exactInterval 15 10344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10344 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10344) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10344 : oddCount 10344 15 = 6 ∧ acceleratedOrbit 15 10344 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10344 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10344) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10344.1, data_15_10344.2]

/-- Complete interval computation for depth 15, residue 10345. -/
theorem bounds_15_10345 : exactInterval 15 10345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10345 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10345) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10345 : oddCount 10345 15 = 8 ∧ acceleratedOrbit 15 10345 = 2072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10345 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10345) = 3 ^ 8 * m + 2072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10345.1, data_15_10345.2]

/-- Complete interval computation for depth 15, residue 10346. -/
theorem bounds_15_10346 : exactInterval 15 10346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10346 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10346) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10346 : oddCount 10346 15 = 6 ∧ acceleratedOrbit 15 10346 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10346 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10346) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10346.1, data_15_10346.2]

/-- Complete interval computation for depth 15, residue 10347. -/
theorem bounds_15_10347 : exactInterval 15 10347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10347 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10347) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10347 : oddCount 10347 15 = 10 ∧ acceleratedOrbit 15 10347 = 18650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10347 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10347) = 3 ^ 10 * m + 18650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10347.1, data_15_10347.2]

/-- Complete interval computation for depth 15, residue 10348. -/
theorem bounds_15_10348 : exactInterval 15 10348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10348 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10348) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10348 : oddCount 10348 15 = 7 ∧ acceleratedOrbit 15 10348 = 691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10348 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10348) = 3 ^ 7 * m + 691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10348.1, data_15_10348.2]

/-- Complete interval computation for depth 15, residue 10349. -/
theorem bounds_15_10349 : exactInterval 15 10349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10349 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10349) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10349 : oddCount 10349 15 = 7 ∧ acceleratedOrbit 15 10349 = 691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10349 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10349) = 3 ^ 7 * m + 691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10349.1, data_15_10349.2]

/-- Complete interval computation for depth 15, residue 10350. -/
theorem bounds_15_10350 : exactInterval 15 10350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10350 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10350) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10350 : oddCount 10350 15 = 7 ∧ acceleratedOrbit 15 10350 = 691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10350 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10350) = 3 ^ 7 * m + 691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10350.1, data_15_10350.2]

/-- Complete interval computation for depth 15, residue 10351. -/
theorem bounds_15_10351 : exactInterval 15 10351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10351 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10351) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10351 : oddCount 10351 15 = 11 ∧ acceleratedOrbit 15 10351 = 55966 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10351 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10351) = 3 ^ 11 * m + 55966 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10351.1, data_15_10351.2]

/-- Complete interval computation for depth 15, residue 10352. -/
theorem bounds_15_10352 : exactInterval 15 10352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10352 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10352) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10352 : oddCount 10352 15 = 5 ∧ acceleratedOrbit 15 10352 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10352 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10352) = 3 ^ 5 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10352.1, data_15_10352.2]

/-- Complete interval computation for depth 15, residue 10353. -/
theorem bounds_15_10353 : exactInterval 15 10353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10353 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10353) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10353 : oddCount 10353 15 = 6 ∧ acceleratedOrbit 15 10353 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10353 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10353) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10353.1, data_15_10353.2]

end Collatz.Research.PassageAtlas.Batch0316
