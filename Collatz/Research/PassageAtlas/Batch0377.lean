import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0377

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 12320. -/
theorem bounds_15_12320 : exactInterval 15 12320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12320 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12320) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12320 : oddCount 12320 15 = 5 ∧ acceleratedOrbit 15 12320 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12320 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12320) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12320.1, data_15_12320.2]

/-- Complete interval computation for depth 15, residue 12321. -/
theorem bounds_15_12321 : exactInterval 15 12321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12321 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12321) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12321 : oddCount 12321 15 = 8 ∧ acceleratedOrbit 15 12321 = 2468 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12321 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12321) = 3 ^ 8 * m + 2468 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12321.1, data_15_12321.2]

/-- Complete interval computation for depth 15, residue 12322. -/
theorem bounds_15_12322 : exactInterval 15 12322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12322 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12322) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12322 : oddCount 12322 15 = 5 ∧ acceleratedOrbit 15 12322 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12322 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12322) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12322.1, data_15_12322.2]

/-- Complete interval computation for depth 15, residue 12323. -/
theorem bounds_15_12323 : exactInterval 15 12323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12323 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12323) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12323 : oddCount 12323 15 = 5 ∧ acceleratedOrbit 15 12323 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12323 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12323) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12323.1, data_15_12323.2]

/-- Complete interval computation for depth 15, residue 12324. -/
theorem bounds_15_12324 : exactInterval 15 12324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12324 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12324) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12324 : oddCount 12324 15 = 8 ∧ acceleratedOrbit 15 12324 = 2470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12324 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12324) = 3 ^ 8 * m + 2470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12324.1, data_15_12324.2]

/-- Complete interval computation for depth 15, residue 12325. -/
theorem bounds_15_12325 : exactInterval 15 12325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12325 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12325) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12325 : oddCount 12325 15 = 8 ∧ acceleratedOrbit 15 12325 = 2470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12325 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12325) = 3 ^ 8 * m + 2470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12325.1, data_15_12325.2]

/-- Complete interval computation for depth 15, residue 12326. -/
theorem bounds_15_12326 : exactInterval 15 12326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12326 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12326) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12326 : oddCount 12326 15 = 8 ∧ acceleratedOrbit 15 12326 = 2470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12326 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12326) = 3 ^ 8 * m + 2470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12326.1, data_15_12326.2]

/-- Complete interval computation for depth 15, residue 12327. -/
theorem bounds_15_12327 : exactInterval 15 12327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12327 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12327) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12327 : oddCount 12327 15 = 10 ∧ acceleratedOrbit 15 12327 = 22220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12327 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12327) = 3 ^ 10 * m + 22220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12327.1, data_15_12327.2]

/-- Complete interval computation for depth 15, residue 12328. -/
theorem bounds_15_12328 : exactInterval 15 12328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12328 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12328) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12328 : oddCount 12328 15 = 5 ∧ acceleratedOrbit 15 12328 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12328 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12328) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12328.1, data_15_12328.2]

/-- Complete interval computation for depth 15, residue 12329. -/
theorem bounds_15_12329 : exactInterval 15 12329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12329 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12329) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12329 : oddCount 12329 15 = 12 ∧ acceleratedOrbit 15 12329 = 199988 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12329 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12329) = 3 ^ 12 * m + 199988 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12329.1, data_15_12329.2]

/-- Complete interval computation for depth 15, residue 12330. -/
theorem bounds_15_12330 : exactInterval 15 12330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12330 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12330) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12330 : oddCount 12330 15 = 5 ∧ acceleratedOrbit 15 12330 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12330 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12330) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12330.1, data_15_12330.2]

/-- Complete interval computation for depth 15, residue 12331. -/
theorem bounds_15_12331 : exactInterval 15 12331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12331 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12331) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12331 : oddCount 12331 15 = 9 ∧ acceleratedOrbit 15 12331 = 7411 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12331 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12331) = 3 ^ 9 * m + 7411 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12331.1, data_15_12331.2]

/-- Complete interval computation for depth 15, residue 12332. -/
theorem bounds_15_12332 : exactInterval 15 12332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12332 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12332) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12332 : oddCount 12332 15 = 5 ∧ acceleratedOrbit 15 12332 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12332 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12332) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12332.1, data_15_12332.2]

/-- Complete interval computation for depth 15, residue 12333. -/
theorem bounds_15_12333 : exactInterval 15 12333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12333 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12333) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12333 : oddCount 12333 15 = 5 ∧ acceleratedOrbit 15 12333 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12333 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12333) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12333.1, data_15_12333.2]

/-- Complete interval computation for depth 15, residue 12334. -/
theorem bounds_15_12334 : exactInterval 15 12334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12334 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12334) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12334 : oddCount 12334 15 = 5 ∧ acceleratedOrbit 15 12334 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12334 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12334) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12334.1, data_15_12334.2]

/-- Complete interval computation for depth 15, residue 12335. -/
theorem bounds_15_12335 : exactInterval 15 12335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12335 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12335) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12335 : oddCount 12335 15 = 10 ∧ acceleratedOrbit 15 12335 = 22231 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12335 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12335) = 3 ^ 10 * m + 22231 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12335.1, data_15_12335.2]

/-- Complete interval computation for depth 15, residue 12336. -/
theorem bounds_15_12336 : exactInterval 15 12336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12336 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12336) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12336 : oddCount 12336 15 = 5 ∧ acceleratedOrbit 15 12336 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12336 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12336) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12336.1, data_15_12336.2]

/-- Complete interval computation for depth 15, residue 12337. -/
theorem bounds_15_12337 : exactInterval 15 12337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12337 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12337) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12337 : oddCount 12337 15 = 7 ∧ acceleratedOrbit 15 12337 = 824 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12337 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12337) = 3 ^ 7 * m + 824 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12337.1, data_15_12337.2]

/-- Complete interval computation for depth 15, residue 12338. -/
theorem bounds_15_12338 : exactInterval 15 12338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12338 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12338) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12338 : oddCount 12338 15 = 7 ∧ acceleratedOrbit 15 12338 = 824 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12338 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12338) = 3 ^ 7 * m + 824 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12338.1, data_15_12338.2]

/-- Complete interval computation for depth 15, residue 12339. -/
theorem bounds_15_12339 : exactInterval 15 12339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12339 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12339) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12339 : oddCount 12339 15 = 7 ∧ acceleratedOrbit 15 12339 = 824 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12339 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12339) = 3 ^ 7 * m + 824 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12339.1, data_15_12339.2]

/-- Complete interval computation for depth 15, residue 12340. -/
theorem bounds_15_12340 : exactInterval 15 12340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12340 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12340) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12340 : oddCount 12340 15 = 5 ∧ acceleratedOrbit 15 12340 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12340 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12340) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12340.1, data_15_12340.2]

/-- Complete interval computation for depth 15, residue 12341. -/
theorem bounds_15_12341 : exactInterval 15 12341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12341 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12341) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12341 : oddCount 12341 15 = 5 ∧ acceleratedOrbit 15 12341 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12341 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12341) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12341.1, data_15_12341.2]

/-- Complete interval computation for depth 15, residue 12342. -/
theorem bounds_15_12342 : exactInterval 15 12342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12342 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12342) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12342 : oddCount 12342 15 = 10 ∧ acceleratedOrbit 15 12342 = 22247 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12342 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12342) = 3 ^ 10 * m + 22247 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12342.1, data_15_12342.2]

/-- Complete interval computation for depth 15, residue 12343. -/
theorem bounds_15_12343 : exactInterval 15 12343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12343 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12343) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12343 : oddCount 12343 15 = 10 ∧ acceleratedOrbit 15 12343 = 22247 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12343 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12343) = 3 ^ 10 * m + 22247 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12343.1, data_15_12343.2]

/-- Complete interval computation for depth 15, residue 12344. -/
theorem bounds_15_12344 : exactInterval 15 12344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12344 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12344) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12344 : oddCount 12344 15 = 6 ∧ acceleratedOrbit 15 12344 = 275 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12344 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12344) = 3 ^ 6 * m + 275 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12344.1, data_15_12344.2]

/-- Complete interval computation for depth 15, residue 12345. -/
theorem bounds_15_12345 : exactInterval 15 12345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12345 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12345) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12345 : oddCount 12345 15 = 8 ∧ acceleratedOrbit 15 12345 = 2474 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12345 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12345) = 3 ^ 8 * m + 2474 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12345.1, data_15_12345.2]

/-- Complete interval computation for depth 15, residue 12346. -/
theorem bounds_15_12346 : exactInterval 15 12346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12346 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12346) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12346 : oddCount 12346 15 = 6 ∧ acceleratedOrbit 15 12346 = 275 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12346 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12346) = 3 ^ 6 * m + 275 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12346.1, data_15_12346.2]

/-- Complete interval computation for depth 15, residue 12347. -/
theorem bounds_15_12347 : exactInterval 15 12347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12347 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12347) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12347 : oddCount 12347 15 = 8 ∧ acceleratedOrbit 15 12347 = 2474 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12347 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12347) = 3 ^ 8 * m + 2474 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12347.1, data_15_12347.2]

/-- Complete interval computation for depth 15, residue 12348. -/
theorem bounds_15_12348 : exactInterval 15 12348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12348 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12348) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12348 : oddCount 12348 15 = 6 ∧ acceleratedOrbit 15 12348 = 275 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12348 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12348) = 3 ^ 6 * m + 275 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12348.1, data_15_12348.2]

/-- Complete interval computation for depth 15, residue 12349. -/
theorem bounds_15_12349 : exactInterval 15 12349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12349 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12349) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12349 : oddCount 12349 15 = 6 ∧ acceleratedOrbit 15 12349 = 275 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12349 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12349) = 3 ^ 6 * m + 275 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12349.1, data_15_12349.2]

/-- Complete interval computation for depth 15, residue 12350. -/
theorem bounds_15_12350 : exactInterval 15 12350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12350 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12350) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12350 : oddCount 12350 15 = 9 ∧ acceleratedOrbit 15 12350 = 7420 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12350 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12350) = 3 ^ 9 * m + 7420 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12350.1, data_15_12350.2]

/-- Complete interval computation for depth 15, residue 12351. -/
theorem bounds_15_12351 : exactInterval 15 12351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12351 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12351) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12351 : oddCount 12351 15 = 9 ∧ acceleratedOrbit 15 12351 = 7420 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12351 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12351) = 3 ^ 9 * m + 7420 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12351.1, data_15_12351.2]

/-- Complete interval computation for depth 15, residue 12352. -/
theorem bounds_15_12352 : exactInterval 15 12352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12352 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12352) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12352 : oddCount 12352 15 = 4 ∧ acceleratedOrbit 15 12352 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12352 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12352) = 3 ^ 4 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12352.1, data_15_12352.2]

end Collatz.Research.PassageAtlas.Batch0377
