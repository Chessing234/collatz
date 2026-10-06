import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0620

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2339. -/
theorem bounds_13_2339 : exactInterval 13 2339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2339 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2339) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2339 : oddCount 2339 13 = 6 ∧ acceleratedOrbit 13 2339 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2339 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2339) = 3 ^ 6 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2339.1, data_13_2339.2]

/-- Complete interval computation for depth 13, residue 2340. -/
theorem bounds_13_2340 : exactInterval 13 2340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2340 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2340) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2340 : oddCount 2340 13 = 6 ∧ acceleratedOrbit 13 2340 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2340 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2340) = 3 ^ 6 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2340.1, data_13_2340.2]

/-- Complete interval computation for depth 13, residue 2341. -/
theorem bounds_13_2341 : exactInterval 13 2341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2341 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2341) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2341 : oddCount 2341 13 = 6 ∧ acceleratedOrbit 13 2341 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2341 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2341) = 3 ^ 6 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2341.1, data_13_2341.2]

/-- Complete interval computation for depth 13, residue 2342. -/
theorem bounds_13_2342 : exactInterval 13 2342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2342 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2342) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2342 : oddCount 2342 13 = 6 ∧ acceleratedOrbit 13 2342 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2342 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2342) = 3 ^ 6 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2342.1, data_13_2342.2]

/-- Complete interval computation for depth 13, residue 2343. -/
theorem bounds_13_2343 : exactInterval 13 2343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2343 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2343) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2343 : oddCount 2343 13 = 7 ∧ acceleratedOrbit 13 2343 = 626 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2343 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2343) = 3 ^ 7 * m + 626 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2343.1, data_13_2343.2]

/-- Complete interval computation for depth 13, residue 2344. -/
theorem bounds_13_2344 : exactInterval 13 2344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2344 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2344) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2344 : oddCount 2344 13 = 5 ∧ acceleratedOrbit 13 2344 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2344 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2344) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2344.1, data_13_2344.2]

/-- Complete interval computation for depth 13, residue 2345. -/
theorem bounds_13_2345 : exactInterval 13 2345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2345 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2345) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2345 : oddCount 2345 13 = 8 ∧ acceleratedOrbit 13 2345 = 1880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2345 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2345) = 3 ^ 8 * m + 1880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2345.1, data_13_2345.2]

/-- Complete interval computation for depth 13, residue 2346. -/
theorem bounds_13_2346 : exactInterval 13 2346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2346 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2346) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2346 : oddCount 2346 13 = 5 ∧ acceleratedOrbit 13 2346 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2346 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2346) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2346.1, data_13_2346.2]

/-- Complete interval computation for depth 13, residue 2347. -/
theorem bounds_13_2347 : exactInterval 13 2347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2347 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2347) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2347 : oddCount 2347 13 = 8 ∧ acceleratedOrbit 13 2347 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2347 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2347) = 3 ^ 8 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2347.1, data_13_2347.2]

/-- Complete interval computation for depth 13, residue 2348. -/
theorem bounds_13_2348 : exactInterval 13 2348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2348 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2348) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2348 : oddCount 2348 13 = 5 ∧ acceleratedOrbit 13 2348 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2348 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2348) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2348.1, data_13_2348.2]

/-- Complete interval computation for depth 13, residue 2349. -/
theorem bounds_13_2349 : exactInterval 13 2349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2349 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2349) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2349 : oddCount 2349 13 = 5 ∧ acceleratedOrbit 13 2349 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2349 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2349) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2349.1, data_13_2349.2]

/-- Complete interval computation for depth 13, residue 2350. -/
theorem bounds_13_2350 : exactInterval 13 2350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2350 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2350) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2350 : oddCount 2350 13 = 5 ∧ acceleratedOrbit 13 2350 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2350 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2350) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2350.1, data_13_2350.2]

/-- Complete interval computation for depth 13, residue 2351. -/
theorem bounds_13_2351 : exactInterval 13 2351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2351 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2351) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2351 : oddCount 2351 13 = 7 ∧ acceleratedOrbit 13 2351 = 628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2351 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2351) = 3 ^ 7 * m + 628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2351.1, data_13_2351.2]

/-- Complete interval computation for depth 13, residue 2352. -/
theorem bounds_13_2352 : exactInterval 13 2352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2352 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2352) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2352 : oddCount 2352 13 = 5 ∧ acceleratedOrbit 13 2352 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2352 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2352) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2352.1, data_13_2352.2]

/-- Complete interval computation for depth 13, residue 2353. -/
theorem bounds_13_2353 : exactInterval 13 2353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2353 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2353) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2353 : oddCount 2353 13 = 5 ∧ acceleratedOrbit 13 2353 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2353 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2353) = 3 ^ 5 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2353.1, data_13_2353.2]

/-- Complete interval computation for depth 13, residue 2354. -/
theorem bounds_13_2354 : exactInterval 13 2354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2354 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2354) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2354 : oddCount 2354 13 = 5 ∧ acceleratedOrbit 13 2354 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2354 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2354) = 3 ^ 5 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2354.1, data_13_2354.2]

end Collatz.Research.StoppingAtlas.Batch0620
