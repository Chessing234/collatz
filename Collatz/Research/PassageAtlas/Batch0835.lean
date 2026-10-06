import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0835

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 27328. -/
theorem bounds_15_27328 : exactInterval 15 27328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27328 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27328) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27328 : oddCount 27328 15 = 6 ∧ acceleratedOrbit 15 27328 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27328 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27328) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27328.1, data_15_27328.2]

/-- Complete interval computation for depth 15, residue 27329. -/
theorem bounds_15_27329 : exactInterval 15 27329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27329 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27329) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27329 : oddCount 27329 15 = 7 ∧ acceleratedOrbit 15 27329 = 1826 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27329 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27329) = 3 ^ 7 * m + 1826 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27329.1, data_15_27329.2]

/-- Complete interval computation for depth 15, residue 27330. -/
theorem bounds_15_27330 : exactInterval 15 27330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27330 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27330) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27330 : oddCount 27330 15 = 8 ∧ acceleratedOrbit 15 27330 = 5474 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27330 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27330) = 3 ^ 8 * m + 5474 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27330.1, data_15_27330.2]

/-- Complete interval computation for depth 15, residue 27331. -/
theorem bounds_15_27331 : exactInterval 15 27331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27331 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27331) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27331 : oddCount 27331 15 = 8 ∧ acceleratedOrbit 15 27331 = 5474 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27331 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27331) = 3 ^ 8 * m + 5474 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27331.1, data_15_27331.2]

/-- Complete interval computation for depth 15, residue 27332. -/
theorem bounds_15_27332 : exactInterval 15 27332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27332 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27332) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27332 : oddCount 27332 15 = 5 ∧ acceleratedOrbit 15 27332 = 203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27332 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27332) = 3 ^ 5 * m + 203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27332.1, data_15_27332.2]

/-- Complete interval computation for depth 15, residue 27333. -/
theorem bounds_15_27333 : exactInterval 15 27333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27333 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27333) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27333 : oddCount 27333 15 = 5 ∧ acceleratedOrbit 15 27333 = 203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27333 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27333) = 3 ^ 5 * m + 203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27333.1, data_15_27333.2]

/-- Complete interval computation for depth 15, residue 27334. -/
theorem bounds_15_27334 : exactInterval 15 27334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27334 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27334) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27334 : oddCount 27334 15 = 5 ∧ acceleratedOrbit 15 27334 = 203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27334 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27334) = 3 ^ 5 * m + 203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27334.1, data_15_27334.2]

/-- Complete interval computation for depth 15, residue 27335. -/
theorem bounds_15_27335 : exactInterval 15 27335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27335 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27335) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27335 : oddCount 27335 15 = 8 ∧ acceleratedOrbit 15 27335 = 5474 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27335 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27335) = 3 ^ 8 * m + 5474 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27335.1, data_15_27335.2]

/-- Complete interval computation for depth 15, residue 27336. -/
theorem bounds_15_27336 : exactInterval 15 27336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27336 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27336) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27336 : oddCount 27336 15 = 5 ∧ acceleratedOrbit 15 27336 = 203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27336 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27336) = 3 ^ 5 * m + 203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27336.1, data_15_27336.2]

/-- Complete interval computation for depth 15, residue 27337. -/
theorem bounds_15_27337 : exactInterval 15 27337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27337 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27337) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27337 : oddCount 27337 15 = 7 ∧ acceleratedOrbit 15 27337 = 1826 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27337 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27337) = 3 ^ 7 * m + 1826 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27337.1, data_15_27337.2]

/-- Complete interval computation for depth 15, residue 27338. -/
theorem bounds_15_27338 : exactInterval 15 27338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27338 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27338) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27338 : oddCount 27338 15 = 5 ∧ acceleratedOrbit 15 27338 = 203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27338 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27338) = 3 ^ 5 * m + 203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27338.1, data_15_27338.2]

/-- Complete interval computation for depth 15, residue 27339. -/
theorem bounds_15_27339 : exactInterval 15 27339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27339 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27339) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27339 : oddCount 27339 15 = 7 ∧ acceleratedOrbit 15 27339 = 1825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27339 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27339) = 3 ^ 7 * m + 1825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27339.1, data_15_27339.2]

/-- Complete interval computation for depth 15, residue 27340. -/
theorem bounds_15_27340 : exactInterval 15 27340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27340 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27340) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27340 : oddCount 27340 15 = 5 ∧ acceleratedOrbit 15 27340 = 203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27340 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27340) = 3 ^ 5 * m + 203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27340.1, data_15_27340.2]

/-- Complete interval computation for depth 15, residue 27341. -/
theorem bounds_15_27341 : exactInterval 15 27341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27341 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27341) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27341 : oddCount 27341 15 = 5 ∧ acceleratedOrbit 15 27341 = 203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27341 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27341) = 3 ^ 5 * m + 203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27341.1, data_15_27341.2]

/-- Complete interval computation for depth 15, residue 27342. -/
theorem bounds_15_27342 : exactInterval 15 27342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27342 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27342) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27342 : oddCount 27342 15 = 10 ∧ acceleratedOrbit 15 27342 = 49276 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27342 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27342) = 3 ^ 10 * m + 49276 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27342.1, data_15_27342.2]

/-- Complete interval computation for depth 15, residue 27343. -/
theorem bounds_15_27343 : exactInterval 15 27343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27343 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27343) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27343 : oddCount 27343 15 = 10 ∧ acceleratedOrbit 15 27343 = 49276 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27343 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27343) = 3 ^ 10 * m + 49276 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27343.1, data_15_27343.2]

/-- Complete interval computation for depth 15, residue 27344. -/
theorem bounds_15_27344 : exactInterval 15 27344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27344 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27344) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27344 : oddCount 27344 15 = 6 ∧ acceleratedOrbit 15 27344 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27344 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27344) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27344.1, data_15_27344.2]

/-- Complete interval computation for depth 15, residue 27345. -/
theorem bounds_15_27345 : exactInterval 15 27345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27345 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27345) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27345 : oddCount 27345 15 = 7 ∧ acceleratedOrbit 15 27345 = 1826 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27345 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27345) = 3 ^ 7 * m + 1826 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27345.1, data_15_27345.2]

/-- Complete interval computation for depth 15, residue 27346. -/
theorem bounds_15_27346 : exactInterval 15 27346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27346 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27346) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27346 : oddCount 27346 15 = 7 ∧ acceleratedOrbit 15 27346 = 1826 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27346 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27346) = 3 ^ 7 * m + 1826 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27346.1, data_15_27346.2]

/-- Complete interval computation for depth 15, residue 27347. -/
theorem bounds_15_27347 : exactInterval 15 27347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27347 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27347) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27347 : oddCount 27347 15 = 7 ∧ acceleratedOrbit 15 27347 = 1826 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27347 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27347) = 3 ^ 7 * m + 1826 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27347.1, data_15_27347.2]

/-- Complete interval computation for depth 15, residue 27348. -/
theorem bounds_15_27348 : exactInterval 15 27348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27348 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27348) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27348 : oddCount 27348 15 = 6 ∧ acceleratedOrbit 15 27348 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27348 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27348) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27348.1, data_15_27348.2]

/-- Complete interval computation for depth 15, residue 27349. -/
theorem bounds_15_27349 : exactInterval 15 27349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27349 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27349) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27349 : oddCount 27349 15 = 6 ∧ acceleratedOrbit 15 27349 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27349 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27349) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27349.1, data_15_27349.2]

/-- Complete interval computation for depth 15, residue 27350. -/
theorem bounds_15_27350 : exactInterval 15 27350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27350 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27350) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27350 : oddCount 27350 15 = 9 ∧ acceleratedOrbit 15 27350 = 16433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27350 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27350) = 3 ^ 9 * m + 16433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27350.1, data_15_27350.2]

/-- Complete interval computation for depth 15, residue 27351. -/
theorem bounds_15_27351 : exactInterval 15 27351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27351 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27351) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27351 : oddCount 27351 15 = 9 ∧ acceleratedOrbit 15 27351 = 16433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27351 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27351) = 3 ^ 9 * m + 16433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27351.1, data_15_27351.2]

/-- Complete interval computation for depth 15, residue 27352. -/
theorem bounds_15_27352 : exactInterval 15 27352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27352 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27352) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27352 : oddCount 27352 15 = 8 ∧ acceleratedOrbit 15 27352 = 5480 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27352 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27352) = 3 ^ 8 * m + 5480 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27352.1, data_15_27352.2]

/-- Complete interval computation for depth 15, residue 27353. -/
theorem bounds_15_27353 : exactInterval 15 27353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27353 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27353) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27353 : oddCount 27353 15 = 5 ∧ acceleratedOrbit 15 27353 = 203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27353 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27353) = 3 ^ 5 * m + 203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27353.1, data_15_27353.2]

/-- Complete interval computation for depth 15, residue 27354. -/
theorem bounds_15_27354 : exactInterval 15 27354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27354 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27354) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27354 : oddCount 27354 15 = 8 ∧ acceleratedOrbit 15 27354 = 5480 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27354 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27354) = 3 ^ 8 * m + 5480 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27354.1, data_15_27354.2]

/-- Complete interval computation for depth 15, residue 27355. -/
theorem bounds_15_27355 : exactInterval 15 27355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27355 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27355) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27355 : oddCount 27355 15 = 11 ∧ acceleratedOrbit 15 27355 = 147896 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27355 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27355) = 3 ^ 11 * m + 147896 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27355.1, data_15_27355.2]

/-- Complete interval computation for depth 15, residue 27356. -/
theorem bounds_15_27356 : exactInterval 15 27356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27356 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27356) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27356 : oddCount 27356 15 = 8 ∧ acceleratedOrbit 15 27356 = 5480 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27356 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27356) = 3 ^ 8 * m + 5480 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27356.1, data_15_27356.2]

/-- Complete interval computation for depth 15, residue 27357. -/
theorem bounds_15_27357 : exactInterval 15 27357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27357 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27357) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27357 : oddCount 27357 15 = 8 ∧ acceleratedOrbit 15 27357 = 5480 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27357 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27357) = 3 ^ 8 * m + 5480 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27357.1, data_15_27357.2]

/-- Complete interval computation for depth 15, residue 27358. -/
theorem bounds_15_27358 : exactInterval 15 27358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27358 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27358) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27358 : oddCount 27358 15 = 9 ∧ acceleratedOrbit 15 27358 = 16436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27358 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27358) = 3 ^ 9 * m + 16436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27358.1, data_15_27358.2]

/-- Complete interval computation for depth 15, residue 27359. -/
theorem bounds_15_27359 : exactInterval 15 27359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27359 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27359) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27359 : oddCount 27359 15 = 9 ∧ acceleratedOrbit 15 27359 = 16436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27359 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27359) = 3 ^ 9 * m + 16436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27359.1, data_15_27359.2]

/-- Complete interval computation for depth 15, residue 27360. -/
theorem bounds_15_27360 : exactInterval 15 27360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27360 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27360) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27360 : oddCount 27360 15 = 6 ∧ acceleratedOrbit 15 27360 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27360 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27360) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27360.1, data_15_27360.2]

end Collatz.Research.PassageAtlas.Batch0835
