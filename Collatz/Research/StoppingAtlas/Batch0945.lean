import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0945

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7331. -/
theorem bounds_13_7331 : exactInterval 13 7331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7331 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7331) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7331 : oddCount 7331 13 = 6 ∧ acceleratedOrbit 13 7331 = 653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7331 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7331) = 3 ^ 6 * m + 653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7331.1, data_13_7331.2]

/-- Complete interval computation for depth 13, residue 7332. -/
theorem bounds_13_7332 : exactInterval 13 7332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7332 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7332) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7332 : oddCount 7332 13 = 6 ∧ acceleratedOrbit 13 7332 = 653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7332 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7332) = 3 ^ 6 * m + 653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7332.1, data_13_7332.2]

/-- Complete interval computation for depth 13, residue 7333. -/
theorem bounds_13_7333 : exactInterval 13 7333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7333 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7333) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7333 : oddCount 7333 13 = 6 ∧ acceleratedOrbit 13 7333 = 653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7333 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7333) = 3 ^ 6 * m + 653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7333.1, data_13_7333.2]

/-- Complete interval computation for depth 13, residue 7334. -/
theorem bounds_13_7334 : exactInterval 13 7334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7334 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7334) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7334 : oddCount 7334 13 = 6 ∧ acceleratedOrbit 13 7334 = 653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7334 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7334) = 3 ^ 6 * m + 653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7334.1, data_13_7334.2]

/-- Complete interval computation for depth 13, residue 7335. -/
theorem bounds_13_7335 : exactInterval 13 7335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7335 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7335) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7335 : oddCount 7335 13 = 10 ∧ acceleratedOrbit 13 7335 = 52883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7335 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7335) = 3 ^ 10 * m + 52883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7335.1, data_13_7335.2]

/-- Complete interval computation for depth 13, residue 7336. -/
theorem bounds_13_7336 : exactInterval 13 7336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7336 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7336) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7336 : oddCount 7336 13 = 4 ∧ acceleratedOrbit 13 7336 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7336 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7336) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7336.1, data_13_7336.2]

/-- Complete interval computation for depth 13, residue 7337. -/
theorem bounds_13_7337 : exactInterval 13 7337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7337 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7337) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7337 : oddCount 7337 13 = 9 ∧ acceleratedOrbit 13 7337 = 17633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7337 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7337) = 3 ^ 9 * m + 17633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7337.1, data_13_7337.2]

/-- Complete interval computation for depth 13, residue 7338. -/
theorem bounds_13_7338 : exactInterval 13 7338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7338 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7338) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7338 : oddCount 7338 13 = 4 ∧ acceleratedOrbit 13 7338 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7338 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7338) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7338.1, data_13_7338.2]

/-- Complete interval computation for depth 13, residue 7339. -/
theorem bounds_13_7339 : exactInterval 13 7339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7339 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7339) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7339 : oddCount 7339 13 = 7 ∧ acceleratedOrbit 13 7339 = 1961 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7339 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7339) = 3 ^ 7 * m + 1961 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7339.1, data_13_7339.2]

/-- Complete interval computation for depth 13, residue 7340. -/
theorem bounds_13_7340 : exactInterval 13 7340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7340 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7340) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7340 : oddCount 7340 13 = 5 ∧ acceleratedOrbit 13 7340 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7340 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7340) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7340.1, data_13_7340.2]

/-- Complete interval computation for depth 13, residue 7341. -/
theorem bounds_13_7341 : exactInterval 13 7341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7341 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7341) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7341 : oddCount 7341 13 = 5 ∧ acceleratedOrbit 13 7341 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7341 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7341) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7341.1, data_13_7341.2]

/-- Complete interval computation for depth 13, residue 7342. -/
theorem bounds_13_7342 : exactInterval 13 7342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7342 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7342) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7342 : oddCount 7342 13 = 5 ∧ acceleratedOrbit 13 7342 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7342 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7342) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7342.1, data_13_7342.2]

/-- Complete interval computation for depth 13, residue 7343. -/
theorem bounds_13_7343 : exactInterval 13 7343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7343 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7343) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7343 : oddCount 7343 13 = 9 ∧ acceleratedOrbit 13 7343 = 17648 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7343 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7343) = 3 ^ 9 * m + 17648 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7343.1, data_13_7343.2]

/-- Complete interval computation for depth 13, residue 7344. -/
theorem bounds_13_7344 : exactInterval 13 7344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7344 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7344) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7344 : oddCount 7344 13 = 4 ∧ acceleratedOrbit 13 7344 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7344 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7344) = 3 ^ 4 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7344.1, data_13_7344.2]

/-- Complete interval computation for depth 13, residue 7345. -/
theorem bounds_13_7345 : exactInterval 13 7345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7345 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7345) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7345 : oddCount 7345 13 = 7 ∧ acceleratedOrbit 13 7345 = 1964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7345 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7345) = 3 ^ 7 * m + 1964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7345.1, data_13_7345.2]

/-- Complete interval computation for depth 13, residue 7346. -/
theorem bounds_13_7346 : exactInterval 13 7346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7346 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7346) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7346 : oddCount 7346 13 = 7 ∧ acceleratedOrbit 13 7346 = 1964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7346 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7346) = 3 ^ 7 * m + 1964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7346.1, data_13_7346.2]

end Collatz.Research.StoppingAtlas.Batch0945
