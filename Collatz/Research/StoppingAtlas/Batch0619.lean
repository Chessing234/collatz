import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0619

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2324. -/
theorem bounds_13_2324 : exactInterval 13 2324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2324 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2324) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2324 : oddCount 2324 13 = 5 ∧ acceleratedOrbit 13 2324 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2324 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2324) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2324.1, data_13_2324.2]

/-- Complete interval computation for depth 13, residue 2325. -/
theorem bounds_13_2325 : exactInterval 13 2325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2325 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2325) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2325 : oddCount 2325 13 = 5 ∧ acceleratedOrbit 13 2325 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2325 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2325) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2325.1, data_13_2325.2]

/-- Complete interval computation for depth 13, residue 2326. -/
theorem bounds_13_2326 : exactInterval 13 2326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2326 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2326) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2326 : oddCount 2326 13 = 7 ∧ acceleratedOrbit 13 2326 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2326 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2326) = 3 ^ 7 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2326.1, data_13_2326.2]

/-- Complete interval computation for depth 13, residue 2327. -/
theorem bounds_13_2327 : exactInterval 13 2327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2327 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2327) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2327 : oddCount 2327 13 = 7 ∧ acceleratedOrbit 13 2327 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2327 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2327) = 3 ^ 7 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2327.1, data_13_2327.2]

/-- Complete interval computation for depth 13, residue 2328. -/
theorem bounds_13_2328 : exactInterval 13 2328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2328 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2328) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2328 : oddCount 2328 13 = 5 ∧ acceleratedOrbit 13 2328 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2328 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2328) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2328.1, data_13_2328.2]

/-- Complete interval computation for depth 13, residue 2329. -/
theorem bounds_13_2329 : exactInterval 13 2329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2329 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2329) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2329 : oddCount 2329 13 = 7 ∧ acceleratedOrbit 13 2329 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2329 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2329) = 3 ^ 7 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2329.1, data_13_2329.2]

/-- Complete interval computation for depth 13, residue 2330. -/
theorem bounds_13_2330 : exactInterval 13 2330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2330 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2330) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2330 : oddCount 2330 13 = 5 ∧ acceleratedOrbit 13 2330 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2330 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2330) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2330.1, data_13_2330.2]

/-- Complete interval computation for depth 13, residue 2331. -/
theorem bounds_13_2331 : exactInterval 13 2331 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2331 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2331) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2331 : oddCount 2331 13 = 8 ∧ acceleratedOrbit 13 2331 = 1868 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2331 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2331) = 3 ^ 8 * m + 1868 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2331.1, data_13_2331.2]

/-- Complete interval computation for depth 13, residue 2332. -/
theorem bounds_13_2332 : exactInterval 13 2332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2332 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2332) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2332 : oddCount 2332 13 = 6 ∧ acceleratedOrbit 13 2332 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2332 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2332) = 3 ^ 6 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2332.1, data_13_2332.2]

/-- Complete interval computation for depth 13, residue 2333. -/
theorem bounds_13_2333 : exactInterval 13 2333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2333 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2333) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2333 : oddCount 2333 13 = 6 ∧ acceleratedOrbit 13 2333 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2333 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2333) = 3 ^ 6 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2333.1, data_13_2333.2]

/-- Complete interval computation for depth 13, residue 2334. -/
theorem bounds_13_2334 : exactInterval 13 2334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2334 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2334) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2334 : oddCount 2334 13 = 6 ∧ acceleratedOrbit 13 2334 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2334 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2334) = 3 ^ 6 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2334.1, data_13_2334.2]

/-- Complete interval computation for depth 13, residue 2335. -/
theorem bounds_13_2335 : exactInterval 13 2335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2335 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2335) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2335 : oddCount 2335 13 = 9 ∧ acceleratedOrbit 13 2335 = 5615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2335 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2335) = 3 ^ 9 * m + 5615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2335.1, data_13_2335.2]

/-- Complete interval computation for depth 13, residue 2336. -/
theorem bounds_13_2336 : exactInterval 13 2336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2336 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2336) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2336 : oddCount 2336 13 = 5 ∧ acceleratedOrbit 13 2336 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2336 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2336) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2336.1, data_13_2336.2]

/-- Complete interval computation for depth 13, residue 2337. -/
theorem bounds_13_2337 : exactInterval 13 2337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2337 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2337) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2337 : oddCount 2337 13 = 6 ∧ acceleratedOrbit 13 2337 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2337 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2337) = 3 ^ 6 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2337.1, data_13_2337.2]

/-- Complete interval computation for depth 13, residue 2338. -/
theorem bounds_13_2338 : exactInterval 13 2338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2338 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2338) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2338 : oddCount 2338 13 = 6 ∧ acceleratedOrbit 13 2338 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2338 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2338) = 3 ^ 6 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2338.1, data_13_2338.2]

end Collatz.Research.StoppingAtlas.Batch0619
