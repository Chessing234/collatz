import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0352

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2319. -/
theorem bounds_12_2319 : exactInterval 12 2319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2319 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2319) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2319 : oddCount 2319 12 = 7 ∧ acceleratedOrbit 12 2319 = 1241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2319 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2319) = 3 ^ 7 * m + 1241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2319.1, data_12_2319.2]

/-- Complete interval computation for depth 12, residue 2320. -/
theorem bounds_12_2320 : exactInterval 12 2320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2320 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2320) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2320 : oddCount 2320 12 = 4 ∧ acceleratedOrbit 12 2320 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2320 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2320) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2320.1, data_12_2320.2]

/-- Complete interval computation for depth 12, residue 2321. -/
theorem bounds_12_2321 : exactInterval 12 2321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2321 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2321) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2321 : oddCount 2321 12 = 4 ∧ acceleratedOrbit 12 2321 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2321 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2321) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2321.1, data_12_2321.2]

/-- Complete interval computation for depth 12, residue 2322. -/
theorem bounds_12_2322 : exactInterval 12 2322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2322 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2322) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2322 : oddCount 2322 12 = 9 ∧ acceleratedOrbit 12 2322 = 11177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2322 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2322) = 3 ^ 9 * m + 11177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2322.1, data_12_2322.2]

/-- Complete interval computation for depth 12, residue 2323. -/
theorem bounds_12_2323 : exactInterval 12 2323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2323 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2323) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2323 : oddCount 2323 12 = 9 ∧ acceleratedOrbit 12 2323 = 11177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2323 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2323) = 3 ^ 9 * m + 11177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2323.1, data_12_2323.2]

/-- Complete interval computation for depth 12, residue 2324. -/
theorem bounds_12_2324 : exactInterval 12 2324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2324 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2324) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2324 : oddCount 2324 12 = 4 ∧ acceleratedOrbit 12 2324 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2324 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2324) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2324.1, data_12_2324.2]

/-- Complete interval computation for depth 12, residue 2325. -/
theorem bounds_12_2325 : exactInterval 12 2325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2325 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2325) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2325 : oddCount 2325 12 = 4 ∧ acceleratedOrbit 12 2325 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2325 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2325) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2325.1, data_12_2325.2]

/-- Complete interval computation for depth 12, residue 2326. -/
theorem bounds_12_2326 : exactInterval 12 2326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2326 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2326) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2326 : oddCount 2326 12 = 6 ∧ acceleratedOrbit 12 2326 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2326 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2326) = 3 ^ 6 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2326.1, data_12_2326.2]

/-- Complete interval computation for depth 12, residue 2327. -/
theorem bounds_12_2327 : exactInterval 12 2327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2327 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2327) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2327 : oddCount 2327 12 = 6 ∧ acceleratedOrbit 12 2327 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2327 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2327) = 3 ^ 6 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2327.1, data_12_2327.2]

/-- Complete interval computation for depth 12, residue 2328. -/
theorem bounds_12_2328 : exactInterval 12 2328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2328 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2328) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2328 : oddCount 2328 12 = 4 ∧ acceleratedOrbit 12 2328 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2328 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2328) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2328.1, data_12_2328.2]

/-- Complete interval computation for depth 12, residue 2329. -/
theorem bounds_12_2329 : exactInterval 12 2329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2329 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2329) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2329 : oddCount 2329 12 = 6 ∧ acceleratedOrbit 12 2329 = 415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2329 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2329) = 3 ^ 6 * m + 415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2329.1, data_12_2329.2]

/-- Complete interval computation for depth 12, residue 2330. -/
theorem bounds_12_2330 : exactInterval 12 2330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2330 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2330) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2330 : oddCount 2330 12 = 4 ∧ acceleratedOrbit 12 2330 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2330 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2330) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2330.1, data_12_2330.2]

/-- Complete interval computation for depth 12, residue 2331. -/
theorem bounds_12_2331 : exactInterval 12 2331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2331 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2331) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2331 : oddCount 2331 12 = 8 ∧ acceleratedOrbit 12 2331 = 3736 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2331 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2331) = 3 ^ 8 * m + 3736 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2331.1, data_12_2331.2]

/-- Complete interval computation for depth 12, residue 2332. -/
theorem bounds_12_2332 : exactInterval 12 2332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2332 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2332) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2332 : oddCount 2332 12 = 6 ∧ acceleratedOrbit 12 2332 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2332 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2332) = 3 ^ 6 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2332.1, data_12_2332.2]

/-- Complete interval computation for depth 12, residue 2333. -/
theorem bounds_12_2333 : exactInterval 12 2333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2333 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2333) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2333 : oddCount 2333 12 = 6 ∧ acceleratedOrbit 12 2333 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2333 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2333) = 3 ^ 6 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2333.1, data_12_2333.2]

end Collatz.Research.StoppingAtlas.Batch0352
