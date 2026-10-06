import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0749

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4321. -/
theorem bounds_13_4321 : exactInterval 13 4321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4321 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4321) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4321 : oddCount 4321 13 = 9 ∧ acceleratedOrbit 13 4321 = 10388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4321 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4321) = 3 ^ 9 * m + 10388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4321.1, data_13_4321.2]

/-- Complete interval computation for depth 13, residue 4322. -/
theorem bounds_13_4322 : exactInterval 13 4322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4322 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4322) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4322 : oddCount 4322 13 = 4 ∧ acceleratedOrbit 13 4322 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4322 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4322) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4322.1, data_13_4322.2]

/-- Complete interval computation for depth 13, residue 4323. -/
theorem bounds_13_4323 : exactInterval 13 4323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4323 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4323) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4323 : oddCount 4323 13 = 4 ∧ acceleratedOrbit 13 4323 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4323 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4323) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4323.1, data_13_4323.2]

/-- Complete interval computation for depth 13, residue 4324. -/
theorem bounds_13_4324 : exactInterval 13 4324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4324 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4324) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4324 : oddCount 4324 13 = 6 ∧ acceleratedOrbit 13 4324 = 386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4324 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4324) = 3 ^ 6 * m + 386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4324.1, data_13_4324.2]

/-- Complete interval computation for depth 13, residue 4325. -/
theorem bounds_13_4325 : exactInterval 13 4325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4325 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4325) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4325 : oddCount 4325 13 = 6 ∧ acceleratedOrbit 13 4325 = 386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4325 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4325) = 3 ^ 6 * m + 386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4325.1, data_13_4325.2]

/-- Complete interval computation for depth 13, residue 4326. -/
theorem bounds_13_4326 : exactInterval 13 4326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4326 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4326) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4326 : oddCount 4326 13 = 6 ∧ acceleratedOrbit 13 4326 = 386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4326 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4326) = 3 ^ 6 * m + 386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4326.1, data_13_4326.2]

/-- Complete interval computation for depth 13, residue 4327. -/
theorem bounds_13_4327 : exactInterval 13 4327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4327 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4327) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4327 : oddCount 4327 13 = 8 ∧ acceleratedOrbit 13 4327 = 3467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4327 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4327) = 3 ^ 8 * m + 3467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4327.1, data_13_4327.2]

/-- Complete interval computation for depth 13, residue 4328. -/
theorem bounds_13_4328 : exactInterval 13 4328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4328 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4328) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4328 : oddCount 4328 13 = 4 ∧ acceleratedOrbit 13 4328 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4328 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4328) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4328.1, data_13_4328.2]

/-- Complete interval computation for depth 13, residue 4329. -/
theorem bounds_13_4329 : exactInterval 13 4329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4329 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4329) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4329 : oddCount 4329 13 = 8 ∧ acceleratedOrbit 13 4329 = 3469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4329 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4329) = 3 ^ 8 * m + 3469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4329.1, data_13_4329.2]

/-- Complete interval computation for depth 13, residue 4330. -/
theorem bounds_13_4330 : exactInterval 13 4330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4330 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4330) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4330 : oddCount 4330 13 = 4 ∧ acceleratedOrbit 13 4330 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4330 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4330) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4330.1, data_13_4330.2]

/-- Complete interval computation for depth 13, residue 4331. -/
theorem bounds_13_4331 : exactInterval 13 4331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4331 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4331) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4331 : oddCount 4331 13 = 9 ∧ acceleratedOrbit 13 4331 = 10412 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4331 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4331) = 3 ^ 9 * m + 10412 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4331.1, data_13_4331.2]

/-- Complete interval computation for depth 13, residue 4332. -/
theorem bounds_13_4332 : exactInterval 13 4332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4332 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4332) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4332 : oddCount 4332 13 = 7 ∧ acceleratedOrbit 13 4332 = 1160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4332 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4332) = 3 ^ 7 * m + 1160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4332.1, data_13_4332.2]

/-- Complete interval computation for depth 13, residue 4333. -/
theorem bounds_13_4333 : exactInterval 13 4333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4333 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4333) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4333 : oddCount 4333 13 = 7 ∧ acceleratedOrbit 13 4333 = 1160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4333 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4333) = 3 ^ 7 * m + 1160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4333.1, data_13_4333.2]

/-- Complete interval computation for depth 13, residue 4334. -/
theorem bounds_13_4334 : exactInterval 13 4334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4334 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4334) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4334 : oddCount 4334 13 = 7 ∧ acceleratedOrbit 13 4334 = 1160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4334 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4334) = 3 ^ 7 * m + 1160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4334.1, data_13_4334.2]

/-- Complete interval computation for depth 13, residue 4335. -/
theorem bounds_13_4335 : exactInterval 13 4335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4335 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4335) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4335 : oddCount 4335 13 = 10 ∧ acceleratedOrbit 13 4335 = 31256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4335 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4335) = 3 ^ 10 * m + 31256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4335.1, data_13_4335.2]

end Collatz.Research.StoppingAtlas.Batch0749
