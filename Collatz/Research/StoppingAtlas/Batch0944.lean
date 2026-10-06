import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0944

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7316. -/
theorem bounds_13_7316 : exactInterval 13 7316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7316 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7316) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7316 : oddCount 7316 13 = 5 ∧ acceleratedOrbit 13 7316 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7316 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7316) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7316.1, data_13_7316.2]

/-- Complete interval computation for depth 13, residue 7317. -/
theorem bounds_13_7317 : exactInterval 13 7317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7317 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7317) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7317 : oddCount 7317 13 = 5 ∧ acceleratedOrbit 13 7317 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7317 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7317) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7317.1, data_13_7317.2]

/-- Complete interval computation for depth 13, residue 7318. -/
theorem bounds_13_7318 : exactInterval 13 7318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7318 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7318) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7318 : oddCount 7318 13 = 5 ∧ acceleratedOrbit 13 7318 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7318 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7318) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7318.1, data_13_7318.2]

/-- Complete interval computation for depth 13, residue 7319. -/
theorem bounds_13_7319 : exactInterval 13 7319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7319 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7319) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7319 : oddCount 7319 13 = 5 ∧ acceleratedOrbit 13 7319 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7319 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7319) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7319.1, data_13_7319.2]

/-- Complete interval computation for depth 13, residue 7320. -/
theorem bounds_13_7320 : exactInterval 13 7320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7320 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7320) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7320 : oddCount 7320 13 = 5 ∧ acceleratedOrbit 13 7320 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7320 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7320) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7320.1, data_13_7320.2]

/-- Complete interval computation for depth 13, residue 7321. -/
theorem bounds_13_7321 : exactInterval 13 7321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7321 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7321) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7321 : oddCount 7321 13 = 6 ∧ acceleratedOrbit 13 7321 = 652 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7321 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7321) = 3 ^ 6 * m + 652 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7321.1, data_13_7321.2]

/-- Complete interval computation for depth 13, residue 7322. -/
theorem bounds_13_7322 : exactInterval 13 7322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7322 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7322) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7322 : oddCount 7322 13 = 5 ∧ acceleratedOrbit 13 7322 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7322 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7322) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7322.1, data_13_7322.2]

/-- Complete interval computation for depth 13, residue 7323. -/
theorem bounds_13_7323 : exactInterval 13 7323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7323 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7323) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7323 : oddCount 7323 13 = 9 ∧ acceleratedOrbit 13 7323 = 17599 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7323 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7323) = 3 ^ 9 * m + 17599 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7323.1, data_13_7323.2]

/-- Complete interval computation for depth 13, residue 7324. -/
theorem bounds_13_7324 : exactInterval 13 7324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7324 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7324) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7324 : oddCount 7324 13 = 7 ∧ acceleratedOrbit 13 7324 = 1957 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7324 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7324) = 3 ^ 7 * m + 1957 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7324.1, data_13_7324.2]

/-- Complete interval computation for depth 13, residue 7325. -/
theorem bounds_13_7325 : exactInterval 13 7325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7325 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7325) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7325 : oddCount 7325 13 = 7 ∧ acceleratedOrbit 13 7325 = 1957 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7325 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7325) = 3 ^ 7 * m + 1957 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7325.1, data_13_7325.2]

/-- Complete interval computation for depth 13, residue 7326. -/
theorem bounds_13_7326 : exactInterval 13 7326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7326 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7326) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7326 : oddCount 7326 13 = 7 ∧ acceleratedOrbit 13 7326 = 1957 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7326 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7326) = 3 ^ 7 * m + 1957 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7326.1, data_13_7326.2]

/-- Complete interval computation for depth 13, residue 7327. -/
theorem bounds_13_7327 : exactInterval 13 7327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7327 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7327) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7327 : oddCount 7327 13 = 10 ∧ acceleratedOrbit 13 7327 = 52822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7327 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7327) = 3 ^ 10 * m + 52822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7327.1, data_13_7327.2]

/-- Complete interval computation for depth 13, residue 7328. -/
theorem bounds_13_7328 : exactInterval 13 7328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7328 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7328) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7328 : oddCount 7328 13 = 4 ∧ acceleratedOrbit 13 7328 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7328 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7328) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7328.1, data_13_7328.2]

/-- Complete interval computation for depth 13, residue 7329. -/
theorem bounds_13_7329 : exactInterval 13 7329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7329 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7329) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7329 : oddCount 7329 13 = 9 ∧ acceleratedOrbit 13 7329 = 17617 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7329 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7329) = 3 ^ 9 * m + 17617 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7329.1, data_13_7329.2]

/-- Complete interval computation for depth 13, residue 7330. -/
theorem bounds_13_7330 : exactInterval 13 7330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7330 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7330) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7330 : oddCount 7330 13 = 6 ∧ acceleratedOrbit 13 7330 = 653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7330 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7330) = 3 ^ 6 * m + 653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7330.1, data_13_7330.2]

end Collatz.Research.StoppingAtlas.Batch0944
