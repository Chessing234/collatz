import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0814

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5319. -/
theorem bounds_13_5319 : exactInterval 13 5319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5319 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5319) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5319 : oddCount 5319 13 = 7 ∧ acceleratedOrbit 13 5319 = 1421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5319 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5319) = 3 ^ 7 * m + 1421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5319.1, data_13_5319.2]

/-- Complete interval computation for depth 13, residue 5320. -/
theorem bounds_13_5320 : exactInterval 13 5320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5320 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5320) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5320 : oddCount 5320 13 = 6 ∧ acceleratedOrbit 13 5320 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5320 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5320) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5320.1, data_13_5320.2]

/-- Complete interval computation for depth 13, residue 5321. -/
theorem bounds_13_5321 : exactInterval 13 5321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5321 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5321) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5321 : oddCount 5321 13 = 5 ∧ acceleratedOrbit 13 5321 = 158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5321 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5321) = 3 ^ 5 * m + 158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5321.1, data_13_5321.2]

/-- Complete interval computation for depth 13, residue 5322. -/
theorem bounds_13_5322 : exactInterval 13 5322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5322 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5322) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5322 : oddCount 5322 13 = 6 ∧ acceleratedOrbit 13 5322 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5322 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5322) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5322.1, data_13_5322.2]

/-- Complete interval computation for depth 13, residue 5323. -/
theorem bounds_13_5323 : exactInterval 13 5323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5323 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5323) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5323 : oddCount 5323 13 = 5 ∧ acceleratedOrbit 13 5323 = 158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5323 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5323) = 3 ^ 5 * m + 158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5323.1, data_13_5323.2]

/-- Complete interval computation for depth 13, residue 5324. -/
theorem bounds_13_5324 : exactInterval 13 5324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5324 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5324) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5324 : oddCount 5324 13 = 6 ∧ acceleratedOrbit 13 5324 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5324 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5324) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5324.1, data_13_5324.2]

/-- Complete interval computation for depth 13, residue 5325. -/
theorem bounds_13_5325 : exactInterval 13 5325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5325 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5325) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5325 : oddCount 5325 13 = 6 ∧ acceleratedOrbit 13 5325 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5325 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5325) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5325.1, data_13_5325.2]

/-- Complete interval computation for depth 13, residue 5326. -/
theorem bounds_13_5326 : exactInterval 13 5326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5326 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5326) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5326 : oddCount 5326 13 = 8 ∧ acceleratedOrbit 13 5326 = 4268 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5326 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5326) = 3 ^ 8 * m + 4268 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5326.1, data_13_5326.2]

/-- Complete interval computation for depth 13, residue 5327. -/
theorem bounds_13_5327 : exactInterval 13 5327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5327 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5327) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5327 : oddCount 5327 13 = 8 ∧ acceleratedOrbit 13 5327 = 4268 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5327 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5327) = 3 ^ 8 * m + 4268 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5327.1, data_13_5327.2]

/-- Complete interval computation for depth 13, residue 5328. -/
theorem bounds_13_5328 : exactInterval 13 5328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5328 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5328) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5328 : oddCount 5328 13 = 5 ∧ acceleratedOrbit 13 5328 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5328 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5328) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5328.1, data_13_5328.2]

/-- Complete interval computation for depth 13, residue 5329. -/
theorem bounds_13_5329 : exactInterval 13 5329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5329 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5329) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5329 : oddCount 5329 13 = 7 ∧ acceleratedOrbit 13 5329 = 1424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5329 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5329) = 3 ^ 7 * m + 1424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5329.1, data_13_5329.2]

/-- Complete interval computation for depth 13, residue 5330. -/
theorem bounds_13_5330 : exactInterval 13 5330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5330 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5330) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5330 : oddCount 5330 13 = 7 ∧ acceleratedOrbit 13 5330 = 1424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5330 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5330) = 3 ^ 7 * m + 1424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5330.1, data_13_5330.2]

/-- Complete interval computation for depth 13, residue 5331. -/
theorem bounds_13_5331 : exactInterval 13 5331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5331 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5331) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5331 : oddCount 5331 13 = 7 ∧ acceleratedOrbit 13 5331 = 1424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5331 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5331) = 3 ^ 7 * m + 1424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5331.1, data_13_5331.2]

/-- Complete interval computation for depth 13, residue 5332. -/
theorem bounds_13_5332 : exactInterval 13 5332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5332 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5332) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5332 : oddCount 5332 13 = 5 ∧ acceleratedOrbit 13 5332 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5332 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5332) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5332.1, data_13_5332.2]

/-- Complete interval computation for depth 13, residue 5333. -/
theorem bounds_13_5333 : exactInterval 13 5333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5333 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5333) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5333 : oddCount 5333 13 = 5 ∧ acceleratedOrbit 13 5333 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5333 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5333) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5333.1, data_13_5333.2]

/-- Complete interval computation for depth 13, residue 5334. -/
theorem bounds_13_5334 : exactInterval 13 5334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5334 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5334) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5334 : oddCount 5334 13 = 6 ∧ acceleratedOrbit 13 5334 = 475 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5334 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5334) = 3 ^ 6 * m + 475 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5334.1, data_13_5334.2]

end Collatz.Research.StoppingAtlas.Batch0814
