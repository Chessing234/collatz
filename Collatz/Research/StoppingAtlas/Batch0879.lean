import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0879

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6318. -/
theorem bounds_13_6318 : exactInterval 13 6318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6318 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6318) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6318 : oddCount 6318 13 = 5 ∧ acceleratedOrbit 13 6318 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6318 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6318) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6318.1, data_13_6318.2]

/-- Complete interval computation for depth 13, residue 6319. -/
theorem bounds_13_6319 : exactInterval 13 6319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6319 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6319) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6319 : oddCount 6319 13 = 9 ∧ acceleratedOrbit 13 6319 = 15187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6319 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6319) = 3 ^ 9 * m + 15187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6319.1, data_13_6319.2]

/-- Complete interval computation for depth 13, residue 6320. -/
theorem bounds_13_6320 : exactInterval 13 6320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6320 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6320) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6320 : oddCount 6320 13 = 6 ∧ acceleratedOrbit 13 6320 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6320 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6320) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6320.1, data_13_6320.2]

/-- Complete interval computation for depth 13, residue 6321. -/
theorem bounds_13_6321 : exactInterval 13 6321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6321 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6321) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6321 : oddCount 6321 13 = 7 ∧ acceleratedOrbit 13 6321 = 1691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6321 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6321) = 3 ^ 7 * m + 1691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6321.1, data_13_6321.2]

/-- Complete interval computation for depth 13, residue 6322. -/
theorem bounds_13_6322 : exactInterval 13 6322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6322 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6322) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6322 : oddCount 6322 13 = 7 ∧ acceleratedOrbit 13 6322 = 1691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6322 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6322) = 3 ^ 7 * m + 1691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6322.1, data_13_6322.2]

/-- Complete interval computation for depth 13, residue 6323. -/
theorem bounds_13_6323 : exactInterval 13 6323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6323 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6323) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6323 : oddCount 6323 13 = 7 ∧ acceleratedOrbit 13 6323 = 1691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6323 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6323) = 3 ^ 7 * m + 1691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6323.1, data_13_6323.2]

/-- Complete interval computation for depth 13, residue 6324. -/
theorem bounds_13_6324 : exactInterval 13 6324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6324 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6324) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6324 : oddCount 6324 13 = 6 ∧ acceleratedOrbit 13 6324 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6324 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6324) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6324.1, data_13_6324.2]

/-- Complete interval computation for depth 13, residue 6325. -/
theorem bounds_13_6325 : exactInterval 13 6325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6325 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6325) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6325 : oddCount 6325 13 = 6 ∧ acceleratedOrbit 13 6325 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6325 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6325) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6325.1, data_13_6325.2]

/-- Complete interval computation for depth 13, residue 6326. -/
theorem bounds_13_6326 : exactInterval 13 6326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6326 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6326) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6326 : oddCount 6326 13 = 8 ∧ acceleratedOrbit 13 6326 = 5069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6326 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6326) = 3 ^ 8 * m + 5069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6326.1, data_13_6326.2]

/-- Complete interval computation for depth 13, residue 6327. -/
theorem bounds_13_6327 : exactInterval 13 6327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6327 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6327) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6327 : oddCount 6327 13 = 8 ∧ acceleratedOrbit 13 6327 = 5069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6327 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6327) = 3 ^ 8 * m + 5069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6327.1, data_13_6327.2]

/-- Complete interval computation for depth 13, residue 6328. -/
theorem bounds_13_6328 : exactInterval 13 6328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6328 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6328) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6328 : oddCount 6328 13 = 6 ∧ acceleratedOrbit 13 6328 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6328 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6328) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6328.1, data_13_6328.2]

/-- Complete interval computation for depth 13, residue 6329. -/
theorem bounds_13_6329 : exactInterval 13 6329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6329 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6329) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6329 : oddCount 6329 13 = 7 ∧ acceleratedOrbit 13 6329 = 1691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6329 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6329) = 3 ^ 7 * m + 1691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6329.1, data_13_6329.2]

/-- Complete interval computation for depth 13, residue 6330. -/
theorem bounds_13_6330 : exactInterval 13 6330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6330 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6330) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6330 : oddCount 6330 13 = 6 ∧ acceleratedOrbit 13 6330 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6330 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6330) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6330.1, data_13_6330.2]

/-- Complete interval computation for depth 13, residue 6331. -/
theorem bounds_13_6331 : exactInterval 13 6331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6331 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6331) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6331 : oddCount 6331 13 = 9 ∧ acceleratedOrbit 13 6331 = 15218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6331 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6331) = 3 ^ 9 * m + 15218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6331.1, data_13_6331.2]

/-- Complete interval computation for depth 13, residue 6332. -/
theorem bounds_13_6332 : exactInterval 13 6332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6332 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6332) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6332 : oddCount 6332 13 = 9 ∧ acceleratedOrbit 13 6332 = 15227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6332 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6332) = 3 ^ 9 * m + 15227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6332.1, data_13_6332.2]

end Collatz.Research.StoppingAtlas.Batch0879
