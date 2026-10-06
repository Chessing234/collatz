import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0560

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 18317. -/
theorem bounds_15_18317 : exactInterval 15 18317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18317 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18317) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18317 : oddCount 18317 15 = 5 ∧ acceleratedOrbit 15 18317 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18317 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18317) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18317.1, data_15_18317.2]

/-- Complete interval computation for depth 15, residue 18318. -/
theorem bounds_15_18318 : exactInterval 15 18318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18318 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18318) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18318 : oddCount 18318 15 = 9 ∧ acceleratedOrbit 15 18318 = 11006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18318 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18318) = 3 ^ 9 * m + 11006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18318.1, data_15_18318.2]

/-- Complete interval computation for depth 15, residue 18319. -/
theorem bounds_15_18319 : exactInterval 15 18319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18319 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18319) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18319 : oddCount 18319 15 = 9 ∧ acceleratedOrbit 15 18319 = 11006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18319 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18319) = 3 ^ 9 * m + 11006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18319.1, data_15_18319.2]

/-- Complete interval computation for depth 15, residue 18320. -/
theorem bounds_15_18320 : exactInterval 15 18320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18320 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18320) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18320 : oddCount 18320 15 = 7 ∧ acceleratedOrbit 15 18320 = 1225 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18320 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18320) = 3 ^ 7 * m + 1225 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18320.1, data_15_18320.2]

/-- Complete interval computation for depth 15, residue 18321. -/
theorem bounds_15_18321 : exactInterval 15 18321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18321 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18321) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18321 : oddCount 18321 15 = 8 ∧ acceleratedOrbit 15 18321 = 3671 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18321 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18321) = 3 ^ 8 * m + 3671 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18321.1, data_15_18321.2]

/-- Complete interval computation for depth 15, residue 18322. -/
theorem bounds_15_18322 : exactInterval 15 18322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18322 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18322) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18322 : oddCount 18322 15 = 8 ∧ acceleratedOrbit 15 18322 = 3671 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18322 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18322) = 3 ^ 8 * m + 3671 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18322.1, data_15_18322.2]

/-- Complete interval computation for depth 15, residue 18323. -/
theorem bounds_15_18323 : exactInterval 15 18323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18323 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18323) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18323 : oddCount 18323 15 = 8 ∧ acceleratedOrbit 15 18323 = 3671 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18323 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18323) = 3 ^ 8 * m + 3671 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18323.1, data_15_18323.2]

/-- Complete interval computation for depth 15, residue 18324. -/
theorem bounds_15_18324 : exactInterval 15 18324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18324 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18324) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18324 : oddCount 18324 15 = 7 ∧ acceleratedOrbit 15 18324 = 1225 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18324 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18324) = 3 ^ 7 * m + 1225 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18324.1, data_15_18324.2]

/-- Complete interval computation for depth 15, residue 18325. -/
theorem bounds_15_18325 : exactInterval 15 18325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18325 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18325) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18325 : oddCount 18325 15 = 7 ∧ acceleratedOrbit 15 18325 = 1225 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18325 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18325) = 3 ^ 7 * m + 1225 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18325.1, data_15_18325.2]

/-- Complete interval computation for depth 15, residue 18326. -/
theorem bounds_15_18326 : exactInterval 15 18326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18326 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18326) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18326 : oddCount 18326 15 = 5 ∧ acceleratedOrbit 15 18326 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18326 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18326) = 3 ^ 5 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18326.1, data_15_18326.2]

/-- Complete interval computation for depth 15, residue 18327. -/
theorem bounds_15_18327 : exactInterval 15 18327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18327 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18327) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18327 : oddCount 18327 15 = 5 ∧ acceleratedOrbit 15 18327 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18327 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18327) = 3 ^ 5 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18327.1, data_15_18327.2]

/-- Complete interval computation for depth 15, residue 18328. -/
theorem bounds_15_18328 : exactInterval 15 18328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18328 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18328) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18328 : oddCount 18328 15 = 7 ∧ acceleratedOrbit 15 18328 = 1225 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18328 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18328) = 3 ^ 7 * m + 1225 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18328.1, data_15_18328.2]

/-- Complete interval computation for depth 15, residue 18329. -/
theorem bounds_15_18329 : exactInterval 15 18329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18329 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18329) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18329 : oddCount 18329 15 = 5 ∧ acceleratedOrbit 15 18329 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18329 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18329) = 3 ^ 5 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18329.1, data_15_18329.2]

/-- Complete interval computation for depth 15, residue 18330. -/
theorem bounds_15_18330 : exactInterval 15 18330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18330 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18330) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18330 : oddCount 18330 15 = 7 ∧ acceleratedOrbit 15 18330 = 1225 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18330 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18330) = 3 ^ 7 * m + 1225 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18330.1, data_15_18330.2]

/-- Complete interval computation for depth 15, residue 18331. -/
theorem bounds_15_18331 : exactInterval 15 18331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18331 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18331) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18331 : oddCount 18331 15 = 10 ∧ acceleratedOrbit 15 18331 = 33038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18331 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18331) = 3 ^ 10 * m + 33038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18331.1, data_15_18331.2]

/-- Complete interval computation for depth 15, residue 18332. -/
theorem bounds_15_18332 : exactInterval 15 18332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18332 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18332) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18332 : oddCount 18332 15 = 10 ∧ acceleratedOrbit 15 18332 = 33047 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18332 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18332) = 3 ^ 10 * m + 33047 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18332.1, data_15_18332.2]

/-- Complete interval computation for depth 15, residue 18333. -/
theorem bounds_15_18333 : exactInterval 15 18333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18333 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18333) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18333 : oddCount 18333 15 = 10 ∧ acceleratedOrbit 15 18333 = 33047 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18333 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18333) = 3 ^ 10 * m + 33047 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18333.1, data_15_18333.2]

/-- Complete interval computation for depth 15, residue 18334. -/
theorem bounds_15_18334 : exactInterval 15 18334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18334 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18334) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18334 : oddCount 18334 15 = 10 ∧ acceleratedOrbit 15 18334 = 33047 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18334 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18334) = 3 ^ 10 * m + 33047 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18334.1, data_15_18334.2]

/-- Complete interval computation for depth 15, residue 18335. -/
theorem bounds_15_18335 : exactInterval 15 18335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18335 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18335) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18335 : oddCount 18335 15 = 10 ∧ acceleratedOrbit 15 18335 = 33043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18335 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18335) = 3 ^ 10 * m + 33043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18335.1, data_15_18335.2]

/-- Complete interval computation for depth 15, residue 18336. -/
theorem bounds_15_18336 : exactInterval 15 18336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18336 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18336) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18336 : oddCount 18336 15 = 5 ∧ acceleratedOrbit 15 18336 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18336 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18336) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18336.1, data_15_18336.2]

/-- Complete interval computation for depth 15, residue 18337. -/
theorem bounds_15_18337 : exactInterval 15 18337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18337 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18337) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18337 : oddCount 18337 15 = 5 ∧ acceleratedOrbit 15 18337 = 136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18337 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18337) = 3 ^ 5 * m + 136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18337.1, data_15_18337.2]

/-- Complete interval computation for depth 15, residue 18338. -/
theorem bounds_15_18338 : exactInterval 15 18338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18338 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18338) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18338 : oddCount 18338 15 = 7 ∧ acceleratedOrbit 15 18338 = 1225 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18338 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18338) = 3 ^ 7 * m + 1225 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18338.1, data_15_18338.2]

/-- Complete interval computation for depth 15, residue 18339. -/
theorem bounds_15_18339 : exactInterval 15 18339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18339 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18339) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18339 : oddCount 18339 15 = 7 ∧ acceleratedOrbit 15 18339 = 1225 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18339 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18339) = 3 ^ 7 * m + 1225 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18339.1, data_15_18339.2]

/-- Complete interval computation for depth 15, residue 18340. -/
theorem bounds_15_18340 : exactInterval 15 18340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18340 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18340) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18340 : oddCount 18340 15 = 8 ∧ acceleratedOrbit 15 18340 = 3674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18340 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18340) = 3 ^ 8 * m + 3674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18340.1, data_15_18340.2]

/-- Complete interval computation for depth 15, residue 18341. -/
theorem bounds_15_18341 : exactInterval 15 18341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18341 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18341) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18341 : oddCount 18341 15 = 8 ∧ acceleratedOrbit 15 18341 = 3674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18341 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18341) = 3 ^ 8 * m + 3674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18341.1, data_15_18341.2]

/-- Complete interval computation for depth 15, residue 18342. -/
theorem bounds_15_18342 : exactInterval 15 18342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18342 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18342) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18342 : oddCount 18342 15 = 8 ∧ acceleratedOrbit 15 18342 = 3674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18342 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18342) = 3 ^ 8 * m + 3674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18342.1, data_15_18342.2]

/-- Complete interval computation for depth 15, residue 18343. -/
theorem bounds_15_18343 : exactInterval 15 18343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18343 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18343) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18343 : oddCount 18343 15 = 10 ∧ acceleratedOrbit 15 18343 = 33058 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18343 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18343) = 3 ^ 10 * m + 33058 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18343.1, data_15_18343.2]

/-- Complete interval computation for depth 15, residue 18344. -/
theorem bounds_15_18344 : exactInterval 15 18344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18344 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18344) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18344 : oddCount 18344 15 = 5 ∧ acceleratedOrbit 15 18344 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18344 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18344) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18344.1, data_15_18344.2]

/-- Complete interval computation for depth 15, residue 18345. -/
theorem bounds_15_18345 : exactInterval 15 18345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18345 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18345) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18345 : oddCount 18345 15 = 12 ∧ acceleratedOrbit 15 18345 = 297553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18345 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18345) = 3 ^ 12 * m + 297553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18345.1, data_15_18345.2]

/-- Complete interval computation for depth 15, residue 18346. -/
theorem bounds_15_18346 : exactInterval 15 18346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18346 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18346) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18346 : oddCount 18346 15 = 5 ∧ acceleratedOrbit 15 18346 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18346 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18346) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18346.1, data_15_18346.2]

/-- Complete interval computation for depth 15, residue 18347. -/
theorem bounds_15_18347 : exactInterval 15 18347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18347 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18347) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18347 : oddCount 18347 15 = 10 ∧ acceleratedOrbit 15 18347 = 33068 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18347 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18347) = 3 ^ 10 * m + 33068 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18347.1, data_15_18347.2]

/-- Complete interval computation for depth 15, residue 18348. -/
theorem bounds_15_18348 : exactInterval 15 18348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18348 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18348) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18348 : oddCount 18348 15 = 9 ∧ acceleratedOrbit 15 18348 = 11026 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18348 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18348) = 3 ^ 9 * m + 11026 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18348.1, data_15_18348.2]

/-- Complete interval computation for depth 15, residue 18349. -/
theorem bounds_15_18349 : exactInterval 15 18349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18349 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18349) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18349 : oddCount 18349 15 = 9 ∧ acceleratedOrbit 15 18349 = 11026 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18349 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18349) = 3 ^ 9 * m + 11026 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18349.1, data_15_18349.2]

end Collatz.Research.PassageAtlas.Batch0560
