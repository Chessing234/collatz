import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0285

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 9306. -/
theorem bounds_15_9306 : exactInterval 15 9306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9306 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9306) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9306 : oddCount 9306 15 = 7 ∧ acceleratedOrbit 15 9306 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9306 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9306) = 3 ^ 7 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9306.1, data_15_9306.2]

/-- Complete interval computation for depth 15, residue 9307. -/
theorem bounds_15_9307 : exactInterval 15 9307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9307 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9307) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9307 : oddCount 9307 15 = 10 ∧ acceleratedOrbit 15 9307 = 16775 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9307 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9307) = 3 ^ 10 * m + 16775 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9307.1, data_15_9307.2]

/-- Complete interval computation for depth 15, residue 9308. -/
theorem bounds_15_9308 : exactInterval 15 9308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9308 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9308) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9308 : oddCount 9308 15 = 7 ∧ acceleratedOrbit 15 9308 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9308 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9308) = 3 ^ 7 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9308.1, data_15_9308.2]

/-- Complete interval computation for depth 15, residue 9309. -/
theorem bounds_15_9309 : exactInterval 15 9309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9309 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9309) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9309 : oddCount 9309 15 = 7 ∧ acceleratedOrbit 15 9309 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9309 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9309) = 3 ^ 7 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9309.1, data_15_9309.2]

/-- Complete interval computation for depth 15, residue 9310. -/
theorem bounds_15_9310 : exactInterval 15 9310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9310 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9310) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9310 : oddCount 9310 15 = 9 ∧ acceleratedOrbit 15 9310 = 5594 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9310 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9310) = 3 ^ 9 * m + 5594 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9310.1, data_15_9310.2]

/-- Complete interval computation for depth 15, residue 9311. -/
theorem bounds_15_9311 : exactInterval 15 9311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9311 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9311) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9311 : oddCount 9311 15 = 9 ∧ acceleratedOrbit 15 9311 = 5594 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9311 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9311) = 3 ^ 9 * m + 5594 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9311.1, data_15_9311.2]

/-- Complete interval computation for depth 15, residue 9312. -/
theorem bounds_15_9312 : exactInterval 15 9312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9312 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9312) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9312 : oddCount 9312 15 = 5 ∧ acceleratedOrbit 15 9312 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9312 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9312) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9312.1, data_15_9312.2]

/-- Complete interval computation for depth 15, residue 9313. -/
theorem bounds_15_9313 : exactInterval 15 9313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9313 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9313) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9313 : oddCount 9313 15 = 7 ∧ acceleratedOrbit 15 9313 = 622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9313 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9313) = 3 ^ 7 * m + 622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9313.1, data_15_9313.2]

/-- Complete interval computation for depth 15, residue 9314. -/
theorem bounds_15_9314 : exactInterval 15 9314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9314 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9314) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9314 : oddCount 9314 15 = 7 ∧ acceleratedOrbit 15 9314 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9314 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9314) = 3 ^ 7 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9314.1, data_15_9314.2]

/-- Complete interval computation for depth 15, residue 9315. -/
theorem bounds_15_9315 : exactInterval 15 9315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9315 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9315) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9315 : oddCount 9315 15 = 7 ∧ acceleratedOrbit 15 9315 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9315 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9315) = 3 ^ 7 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9315.1, data_15_9315.2]

/-- Complete interval computation for depth 15, residue 9316. -/
theorem bounds_15_9316 : exactInterval 15 9316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9316 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9316) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9316 : oddCount 9316 15 = 7 ∧ acceleratedOrbit 15 9316 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9316 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9316) = 3 ^ 7 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9316.1, data_15_9316.2]

/-- Complete interval computation for depth 15, residue 9317. -/
theorem bounds_15_9317 : exactInterval 15 9317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9317 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9317) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9317 : oddCount 9317 15 = 7 ∧ acceleratedOrbit 15 9317 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9317 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9317) = 3 ^ 7 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9317.1, data_15_9317.2]

/-- Complete interval computation for depth 15, residue 9318. -/
theorem bounds_15_9318 : exactInterval 15 9318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9318 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9318) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9318 : oddCount 9318 15 = 7 ∧ acceleratedOrbit 15 9318 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9318 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9318) = 3 ^ 7 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9318.1, data_15_9318.2]

/-- Complete interval computation for depth 15, residue 9319. -/
theorem bounds_15_9319 : exactInterval 15 9319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9319 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9319) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9319 : oddCount 9319 15 = 10 ∧ acceleratedOrbit 15 9319 = 16796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9319 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9319) = 3 ^ 10 * m + 16796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9319.1, data_15_9319.2]

/-- Complete interval computation for depth 15, residue 9320. -/
theorem bounds_15_9320 : exactInterval 15 9320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9320 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9320) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9320 : oddCount 9320 15 = 5 ∧ acceleratedOrbit 15 9320 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9320 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9320) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9320.1, data_15_9320.2]

/-- Complete interval computation for depth 15, residue 9321. -/
theorem bounds_15_9321 : exactInterval 15 9321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9321 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9321) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9321 : oddCount 9321 15 = 8 ∧ acceleratedOrbit 15 9321 = 1867 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9321 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9321) = 3 ^ 8 * m + 1867 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9321.1, data_15_9321.2]

/-- Complete interval computation for depth 15, residue 9322. -/
theorem bounds_15_9322 : exactInterval 15 9322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9322 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9322) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9322 : oddCount 9322 15 = 5 ∧ acceleratedOrbit 15 9322 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9322 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9322) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9322.1, data_15_9322.2]

/-- Complete interval computation for depth 15, residue 9323. -/
theorem bounds_15_9323 : exactInterval 15 9323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9323 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9323) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9323 : oddCount 9323 15 = 9 ∧ acceleratedOrbit 15 9323 = 5602 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9323 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9323) = 3 ^ 9 * m + 5602 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9323.1, data_15_9323.2]

/-- Complete interval computation for depth 15, residue 9324. -/
theorem bounds_15_9324 : exactInterval 15 9324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9324 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9324) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9324 : oddCount 9324 15 = 8 ∧ acceleratedOrbit 15 9324 = 1868 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9324 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9324) = 3 ^ 8 * m + 1868 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9324.1, data_15_9324.2]

/-- Complete interval computation for depth 15, residue 9325. -/
theorem bounds_15_9325 : exactInterval 15 9325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9325 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9325) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9325 : oddCount 9325 15 = 8 ∧ acceleratedOrbit 15 9325 = 1868 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9325 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9325) = 3 ^ 8 * m + 1868 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9325.1, data_15_9325.2]

/-- Complete interval computation for depth 15, residue 9326. -/
theorem bounds_15_9326 : exactInterval 15 9326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9326 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9326) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9326 : oddCount 9326 15 = 8 ∧ acceleratedOrbit 15 9326 = 1868 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9326 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9326) = 3 ^ 8 * m + 1868 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9326.1, data_15_9326.2]

/-- Complete interval computation for depth 15, residue 9327. -/
theorem bounds_15_9327 : exactInterval 15 9327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9327 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9327) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9327 : oddCount 9327 15 = 10 ∧ acceleratedOrbit 15 9327 = 16811 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9327 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9327) = 3 ^ 10 * m + 16811 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9327.1, data_15_9327.2]

/-- Complete interval computation for depth 15, residue 9328. -/
theorem bounds_15_9328 : exactInterval 15 9328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9328 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9328) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9328 : oddCount 9328 15 = 6 ∧ acceleratedOrbit 15 9328 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9328 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9328) = 3 ^ 6 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9328.1, data_15_9328.2]

/-- Complete interval computation for depth 15, residue 9329. -/
theorem bounds_15_9329 : exactInterval 15 9329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9329 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9329) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9329 : oddCount 9329 15 = 5 ∧ acceleratedOrbit 15 9329 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9329 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9329) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9329.1, data_15_9329.2]

/-- Complete interval computation for depth 15, residue 9330. -/
theorem bounds_15_9330 : exactInterval 15 9330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9330 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9330) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9330 : oddCount 9330 15 = 9 ∧ acceleratedOrbit 15 9330 = 5609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9330 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9330) = 3 ^ 9 * m + 5609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9330.1, data_15_9330.2]

/-- Complete interval computation for depth 15, residue 9331. -/
theorem bounds_15_9331 : exactInterval 15 9331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9331 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9331) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9331 : oddCount 9331 15 = 9 ∧ acceleratedOrbit 15 9331 = 5609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9331 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9331) = 3 ^ 9 * m + 5609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9331.1, data_15_9331.2]

/-- Complete interval computation for depth 15, residue 9332. -/
theorem bounds_15_9332 : exactInterval 15 9332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9332 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9332) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9332 : oddCount 9332 15 = 6 ∧ acceleratedOrbit 15 9332 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9332 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9332) = 3 ^ 6 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9332.1, data_15_9332.2]

/-- Complete interval computation for depth 15, residue 9333. -/
theorem bounds_15_9333 : exactInterval 15 9333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9333 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9333) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9333 : oddCount 9333 15 = 6 ∧ acceleratedOrbit 15 9333 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9333 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9333) = 3 ^ 6 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9333.1, data_15_9333.2]

/-- Complete interval computation for depth 15, residue 9334. -/
theorem bounds_15_9334 : exactInterval 15 9334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9334 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9334) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9334 : oddCount 9334 15 = 6 ∧ acceleratedOrbit 15 9334 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9334 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9334) = 3 ^ 6 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9334.1, data_15_9334.2]

/-- Complete interval computation for depth 15, residue 9335. -/
theorem bounds_15_9335 : exactInterval 15 9335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9335 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9335) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9335 : oddCount 9335 15 = 6 ∧ acceleratedOrbit 15 9335 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9335 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9335) = 3 ^ 6 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9335.1, data_15_9335.2]

/-- Complete interval computation for depth 15, residue 9336. -/
theorem bounds_15_9336 : exactInterval 15 9336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9336 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9336) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9336 : oddCount 9336 15 = 6 ∧ acceleratedOrbit 15 9336 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9336 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9336) = 3 ^ 6 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9336.1, data_15_9336.2]

/-- Complete interval computation for depth 15, residue 9337. -/
theorem bounds_15_9337 : exactInterval 15 9337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9337 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9337) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9337 : oddCount 9337 15 = 8 ∧ acceleratedOrbit 15 9337 = 1870 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9337 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9337) = 3 ^ 8 * m + 1870 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9337.1, data_15_9337.2]

end Collatz.Research.PassageAtlas.Batch0285
