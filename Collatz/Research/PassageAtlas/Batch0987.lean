import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0987

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 32309. -/
theorem bounds_15_32309 : exactInterval 15 32309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32309 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32309) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32309 : oddCount 32309 15 = 5 ∧ acceleratedOrbit 15 32309 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32309 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32309) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32309.1, data_15_32309.2]

/-- Complete interval computation for depth 15, residue 32310. -/
theorem bounds_15_32310 : exactInterval 15 32310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32310 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32310) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32310 : oddCount 32310 15 = 12 ∧ acceleratedOrbit 15 32310 = 524060 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32310 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32310) = 3 ^ 12 * m + 524060 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32310.1, data_15_32310.2]

/-- Complete interval computation for depth 15, residue 32311. -/
theorem bounds_15_32311 : exactInterval 15 32311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32311 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32311) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32311 : oddCount 32311 15 = 12 ∧ acceleratedOrbit 15 32311 = 524060 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32311 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32311) = 3 ^ 12 * m + 524060 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32311.1, data_15_32311.2]

/-- Complete interval computation for depth 15, residue 32312. -/
theorem bounds_15_32312 : exactInterval 15 32312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32312 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32312) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32312 : oddCount 32312 15 = 8 ∧ acceleratedOrbit 15 32312 = 6473 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32312 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32312) = 3 ^ 8 * m + 6473 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32312.1, data_15_32312.2]

/-- Complete interval computation for depth 15, residue 32313. -/
theorem bounds_15_32313 : exactInterval 15 32313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32313 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32313) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32313 : oddCount 32313 15 = 10 ∧ acceleratedOrbit 15 32313 = 58238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32313 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32313) = 3 ^ 10 * m + 58238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32313.1, data_15_32313.2]

/-- Complete interval computation for depth 15, residue 32314. -/
theorem bounds_15_32314 : exactInterval 15 32314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32314 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32314) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32314 : oddCount 32314 15 = 8 ∧ acceleratedOrbit 15 32314 = 6473 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32314 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32314) = 3 ^ 8 * m + 6473 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32314.1, data_15_32314.2]

/-- Complete interval computation for depth 15, residue 32315. -/
theorem bounds_15_32315 : exactInterval 15 32315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32315 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32315) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32315 : oddCount 32315 15 = 6 ∧ acceleratedOrbit 15 32315 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32315 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32315) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32315.1, data_15_32315.2]

/-- Complete interval computation for depth 15, residue 32316. -/
theorem bounds_15_32316 : exactInterval 15 32316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32316 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32316) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32316 : oddCount 32316 15 = 8 ∧ acceleratedOrbit 15 32316 = 6473 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32316 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32316) = 3 ^ 8 * m + 6473 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32316.1, data_15_32316.2]

/-- Complete interval computation for depth 15, residue 32317. -/
theorem bounds_15_32317 : exactInterval 15 32317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32317 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32317) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32317 : oddCount 32317 15 = 8 ∧ acceleratedOrbit 15 32317 = 6473 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32317 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32317) = 3 ^ 8 * m + 6473 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32317.1, data_15_32317.2]

/-- Complete interval computation for depth 15, residue 32318. -/
theorem bounds_15_32318 : exactInterval 15 32318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32318 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32318) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32318 : oddCount 32318 15 = 9 ∧ acceleratedOrbit 15 32318 = 19415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32318 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32318) = 3 ^ 9 * m + 19415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32318.1, data_15_32318.2]

/-- Complete interval computation for depth 15, residue 32319. -/
theorem bounds_15_32319 : exactInterval 15 32319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32319 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32319) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32319 : oddCount 32319 15 = 9 ∧ acceleratedOrbit 15 32319 = 19415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32319 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32319) = 3 ^ 9 * m + 19415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32319.1, data_15_32319.2]

/-- Complete interval computation for depth 15, residue 32320. -/
theorem bounds_15_32320 : exactInterval 15 32320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32320 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32320) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32320 : oddCount 32320 15 = 6 ∧ acceleratedOrbit 15 32320 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32320 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32320) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32320.1, data_15_32320.2]

/-- Complete interval computation for depth 15, residue 32321. -/
theorem bounds_15_32321 : exactInterval 15 32321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32321 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32321) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32321 : oddCount 32321 15 = 7 ∧ acceleratedOrbit 15 32321 = 2159 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32321 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32321) = 3 ^ 7 * m + 2159 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32321.1, data_15_32321.2]

/-- Complete interval computation for depth 15, residue 32322. -/
theorem bounds_15_32322 : exactInterval 15 32322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32322 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32322) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32322 : oddCount 32322 15 = 7 ∧ acceleratedOrbit 15 32322 = 2159 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32322 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32322) = 3 ^ 7 * m + 2159 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32322.1, data_15_32322.2]

/-- Complete interval computation for depth 15, residue 32323. -/
theorem bounds_15_32323 : exactInterval 15 32323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32323 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32323) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32323 : oddCount 32323 15 = 7 ∧ acceleratedOrbit 15 32323 = 2159 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32323 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32323) = 3 ^ 7 * m + 2159 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32323.1, data_15_32323.2]

/-- Complete interval computation for depth 15, residue 32324. -/
theorem bounds_15_32324 : exactInterval 15 32324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32324 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32324) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32324 : oddCount 32324 15 = 8 ∧ acceleratedOrbit 15 32324 = 6479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32324 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32324) = 3 ^ 8 * m + 6479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32324.1, data_15_32324.2]

/-- Complete interval computation for depth 15, residue 32325. -/
theorem bounds_15_32325 : exactInterval 15 32325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32325 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32325) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32325 : oddCount 32325 15 = 8 ∧ acceleratedOrbit 15 32325 = 6479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32325 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32325) = 3 ^ 8 * m + 6479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32325.1, data_15_32325.2]

/-- Complete interval computation for depth 15, residue 32326. -/
theorem bounds_15_32326 : exactInterval 15 32326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32326 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32326) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32326 : oddCount 32326 15 = 8 ∧ acceleratedOrbit 15 32326 = 6479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32326 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32326) = 3 ^ 8 * m + 6479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32326.1, data_15_32326.2]

/-- Complete interval computation for depth 15, residue 32327. -/
theorem bounds_15_32327 : exactInterval 15 32327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32327 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32327) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32327 : oddCount 32327 15 = 10 ∧ acceleratedOrbit 15 32327 = 58259 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32327 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32327) = 3 ^ 10 * m + 58259 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32327.1, data_15_32327.2]

/-- Complete interval computation for depth 15, residue 32328. -/
theorem bounds_15_32328 : exactInterval 15 32328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32328 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32328) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32328 : oddCount 32328 15 = 8 ∧ acceleratedOrbit 15 32328 = 6479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32328 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32328) = 3 ^ 8 * m + 6479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32328.1, data_15_32328.2]

/-- Complete interval computation for depth 15, residue 32329. -/
theorem bounds_15_32329 : exactInterval 15 32329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32329 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32329) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32329 : oddCount 32329 15 = 10 ∧ acceleratedOrbit 15 32329 = 58265 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32329 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32329) = 3 ^ 10 * m + 58265 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32329.1, data_15_32329.2]

/-- Complete interval computation for depth 15, residue 32330. -/
theorem bounds_15_32330 : exactInterval 15 32330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32330 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32330) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32330 : oddCount 32330 15 = 8 ∧ acceleratedOrbit 15 32330 = 6479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32330 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32330) = 3 ^ 8 * m + 6479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32330.1, data_15_32330.2]

/-- Complete interval computation for depth 15, residue 32331. -/
theorem bounds_15_32331 : exactInterval 15 32331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32331 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32331) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32331 : oddCount 32331 15 = 8 ∧ acceleratedOrbit 15 32331 = 6479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32331 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32331) = 3 ^ 8 * m + 6479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32331.1, data_15_32331.2]

/-- Complete interval computation for depth 15, residue 32332. -/
theorem bounds_15_32332 : exactInterval 15 32332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32332 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32332) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32332 : oddCount 32332 15 = 8 ∧ acceleratedOrbit 15 32332 = 6479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32332 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32332) = 3 ^ 8 * m + 6479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32332.1, data_15_32332.2]

/-- Complete interval computation for depth 15, residue 32333. -/
theorem bounds_15_32333 : exactInterval 15 32333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32333 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32333) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32333 : oddCount 32333 15 = 8 ∧ acceleratedOrbit 15 32333 = 6479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32333 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32333) = 3 ^ 8 * m + 6479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32333.1, data_15_32333.2]

/-- Complete interval computation for depth 15, residue 32334. -/
theorem bounds_15_32334 : exactInterval 15 32334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32334 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32334) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32334 : oddCount 32334 15 = 8 ∧ acceleratedOrbit 15 32334 = 6475 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32334 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32334) = 3 ^ 8 * m + 6475 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32334.1, data_15_32334.2]

/-- Complete interval computation for depth 15, residue 32335. -/
theorem bounds_15_32335 : exactInterval 15 32335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32335 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32335) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32335 : oddCount 32335 15 = 8 ∧ acceleratedOrbit 15 32335 = 6475 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32335 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32335) = 3 ^ 8 * m + 6475 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32335.1, data_15_32335.2]

/-- Complete interval computation for depth 15, residue 32336. -/
theorem bounds_15_32336 : exactInterval 15 32336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32336 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32336) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32336 : oddCount 32336 15 = 6 ∧ acceleratedOrbit 15 32336 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32336 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32336) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32336.1, data_15_32336.2]

/-- Complete interval computation for depth 15, residue 32337. -/
theorem bounds_15_32337 : exactInterval 15 32337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32337 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32337) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32337 : oddCount 32337 15 = 7 ∧ acceleratedOrbit 15 32337 = 2159 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32337 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32337) = 3 ^ 7 * m + 2159 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32337.1, data_15_32337.2]

/-- Complete interval computation for depth 15, residue 32338. -/
theorem bounds_15_32338 : exactInterval 15 32338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32338 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32338) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32338 : oddCount 32338 15 = 7 ∧ acceleratedOrbit 15 32338 = 2159 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32338 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32338) = 3 ^ 7 * m + 2159 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32338.1, data_15_32338.2]

/-- Complete interval computation for depth 15, residue 32339. -/
theorem bounds_15_32339 : exactInterval 15 32339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32339 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32339) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32339 : oddCount 32339 15 = 7 ∧ acceleratedOrbit 15 32339 = 2159 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32339 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32339) = 3 ^ 7 * m + 2159 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32339.1, data_15_32339.2]

/-- Complete interval computation for depth 15, residue 32340. -/
theorem bounds_15_32340 : exactInterval 15 32340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32340 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32340) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32340 : oddCount 32340 15 = 6 ∧ acceleratedOrbit 15 32340 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32340 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32340) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32340.1, data_15_32340.2]

/-- Complete interval computation for depth 15, residue 32341. -/
theorem bounds_15_32341 : exactInterval 15 32341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32341 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32341) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32341 : oddCount 32341 15 = 6 ∧ acceleratedOrbit 15 32341 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32341 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32341) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32341.1, data_15_32341.2]

end Collatz.Research.PassageAtlas.Batch0987
