import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0224

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 7307. -/
theorem bounds_15_7307 : exactInterval 15 7307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7307 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7307) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7307 : oddCount 7307 15 = 7 ∧ acceleratedOrbit 15 7307 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7307 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7307) = 3 ^ 7 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7307.1, data_15_7307.2]

/-- Complete interval computation for depth 15, residue 7308. -/
theorem bounds_15_7308 : exactInterval 15 7308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7308 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7308) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7308 : oddCount 7308 15 = 6 ∧ acceleratedOrbit 15 7308 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7308 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7308) = 3 ^ 6 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7308.1, data_15_7308.2]

/-- Complete interval computation for depth 15, residue 7309. -/
theorem bounds_15_7309 : exactInterval 15 7309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7309 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7309) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7309 : oddCount 7309 15 = 6 ∧ acceleratedOrbit 15 7309 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7309 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7309) = 3 ^ 6 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7309.1, data_15_7309.2]

/-- Complete interval computation for depth 15, residue 7310. -/
theorem bounds_15_7310 : exactInterval 15 7310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7310 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7310) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7310 : oddCount 7310 15 = 9 ∧ acceleratedOrbit 15 7310 = 4394 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7310 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7310) = 3 ^ 9 * m + 4394 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7310.1, data_15_7310.2]

/-- Complete interval computation for depth 15, residue 7311. -/
theorem bounds_15_7311 : exactInterval 15 7311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7311 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7311) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7311 : oddCount 7311 15 = 9 ∧ acceleratedOrbit 15 7311 = 4394 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7311 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7311) = 3 ^ 9 * m + 4394 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7311.1, data_15_7311.2]

/-- Complete interval computation for depth 15, residue 7312. -/
theorem bounds_15_7312 : exactInterval 15 7312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7312 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7312) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7312 : oddCount 7312 15 = 6 ∧ acceleratedOrbit 15 7312 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7312 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7312) = 3 ^ 6 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7312.1, data_15_7312.2]

/-- Complete interval computation for depth 15, residue 7313. -/
theorem bounds_15_7313 : exactInterval 15 7313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7313 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7313) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7313 : oddCount 7313 15 = 8 ∧ acceleratedOrbit 15 7313 = 1466 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7313 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7313) = 3 ^ 8 * m + 1466 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7313.1, data_15_7313.2]

/-- Complete interval computation for depth 15, residue 7314. -/
theorem bounds_15_7314 : exactInterval 15 7314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7314 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7314) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7314 : oddCount 7314 15 = 8 ∧ acceleratedOrbit 15 7314 = 1466 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7314 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7314) = 3 ^ 8 * m + 1466 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7314.1, data_15_7314.2]

/-- Complete interval computation for depth 15, residue 7315. -/
theorem bounds_15_7315 : exactInterval 15 7315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7315 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7315) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7315 : oddCount 7315 15 = 8 ∧ acceleratedOrbit 15 7315 = 1466 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7315 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7315) = 3 ^ 8 * m + 1466 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7315.1, data_15_7315.2]

/-- Complete interval computation for depth 15, residue 7316. -/
theorem bounds_15_7316 : exactInterval 15 7316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7316 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7316) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7316 : oddCount 7316 15 = 6 ∧ acceleratedOrbit 15 7316 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7316 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7316) = 3 ^ 6 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7316.1, data_15_7316.2]

/-- Complete interval computation for depth 15, residue 7317. -/
theorem bounds_15_7317 : exactInterval 15 7317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7317 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7317) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7317 : oddCount 7317 15 = 6 ∧ acceleratedOrbit 15 7317 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7317 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7317) = 3 ^ 6 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7317.1, data_15_7317.2]

/-- Complete interval computation for depth 15, residue 7318. -/
theorem bounds_15_7318 : exactInterval 15 7318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7318 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7318) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7318 : oddCount 7318 15 = 6 ∧ acceleratedOrbit 15 7318 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7318 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7318) = 3 ^ 6 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7318.1, data_15_7318.2]

/-- Complete interval computation for depth 15, residue 7319. -/
theorem bounds_15_7319 : exactInterval 15 7319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7319 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7319) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7319 : oddCount 7319 15 = 6 ∧ acceleratedOrbit 15 7319 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7319 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7319) = 3 ^ 6 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7319.1, data_15_7319.2]

/-- Complete interval computation for depth 15, residue 7320. -/
theorem bounds_15_7320 : exactInterval 15 7320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7320 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7320) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7320 : oddCount 7320 15 = 6 ∧ acceleratedOrbit 15 7320 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7320 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7320) = 3 ^ 6 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7320.1, data_15_7320.2]

/-- Complete interval computation for depth 15, residue 7321. -/
theorem bounds_15_7321 : exactInterval 15 7321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7321 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7321) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7321 : oddCount 7321 15 = 6 ∧ acceleratedOrbit 15 7321 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7321 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7321) = 3 ^ 6 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7321.1, data_15_7321.2]

/-- Complete interval computation for depth 15, residue 7322. -/
theorem bounds_15_7322 : exactInterval 15 7322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7322 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7322) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7322 : oddCount 7322 15 = 6 ∧ acceleratedOrbit 15 7322 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7322 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7322) = 3 ^ 6 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7322.1, data_15_7322.2]

/-- Complete interval computation for depth 15, residue 7323. -/
theorem bounds_15_7323 : exactInterval 15 7323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7323 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7323) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7323 : oddCount 7323 15 = 11 ∧ acceleratedOrbit 15 7323 = 39599 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7323 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7323) = 3 ^ 11 * m + 39599 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7323.1, data_15_7323.2]

/-- Complete interval computation for depth 15, residue 7324. -/
theorem bounds_15_7324 : exactInterval 15 7324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7324 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7324) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7324 : oddCount 7324 15 = 8 ∧ acceleratedOrbit 15 7324 = 1468 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7324 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7324) = 3 ^ 8 * m + 1468 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7324.1, data_15_7324.2]

/-- Complete interval computation for depth 15, residue 7325. -/
theorem bounds_15_7325 : exactInterval 15 7325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7325 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7325) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7325 : oddCount 7325 15 = 8 ∧ acceleratedOrbit 15 7325 = 1468 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7325 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7325) = 3 ^ 8 * m + 1468 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7325.1, data_15_7325.2]

/-- Complete interval computation for depth 15, residue 7326. -/
theorem bounds_15_7326 : exactInterval 15 7326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7326 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7326) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7326 : oddCount 7326 15 = 8 ∧ acceleratedOrbit 15 7326 = 1468 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7326 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7326) = 3 ^ 8 * m + 1468 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7326.1, data_15_7326.2]

/-- Complete interval computation for depth 15, residue 7327. -/
theorem bounds_15_7327 : exactInterval 15 7327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7327 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7327) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7327 : oddCount 7327 15 = 11 ∧ acceleratedOrbit 15 7327 = 39617 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7327 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7327) = 3 ^ 11 * m + 39617 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7327.1, data_15_7327.2]

/-- Complete interval computation for depth 15, residue 7328. -/
theorem bounds_15_7328 : exactInterval 15 7328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7328 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7328) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7328 : oddCount 7328 15 = 5 ∧ acceleratedOrbit 15 7328 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7328 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7328) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7328.1, data_15_7328.2]

/-- Complete interval computation for depth 15, residue 7329. -/
theorem bounds_15_7329 : exactInterval 15 7329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7329 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7329) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7329 : oddCount 7329 15 = 10 ∧ acceleratedOrbit 15 7329 = 13213 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7329 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7329) = 3 ^ 10 * m + 13213 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7329.1, data_15_7329.2]

/-- Complete interval computation for depth 15, residue 7330. -/
theorem bounds_15_7330 : exactInterval 15 7330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7330 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7330) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7330 : oddCount 7330 15 = 7 ∧ acceleratedOrbit 15 7330 = 490 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7330 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7330) = 3 ^ 7 * m + 490 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7330.1, data_15_7330.2]

/-- Complete interval computation for depth 15, residue 7331. -/
theorem bounds_15_7331 : exactInterval 15 7331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7331 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7331) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7331 : oddCount 7331 15 = 7 ∧ acceleratedOrbit 15 7331 = 490 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7331 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7331) = 3 ^ 7 * m + 490 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7331.1, data_15_7331.2]

/-- Complete interval computation for depth 15, residue 7332. -/
theorem bounds_15_7332 : exactInterval 15 7332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7332 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7332) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7332 : oddCount 7332 15 = 7 ∧ acceleratedOrbit 15 7332 = 490 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7332 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7332) = 3 ^ 7 * m + 490 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7332.1, data_15_7332.2]

/-- Complete interval computation for depth 15, residue 7333. -/
theorem bounds_15_7333 : exactInterval 15 7333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7333 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7333) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7333 : oddCount 7333 15 = 7 ∧ acceleratedOrbit 15 7333 = 490 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7333 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7333) = 3 ^ 7 * m + 490 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7333.1, data_15_7333.2]

/-- Complete interval computation for depth 15, residue 7334. -/
theorem bounds_15_7334 : exactInterval 15 7334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7334 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7334) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7334 : oddCount 7334 15 = 7 ∧ acceleratedOrbit 15 7334 = 490 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7334 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7334) = 3 ^ 7 * m + 490 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7334.1, data_15_7334.2]

/-- Complete interval computation for depth 15, residue 7335. -/
theorem bounds_15_7335 : exactInterval 15 7335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7335 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7335) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7335 : oddCount 7335 15 = 12 ∧ acceleratedOrbit 15 7335 = 118988 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7335 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7335) = 3 ^ 12 * m + 118988 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7335.1, data_15_7335.2]

/-- Complete interval computation for depth 15, residue 7336. -/
theorem bounds_15_7336 : exactInterval 15 7336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7336 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7336) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7336 : oddCount 7336 15 = 5 ∧ acceleratedOrbit 15 7336 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7336 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7336) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7336.1, data_15_7336.2]

/-- Complete interval computation for depth 15, residue 7337. -/
theorem bounds_15_7337 : exactInterval 15 7337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7337 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7337) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7337 : oddCount 7337 15 = 10 ∧ acceleratedOrbit 15 7337 = 13225 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7337 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7337) = 3 ^ 10 * m + 13225 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7337.1, data_15_7337.2]

/-- Complete interval computation for depth 15, residue 7338. -/
theorem bounds_15_7338 : exactInterval 15 7338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7338 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7338) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7338 : oddCount 7338 15 = 5 ∧ acceleratedOrbit 15 7338 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7338 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7338) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7338.1, data_15_7338.2]

/-- Complete interval computation for depth 15, residue 7339. -/
theorem bounds_15_7339 : exactInterval 15 7339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7339 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7339) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7339 : oddCount 7339 15 = 8 ∧ acceleratedOrbit 15 7339 = 1471 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7339 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7339) = 3 ^ 8 * m + 1471 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7339.1, data_15_7339.2]

end Collatz.Research.PassageAtlas.Batch0224
