import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0804

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 26312. -/
theorem bounds_15_26312 : exactInterval 15 26312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26312 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26312) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26312 : oddCount 26312 15 = 6 ∧ acceleratedOrbit 15 26312 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26312 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26312) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26312.1, data_15_26312.2]

/-- Complete interval computation for depth 15, residue 26313. -/
theorem bounds_15_26313 : exactInterval 15 26313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26313 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26313) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26313 : oddCount 26313 15 = 7 ∧ acceleratedOrbit 15 26313 = 1757 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26313 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26313) = 3 ^ 7 * m + 1757 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26313.1, data_15_26313.2]

/-- Complete interval computation for depth 15, residue 26314. -/
theorem bounds_15_26314 : exactInterval 15 26314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26314 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26314) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26314 : oddCount 26314 15 = 6 ∧ acceleratedOrbit 15 26314 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26314 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26314) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26314.1, data_15_26314.2]

/-- Complete interval computation for depth 15, residue 26315. -/
theorem bounds_15_26315 : exactInterval 15 26315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26315 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26315) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26315 : oddCount 26315 15 = 8 ∧ acceleratedOrbit 15 26315 = 5270 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26315 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26315) = 3 ^ 8 * m + 5270 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26315.1, data_15_26315.2]

/-- Complete interval computation for depth 15, residue 26316. -/
theorem bounds_15_26316 : exactInterval 15 26316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26316 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26316) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26316 : oddCount 26316 15 = 6 ∧ acceleratedOrbit 15 26316 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26316 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26316) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26316.1, data_15_26316.2]

/-- Complete interval computation for depth 15, residue 26317. -/
theorem bounds_15_26317 : exactInterval 15 26317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26317 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26317) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26317 : oddCount 26317 15 = 6 ∧ acceleratedOrbit 15 26317 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26317 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26317) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26317.1, data_15_26317.2]

/-- Complete interval computation for depth 15, residue 26318. -/
theorem bounds_15_26318 : exactInterval 15 26318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26318 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26318) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26318 : oddCount 26318 15 = 11 ∧ acceleratedOrbit 15 26318 = 142292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26318 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26318) = 3 ^ 11 * m + 142292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26318.1, data_15_26318.2]

/-- Complete interval computation for depth 15, residue 26319. -/
theorem bounds_15_26319 : exactInterval 15 26319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26319 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26319) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26319 : oddCount 26319 15 = 11 ∧ acceleratedOrbit 15 26319 = 142292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26319 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26319) = 3 ^ 11 * m + 142292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26319.1, data_15_26319.2]

/-- Complete interval computation for depth 15, residue 26320. -/
theorem bounds_15_26320 : exactInterval 15 26320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26320 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26320) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26320 : oddCount 26320 15 = 6 ∧ acceleratedOrbit 15 26320 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26320 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26320) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26320.1, data_15_26320.2]

/-- Complete interval computation for depth 15, residue 26321. -/
theorem bounds_15_26321 : exactInterval 15 26321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26321 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26321) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26321 : oddCount 26321 15 = 9 ∧ acceleratedOrbit 15 26321 = 15815 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26321 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26321) = 3 ^ 9 * m + 15815 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26321.1, data_15_26321.2]

/-- Complete interval computation for depth 15, residue 26322. -/
theorem bounds_15_26322 : exactInterval 15 26322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26322 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26322) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26322 : oddCount 26322 15 = 9 ∧ acceleratedOrbit 15 26322 = 15815 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26322 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26322) = 3 ^ 9 * m + 15815 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26322.1, data_15_26322.2]

/-- Complete interval computation for depth 15, residue 26323. -/
theorem bounds_15_26323 : exactInterval 15 26323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26323 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26323) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26323 : oddCount 26323 15 = 9 ∧ acceleratedOrbit 15 26323 = 15815 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26323 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26323) = 3 ^ 9 * m + 15815 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26323.1, data_15_26323.2]

/-- Complete interval computation for depth 15, residue 26324. -/
theorem bounds_15_26324 : exactInterval 15 26324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26324 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26324) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26324 : oddCount 26324 15 = 6 ∧ acceleratedOrbit 15 26324 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26324 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26324) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26324.1, data_15_26324.2]

/-- Complete interval computation for depth 15, residue 26325. -/
theorem bounds_15_26325 : exactInterval 15 26325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26325 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26325) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26325 : oddCount 26325 15 = 6 ∧ acceleratedOrbit 15 26325 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26325 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26325) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26325.1, data_15_26325.2]

/-- Complete interval computation for depth 15, residue 26326. -/
theorem bounds_15_26326 : exactInterval 15 26326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26326 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26326) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26326 : oddCount 26326 15 = 6 ∧ acceleratedOrbit 15 26326 = 586 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26326 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26326) = 3 ^ 6 * m + 586 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26326.1, data_15_26326.2]

/-- Complete interval computation for depth 15, residue 26327. -/
theorem bounds_15_26327 : exactInterval 15 26327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26327 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26327) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26327 : oddCount 26327 15 = 6 ∧ acceleratedOrbit 15 26327 = 586 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26327 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26327) = 3 ^ 6 * m + 586 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26327.1, data_15_26327.2]

/-- Complete interval computation for depth 15, residue 26328. -/
theorem bounds_15_26328 : exactInterval 15 26328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26328 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26328) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26328 : oddCount 26328 15 = 6 ∧ acceleratedOrbit 15 26328 = 586 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26328 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26328) = 3 ^ 6 * m + 586 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26328.1, data_15_26328.2]

/-- Complete interval computation for depth 15, residue 26329. -/
theorem bounds_15_26329 : exactInterval 15 26329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26329 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26329) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26329 : oddCount 26329 15 = 6 ∧ acceleratedOrbit 15 26329 = 586 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26329 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26329) = 3 ^ 6 * m + 586 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26329.1, data_15_26329.2]

/-- Complete interval computation for depth 15, residue 26330. -/
theorem bounds_15_26330 : exactInterval 15 26330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26330 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26330) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26330 : oddCount 26330 15 = 6 ∧ acceleratedOrbit 15 26330 = 586 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26330 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26330) = 3 ^ 6 * m + 586 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26330.1, data_15_26330.2]

/-- Complete interval computation for depth 15, residue 26331. -/
theorem bounds_15_26331 : exactInterval 15 26331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26331 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26331) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26331 : oddCount 26331 15 = 8 ∧ acceleratedOrbit 15 26331 = 5273 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26331 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26331) = 3 ^ 8 * m + 5273 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26331.1, data_15_26331.2]

/-- Complete interval computation for depth 15, residue 26332. -/
theorem bounds_15_26332 : exactInterval 15 26332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26332 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26332) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26332 : oddCount 26332 15 = 6 ∧ acceleratedOrbit 15 26332 = 586 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26332 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26332) = 3 ^ 6 * m + 586 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26332.1, data_15_26332.2]

/-- Complete interval computation for depth 15, residue 26333. -/
theorem bounds_15_26333 : exactInterval 15 26333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26333 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26333) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26333 : oddCount 26333 15 = 6 ∧ acceleratedOrbit 15 26333 = 586 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26333 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26333) = 3 ^ 6 * m + 586 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26333.1, data_15_26333.2]

/-- Complete interval computation for depth 15, residue 26334. -/
theorem bounds_15_26334 : exactInterval 15 26334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26334 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26334) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26334 : oddCount 26334 15 = 9 ∧ acceleratedOrbit 15 26334 = 15821 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26334 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26334) = 3 ^ 9 * m + 15821 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26334.1, data_15_26334.2]

/-- Complete interval computation for depth 15, residue 26335. -/
theorem bounds_15_26335 : exactInterval 15 26335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26335 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26335) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26335 : oddCount 26335 15 = 9 ∧ acceleratedOrbit 15 26335 = 15821 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26335 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26335) = 3 ^ 9 * m + 15821 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26335.1, data_15_26335.2]

/-- Complete interval computation for depth 15, residue 26336. -/
theorem bounds_15_26336 : exactInterval 15 26336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26336 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26336) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26336 : oddCount 26336 15 = 6 ∧ acceleratedOrbit 15 26336 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26336 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26336) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26336.1, data_15_26336.2]

/-- Complete interval computation for depth 15, residue 26337. -/
theorem bounds_15_26337 : exactInterval 15 26337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26337 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26337) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26337 : oddCount 26337 15 = 11 ∧ acceleratedOrbit 15 26337 = 142397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26337 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26337) = 3 ^ 11 * m + 142397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26337.1, data_15_26337.2]

/-- Complete interval computation for depth 15, residue 26338. -/
theorem bounds_15_26338 : exactInterval 15 26338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26338 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26338) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26338 : oddCount 26338 15 = 6 ∧ acceleratedOrbit 15 26338 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26338 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26338) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26338.1, data_15_26338.2]

/-- Complete interval computation for depth 15, residue 26339. -/
theorem bounds_15_26339 : exactInterval 15 26339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26339 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26339) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26339 : oddCount 26339 15 = 6 ∧ acceleratedOrbit 15 26339 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26339 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26339) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26339.1, data_15_26339.2]

/-- Complete interval computation for depth 15, residue 26340. -/
theorem bounds_15_26340 : exactInterval 15 26340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26340 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26340) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26340 : oddCount 26340 15 = 6 ∧ acceleratedOrbit 15 26340 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26340 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26340) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26340.1, data_15_26340.2]

/-- Complete interval computation for depth 15, residue 26341. -/
theorem bounds_15_26341 : exactInterval 15 26341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26341 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26341) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26341 : oddCount 26341 15 = 6 ∧ acceleratedOrbit 15 26341 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26341 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26341) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26341.1, data_15_26341.2]

/-- Complete interval computation for depth 15, residue 26342. -/
theorem bounds_15_26342 : exactInterval 15 26342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26342 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26342) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26342 : oddCount 26342 15 = 6 ∧ acceleratedOrbit 15 26342 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26342 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26342) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26342.1, data_15_26342.2]

/-- Complete interval computation for depth 15, residue 26343. -/
theorem bounds_15_26343 : exactInterval 15 26343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26343 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26343) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26343 : oddCount 26343 15 = 10 ∧ acceleratedOrbit 15 26343 = 47474 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26343 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26343) = 3 ^ 10 * m + 47474 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26343.1, data_15_26343.2]

/-- Complete interval computation for depth 15, residue 26344. -/
theorem bounds_15_26344 : exactInterval 15 26344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26344 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26344) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26344 : oddCount 26344 15 = 6 ∧ acceleratedOrbit 15 26344 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26344 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26344) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26344.1, data_15_26344.2]

end Collatz.Research.PassageAtlas.Batch0804
