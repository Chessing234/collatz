import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0163

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 5308. -/
theorem bounds_15_5308 : exactInterval 15 5308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5308 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5308) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5308 : oddCount 5308 15 = 8 ∧ acceleratedOrbit 15 5308 = 1064 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5308 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5308) = 3 ^ 8 * m + 1064 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5308.1, data_15_5308.2]

/-- Complete interval computation for depth 15, residue 5309. -/
theorem bounds_15_5309 : exactInterval 15 5309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5309 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5309) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5309 : oddCount 5309 15 = 8 ∧ acceleratedOrbit 15 5309 = 1064 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5309 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5309) = 3 ^ 8 * m + 1064 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5309.1, data_15_5309.2]

/-- Complete interval computation for depth 15, residue 5310. -/
theorem bounds_15_5310 : exactInterval 15 5310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5310 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5310) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5310 : oddCount 5310 15 = 8 ∧ acceleratedOrbit 15 5310 = 1064 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5310 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5310) = 3 ^ 8 * m + 1064 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5310.1, data_15_5310.2]

/-- Complete interval computation for depth 15, residue 5311. -/
theorem bounds_15_5311 : exactInterval 15 5311 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5311 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5311) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5311 : oddCount 5311 15 = 9 ∧ acceleratedOrbit 15 5311 = 3191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5311 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5311) = 3 ^ 9 * m + 3191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5311.1, data_15_5311.2]

/-- Complete interval computation for depth 15, residue 5312. -/
theorem bounds_15_5312 : exactInterval 15 5312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5312 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5312) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5312 : oddCount 5312 15 = 6 ∧ acceleratedOrbit 15 5312 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5312 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5312) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5312.1, data_15_5312.2]

/-- Complete interval computation for depth 15, residue 5313. -/
theorem bounds_15_5313 : exactInterval 15 5313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5313 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5313) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5313 : oddCount 5313 15 = 8 ∧ acceleratedOrbit 15 5313 = 1066 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5313 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5313) = 3 ^ 8 * m + 1066 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5313.1, data_15_5313.2]

/-- Complete interval computation for depth 15, residue 5314. -/
theorem bounds_15_5314 : exactInterval 15 5314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5314 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5314) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5314 : oddCount 5314 15 = 8 ∧ acceleratedOrbit 15 5314 = 1066 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5314 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5314) = 3 ^ 8 * m + 1066 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5314.1, data_15_5314.2]

/-- Complete interval computation for depth 15, residue 5315. -/
theorem bounds_15_5315 : exactInterval 15 5315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5315 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5315) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5315 : oddCount 5315 15 = 8 ∧ acceleratedOrbit 15 5315 = 1066 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5315 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5315) = 3 ^ 8 * m + 1066 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5315.1, data_15_5315.2]

/-- Complete interval computation for depth 15, residue 5316. -/
theorem bounds_15_5316 : exactInterval 15 5316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5316 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5316) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5316 : oddCount 5316 15 = 6 ∧ acceleratedOrbit 15 5316 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5316 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5316) = 3 ^ 6 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5316.1, data_15_5316.2]

/-- Complete interval computation for depth 15, residue 5317. -/
theorem bounds_15_5317 : exactInterval 15 5317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5317 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5317) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5317 : oddCount 5317 15 = 6 ∧ acceleratedOrbit 15 5317 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5317 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5317) = 3 ^ 6 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5317.1, data_15_5317.2]

/-- Complete interval computation for depth 15, residue 5318. -/
theorem bounds_15_5318 : exactInterval 15 5318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5318 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5318) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5318 : oddCount 5318 15 = 6 ∧ acceleratedOrbit 15 5318 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5318 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5318) = 3 ^ 6 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5318.1, data_15_5318.2]

/-- Complete interval computation for depth 15, residue 5319. -/
theorem bounds_15_5319 : exactInterval 15 5319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5319 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5319) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5319 : oddCount 5319 15 = 8 ∧ acceleratedOrbit 15 5319 = 1066 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5319 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5319) = 3 ^ 8 * m + 1066 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5319.1, data_15_5319.2]

/-- Complete interval computation for depth 15, residue 5320. -/
theorem bounds_15_5320 : exactInterval 15 5320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5320 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5320) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5320 : oddCount 5320 15 = 6 ∧ acceleratedOrbit 15 5320 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5320 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5320) = 3 ^ 6 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5320.1, data_15_5320.2]

/-- Complete interval computation for depth 15, residue 5321. -/
theorem bounds_15_5321 : exactInterval 15 5321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5321 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5321) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5321 : oddCount 5321 15 = 6 ∧ acceleratedOrbit 15 5321 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5321 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5321) = 3 ^ 6 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5321.1, data_15_5321.2]

/-- Complete interval computation for depth 15, residue 5322. -/
theorem bounds_15_5322 : exactInterval 15 5322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5322 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5322) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5322 : oddCount 5322 15 = 6 ∧ acceleratedOrbit 15 5322 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5322 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5322) = 3 ^ 6 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5322.1, data_15_5322.2]

/-- Complete interval computation for depth 15, residue 5323. -/
theorem bounds_15_5323 : exactInterval 15 5323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5323 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5323) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5323 : oddCount 5323 15 = 6 ∧ acceleratedOrbit 15 5323 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5323 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5323) = 3 ^ 6 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5323.1, data_15_5323.2]

/-- Complete interval computation for depth 15, residue 5324. -/
theorem bounds_15_5324 : exactInterval 15 5324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5324 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5324) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5324 : oddCount 5324 15 = 6 ∧ acceleratedOrbit 15 5324 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5324 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5324) = 3 ^ 6 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5324.1, data_15_5324.2]

/-- Complete interval computation for depth 15, residue 5325. -/
theorem bounds_15_5325 : exactInterval 15 5325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5325 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5325) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5325 : oddCount 5325 15 = 6 ∧ acceleratedOrbit 15 5325 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5325 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5325) = 3 ^ 6 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5325.1, data_15_5325.2]

/-- Complete interval computation for depth 15, residue 5326. -/
theorem bounds_15_5326 : exactInterval 15 5326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5326 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5326) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5326 : oddCount 5326 15 = 8 ∧ acceleratedOrbit 15 5326 = 1067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5326 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5326) = 3 ^ 8 * m + 1067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5326.1, data_15_5326.2]

/-- Complete interval computation for depth 15, residue 5327. -/
theorem bounds_15_5327 : exactInterval 15 5327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5327 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5327) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5327 : oddCount 5327 15 = 8 ∧ acceleratedOrbit 15 5327 = 1067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5327 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5327) = 3 ^ 8 * m + 1067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5327.1, data_15_5327.2]

/-- Complete interval computation for depth 15, residue 5328. -/
theorem bounds_15_5328 : exactInterval 15 5328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5328 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5328) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5328 : oddCount 5328 15 = 6 ∧ acceleratedOrbit 15 5328 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5328 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5328) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5328.1, data_15_5328.2]

/-- Complete interval computation for depth 15, residue 5329. -/
theorem bounds_15_5329 : exactInterval 15 5329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5329 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5329) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5329 : oddCount 5329 15 = 7 ∧ acceleratedOrbit 15 5329 = 356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5329 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5329) = 3 ^ 7 * m + 356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5329.1, data_15_5329.2]

/-- Complete interval computation for depth 15, residue 5330. -/
theorem bounds_15_5330 : exactInterval 15 5330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5330 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5330) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5330 : oddCount 5330 15 = 7 ∧ acceleratedOrbit 15 5330 = 356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5330 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5330) = 3 ^ 7 * m + 356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5330.1, data_15_5330.2]

/-- Complete interval computation for depth 15, residue 5331. -/
theorem bounds_15_5331 : exactInterval 15 5331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5331 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5331) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5331 : oddCount 5331 15 = 7 ∧ acceleratedOrbit 15 5331 = 356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5331 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5331) = 3 ^ 7 * m + 356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5331.1, data_15_5331.2]

/-- Complete interval computation for depth 15, residue 5332. -/
theorem bounds_15_5332 : exactInterval 15 5332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5332 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5332) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5332 : oddCount 5332 15 = 6 ∧ acceleratedOrbit 15 5332 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5332 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5332) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5332.1, data_15_5332.2]

/-- Complete interval computation for depth 15, residue 5333. -/
theorem bounds_15_5333 : exactInterval 15 5333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5333 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5333) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5333 : oddCount 5333 15 = 6 ∧ acceleratedOrbit 15 5333 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5333 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5333) = 3 ^ 6 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5333.1, data_15_5333.2]

/-- Complete interval computation for depth 15, residue 5334. -/
theorem bounds_15_5334 : exactInterval 15 5334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5334 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5334) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5334 : oddCount 5334 15 = 8 ∧ acceleratedOrbit 15 5334 = 1070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5334 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5334) = 3 ^ 8 * m + 1070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5334.1, data_15_5334.2]

/-- Complete interval computation for depth 15, residue 5335. -/
theorem bounds_15_5335 : exactInterval 15 5335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5335 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5335) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5335 : oddCount 5335 15 = 8 ∧ acceleratedOrbit 15 5335 = 1070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5335 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5335) = 3 ^ 8 * m + 1070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5335.1, data_15_5335.2]

/-- Complete interval computation for depth 15, residue 5336. -/
theorem bounds_15_5336 : exactInterval 15 5336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5336 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5336) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5336 : oddCount 5336 15 = 10 ∧ acceleratedOrbit 15 5336 = 9638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5336 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5336) = 3 ^ 10 * m + 9638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5336.1, data_15_5336.2]

/-- Complete interval computation for depth 15, residue 5337. -/
theorem bounds_15_5337 : exactInterval 15 5337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5337 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5337) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5337 : oddCount 5337 15 = 6 ∧ acceleratedOrbit 15 5337 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5337 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5337) = 3 ^ 6 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5337.1, data_15_5337.2]

/-- Complete interval computation for depth 15, residue 5338. -/
theorem bounds_15_5338 : exactInterval 15 5338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5338 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5338) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5338 : oddCount 5338 15 = 10 ∧ acceleratedOrbit 15 5338 = 9638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5338 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5338) = 3 ^ 10 * m + 9638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5338.1, data_15_5338.2]

/-- Complete interval computation for depth 15, residue 5339. -/
theorem bounds_15_5339 : exactInterval 15 5339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5339 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5339) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5339 : oddCount 5339 15 = 8 ∧ acceleratedOrbit 15 5339 = 1070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5339 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5339) = 3 ^ 8 * m + 1070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5339.1, data_15_5339.2]

/-- Complete interval computation for depth 15, residue 5340. -/
theorem bounds_15_5340 : exactInterval 15 5340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5340 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5340) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5340 : oddCount 5340 15 = 10 ∧ acceleratedOrbit 15 5340 = 9638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5340 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5340) = 3 ^ 10 * m + 9638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5340.1, data_15_5340.2]

end Collatz.Research.PassageAtlas.Batch0163
