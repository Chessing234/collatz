import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0529

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 17301. -/
theorem bounds_15_17301 : exactInterval 15 17301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17301 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17301) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17301 : oddCount 17301 15 = 6 ∧ acceleratedOrbit 15 17301 = 386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17301 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17301) = 3 ^ 6 * m + 386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17301.1, data_15_17301.2]

/-- Complete interval computation for depth 15, residue 17302. -/
theorem bounds_15_17302 : exactInterval 15 17302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17302 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17302) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17302 : oddCount 17302 15 = 7 ∧ acceleratedOrbit 15 17302 = 1156 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17302 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17302) = 3 ^ 7 * m + 1156 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17302.1, data_15_17302.2]

/-- Complete interval computation for depth 15, residue 17303. -/
theorem bounds_15_17303 : exactInterval 15 17303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17303 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17303) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17303 : oddCount 17303 15 = 7 ∧ acceleratedOrbit 15 17303 = 1156 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17303 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17303) = 3 ^ 7 * m + 1156 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17303.1, data_15_17303.2]

/-- Complete interval computation for depth 15, residue 17304. -/
theorem bounds_15_17304 : exactInterval 15 17304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17304 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17304) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17304 : oddCount 17304 15 = 6 ∧ acceleratedOrbit 15 17304 = 386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17304 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17304) = 3 ^ 6 * m + 386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17304.1, data_15_17304.2]

/-- Complete interval computation for depth 15, residue 17305. -/
theorem bounds_15_17305 : exactInterval 15 17305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17305 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17305) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17305 : oddCount 17305 15 = 7 ∧ acceleratedOrbit 15 17305 = 1156 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17305 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17305) = 3 ^ 7 * m + 1156 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17305.1, data_15_17305.2]

/-- Complete interval computation for depth 15, residue 17306. -/
theorem bounds_15_17306 : exactInterval 15 17306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17306 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17306) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17306 : oddCount 17306 15 = 6 ∧ acceleratedOrbit 15 17306 = 386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17306 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17306) = 3 ^ 6 * m + 386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17306.1, data_15_17306.2]

/-- Complete interval computation for depth 15, residue 17307. -/
theorem bounds_15_17307 : exactInterval 15 17307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17307 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17307) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17307 : oddCount 17307 15 = 8 ∧ acceleratedOrbit 15 17307 = 3466 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17307 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17307) = 3 ^ 8 * m + 3466 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17307.1, data_15_17307.2]

/-- Complete interval computation for depth 15, residue 17308. -/
theorem bounds_15_17308 : exactInterval 15 17308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17308 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17308) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17308 : oddCount 17308 15 = 8 ∧ acceleratedOrbit 15 17308 = 3467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17308 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17308) = 3 ^ 8 * m + 3467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17308.1, data_15_17308.2]

/-- Complete interval computation for depth 15, residue 17309. -/
theorem bounds_15_17309 : exactInterval 15 17309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17309 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17309) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17309 : oddCount 17309 15 = 8 ∧ acceleratedOrbit 15 17309 = 3467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17309 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17309) = 3 ^ 8 * m + 3467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17309.1, data_15_17309.2]

/-- Complete interval computation for depth 15, residue 17310. -/
theorem bounds_15_17310 : exactInterval 15 17310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17310 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17310) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17310 : oddCount 17310 15 = 8 ∧ acceleratedOrbit 15 17310 = 3467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17310 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17310) = 3 ^ 8 * m + 3467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17310.1, data_15_17310.2]

/-- Complete interval computation for depth 15, residue 17311. -/
theorem bounds_15_17311 : exactInterval 15 17311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17311 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17311) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17311 : oddCount 17311 15 = 10 ∧ acceleratedOrbit 15 17311 = 31198 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17311 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17311) = 3 ^ 10 * m + 31198 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17311.1, data_15_17311.2]

/-- Complete interval computation for depth 15, residue 17312. -/
theorem bounds_15_17312 : exactInterval 15 17312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17312 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17312) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17312 : oddCount 17312 15 = 4 ∧ acceleratedOrbit 15 17312 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17312 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17312) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17312.1, data_15_17312.2]

/-- Complete interval computation for depth 15, residue 17313. -/
theorem bounds_15_17313 : exactInterval 15 17313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17313 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17313) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17313 : oddCount 17313 15 = 7 ∧ acceleratedOrbit 15 17313 = 1156 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17313 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17313) = 3 ^ 7 * m + 1156 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17313.1, data_15_17313.2]

/-- Complete interval computation for depth 15, residue 17314. -/
theorem bounds_15_17314 : exactInterval 15 17314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17314 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17314) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17314 : oddCount 17314 15 = 6 ∧ acceleratedOrbit 15 17314 = 386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17314 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17314) = 3 ^ 6 * m + 386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17314.1, data_15_17314.2]

/-- Complete interval computation for depth 15, residue 17315. -/
theorem bounds_15_17315 : exactInterval 15 17315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17315 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17315) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17315 : oddCount 17315 15 = 6 ∧ acceleratedOrbit 15 17315 = 386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17315 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17315) = 3 ^ 6 * m + 386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17315.1, data_15_17315.2]

/-- Complete interval computation for depth 15, residue 17316. -/
theorem bounds_15_17316 : exactInterval 15 17316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17316 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17316) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17316 : oddCount 17316 15 = 8 ∧ acceleratedOrbit 15 17316 = 3469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17316 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17316) = 3 ^ 8 * m + 3469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17316.1, data_15_17316.2]

/-- Complete interval computation for depth 15, residue 17317. -/
theorem bounds_15_17317 : exactInterval 15 17317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17317 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17317) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17317 : oddCount 17317 15 = 8 ∧ acceleratedOrbit 15 17317 = 3469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17317 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17317) = 3 ^ 8 * m + 3469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17317.1, data_15_17317.2]

/-- Complete interval computation for depth 15, residue 17318. -/
theorem bounds_15_17318 : exactInterval 15 17318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17318 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17318) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17318 : oddCount 17318 15 = 8 ∧ acceleratedOrbit 15 17318 = 3469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17318 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17318) = 3 ^ 8 * m + 3469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17318.1, data_15_17318.2]

/-- Complete interval computation for depth 15, residue 17319. -/
theorem bounds_15_17319 : exactInterval 15 17319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17319 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17319) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17319 : oddCount 17319 15 = 7 ∧ acceleratedOrbit 15 17319 = 1156 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17319 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17319) = 3 ^ 7 * m + 1156 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17319.1, data_15_17319.2]

/-- Complete interval computation for depth 15, residue 17320. -/
theorem bounds_15_17320 : exactInterval 15 17320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17320 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17320) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17320 : oddCount 17320 15 = 4 ∧ acceleratedOrbit 15 17320 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17320 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17320) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17320.1, data_15_17320.2]

/-- Complete interval computation for depth 15, residue 17321. -/
theorem bounds_15_17321 : exactInterval 15 17321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17321 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17321) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17321 : oddCount 17321 15 = 11 ∧ acceleratedOrbit 15 17321 = 93649 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17321 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17321) = 3 ^ 11 * m + 93649 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17321.1, data_15_17321.2]

/-- Complete interval computation for depth 15, residue 17322. -/
theorem bounds_15_17322 : exactInterval 15 17322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17322 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17322) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17322 : oddCount 17322 15 = 4 ∧ acceleratedOrbit 15 17322 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17322 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17322) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17322.1, data_15_17322.2]

/-- Complete interval computation for depth 15, residue 17323. -/
theorem bounds_15_17323 : exactInterval 15 17323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17323 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17323) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17323 : oddCount 17323 15 = 9 ∧ acceleratedOrbit 15 17323 = 10408 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17323 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17323) = 3 ^ 9 * m + 10408 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17323.1, data_15_17323.2]

/-- Complete interval computation for depth 15, residue 17324. -/
theorem bounds_15_17324 : exactInterval 15 17324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17324 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17324) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17324 : oddCount 17324 15 = 9 ∧ acceleratedOrbit 15 17324 = 10412 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17324 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17324) = 3 ^ 9 * m + 10412 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17324.1, data_15_17324.2]

/-- Complete interval computation for depth 15, residue 17325. -/
theorem bounds_15_17325 : exactInterval 15 17325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17325 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17325) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17325 : oddCount 17325 15 = 9 ∧ acceleratedOrbit 15 17325 = 10412 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17325 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17325) = 3 ^ 9 * m + 10412 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17325.1, data_15_17325.2]

/-- Complete interval computation for depth 15, residue 17326. -/
theorem bounds_15_17326 : exactInterval 15 17326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17326 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17326) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17326 : oddCount 17326 15 = 9 ∧ acceleratedOrbit 15 17326 = 10412 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17326 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17326) = 3 ^ 9 * m + 10412 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17326.1, data_15_17326.2]

/-- Complete interval computation for depth 15, residue 17327. -/
theorem bounds_15_17327 : exactInterval 15 17327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17327 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17327) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17327 : oddCount 17327 15 = 6 ∧ acceleratedOrbit 15 17327 = 386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17327 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17327) = 3 ^ 6 * m + 386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17327.1, data_15_17327.2]

/-- Complete interval computation for depth 15, residue 17328. -/
theorem bounds_15_17328 : exactInterval 15 17328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17328 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17328) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17328 : oddCount 17328 15 = 7 ∧ acceleratedOrbit 15 17328 = 1160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17328 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17328) = 3 ^ 7 * m + 1160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17328.1, data_15_17328.2]

/-- Complete interval computation for depth 15, residue 17329. -/
theorem bounds_15_17329 : exactInterval 15 17329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17329 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17329) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17329 : oddCount 17329 15 = 7 ∧ acceleratedOrbit 15 17329 = 1160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17329 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17329) = 3 ^ 7 * m + 1160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17329.1, data_15_17329.2]

/-- Complete interval computation for depth 15, residue 17330. -/
theorem bounds_15_17330 : exactInterval 15 17330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17330 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17330) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17330 : oddCount 17330 15 = 7 ∧ acceleratedOrbit 15 17330 = 1160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17330 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17330) = 3 ^ 7 * m + 1160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17330.1, data_15_17330.2]

/-- Complete interval computation for depth 15, residue 17331. -/
theorem bounds_15_17331 : exactInterval 15 17331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17331 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17331) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17331 : oddCount 17331 15 = 7 ∧ acceleratedOrbit 15 17331 = 1160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17331 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17331) = 3 ^ 7 * m + 1160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17331.1, data_15_17331.2]

/-- Complete interval computation for depth 15, residue 17332. -/
theorem bounds_15_17332 : exactInterval 15 17332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17332 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17332) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17332 : oddCount 17332 15 = 7 ∧ acceleratedOrbit 15 17332 = 1160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17332 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17332) = 3 ^ 7 * m + 1160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17332.1, data_15_17332.2]

/-- Complete interval computation for depth 15, residue 17333. -/
theorem bounds_15_17333 : exactInterval 15 17333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17333 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17333) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17333 : oddCount 17333 15 = 7 ∧ acceleratedOrbit 15 17333 = 1160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17333 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17333) = 3 ^ 7 * m + 1160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17333.1, data_15_17333.2]

end Collatz.Research.PassageAtlas.Batch0529
