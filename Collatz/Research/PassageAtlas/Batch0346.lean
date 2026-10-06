import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0346

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 11304. -/
theorem bounds_15_11304 : exactInterval 15 11304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11304 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11304) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11304 : oddCount 11304 15 = 6 ∧ acceleratedOrbit 15 11304 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11304 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11304) = 3 ^ 6 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11304.1, data_15_11304.2]

/-- Complete interval computation for depth 15, residue 11305. -/
theorem bounds_15_11305 : exactInterval 15 11305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11305 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11305) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11305 : oddCount 11305 15 = 8 ∧ acceleratedOrbit 15 11305 = 2264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11305 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11305) = 3 ^ 8 * m + 2264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11305.1, data_15_11305.2]

/-- Complete interval computation for depth 15, residue 11306. -/
theorem bounds_15_11306 : exactInterval 15 11306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11306 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11306) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11306 : oddCount 11306 15 = 6 ∧ acceleratedOrbit 15 11306 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11306 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11306) = 3 ^ 6 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11306.1, data_15_11306.2]

/-- Complete interval computation for depth 15, residue 11307. -/
theorem bounds_15_11307 : exactInterval 15 11307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11307 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11307) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11307 : oddCount 11307 15 = 8 ∧ acceleratedOrbit 15 11307 = 2267 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11307 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11307) = 3 ^ 8 * m + 2267 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11307.1, data_15_11307.2]

/-- Complete interval computation for depth 15, residue 11308. -/
theorem bounds_15_11308 : exactInterval 15 11308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11308 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11308) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11308 : oddCount 11308 15 = 9 ∧ acceleratedOrbit 15 11308 = 6803 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11308 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11308) = 3 ^ 9 * m + 6803 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11308.1, data_15_11308.2]

/-- Complete interval computation for depth 15, residue 11309. -/
theorem bounds_15_11309 : exactInterval 15 11309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11309 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11309) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11309 : oddCount 11309 15 = 9 ∧ acceleratedOrbit 15 11309 = 6803 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11309 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11309) = 3 ^ 9 * m + 6803 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11309.1, data_15_11309.2]

/-- Complete interval computation for depth 15, residue 11310. -/
theorem bounds_15_11310 : exactInterval 15 11310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11310 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11310) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11310 : oddCount 11310 15 = 9 ∧ acceleratedOrbit 15 11310 = 6803 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11310 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11310) = 3 ^ 9 * m + 6803 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11310.1, data_15_11310.2]

/-- Complete interval computation for depth 15, residue 11311. -/
theorem bounds_15_11311 : exactInterval 15 11311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11311 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11311) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11311 : oddCount 11311 15 = 7 ∧ acceleratedOrbit 15 11311 = 755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11311 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11311) = 3 ^ 7 * m + 755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11311.1, data_15_11311.2]

/-- Complete interval computation for depth 15, residue 11312. -/
theorem bounds_15_11312 : exactInterval 15 11312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11312 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11312) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11312 : oddCount 11312 15 = 6 ∧ acceleratedOrbit 15 11312 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11312 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11312) = 3 ^ 6 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11312.1, data_15_11312.2]

/-- Complete interval computation for depth 15, residue 11313. -/
theorem bounds_15_11313 : exactInterval 15 11313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11313 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11313) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11313 : oddCount 11313 15 = 9 ∧ acceleratedOrbit 15 11313 = 6803 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11313 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11313) = 3 ^ 9 * m + 6803 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11313.1, data_15_11313.2]

/-- Complete interval computation for depth 15, residue 11314. -/
theorem bounds_15_11314 : exactInterval 15 11314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11314 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11314) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11314 : oddCount 11314 15 = 9 ∧ acceleratedOrbit 15 11314 = 6803 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11314 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11314) = 3 ^ 9 * m + 6803 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11314.1, data_15_11314.2]

/-- Complete interval computation for depth 15, residue 11315. -/
theorem bounds_15_11315 : exactInterval 15 11315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11315 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11315) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11315 : oddCount 11315 15 = 9 ∧ acceleratedOrbit 15 11315 = 6803 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11315 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11315) = 3 ^ 9 * m + 6803 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11315.1, data_15_11315.2]

/-- Complete interval computation for depth 15, residue 11316. -/
theorem bounds_15_11316 : exactInterval 15 11316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11316 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11316) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11316 : oddCount 11316 15 = 6 ∧ acceleratedOrbit 15 11316 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11316 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11316) = 3 ^ 6 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11316.1, data_15_11316.2]

/-- Complete interval computation for depth 15, residue 11317. -/
theorem bounds_15_11317 : exactInterval 15 11317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11317 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11317) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11317 : oddCount 11317 15 = 6 ∧ acceleratedOrbit 15 11317 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11317 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11317) = 3 ^ 6 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11317.1, data_15_11317.2]

/-- Complete interval computation for depth 15, residue 11318. -/
theorem bounds_15_11318 : exactInterval 15 11318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11318 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11318) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11318 : oddCount 11318 15 = 10 ∧ acceleratedOrbit 15 11318 = 20402 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11318 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11318) = 3 ^ 10 * m + 20402 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11318.1, data_15_11318.2]

/-- Complete interval computation for depth 15, residue 11319. -/
theorem bounds_15_11319 : exactInterval 15 11319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11319 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11319) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11319 : oddCount 11319 15 = 10 ∧ acceleratedOrbit 15 11319 = 20402 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11319 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11319) = 3 ^ 10 * m + 20402 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11319.1, data_15_11319.2]

/-- Complete interval computation for depth 15, residue 11320. -/
theorem bounds_15_11320 : exactInterval 15 11320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11320 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11320) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11320 : oddCount 11320 15 = 4 ∧ acceleratedOrbit 15 11320 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11320 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11320) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11320.1, data_15_11320.2]

/-- Complete interval computation for depth 15, residue 11321. -/
theorem bounds_15_11321 : exactInterval 15 11321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11321 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11321) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11321 : oddCount 11321 15 = 10 ∧ acceleratedOrbit 15 11321 = 20411 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11321 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11321) = 3 ^ 10 * m + 20411 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11321.1, data_15_11321.2]

/-- Complete interval computation for depth 15, residue 11322. -/
theorem bounds_15_11322 : exactInterval 15 11322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11322 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11322) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11322 : oddCount 11322 15 = 4 ∧ acceleratedOrbit 15 11322 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11322 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11322) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11322.1, data_15_11322.2]

/-- Complete interval computation for depth 15, residue 11323. -/
theorem bounds_15_11323 : exactInterval 15 11323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11323 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11323) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11323 : oddCount 11323 15 = 11 ∧ acceleratedOrbit 15 11323 = 61235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11323 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11323) = 3 ^ 11 * m + 61235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11323.1, data_15_11323.2]

/-- Complete interval computation for depth 15, residue 11324. -/
theorem bounds_15_11324 : exactInterval 15 11324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11324 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11324) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11324 : oddCount 11324 15 = 4 ∧ acceleratedOrbit 15 11324 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11324 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11324) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11324.1, data_15_11324.2]

/-- Complete interval computation for depth 15, residue 11325. -/
theorem bounds_15_11325 : exactInterval 15 11325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11325 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11325) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11325 : oddCount 11325 15 = 4 ∧ acceleratedOrbit 15 11325 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11325 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11325) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11325.1, data_15_11325.2]

/-- Complete interval computation for depth 15, residue 11326. -/
theorem bounds_15_11326 : exactInterval 15 11326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11326 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11326) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11326 : oddCount 11326 15 = 9 ∧ acceleratedOrbit 15 11326 = 6805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11326 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11326) = 3 ^ 9 * m + 6805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11326.1, data_15_11326.2]

/-- Complete interval computation for depth 15, residue 11327. -/
theorem bounds_15_11327 : exactInterval 15 11327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11327 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11327) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11327 : oddCount 11327 15 = 9 ∧ acceleratedOrbit 15 11327 = 6805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11327 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11327) = 3 ^ 9 * m + 6805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11327.1, data_15_11327.2]

/-- Complete interval computation for depth 15, residue 11328. -/
theorem bounds_15_11328 : exactInterval 15 11328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11328 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11328) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11328 : oddCount 11328 15 = 4 ∧ acceleratedOrbit 15 11328 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11328 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11328) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11328.1, data_15_11328.2]

/-- Complete interval computation for depth 15, residue 11329. -/
theorem bounds_15_11329 : exactInterval 15 11329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11329 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11329) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11329 : oddCount 11329 15 = 7 ∧ acceleratedOrbit 15 11329 = 757 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11329 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11329) = 3 ^ 7 * m + 757 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11329.1, data_15_11329.2]

/-- Complete interval computation for depth 15, residue 11330. -/
theorem bounds_15_11330 : exactInterval 15 11330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11330 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11330) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11330 : oddCount 11330 15 = 7 ∧ acceleratedOrbit 15 11330 = 757 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11330 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11330) = 3 ^ 7 * m + 757 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11330.1, data_15_11330.2]

/-- Complete interval computation for depth 15, residue 11331. -/
theorem bounds_15_11331 : exactInterval 15 11331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11331 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11331) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11331 : oddCount 11331 15 = 7 ∧ acceleratedOrbit 15 11331 = 757 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11331 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11331) = 3 ^ 7 * m + 757 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11331.1, data_15_11331.2]

/-- Complete interval computation for depth 15, residue 11332. -/
theorem bounds_15_11332 : exactInterval 15 11332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11332 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11332) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11332 : oddCount 11332 15 = 6 ∧ acceleratedOrbit 15 11332 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11332 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11332) = 3 ^ 6 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11332.1, data_15_11332.2]

/-- Complete interval computation for depth 15, residue 11333. -/
theorem bounds_15_11333 : exactInterval 15 11333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11333 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11333) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11333 : oddCount 11333 15 = 6 ∧ acceleratedOrbit 15 11333 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11333 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11333) = 3 ^ 6 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11333.1, data_15_11333.2]

/-- Complete interval computation for depth 15, residue 11334. -/
theorem bounds_15_11334 : exactInterval 15 11334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11334 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11334) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11334 : oddCount 11334 15 = 6 ∧ acceleratedOrbit 15 11334 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11334 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11334) = 3 ^ 6 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11334.1, data_15_11334.2]

/-- Complete interval computation for depth 15, residue 11335. -/
theorem bounds_15_11335 : exactInterval 15 11335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11335 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11335) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11335 : oddCount 11335 15 = 8 ∧ acceleratedOrbit 15 11335 = 2270 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11335 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11335) = 3 ^ 8 * m + 2270 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11335.1, data_15_11335.2]

/-- Complete interval computation for depth 15, residue 11336. -/
theorem bounds_15_11336 : exactInterval 15 11336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11336 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11336) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11336 : oddCount 11336 15 = 7 ∧ acceleratedOrbit 15 11336 = 758 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11336 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11336) = 3 ^ 7 * m + 758 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11336.1, data_15_11336.2]

end Collatz.Research.PassageAtlas.Batch0346
