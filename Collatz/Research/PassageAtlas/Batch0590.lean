import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0590

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 19300. -/
theorem bounds_15_19300 : exactInterval 15 19300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19300 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19300) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19300 : oddCount 19300 15 = 6 ∧ acceleratedOrbit 15 19300 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19300 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19300) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19300.1, data_15_19300.2]

/-- Complete interval computation for depth 15, residue 19301. -/
theorem bounds_15_19301 : exactInterval 15 19301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19301 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19301) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19301 : oddCount 19301 15 = 6 ∧ acceleratedOrbit 15 19301 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19301 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19301) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19301.1, data_15_19301.2]

/-- Complete interval computation for depth 15, residue 19302. -/
theorem bounds_15_19302 : exactInterval 15 19302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19302 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19302) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19302 : oddCount 19302 15 = 6 ∧ acceleratedOrbit 15 19302 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19302 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19302) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19302.1, data_15_19302.2]

/-- Complete interval computation for depth 15, residue 19303. -/
theorem bounds_15_19303 : exactInterval 15 19303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19303 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19303) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19303 : oddCount 19303 15 = 10 ∧ acceleratedOrbit 15 19303 = 34787 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19303 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19303) = 3 ^ 10 * m + 34787 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19303.1, data_15_19303.2]

/-- Complete interval computation for depth 15, residue 19304. -/
theorem bounds_15_19304 : exactInterval 15 19304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19304 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19304) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19304 : oddCount 19304 15 = 7 ∧ acceleratedOrbit 15 19304 = 1291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19304 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19304) = 3 ^ 7 * m + 1291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19304.1, data_15_19304.2]

/-- Complete interval computation for depth 15, residue 19305. -/
theorem bounds_15_19305 : exactInterval 15 19305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19305 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19305) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19305 : oddCount 19305 15 = 8 ∧ acceleratedOrbit 15 19305 = 3866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19305 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19305) = 3 ^ 8 * m + 3866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19305.1, data_15_19305.2]

/-- Complete interval computation for depth 15, residue 19306. -/
theorem bounds_15_19306 : exactInterval 15 19306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19306 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19306) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19306 : oddCount 19306 15 = 7 ∧ acceleratedOrbit 15 19306 = 1291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19306 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19306) = 3 ^ 7 * m + 1291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19306.1, data_15_19306.2]

/-- Complete interval computation for depth 15, residue 19307. -/
theorem bounds_15_19307 : exactInterval 15 19307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19307 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19307) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19307 : oddCount 19307 15 = 7 ∧ acceleratedOrbit 15 19307 = 1289 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19307 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19307) = 3 ^ 7 * m + 1289 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19307.1, data_15_19307.2]

/-- Complete interval computation for depth 15, residue 19308. -/
theorem bounds_15_19308 : exactInterval 15 19308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19308 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19308) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19308 : oddCount 19308 15 = 9 ∧ acceleratedOrbit 15 19308 = 11603 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19308 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19308) = 3 ^ 9 * m + 11603 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19308.1, data_15_19308.2]

/-- Complete interval computation for depth 15, residue 19309. -/
theorem bounds_15_19309 : exactInterval 15 19309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19309 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19309) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19309 : oddCount 19309 15 = 9 ∧ acceleratedOrbit 15 19309 = 11603 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19309 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19309) = 3 ^ 9 * m + 11603 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19309.1, data_15_19309.2]

/-- Complete interval computation for depth 15, residue 19310. -/
theorem bounds_15_19310 : exactInterval 15 19310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19310 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19310) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19310 : oddCount 19310 15 = 9 ∧ acceleratedOrbit 15 19310 = 11603 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19310 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19310) = 3 ^ 9 * m + 11603 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19310.1, data_15_19310.2]

/-- Complete interval computation for depth 15, residue 19311. -/
theorem bounds_15_19311 : exactInterval 15 19311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19311 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19311) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19311 : oddCount 19311 15 = 11 ∧ acceleratedOrbit 15 19311 = 104408 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19311 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19311) = 3 ^ 11 * m + 104408 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19311.1, data_15_19311.2]

/-- Complete interval computation for depth 15, residue 19312. -/
theorem bounds_15_19312 : exactInterval 15 19312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19312 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19312) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19312 : oddCount 19312 15 = 7 ∧ acceleratedOrbit 15 19312 = 1291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19312 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19312) = 3 ^ 7 * m + 1291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19312.1, data_15_19312.2]

/-- Complete interval computation for depth 15, residue 19313. -/
theorem bounds_15_19313 : exactInterval 15 19313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19313 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19313) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19313 : oddCount 19313 15 = 7 ∧ acceleratedOrbit 15 19313 = 1291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19313 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19313) = 3 ^ 7 * m + 1291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19313.1, data_15_19313.2]

/-- Complete interval computation for depth 15, residue 19314. -/
theorem bounds_15_19314 : exactInterval 15 19314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19314 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19314) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19314 : oddCount 19314 15 = 6 ∧ acceleratedOrbit 15 19314 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19314 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19314) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19314.1, data_15_19314.2]

/-- Complete interval computation for depth 15, residue 19315. -/
theorem bounds_15_19315 : exactInterval 15 19315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19315 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19315) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19315 : oddCount 19315 15 = 6 ∧ acceleratedOrbit 15 19315 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19315 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19315) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19315.1, data_15_19315.2]

/-- Complete interval computation for depth 15, residue 19316. -/
theorem bounds_15_19316 : exactInterval 15 19316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19316 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19316) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19316 : oddCount 19316 15 = 7 ∧ acceleratedOrbit 15 19316 = 1291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19316 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19316) = 3 ^ 7 * m + 1291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19316.1, data_15_19316.2]

/-- Complete interval computation for depth 15, residue 19317. -/
theorem bounds_15_19317 : exactInterval 15 19317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19317 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19317) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19317 : oddCount 19317 15 = 7 ∧ acceleratedOrbit 15 19317 = 1291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19317 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19317) = 3 ^ 7 * m + 1291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19317.1, data_15_19317.2]

/-- Complete interval computation for depth 15, residue 19318. -/
theorem bounds_15_19318 : exactInterval 15 19318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19318 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19318) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19318 : oddCount 19318 15 = 9 ∧ acceleratedOrbit 15 19318 = 11609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19318 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19318) = 3 ^ 9 * m + 11609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19318.1, data_15_19318.2]

/-- Complete interval computation for depth 15, residue 19319. -/
theorem bounds_15_19319 : exactInterval 15 19319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19319 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19319) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19319 : oddCount 19319 15 = 9 ∧ acceleratedOrbit 15 19319 = 11609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19319 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19319) = 3 ^ 9 * m + 11609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19319.1, data_15_19319.2]

/-- Complete interval computation for depth 15, residue 19320. -/
theorem bounds_15_19320 : exactInterval 15 19320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19320 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19320) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19320 : oddCount 19320 15 = 6 ∧ acceleratedOrbit 15 19320 = 430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19320 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19320) = 3 ^ 6 * m + 430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19320.1, data_15_19320.2]

/-- Complete interval computation for depth 15, residue 19321. -/
theorem bounds_15_19321 : exactInterval 15 19321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19321 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19321) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19321 : oddCount 19321 15 = 8 ∧ acceleratedOrbit 15 19321 = 3869 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19321 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19321) = 3 ^ 8 * m + 3869 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19321.1, data_15_19321.2]

/-- Complete interval computation for depth 15, residue 19322. -/
theorem bounds_15_19322 : exactInterval 15 19322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19322 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19322) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19322 : oddCount 19322 15 = 6 ∧ acceleratedOrbit 15 19322 = 430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19322 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19322) = 3 ^ 6 * m + 430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19322.1, data_15_19322.2]

/-- Complete interval computation for depth 15, residue 19323. -/
theorem bounds_15_19323 : exactInterval 15 19323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19323 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19323) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19323 : oddCount 19323 15 = 10 ∧ acceleratedOrbit 15 19323 = 34825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19323 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19323) = 3 ^ 10 * m + 34825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19323.1, data_15_19323.2]

/-- Complete interval computation for depth 15, residue 19324. -/
theorem bounds_15_19324 : exactInterval 15 19324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19324 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19324) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19324 : oddCount 19324 15 = 6 ∧ acceleratedOrbit 15 19324 = 430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19324 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19324) = 3 ^ 6 * m + 430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19324.1, data_15_19324.2]

/-- Complete interval computation for depth 15, residue 19325. -/
theorem bounds_15_19325 : exactInterval 15 19325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19325 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19325) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19325 : oddCount 19325 15 = 6 ∧ acceleratedOrbit 15 19325 = 430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19325 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19325) = 3 ^ 6 * m + 430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19325.1, data_15_19325.2]

/-- Complete interval computation for depth 15, residue 19326. -/
theorem bounds_15_19326 : exactInterval 15 19326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19326 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19326) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19326 : oddCount 19326 15 = 13 ∧ acceleratedOrbit 15 19326 = 940409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19326 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19326) = 3 ^ 13 * m + 940409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19326.1, data_15_19326.2]

/-- Complete interval computation for depth 15, residue 19327. -/
theorem bounds_15_19327 : exactInterval 15 19327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19327 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19327) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19327 : oddCount 19327 15 = 13 ∧ acceleratedOrbit 15 19327 = 940409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19327 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19327) = 3 ^ 13 * m + 940409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19327.1, data_15_19327.2]

/-- Complete interval computation for depth 15, residue 19328. -/
theorem bounds_15_19328 : exactInterval 15 19328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19328 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19328) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19328 : oddCount 19328 15 = 3 ∧ acceleratedOrbit 15 19328 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19328 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19328) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19328.1, data_15_19328.2]

/-- Complete interval computation for depth 15, residue 19329. -/
theorem bounds_15_19329 : exactInterval 15 19329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19329 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19329) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19329 : oddCount 19329 15 = 8 ∧ acceleratedOrbit 15 19329 = 3871 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19329 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19329) = 3 ^ 8 * m + 3871 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19329.1, data_15_19329.2]

/-- Complete interval computation for depth 15, residue 19330. -/
theorem bounds_15_19330 : exactInterval 15 19330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19330 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19330) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19330 : oddCount 19330 15 = 7 ∧ acceleratedOrbit 15 19330 = 1291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19330 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19330) = 3 ^ 7 * m + 1291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19330.1, data_15_19330.2]

/-- Complete interval computation for depth 15, residue 19331. -/
theorem bounds_15_19331 : exactInterval 15 19331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19331 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19331) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19331 : oddCount 19331 15 = 7 ∧ acceleratedOrbit 15 19331 = 1291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19331 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19331) = 3 ^ 7 * m + 1291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19331.1, data_15_19331.2]

/-- Complete interval computation for depth 15, residue 19332. -/
theorem bounds_15_19332 : exactInterval 15 19332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19332 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19332) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19332 : oddCount 19332 15 = 10 ∧ acceleratedOrbit 15 19332 = 34856 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19332 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19332) = 3 ^ 10 * m + 34856 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19332.1, data_15_19332.2]

end Collatz.Research.PassageAtlas.Batch0590
