import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0926

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 30310. -/
theorem bounds_15_30310 : exactInterval 15 30310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30310 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30310) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30310 : oddCount 30310 15 = 8 ∧ acceleratedOrbit 15 30310 = 6074 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30310 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30310) = 3 ^ 8 * m + 6074 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30310.1, data_15_30310.2]

/-- Complete interval computation for depth 15, residue 30311. -/
theorem bounds_15_30311 : exactInterval 15 30311 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30311 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30311) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30311 : oddCount 30311 15 = 9 ∧ acceleratedOrbit 15 30311 = 18208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30311 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30311) = 3 ^ 9 * m + 18208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30311.1, data_15_30311.2]

/-- Complete interval computation for depth 15, residue 30312. -/
theorem bounds_15_30312 : exactInterval 15 30312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30312 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30312) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30312 : oddCount 30312 15 = 3 ∧ acceleratedOrbit 15 30312 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30312 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30312) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30312.1, data_15_30312.2]

/-- Complete interval computation for depth 15, residue 30313. -/
theorem bounds_15_30313 : exactInterval 15 30313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30313 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30313) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30313 : oddCount 30313 15 = 11 ∧ acceleratedOrbit 15 30313 = 163889 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30313 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30313) = 3 ^ 11 * m + 163889 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30313.1, data_15_30313.2]

/-- Complete interval computation for depth 15, residue 30314. -/
theorem bounds_15_30314 : exactInterval 15 30314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30314 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30314) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30314 : oddCount 30314 15 = 3 ∧ acceleratedOrbit 15 30314 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30314 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30314) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30314.1, data_15_30314.2]

/-- Complete interval computation for depth 15, residue 30315. -/
theorem bounds_15_30315 : exactInterval 15 30315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30315 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30315) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30315 : oddCount 30315 15 = 10 ∧ acceleratedOrbit 15 30315 = 54634 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30315 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30315) = 3 ^ 10 * m + 54634 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30315.1, data_15_30315.2]

/-- Complete interval computation for depth 15, residue 30316. -/
theorem bounds_15_30316 : exactInterval 15 30316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30316 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30316) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30316 : oddCount 30316 15 = 9 ∧ acceleratedOrbit 15 30316 = 18215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30316 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30316) = 3 ^ 9 * m + 18215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30316.1, data_15_30316.2]

/-- Complete interval computation for depth 15, residue 30317. -/
theorem bounds_15_30317 : exactInterval 15 30317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30317 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30317) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30317 : oddCount 30317 15 = 9 ∧ acceleratedOrbit 15 30317 = 18215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30317 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30317) = 3 ^ 9 * m + 18215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30317.1, data_15_30317.2]

/-- Complete interval computation for depth 15, residue 30318. -/
theorem bounds_15_30318 : exactInterval 15 30318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30318 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30318) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30318 : oddCount 30318 15 = 9 ∧ acceleratedOrbit 15 30318 = 18215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30318 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30318) = 3 ^ 9 * m + 18215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30318.1, data_15_30318.2]

/-- Complete interval computation for depth 15, residue 30319. -/
theorem bounds_15_30319 : exactInterval 15 30319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30319 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30319) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30319 : oddCount 30319 15 = 8 ∧ acceleratedOrbit 15 30319 = 6071 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30319 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30319) = 3 ^ 8 * m + 6071 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30319.1, data_15_30319.2]

/-- Complete interval computation for depth 15, residue 30320. -/
theorem bounds_15_30320 : exactInterval 15 30320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30320 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30320) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30320 : oddCount 30320 15 = 10 ∧ acceleratedOrbit 15 30320 = 54674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30320 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30320) = 3 ^ 10 * m + 54674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30320.1, data_15_30320.2]

/-- Complete interval computation for depth 15, residue 30321. -/
theorem bounds_15_30321 : exactInterval 15 30321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30321 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30321) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30321 : oddCount 30321 15 = 3 ∧ acceleratedOrbit 15 30321 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30321 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30321) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30321.1, data_15_30321.2]

/-- Complete interval computation for depth 15, residue 30322. -/
theorem bounds_15_30322 : exactInterval 15 30322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30322 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30322) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30322 : oddCount 30322 15 = 9 ∧ acceleratedOrbit 15 30322 = 18218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30322 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30322) = 3 ^ 9 * m + 18218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30322.1, data_15_30322.2]

/-- Complete interval computation for depth 15, residue 30323. -/
theorem bounds_15_30323 : exactInterval 15 30323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30323 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30323) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30323 : oddCount 30323 15 = 9 ∧ acceleratedOrbit 15 30323 = 18218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30323 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30323) = 3 ^ 9 * m + 18218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30323.1, data_15_30323.2]

/-- Complete interval computation for depth 15, residue 30324. -/
theorem bounds_15_30324 : exactInterval 15 30324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30324 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30324) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30324 : oddCount 30324 15 = 10 ∧ acceleratedOrbit 15 30324 = 54674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30324 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30324) = 3 ^ 10 * m + 54674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30324.1, data_15_30324.2]

/-- Complete interval computation for depth 15, residue 30325. -/
theorem bounds_15_30325 : exactInterval 15 30325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30325 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30325) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30325 : oddCount 30325 15 = 10 ∧ acceleratedOrbit 15 30325 = 54674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30325 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30325) = 3 ^ 10 * m + 54674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30325.1, data_15_30325.2]

/-- Complete interval computation for depth 15, residue 30326. -/
theorem bounds_15_30326 : exactInterval 15 30326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30326 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30326) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30326 : oddCount 30326 15 = 9 ∧ acceleratedOrbit 15 30326 = 18224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30326 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30326) = 3 ^ 9 * m + 18224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30326.1, data_15_30326.2]

/-- Complete interval computation for depth 15, residue 30327. -/
theorem bounds_15_30327 : exactInterval 15 30327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30327 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30327) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30327 : oddCount 30327 15 = 9 ∧ acceleratedOrbit 15 30327 = 18224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30327 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30327) = 3 ^ 9 * m + 18224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30327.1, data_15_30327.2]

/-- Complete interval computation for depth 15, residue 30328. -/
theorem bounds_15_30328 : exactInterval 15 30328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30328 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30328) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30328 : oddCount 30328 15 = 10 ∧ acceleratedOrbit 15 30328 = 54674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30328 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30328) = 3 ^ 10 * m + 54674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30328.1, data_15_30328.2]

/-- Complete interval computation for depth 15, residue 30329. -/
theorem bounds_15_30329 : exactInterval 15 30329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30329 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30329) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30329 : oddCount 30329 15 = 9 ∧ acceleratedOrbit 15 30329 = 18220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30329 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30329) = 3 ^ 9 * m + 18220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30329.1, data_15_30329.2]

/-- Complete interval computation for depth 15, residue 30330. -/
theorem bounds_15_30330 : exactInterval 15 30330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30330 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30330) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30330 : oddCount 30330 15 = 10 ∧ acceleratedOrbit 15 30330 = 54674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30330 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30330) = 3 ^ 10 * m + 54674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30330.1, data_15_30330.2]

/-- Complete interval computation for depth 15, residue 30331. -/
theorem bounds_15_30331 : exactInterval 15 30331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30331 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30331) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30331 : oddCount 30331 15 = 9 ∧ acceleratedOrbit 15 30331 = 18224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30331 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30331) = 3 ^ 9 * m + 18224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30331.1, data_15_30331.2]

/-- Complete interval computation for depth 15, residue 30332. -/
theorem bounds_15_30332 : exactInterval 15 30332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30332 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30332) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30332 : oddCount 30332 15 = 10 ∧ acceleratedOrbit 15 30332 = 54668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30332 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30332) = 3 ^ 10 * m + 54668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30332.1, data_15_30332.2]

/-- Complete interval computation for depth 15, residue 30333. -/
theorem bounds_15_30333 : exactInterval 15 30333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30333 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30333) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30333 : oddCount 30333 15 = 10 ∧ acceleratedOrbit 15 30333 = 54668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30333 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30333) = 3 ^ 10 * m + 54668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30333.1, data_15_30333.2]

/-- Complete interval computation for depth 15, residue 30334. -/
theorem bounds_15_30334 : exactInterval 15 30334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30334 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30334) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30334 : oddCount 30334 15 = 10 ∧ acceleratedOrbit 15 30334 = 54668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30334 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30334) = 3 ^ 10 * m + 54668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30334.1, data_15_30334.2]

/-- Complete interval computation for depth 15, residue 30335. -/
theorem bounds_15_30335 : exactInterval 15 30335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30335 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30335) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30335 : oddCount 30335 15 = 11 ∧ acceleratedOrbit 15 30335 = 164000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30335 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30335) = 3 ^ 11 * m + 164000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30335.1, data_15_30335.2]

/-- Complete interval computation for depth 15, residue 30336. -/
theorem bounds_15_30336 : exactInterval 15 30336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30336 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30336) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30336 : oddCount 30336 15 = 4 ∧ acceleratedOrbit 15 30336 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30336 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30336) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30336.1, data_15_30336.2]

/-- Complete interval computation for depth 15, residue 30337. -/
theorem bounds_15_30337 : exactInterval 15 30337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30337 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30337) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30337 : oddCount 30337 15 = 12 ∧ acceleratedOrbit 15 30337 = 492074 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30337 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30337) = 3 ^ 12 * m + 492074 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30337.1, data_15_30337.2]

/-- Complete interval computation for depth 15, residue 30338. -/
theorem bounds_15_30338 : exactInterval 15 30338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30338 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30338) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30338 : oddCount 30338 15 = 3 ∧ acceleratedOrbit 15 30338 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30338 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30338) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30338.1, data_15_30338.2]

/-- Complete interval computation for depth 15, residue 30339. -/
theorem bounds_15_30339 : exactInterval 15 30339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30339 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30339) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30339 : oddCount 30339 15 = 3 ∧ acceleratedOrbit 15 30339 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30339 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30339) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30339.1, data_15_30339.2]

/-- Complete interval computation for depth 15, residue 30340. -/
theorem bounds_15_30340 : exactInterval 15 30340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30340 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30340) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30340 : oddCount 30340 15 = 7 ∧ acceleratedOrbit 15 30340 = 2026 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30340 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30340) = 3 ^ 7 * m + 2026 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30340.1, data_15_30340.2]

/-- Complete interval computation for depth 15, residue 30341. -/
theorem bounds_15_30341 : exactInterval 15 30341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30341 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30341) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30341 : oddCount 30341 15 = 7 ∧ acceleratedOrbit 15 30341 = 2026 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30341 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30341) = 3 ^ 7 * m + 2026 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30341.1, data_15_30341.2]

/-- Complete interval computation for depth 15, residue 30342. -/
theorem bounds_15_30342 : exactInterval 15 30342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30342 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30342) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30342 : oddCount 30342 15 = 7 ∧ acceleratedOrbit 15 30342 = 2026 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30342 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30342) = 3 ^ 7 * m + 2026 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30342.1, data_15_30342.2]

end Collatz.Research.PassageAtlas.Batch0926
