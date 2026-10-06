import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0741

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 24248. -/
theorem bounds_15_24248 : exactInterval 15 24248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24248 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24248) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24248 : oddCount 24248 15 = 9 ∧ acceleratedOrbit 15 24248 = 14579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24248 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24248) = 3 ^ 9 * m + 14579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24248.1, data_15_24248.2]

/-- Complete interval computation for depth 15, residue 24249. -/
theorem bounds_15_24249 : exactInterval 15 24249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24249 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24249) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24249 : oddCount 24249 15 = 9 ∧ acceleratedOrbit 15 24249 = 14570 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24249 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24249) = 3 ^ 9 * m + 14570 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24249.1, data_15_24249.2]

/-- Complete interval computation for depth 15, residue 24250. -/
theorem bounds_15_24250 : exactInterval 15 24250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24250 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24250) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24250 : oddCount 24250 15 = 9 ∧ acceleratedOrbit 15 24250 = 14579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24250 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24250) = 3 ^ 9 * m + 14579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24250.1, data_15_24250.2]

/-- Complete interval computation for depth 15, residue 24251. -/
theorem bounds_15_24251 : exactInterval 15 24251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24251 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24251) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24251 : oddCount 24251 15 = 9 ∧ acceleratedOrbit 15 24251 = 14570 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24251 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24251) = 3 ^ 9 * m + 14570 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24251.1, data_15_24251.2]

/-- Complete interval computation for depth 15, residue 24252. -/
theorem bounds_15_24252 : exactInterval 15 24252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24252 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24252) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24252 : oddCount 24252 15 = 8 ∧ acceleratedOrbit 15 24252 = 4859 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24252 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24252) = 3 ^ 8 * m + 4859 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24252.1, data_15_24252.2]

/-- Complete interval computation for depth 15, residue 24253. -/
theorem bounds_15_24253 : exactInterval 15 24253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24253 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24253) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24253 : oddCount 24253 15 = 8 ∧ acceleratedOrbit 15 24253 = 4859 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24253 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24253) = 3 ^ 8 * m + 4859 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24253.1, data_15_24253.2]

/-- Complete interval computation for depth 15, residue 24254. -/
theorem bounds_15_24254 : exactInterval 15 24254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24254 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24254) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24254 : oddCount 24254 15 = 8 ∧ acceleratedOrbit 15 24254 = 4859 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24254 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24254) = 3 ^ 8 * m + 4859 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24254.1, data_15_24254.2]

/-- Complete interval computation for depth 15, residue 24255. -/
theorem bounds_15_24255 : exactInterval 15 24255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24255 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24255) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24255 : oddCount 24255 15 = 11 ∧ acceleratedOrbit 15 24255 = 131132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24255 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24255) = 3 ^ 11 * m + 131132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24255.1, data_15_24255.2]

/-- Complete interval computation for depth 15, residue 24256. -/
theorem bounds_15_24256 : exactInterval 15 24256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24256 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24256) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24256 : oddCount 24256 15 = 6 ∧ acceleratedOrbit 15 24256 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24256 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24256) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24256.1, data_15_24256.2]

/-- Complete interval computation for depth 15, residue 24257. -/
theorem bounds_15_24257 : exactInterval 15 24257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24257 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24257) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24257 : oddCount 24257 15 = 9 ∧ acceleratedOrbit 15 24257 = 14579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24257 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24257) = 3 ^ 9 * m + 14579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24257.1, data_15_24257.2]

/-- Complete interval computation for depth 15, residue 24258. -/
theorem bounds_15_24258 : exactInterval 15 24258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24258 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24258) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24258 : oddCount 24258 15 = 9 ∧ acceleratedOrbit 15 24258 = 14575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24258 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24258) = 3 ^ 9 * m + 14575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24258.1, data_15_24258.2]

/-- Complete interval computation for depth 15, residue 24259. -/
theorem bounds_15_24259 : exactInterval 15 24259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24259 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24259) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24259 : oddCount 24259 15 = 9 ∧ acceleratedOrbit 15 24259 = 14575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24259 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24259) = 3 ^ 9 * m + 14575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24259.1, data_15_24259.2]

/-- Complete interval computation for depth 15, residue 24260. -/
theorem bounds_15_24260 : exactInterval 15 24260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24260 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24260) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24260 : oddCount 24260 15 = 3 ∧ acceleratedOrbit 15 24260 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24260 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24260) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24260.1, data_15_24260.2]

/-- Complete interval computation for depth 15, residue 24261. -/
theorem bounds_15_24261 : exactInterval 15 24261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24261 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24261) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24261 : oddCount 24261 15 = 3 ∧ acceleratedOrbit 15 24261 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24261 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24261) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24261.1, data_15_24261.2]

/-- Complete interval computation for depth 15, residue 24262. -/
theorem bounds_15_24262 : exactInterval 15 24262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24262 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24262) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24262 : oddCount 24262 15 = 3 ∧ acceleratedOrbit 15 24262 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24262 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24262) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24262.1, data_15_24262.2]

/-- Complete interval computation for depth 15, residue 24263. -/
theorem bounds_15_24263 : exactInterval 15 24263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24263 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24263) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24263 : oddCount 24263 15 = 9 ∧ acceleratedOrbit 15 24263 = 14579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24263 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24263) = 3 ^ 9 * m + 14579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24263.1, data_15_24263.2]

/-- Complete interval computation for depth 15, residue 24264. -/
theorem bounds_15_24264 : exactInterval 15 24264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24264 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24264) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24264 : oddCount 24264 15 = 3 ∧ acceleratedOrbit 15 24264 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24264 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24264) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24264.1, data_15_24264.2]

/-- Complete interval computation for depth 15, residue 24265. -/
theorem bounds_15_24265 : exactInterval 15 24265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24265 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24265) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24265 : oddCount 24265 15 = 10 ∧ acceleratedOrbit 15 24265 = 43739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24265 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24265) = 3 ^ 10 * m + 43739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24265.1, data_15_24265.2]

/-- Complete interval computation for depth 15, residue 24266. -/
theorem bounds_15_24266 : exactInterval 15 24266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24266 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24266) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24266 : oddCount 24266 15 = 3 ∧ acceleratedOrbit 15 24266 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24266 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24266) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24266.1, data_15_24266.2]

/-- Complete interval computation for depth 15, residue 24267. -/
theorem bounds_15_24267 : exactInterval 15 24267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24267 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24267) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24267 : oddCount 24267 15 = 11 ∧ acceleratedOrbit 15 24267 = 131219 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24267 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24267) = 3 ^ 11 * m + 131219 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24267.1, data_15_24267.2]

/-- Complete interval computation for depth 15, residue 24268. -/
theorem bounds_15_24268 : exactInterval 15 24268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24268 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24268) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24268 : oddCount 24268 15 = 3 ∧ acceleratedOrbit 15 24268 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24268 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24268) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24268.1, data_15_24268.2]

/-- Complete interval computation for depth 15, residue 24269. -/
theorem bounds_15_24269 : exactInterval 15 24269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24269 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24269) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24269 : oddCount 24269 15 = 3 ∧ acceleratedOrbit 15 24269 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24269 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24269) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24269.1, data_15_24269.2]

/-- Complete interval computation for depth 15, residue 24270. -/
theorem bounds_15_24270 : exactInterval 15 24270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24270 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24270) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24270 : oddCount 24270 15 = 13 ∧ acceleratedOrbit 15 24270 = 1180979 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24270 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24270) = 3 ^ 13 * m + 1180979 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24270.1, data_15_24270.2]

/-- Complete interval computation for depth 15, residue 24271. -/
theorem bounds_15_24271 : exactInterval 15 24271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24271 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24271) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24271 : oddCount 24271 15 = 13 ∧ acceleratedOrbit 15 24271 = 1180979 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24271 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24271) = 3 ^ 13 * m + 1180979 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24271.1, data_15_24271.2]

/-- Complete interval computation for depth 15, residue 24272. -/
theorem bounds_15_24272 : exactInterval 15 24272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24272 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24272) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24272 : oddCount 24272 15 = 6 ∧ acceleratedOrbit 15 24272 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24272 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24272) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24272.1, data_15_24272.2]

/-- Complete interval computation for depth 15, residue 24273. -/
theorem bounds_15_24273 : exactInterval 15 24273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24273 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24273) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24273 : oddCount 24273 15 = 8 ∧ acceleratedOrbit 15 24273 = 4862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24273 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24273) = 3 ^ 8 * m + 4862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24273.1, data_15_24273.2]

/-- Complete interval computation for depth 15, residue 24274. -/
theorem bounds_15_24274 : exactInterval 15 24274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24274 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24274) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24274 : oddCount 24274 15 = 8 ∧ acceleratedOrbit 15 24274 = 4862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24274 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24274) = 3 ^ 8 * m + 4862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24274.1, data_15_24274.2]

/-- Complete interval computation for depth 15, residue 24275. -/
theorem bounds_15_24275 : exactInterval 15 24275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24275 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24275) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24275 : oddCount 24275 15 = 8 ∧ acceleratedOrbit 15 24275 = 4862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24275 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24275) = 3 ^ 8 * m + 4862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24275.1, data_15_24275.2]

/-- Complete interval computation for depth 15, residue 24276. -/
theorem bounds_15_24276 : exactInterval 15 24276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24276 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24276) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24276 : oddCount 24276 15 = 6 ∧ acceleratedOrbit 15 24276 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24276 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24276) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24276.1, data_15_24276.2]

/-- Complete interval computation for depth 15, residue 24277. -/
theorem bounds_15_24277 : exactInterval 15 24277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24277 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24277) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24277 : oddCount 24277 15 = 6 ∧ acceleratedOrbit 15 24277 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24277 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24277) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24277.1, data_15_24277.2]

/-- Complete interval computation for depth 15, residue 24278. -/
theorem bounds_15_24278 : exactInterval 15 24278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24278 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24278) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24278 : oddCount 24278 15 = 7 ∧ acceleratedOrbit 15 24278 = 1621 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24278 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24278) = 3 ^ 7 * m + 1621 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24278.1, data_15_24278.2]

/-- Complete interval computation for depth 15, residue 24279. -/
theorem bounds_15_24279 : exactInterval 15 24279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24279 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24279) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24279 : oddCount 24279 15 = 7 ∧ acceleratedOrbit 15 24279 = 1621 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24279 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24279) = 3 ^ 7 * m + 1621 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24279.1, data_15_24279.2]

/-- Complete interval computation for depth 15, residue 24280. -/
theorem bounds_15_24280 : exactInterval 15 24280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24280 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24280) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24280 : oddCount 24280 15 = 7 ∧ acceleratedOrbit 15 24280 = 1622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24280 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24280) = 3 ^ 7 * m + 1622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24280.1, data_15_24280.2]

end Collatz.Research.PassageAtlas.Batch0741
