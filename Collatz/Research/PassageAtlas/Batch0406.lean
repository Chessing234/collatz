import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0406

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 13271. -/
theorem bounds_15_13271 : exactInterval 15 13271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13271 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13271) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13271 : oddCount 13271 15 = 10 ∧ acceleratedOrbit 15 13271 = 23921 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13271 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13271) = 3 ^ 10 * m + 23921 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13271.1, data_15_13271.2]

/-- Complete interval computation for depth 15, residue 13272. -/
theorem bounds_15_13272 : exactInterval 15 13272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13272 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13272) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13272 : oddCount 13272 15 = 6 ∧ acceleratedOrbit 15 13272 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13272 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13272) = 3 ^ 6 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13272.1, data_15_13272.2]

/-- Complete interval computation for depth 15, residue 13273. -/
theorem bounds_15_13273 : exactInterval 15 13273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13273 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13273) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13273 : oddCount 13273 15 = 7 ∧ acceleratedOrbit 15 13273 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13273 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13273) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13273.1, data_15_13273.2]

/-- Complete interval computation for depth 15, residue 13274. -/
theorem bounds_15_13274 : exactInterval 15 13274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13274 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13274) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13274 : oddCount 13274 15 = 6 ∧ acceleratedOrbit 15 13274 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13274 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13274) = 3 ^ 6 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13274.1, data_15_13274.2]

/-- Complete interval computation for depth 15, residue 13275. -/
theorem bounds_15_13275 : exactInterval 15 13275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13275 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13275) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13275 : oddCount 13275 15 = 8 ∧ acceleratedOrbit 15 13275 = 2659 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13275 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13275) = 3 ^ 8 * m + 2659 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13275.1, data_15_13275.2]

/-- Complete interval computation for depth 15, residue 13276. -/
theorem bounds_15_13276 : exactInterval 15 13276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13276 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13276) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13276 : oddCount 13276 15 = 6 ∧ acceleratedOrbit 15 13276 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13276 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13276) = 3 ^ 6 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13276.1, data_15_13276.2]

/-- Complete interval computation for depth 15, residue 13277. -/
theorem bounds_15_13277 : exactInterval 15 13277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13277 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13277) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13277 : oddCount 13277 15 = 6 ∧ acceleratedOrbit 15 13277 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13277 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13277) = 3 ^ 6 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13277.1, data_15_13277.2]

/-- Complete interval computation for depth 15, residue 13278. -/
theorem bounds_15_13278 : exactInterval 15 13278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13278 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13278) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13278 : oddCount 13278 15 = 10 ∧ acceleratedOrbit 15 13278 = 23932 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13278 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13278) = 3 ^ 10 * m + 23932 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13278.1, data_15_13278.2]

/-- Complete interval computation for depth 15, residue 13279. -/
theorem bounds_15_13279 : exactInterval 15 13279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13279 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13279) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13279 : oddCount 13279 15 = 10 ∧ acceleratedOrbit 15 13279 = 23932 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13279 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13279) = 3 ^ 10 * m + 23932 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13279.1, data_15_13279.2]

/-- Complete interval computation for depth 15, residue 13280. -/
theorem bounds_15_13280 : exactInterval 15 13280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13280 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13280) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13280 : oddCount 13280 15 = 8 ∧ acceleratedOrbit 15 13280 = 2666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13280 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13280) = 3 ^ 8 * m + 2666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13280.1, data_15_13280.2]

/-- Complete interval computation for depth 15, residue 13281. -/
theorem bounds_15_13281 : exactInterval 15 13281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13281 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13281) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13281 : oddCount 13281 15 = 10 ∧ acceleratedOrbit 15 13281 = 23939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13281 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13281) = 3 ^ 10 * m + 23939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13281.1, data_15_13281.2]

/-- Complete interval computation for depth 15, residue 13282. -/
theorem bounds_15_13282 : exactInterval 15 13282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13282 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13282) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13282 : oddCount 13282 15 = 7 ∧ acceleratedOrbit 15 13282 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13282 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13282) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13282.1, data_15_13282.2]

/-- Complete interval computation for depth 15, residue 13283. -/
theorem bounds_15_13283 : exactInterval 15 13283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13283 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13283) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13283 : oddCount 13283 15 = 7 ∧ acceleratedOrbit 15 13283 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13283 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13283) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13283.1, data_15_13283.2]

/-- Complete interval computation for depth 15, residue 13284. -/
theorem bounds_15_13284 : exactInterval 15 13284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13284 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13284) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13284 : oddCount 13284 15 = 8 ∧ acceleratedOrbit 15 13284 = 2663 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13284 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13284) = 3 ^ 8 * m + 2663 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13284.1, data_15_13284.2]

/-- Complete interval computation for depth 15, residue 13285. -/
theorem bounds_15_13285 : exactInterval 15 13285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13285 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13285) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13285 : oddCount 13285 15 = 8 ∧ acceleratedOrbit 15 13285 = 2663 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13285 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13285) = 3 ^ 8 * m + 2663 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13285.1, data_15_13285.2]

/-- Complete interval computation for depth 15, residue 13286. -/
theorem bounds_15_13286 : exactInterval 15 13286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13286 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13286) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13286 : oddCount 13286 15 = 8 ∧ acceleratedOrbit 15 13286 = 2663 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13286 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13286) = 3 ^ 8 * m + 2663 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13286.1, data_15_13286.2]

/-- Complete interval computation for depth 15, residue 13287. -/
theorem bounds_15_13287 : exactInterval 15 13287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13287 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13287) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13287 : oddCount 13287 15 = 7 ∧ acceleratedOrbit 15 13287 = 887 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13287 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13287) = 3 ^ 7 * m + 887 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13287.1, data_15_13287.2]

/-- Complete interval computation for depth 15, residue 13288. -/
theorem bounds_15_13288 : exactInterval 15 13288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13288 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13288) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13288 : oddCount 13288 15 = 8 ∧ acceleratedOrbit 15 13288 = 2666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13288 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13288) = 3 ^ 8 * m + 2666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13288.1, data_15_13288.2]

/-- Complete interval computation for depth 15, residue 13289. -/
theorem bounds_15_13289 : exactInterval 15 13289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13289 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13289) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13289 : oddCount 13289 15 = 10 ∧ acceleratedOrbit 15 13289 = 23951 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13289 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13289) = 3 ^ 10 * m + 23951 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13289.1, data_15_13289.2]

/-- Complete interval computation for depth 15, residue 13290. -/
theorem bounds_15_13290 : exactInterval 15 13290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13290 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13290) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13290 : oddCount 13290 15 = 8 ∧ acceleratedOrbit 15 13290 = 2666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13290 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13290) = 3 ^ 8 * m + 2666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13290.1, data_15_13290.2]

/-- Complete interval computation for depth 15, residue 13291. -/
theorem bounds_15_13291 : exactInterval 15 13291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13291 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13291) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13291 : oddCount 13291 15 = 9 ∧ acceleratedOrbit 15 13291 = 7985 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13291 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13291) = 3 ^ 9 * m + 7985 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13291.1, data_15_13291.2]

/-- Complete interval computation for depth 15, residue 13292. -/
theorem bounds_15_13292 : exactInterval 15 13292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13292 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13292) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13292 : oddCount 13292 15 = 10 ∧ acceleratedOrbit 15 13292 = 23966 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13292 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13292) = 3 ^ 10 * m + 23966 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13292.1, data_15_13292.2]

/-- Complete interval computation for depth 15, residue 13293. -/
theorem bounds_15_13293 : exactInterval 15 13293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13293 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13293) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13293 : oddCount 13293 15 = 10 ∧ acceleratedOrbit 15 13293 = 23966 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13293 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13293) = 3 ^ 10 * m + 23966 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13293.1, data_15_13293.2]

/-- Complete interval computation for depth 15, residue 13294. -/
theorem bounds_15_13294 : exactInterval 15 13294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13294 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13294) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13294 : oddCount 13294 15 = 10 ∧ acceleratedOrbit 15 13294 = 23966 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13294 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13294) = 3 ^ 10 * m + 23966 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13294.1, data_15_13294.2]

/-- Complete interval computation for depth 15, residue 13295. -/
theorem bounds_15_13295 : exactInterval 15 13295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13295 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13295) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13295 : oddCount 13295 15 = 9 ∧ acceleratedOrbit 15 13295 = 7987 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13295 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13295) = 3 ^ 9 * m + 7987 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13295.1, data_15_13295.2]

/-- Complete interval computation for depth 15, residue 13296. -/
theorem bounds_15_13296 : exactInterval 15 13296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13296 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13296) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13296 : oddCount 13296 15 = 8 ∧ acceleratedOrbit 15 13296 = 2666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13296 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13296) = 3 ^ 8 * m + 2666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13296.1, data_15_13296.2]

/-- Complete interval computation for depth 15, residue 13297. -/
theorem bounds_15_13297 : exactInterval 15 13297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13297 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13297) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13297 : oddCount 13297 15 = 8 ∧ acceleratedOrbit 15 13297 = 2666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13297 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13297) = 3 ^ 8 * m + 2666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13297.1, data_15_13297.2]

/-- Complete interval computation for depth 15, residue 13298. -/
theorem bounds_15_13298 : exactInterval 15 13298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13298 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13298) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13298 : oddCount 13298 15 = 10 ∧ acceleratedOrbit 15 13298 = 23975 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13298 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13298) = 3 ^ 10 * m + 23975 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13298.1, data_15_13298.2]

/-- Complete interval computation for depth 15, residue 13299. -/
theorem bounds_15_13299 : exactInterval 15 13299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13299 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13299) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13299 : oddCount 13299 15 = 10 ∧ acceleratedOrbit 15 13299 = 23975 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13299 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13299) = 3 ^ 10 * m + 23975 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13299.1, data_15_13299.2]

/-- Complete interval computation for depth 15, residue 13300. -/
theorem bounds_15_13300 : exactInterval 15 13300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13300 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13300) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13300 : oddCount 13300 15 = 8 ∧ acceleratedOrbit 15 13300 = 2666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13300 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13300) = 3 ^ 8 * m + 2666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13300.1, data_15_13300.2]

/-- Complete interval computation for depth 15, residue 13301. -/
theorem bounds_15_13301 : exactInterval 15 13301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13301 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13301) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13301 : oddCount 13301 15 = 8 ∧ acceleratedOrbit 15 13301 = 2666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13301 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13301) = 3 ^ 8 * m + 2666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13301.1, data_15_13301.2]

/-- Complete interval computation for depth 15, residue 13302. -/
theorem bounds_15_13302 : exactInterval 15 13302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13302 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13302) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13302 : oddCount 13302 15 = 6 ∧ acceleratedOrbit 15 13302 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13302 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13302) = 3 ^ 6 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13302.1, data_15_13302.2]

end Collatz.Research.PassageAtlas.Batch0406
