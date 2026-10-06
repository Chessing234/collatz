import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0284

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 9273. -/
theorem bounds_15_9273 : exactInterval 15 9273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9273 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9273) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9273 : oddCount 9273 15 = 8 ∧ acceleratedOrbit 15 9273 = 1858 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9273 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9273) = 3 ^ 8 * m + 1858 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9273.1, data_15_9273.2]

/-- Complete interval computation for depth 15, residue 9274. -/
theorem bounds_15_9274 : exactInterval 15 9274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9274 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9274) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9274 : oddCount 9274 15 = 8 ∧ acceleratedOrbit 15 9274 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9274 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9274) = 3 ^ 8 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9274.1, data_15_9274.2]

/-- Complete interval computation for depth 15, residue 9275. -/
theorem bounds_15_9275 : exactInterval 15 9275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9275 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9275) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9275 : oddCount 9275 15 = 8 ∧ acceleratedOrbit 15 9275 = 1858 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9275 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9275) = 3 ^ 8 * m + 1858 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9275.1, data_15_9275.2]

/-- Complete interval computation for depth 15, residue 9276. -/
theorem bounds_15_9276 : exactInterval 15 9276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9276 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9276) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9276 : oddCount 9276 15 = 8 ∧ acceleratedOrbit 15 9276 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9276 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9276) = 3 ^ 8 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9276.1, data_15_9276.2]

/-- Complete interval computation for depth 15, residue 9277. -/
theorem bounds_15_9277 : exactInterval 15 9277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9277 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9277) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9277 : oddCount 9277 15 = 8 ∧ acceleratedOrbit 15 9277 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9277 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9277) = 3 ^ 8 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9277.1, data_15_9277.2]

/-- Complete interval computation for depth 15, residue 9278. -/
theorem bounds_15_9278 : exactInterval 15 9278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9278 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9278) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9278 : oddCount 9278 15 = 9 ∧ acceleratedOrbit 15 9278 = 5575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9278 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9278) = 3 ^ 9 * m + 5575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9278.1, data_15_9278.2]

/-- Complete interval computation for depth 15, residue 9279. -/
theorem bounds_15_9279 : exactInterval 15 9279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9279 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9279) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9279 : oddCount 9279 15 = 9 ∧ acceleratedOrbit 15 9279 = 5575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9279 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9279) = 3 ^ 9 * m + 5575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9279.1, data_15_9279.2]

/-- Complete interval computation for depth 15, residue 9280. -/
theorem bounds_15_9280 : exactInterval 15 9280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9280 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9280) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9280 : oddCount 9280 15 = 5 ∧ acceleratedOrbit 15 9280 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9280 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9280) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9280.1, data_15_9280.2]

/-- Complete interval computation for depth 15, residue 9281. -/
theorem bounds_15_9281 : exactInterval 15 9281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9281 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9281) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9281 : oddCount 9281 15 = 8 ∧ acceleratedOrbit 15 9281 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9281 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9281) = 3 ^ 8 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9281.1, data_15_9281.2]

/-- Complete interval computation for depth 15, residue 9282. -/
theorem bounds_15_9282 : exactInterval 15 9282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9282 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9282) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9282 : oddCount 9282 15 = 8 ∧ acceleratedOrbit 15 9282 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9282 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9282) = 3 ^ 8 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9282.1, data_15_9282.2]

/-- Complete interval computation for depth 15, residue 9283. -/
theorem bounds_15_9283 : exactInterval 15 9283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9283 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9283) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9283 : oddCount 9283 15 = 8 ∧ acceleratedOrbit 15 9283 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9283 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9283) = 3 ^ 8 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9283.1, data_15_9283.2]

/-- Complete interval computation for depth 15, residue 9284. -/
theorem bounds_15_9284 : exactInterval 15 9284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9284 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9284) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9284 : oddCount 9284 15 = 4 ∧ acceleratedOrbit 15 9284 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9284 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9284) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9284.1, data_15_9284.2]

/-- Complete interval computation for depth 15, residue 9285. -/
theorem bounds_15_9285 : exactInterval 15 9285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9285 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9285) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9285 : oddCount 9285 15 = 4 ∧ acceleratedOrbit 15 9285 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9285 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9285) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9285.1, data_15_9285.2]

/-- Complete interval computation for depth 15, residue 9286. -/
theorem bounds_15_9286 : exactInterval 15 9286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9286 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9286) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9286 : oddCount 9286 15 = 4 ∧ acceleratedOrbit 15 9286 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9286 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9286) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9286.1, data_15_9286.2]

/-- Complete interval computation for depth 15, residue 9287. -/
theorem bounds_15_9287 : exactInterval 15 9287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9287 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9287) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9287 : oddCount 9287 15 = 11 ∧ acceleratedOrbit 15 9287 = 50219 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9287 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9287) = 3 ^ 11 * m + 50219 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9287.1, data_15_9287.2]

/-- Complete interval computation for depth 15, residue 9288. -/
theorem bounds_15_9288 : exactInterval 15 9288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9288 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9288) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9288 : oddCount 9288 15 = 10 ∧ acceleratedOrbit 15 9288 = 16766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9288 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9288) = 3 ^ 10 * m + 16766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9288.1, data_15_9288.2]

/-- Complete interval computation for depth 15, residue 9289. -/
theorem bounds_15_9289 : exactInterval 15 9289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9289 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9289) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9289 : oddCount 9289 15 = 9 ∧ acceleratedOrbit 15 9289 = 5582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9289 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9289) = 3 ^ 9 * m + 5582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9289.1, data_15_9289.2]

/-- Complete interval computation for depth 15, residue 9290. -/
theorem bounds_15_9290 : exactInterval 15 9290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9290 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9290) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9290 : oddCount 9290 15 = 10 ∧ acceleratedOrbit 15 9290 = 16766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9290 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9290) = 3 ^ 10 * m + 16766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9290.1, data_15_9290.2]

/-- Complete interval computation for depth 15, residue 9291. -/
theorem bounds_15_9291 : exactInterval 15 9291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9291 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9291) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9291 : oddCount 9291 15 = 4 ∧ acceleratedOrbit 15 9291 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9291 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9291) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9291.1, data_15_9291.2]

/-- Complete interval computation for depth 15, residue 9292. -/
theorem bounds_15_9292 : exactInterval 15 9292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9292 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9292) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9292 : oddCount 9292 15 = 10 ∧ acceleratedOrbit 15 9292 = 16766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9292 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9292) = 3 ^ 10 * m + 16766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9292.1, data_15_9292.2]

/-- Complete interval computation for depth 15, residue 9293. -/
theorem bounds_15_9293 : exactInterval 15 9293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9293 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9293) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9293 : oddCount 9293 15 = 10 ∧ acceleratedOrbit 15 9293 = 16766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9293 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9293) = 3 ^ 10 * m + 16766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9293.1, data_15_9293.2]

/-- Complete interval computation for depth 15, residue 9294. -/
theorem bounds_15_9294 : exactInterval 15 9294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9294 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9294) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9294 : oddCount 9294 15 = 9 ∧ acceleratedOrbit 15 9294 = 5588 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9294 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9294) = 3 ^ 9 * m + 5588 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9294.1, data_15_9294.2]

/-- Complete interval computation for depth 15, residue 9295. -/
theorem bounds_15_9295 : exactInterval 15 9295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9295 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9295) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9295 : oddCount 9295 15 = 9 ∧ acceleratedOrbit 15 9295 = 5588 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9295 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9295) = 3 ^ 9 * m + 5588 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9295.1, data_15_9295.2]

/-- Complete interval computation for depth 15, residue 9296. -/
theorem bounds_15_9296 : exactInterval 15 9296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9296 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9296) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9296 : oddCount 9296 15 = 5 ∧ acceleratedOrbit 15 9296 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9296 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9296) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9296.1, data_15_9296.2]

/-- Complete interval computation for depth 15, residue 9297. -/
theorem bounds_15_9297 : exactInterval 15 9297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9297 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9297) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9297 : oddCount 9297 15 = 10 ∧ acceleratedOrbit 15 9297 = 16766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9297 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9297) = 3 ^ 10 * m + 16766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9297.1, data_15_9297.2]

/-- Complete interval computation for depth 15, residue 9298. -/
theorem bounds_15_9298 : exactInterval 15 9298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9298 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9298) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9298 : oddCount 9298 15 = 10 ∧ acceleratedOrbit 15 9298 = 16762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9298 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9298) = 3 ^ 10 * m + 16762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9298.1, data_15_9298.2]

/-- Complete interval computation for depth 15, residue 9299. -/
theorem bounds_15_9299 : exactInterval 15 9299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9299 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9299) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9299 : oddCount 9299 15 = 10 ∧ acceleratedOrbit 15 9299 = 16762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9299 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9299) = 3 ^ 10 * m + 16762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9299.1, data_15_9299.2]

/-- Complete interval computation for depth 15, residue 9300. -/
theorem bounds_15_9300 : exactInterval 15 9300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9300 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9300) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9300 : oddCount 9300 15 = 5 ∧ acceleratedOrbit 15 9300 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9300 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9300) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9300.1, data_15_9300.2]

/-- Complete interval computation for depth 15, residue 9301. -/
theorem bounds_15_9301 : exactInterval 15 9301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9301 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9301) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9301 : oddCount 9301 15 = 5 ∧ acceleratedOrbit 15 9301 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9301 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9301) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9301.1, data_15_9301.2]

/-- Complete interval computation for depth 15, residue 9302. -/
theorem bounds_15_9302 : exactInterval 15 9302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9302 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9302) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9302 : oddCount 9302 15 = 4 ∧ acceleratedOrbit 15 9302 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9302 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9302) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9302.1, data_15_9302.2]

/-- Complete interval computation for depth 15, residue 9303. -/
theorem bounds_15_9303 : exactInterval 15 9303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9303 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9303) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9303 : oddCount 9303 15 = 4 ∧ acceleratedOrbit 15 9303 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9303 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9303) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9303.1, data_15_9303.2]

/-- Complete interval computation for depth 15, residue 9304. -/
theorem bounds_15_9304 : exactInterval 15 9304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9304 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9304) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9304 : oddCount 9304 15 = 7 ∧ acceleratedOrbit 15 9304 = 623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9304 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9304) = 3 ^ 7 * m + 623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9304.1, data_15_9304.2]

/-- Complete interval computation for depth 15, residue 9305. -/
theorem bounds_15_9305 : exactInterval 15 9305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9305 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9305) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9305 : oddCount 9305 15 = 8 ∧ acceleratedOrbit 15 9305 = 1865 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9305 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9305) = 3 ^ 8 * m + 1865 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9305.1, data_15_9305.2]

end Collatz.Research.PassageAtlas.Batch0284
