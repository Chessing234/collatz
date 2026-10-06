import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0467

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 15269. -/
theorem bounds_15_15269 : exactInterval 15 15269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15269 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15269) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15269 : oddCount 15269 15 = 8 ∧ acceleratedOrbit 15 15269 = 3059 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15269 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15269) = 3 ^ 8 * m + 3059 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15269.1, data_15_15269.2]

/-- Complete interval computation for depth 15, residue 15270. -/
theorem bounds_15_15270 : exactInterval 15 15270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15270 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15270) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15270 : oddCount 15270 15 = 8 ∧ acceleratedOrbit 15 15270 = 3059 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15270 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15270) = 3 ^ 8 * m + 3059 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15270.1, data_15_15270.2]

/-- Complete interval computation for depth 15, residue 15271. -/
theorem bounds_15_15271 : exactInterval 15 15271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15271 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15271) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15271 : oddCount 15271 15 = 8 ∧ acceleratedOrbit 15 15271 = 3058 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15271 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15271) = 3 ^ 8 * m + 3058 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15271.1, data_15_15271.2]

/-- Complete interval computation for depth 15, residue 15272. -/
theorem bounds_15_15272 : exactInterval 15 15272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15272 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15272) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15272 : oddCount 15272 15 = 4 ∧ acceleratedOrbit 15 15272 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15272 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15272) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15272.1, data_15_15272.2]

/-- Complete interval computation for depth 15, residue 15273. -/
theorem bounds_15_15273 : exactInterval 15 15273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15273 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15273) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15273 : oddCount 15273 15 = 10 ∧ acceleratedOrbit 15 15273 = 27526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15273 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15273) = 3 ^ 10 * m + 27526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15273.1, data_15_15273.2]

/-- Complete interval computation for depth 15, residue 15274. -/
theorem bounds_15_15274 : exactInterval 15 15274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15274 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15274) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15274 : oddCount 15274 15 = 4 ∧ acceleratedOrbit 15 15274 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15274 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15274) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15274.1, data_15_15274.2]

/-- Complete interval computation for depth 15, residue 15275. -/
theorem bounds_15_15275 : exactInterval 15 15275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15275 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15275) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15275 : oddCount 15275 15 = 9 ∧ acceleratedOrbit 15 15275 = 9179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15275 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15275) = 3 ^ 9 * m + 9179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15275.1, data_15_15275.2]

/-- Complete interval computation for depth 15, residue 15276. -/
theorem bounds_15_15276 : exactInterval 15 15276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15276 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15276) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15276 : oddCount 15276 15 = 6 ∧ acceleratedOrbit 15 15276 = 340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15276 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15276) = 3 ^ 6 * m + 340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15276.1, data_15_15276.2]

/-- Complete interval computation for depth 15, residue 15277. -/
theorem bounds_15_15277 : exactInterval 15 15277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15277 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15277) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15277 : oddCount 15277 15 = 6 ∧ acceleratedOrbit 15 15277 = 340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15277 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15277) = 3 ^ 6 * m + 340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15277.1, data_15_15277.2]

/-- Complete interval computation for depth 15, residue 15278. -/
theorem bounds_15_15278 : exactInterval 15 15278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15278 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15278) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15278 : oddCount 15278 15 = 6 ∧ acceleratedOrbit 15 15278 = 340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15278 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15278) = 3 ^ 6 * m + 340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15278.1, data_15_15278.2]

/-- Complete interval computation for depth 15, residue 15279. -/
theorem bounds_15_15279 : exactInterval 15 15279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15279 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15279) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15279 : oddCount 15279 15 = 6 ∧ acceleratedOrbit 15 15279 = 340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15279 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15279) = 3 ^ 6 * m + 340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15279.1, data_15_15279.2]

/-- Complete interval computation for depth 15, residue 15280. -/
theorem bounds_15_15280 : exactInterval 15 15280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15280 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15280) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15280 : oddCount 15280 15 = 6 ∧ acceleratedOrbit 15 15280 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15280 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15280) = 3 ^ 6 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15280.1, data_15_15280.2]

/-- Complete interval computation for depth 15, residue 15281. -/
theorem bounds_15_15281 : exactInterval 15 15281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15281 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15281) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15281 : oddCount 15281 15 = 6 ∧ acceleratedOrbit 15 15281 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15281 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15281) = 3 ^ 6 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15281.1, data_15_15281.2]

/-- Complete interval computation for depth 15, residue 15282. -/
theorem bounds_15_15282 : exactInterval 15 15282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15282 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15282) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15282 : oddCount 15282 15 = 6 ∧ acceleratedOrbit 15 15282 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15282 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15282) = 3 ^ 6 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15282.1, data_15_15282.2]

/-- Complete interval computation for depth 15, residue 15283. -/
theorem bounds_15_15283 : exactInterval 15 15283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15283 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15283) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15283 : oddCount 15283 15 = 6 ∧ acceleratedOrbit 15 15283 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15283 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15283) = 3 ^ 6 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15283.1, data_15_15283.2]

/-- Complete interval computation for depth 15, residue 15284. -/
theorem bounds_15_15284 : exactInterval 15 15284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15284 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15284) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15284 : oddCount 15284 15 = 6 ∧ acceleratedOrbit 15 15284 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15284 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15284) = 3 ^ 6 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15284.1, data_15_15284.2]

/-- Complete interval computation for depth 15, residue 15285. -/
theorem bounds_15_15285 : exactInterval 15 15285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15285 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15285) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15285 : oddCount 15285 15 = 6 ∧ acceleratedOrbit 15 15285 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15285 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15285) = 3 ^ 6 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15285.1, data_15_15285.2]

/-- Complete interval computation for depth 15, residue 15286. -/
theorem bounds_15_15286 : exactInterval 15 15286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15286 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15286) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15286 : oddCount 15286 15 = 7 ∧ acceleratedOrbit 15 15286 = 1021 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15286 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15286) = 3 ^ 7 * m + 1021 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15286.1, data_15_15286.2]

/-- Complete interval computation for depth 15, residue 15287. -/
theorem bounds_15_15287 : exactInterval 15 15287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15287 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15287) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15287 : oddCount 15287 15 = 7 ∧ acceleratedOrbit 15 15287 = 1021 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15287 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15287) = 3 ^ 7 * m + 1021 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15287.1, data_15_15287.2]

/-- Complete interval computation for depth 15, residue 15288. -/
theorem bounds_15_15288 : exactInterval 15 15288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15288 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15288) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15288 : oddCount 15288 15 = 6 ∧ acceleratedOrbit 15 15288 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15288 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15288) = 3 ^ 6 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15288.1, data_15_15288.2]

/-- Complete interval computation for depth 15, residue 15289. -/
theorem bounds_15_15289 : exactInterval 15 15289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15289 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15289) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15289 : oddCount 15289 15 = 7 ∧ acceleratedOrbit 15 15289 = 1021 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15289 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15289) = 3 ^ 7 * m + 1021 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15289.1, data_15_15289.2]

/-- Complete interval computation for depth 15, residue 15290. -/
theorem bounds_15_15290 : exactInterval 15 15290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15290 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15290) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15290 : oddCount 15290 15 = 6 ∧ acceleratedOrbit 15 15290 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15290 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15290) = 3 ^ 6 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15290.1, data_15_15290.2]

/-- Complete interval computation for depth 15, residue 15291. -/
theorem bounds_15_15291 : exactInterval 15 15291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15291 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15291) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15291 : oddCount 15291 15 = 7 ∧ acceleratedOrbit 15 15291 = 1021 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15291 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15291) = 3 ^ 7 * m + 1021 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15291.1, data_15_15291.2]

/-- Complete interval computation for depth 15, residue 15292. -/
theorem bounds_15_15292 : exactInterval 15 15292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15292 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15292) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15292 : oddCount 15292 15 = 10 ∧ acceleratedOrbit 15 15292 = 27566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15292 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15292) = 3 ^ 10 * m + 27566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15292.1, data_15_15292.2]

/-- Complete interval computation for depth 15, residue 15293. -/
theorem bounds_15_15293 : exactInterval 15 15293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15293 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15293) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15293 : oddCount 15293 15 = 10 ∧ acceleratedOrbit 15 15293 = 27566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15293 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15293) = 3 ^ 10 * m + 27566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15293.1, data_15_15293.2]

/-- Complete interval computation for depth 15, residue 15294. -/
theorem bounds_15_15294 : exactInterval 15 15294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15294 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15294) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15294 : oddCount 15294 15 = 10 ∧ acceleratedOrbit 15 15294 = 27566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15294 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15294) = 3 ^ 10 * m + 27566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15294.1, data_15_15294.2]

/-- Complete interval computation for depth 15, residue 15295. -/
theorem bounds_15_15295 : exactInterval 15 15295 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15295 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15295) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15295 : oddCount 15295 15 = 9 ∧ acceleratedOrbit 15 15295 = 9188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15295 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15295) = 3 ^ 9 * m + 9188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15295.1, data_15_15295.2]

/-- Complete interval computation for depth 15, residue 15296. -/
theorem bounds_15_15296 : exactInterval 15 15296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15296 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15296) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15296 : oddCount 15296 15 = 8 ∧ acceleratedOrbit 15 15296 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15296 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15296) = 3 ^ 8 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15296.1, data_15_15296.2]

/-- Complete interval computation for depth 15, residue 15297. -/
theorem bounds_15_15297 : exactInterval 15 15297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15297 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15297) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15297 : oddCount 15297 15 = 9 ∧ acceleratedOrbit 15 15297 = 9193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15297 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15297) = 3 ^ 9 * m + 9193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15297.1, data_15_15297.2]

/-- Complete interval computation for depth 15, residue 15298. -/
theorem bounds_15_15298 : exactInterval 15 15298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15298 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15298) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15298 : oddCount 15298 15 = 9 ∧ acceleratedOrbit 15 15298 = 9193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15298 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15298) = 3 ^ 9 * m + 9193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15298.1, data_15_15298.2]

/-- Complete interval computation for depth 15, residue 15299. -/
theorem bounds_15_15299 : exactInterval 15 15299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15299 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15299) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15299 : oddCount 15299 15 = 9 ∧ acceleratedOrbit 15 15299 = 9193 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15299 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15299) = 3 ^ 9 * m + 9193 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15299.1, data_15_15299.2]

/-- Complete interval computation for depth 15, residue 15300. -/
theorem bounds_15_15300 : exactInterval 15 15300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15300 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15300) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15300 : oddCount 15300 15 = 4 ∧ acceleratedOrbit 15 15300 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15300 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15300) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15300.1, data_15_15300.2]

/-- Complete interval computation for depth 15, residue 15301. -/
theorem bounds_15_15301 : exactInterval 15 15301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15301 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15301) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15301 : oddCount 15301 15 = 4 ∧ acceleratedOrbit 15 15301 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15301 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15301) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15301.1, data_15_15301.2]

end Collatz.Research.PassageAtlas.Batch0467
