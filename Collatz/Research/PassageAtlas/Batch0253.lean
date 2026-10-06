import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0253

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 8257. -/
theorem bounds_15_8257 : exactInterval 15 8257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8257 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8257) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8257 : oddCount 8257 15 = 9 ∧ acceleratedOrbit 15 8257 = 4967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8257 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8257) = 3 ^ 9 * m + 4967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8257.1, data_15_8257.2]

/-- Complete interval computation for depth 15, residue 8258. -/
theorem bounds_15_8258 : exactInterval 15 8258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8258 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8258) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8258 : oddCount 8258 15 = 9 ∧ acceleratedOrbit 15 8258 = 4967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8258 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8258) = 3 ^ 9 * m + 4967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8258.1, data_15_8258.2]

/-- Complete interval computation for depth 15, residue 8259. -/
theorem bounds_15_8259 : exactInterval 15 8259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8259 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8259) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8259 : oddCount 8259 15 = 9 ∧ acceleratedOrbit 15 8259 = 4967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8259 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8259) = 3 ^ 9 * m + 4967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8259.1, data_15_8259.2]

/-- Complete interval computation for depth 15, residue 8260. -/
theorem bounds_15_8260 : exactInterval 15 8260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8260 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8260) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8260 : oddCount 8260 15 = 5 ∧ acceleratedOrbit 15 8260 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8260 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8260) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8260.1, data_15_8260.2]

/-- Complete interval computation for depth 15, residue 8261. -/
theorem bounds_15_8261 : exactInterval 15 8261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8261 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8261) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8261 : oddCount 8261 15 = 5 ∧ acceleratedOrbit 15 8261 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8261 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8261) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8261.1, data_15_8261.2]

/-- Complete interval computation for depth 15, residue 8262. -/
theorem bounds_15_8262 : exactInterval 15 8262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8262 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8262) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8262 : oddCount 8262 15 = 5 ∧ acceleratedOrbit 15 8262 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8262 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8262) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8262.1, data_15_8262.2]

/-- Complete interval computation for depth 15, residue 8263. -/
theorem bounds_15_8263 : exactInterval 15 8263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8263 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8263) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8263 : oddCount 8263 15 = 10 ∧ acceleratedOrbit 15 8263 = 14894 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8263 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8263) = 3 ^ 10 * m + 14894 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8263.1, data_15_8263.2]

/-- Complete interval computation for depth 15, residue 8264. -/
theorem bounds_15_8264 : exactInterval 15 8264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8264 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8264) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8264 : oddCount 8264 15 = 7 ∧ acceleratedOrbit 15 8264 = 553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8264 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8264) = 3 ^ 7 * m + 553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8264.1, data_15_8264.2]

/-- Complete interval computation for depth 15, residue 8265. -/
theorem bounds_15_8265 : exactInterval 15 8265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8265 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8265) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8265 : oddCount 8265 15 = 10 ∧ acceleratedOrbit 15 8265 = 14899 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8265 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8265) = 3 ^ 10 * m + 14899 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8265.1, data_15_8265.2]

/-- Complete interval computation for depth 15, residue 8266. -/
theorem bounds_15_8266 : exactInterval 15 8266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8266 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8266) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8266 : oddCount 8266 15 = 7 ∧ acceleratedOrbit 15 8266 = 553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8266 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8266) = 3 ^ 7 * m + 553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8266.1, data_15_8266.2]

/-- Complete interval computation for depth 15, residue 8267. -/
theorem bounds_15_8267 : exactInterval 15 8267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8267 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8267) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8267 : oddCount 8267 15 = 5 ∧ acceleratedOrbit 15 8267 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8267 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8267) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8267.1, data_15_8267.2]

/-- Complete interval computation for depth 15, residue 8268. -/
theorem bounds_15_8268 : exactInterval 15 8268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8268 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8268) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8268 : oddCount 8268 15 = 7 ∧ acceleratedOrbit 15 8268 = 553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8268 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8268) = 3 ^ 7 * m + 553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8268.1, data_15_8268.2]

/-- Complete interval computation for depth 15, residue 8269. -/
theorem bounds_15_8269 : exactInterval 15 8269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8269 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8269) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8269 : oddCount 8269 15 = 7 ∧ acceleratedOrbit 15 8269 = 553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8269 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8269) = 3 ^ 7 * m + 553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8269.1, data_15_8269.2]

/-- Complete interval computation for depth 15, residue 8270. -/
theorem bounds_15_8270 : exactInterval 15 8270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8270 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8270) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8270 : oddCount 8270 15 = 8 ∧ acceleratedOrbit 15 8270 = 1657 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8270 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8270) = 3 ^ 8 * m + 1657 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8270.1, data_15_8270.2]

/-- Complete interval computation for depth 15, residue 8271. -/
theorem bounds_15_8271 : exactInterval 15 8271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8271 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8271) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8271 : oddCount 8271 15 = 8 ∧ acceleratedOrbit 15 8271 = 1657 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8271 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8271) = 3 ^ 8 * m + 1657 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8271.1, data_15_8271.2]

/-- Complete interval computation for depth 15, residue 8272. -/
theorem bounds_15_8272 : exactInterval 15 8272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8272 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8272) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8272 : oddCount 8272 15 = 6 ∧ acceleratedOrbit 15 8272 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8272 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8272) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8272.1, data_15_8272.2]

/-- Complete interval computation for depth 15, residue 8273. -/
theorem bounds_15_8273 : exactInterval 15 8273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8273 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8273) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8273 : oddCount 8273 15 = 7 ∧ acceleratedOrbit 15 8273 = 553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8273 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8273) = 3 ^ 7 * m + 553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8273.1, data_15_8273.2]

/-- Complete interval computation for depth 15, residue 8274. -/
theorem bounds_15_8274 : exactInterval 15 8274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8274 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8274) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8274 : oddCount 8274 15 = 10 ∧ acceleratedOrbit 15 8274 = 14917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8274 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8274) = 3 ^ 10 * m + 14917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8274.1, data_15_8274.2]

/-- Complete interval computation for depth 15, residue 8275. -/
theorem bounds_15_8275 : exactInterval 15 8275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8275 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8275) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8275 : oddCount 8275 15 = 10 ∧ acceleratedOrbit 15 8275 = 14917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8275 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8275) = 3 ^ 10 * m + 14917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8275.1, data_15_8275.2]

/-- Complete interval computation for depth 15, residue 8276. -/
theorem bounds_15_8276 : exactInterval 15 8276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8276 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8276) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8276 : oddCount 8276 15 = 6 ∧ acceleratedOrbit 15 8276 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8276 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8276) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8276.1, data_15_8276.2]

/-- Complete interval computation for depth 15, residue 8277. -/
theorem bounds_15_8277 : exactInterval 15 8277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8277 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8277) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8277 : oddCount 8277 15 = 6 ∧ acceleratedOrbit 15 8277 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8277 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8277) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8277.1, data_15_8277.2]

/-- Complete interval computation for depth 15, residue 8278. -/
theorem bounds_15_8278 : exactInterval 15 8278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8278 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8278) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8278 : oddCount 8278 15 = 8 ∧ acceleratedOrbit 15 8278 = 1660 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8278 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8278) = 3 ^ 8 * m + 1660 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8278.1, data_15_8278.2]

/-- Complete interval computation for depth 15, residue 8279. -/
theorem bounds_15_8279 : exactInterval 15 8279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8279 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8279) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8279 : oddCount 8279 15 = 8 ∧ acceleratedOrbit 15 8279 = 1660 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8279 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8279) = 3 ^ 8 * m + 1660 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8279.1, data_15_8279.2]

/-- Complete interval computation for depth 15, residue 8280. -/
theorem bounds_15_8280 : exactInterval 15 8280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8280 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8280) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8280 : oddCount 8280 15 = 5 ∧ acceleratedOrbit 15 8280 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8280 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8280) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8280.1, data_15_8280.2]

/-- Complete interval computation for depth 15, residue 8281. -/
theorem bounds_15_8281 : exactInterval 15 8281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8281 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8281) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8281 : oddCount 8281 15 = 8 ∧ acceleratedOrbit 15 8281 = 1660 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8281 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8281) = 3 ^ 8 * m + 1660 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8281.1, data_15_8281.2]

/-- Complete interval computation for depth 15, residue 8282. -/
theorem bounds_15_8282 : exactInterval 15 8282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8282 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8282) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8282 : oddCount 8282 15 = 5 ∧ acceleratedOrbit 15 8282 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8282 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8282) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8282.1, data_15_8282.2]

/-- Complete interval computation for depth 15, residue 8283. -/
theorem bounds_15_8283 : exactInterval 15 8283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8283 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8283) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8283 : oddCount 8283 15 = 11 ∧ acceleratedOrbit 15 8283 = 44788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8283 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8283) = 3 ^ 11 * m + 44788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8283.1, data_15_8283.2]

/-- Complete interval computation for depth 15, residue 8284. -/
theorem bounds_15_8284 : exactInterval 15 8284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8284 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8284) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8284 : oddCount 8284 15 = 5 ∧ acceleratedOrbit 15 8284 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8284 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8284) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8284.1, data_15_8284.2]

/-- Complete interval computation for depth 15, residue 8285. -/
theorem bounds_15_8285 : exactInterval 15 8285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8285 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8285) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8285 : oddCount 8285 15 = 5 ∧ acceleratedOrbit 15 8285 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8285 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8285) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8285.1, data_15_8285.2]

/-- Complete interval computation for depth 15, residue 8286. -/
theorem bounds_15_8286 : exactInterval 15 8286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8286 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8286) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8286 : oddCount 8286 15 = 9 ∧ acceleratedOrbit 15 8286 = 4979 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8286 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8286) = 3 ^ 9 * m + 4979 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8286.1, data_15_8286.2]

/-- Complete interval computation for depth 15, residue 8287. -/
theorem bounds_15_8287 : exactInterval 15 8287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8287 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8287) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8287 : oddCount 8287 15 = 9 ∧ acceleratedOrbit 15 8287 = 4979 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8287 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8287) = 3 ^ 9 * m + 4979 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8287.1, data_15_8287.2]

/-- Complete interval computation for depth 15, residue 8288. -/
theorem bounds_15_8288 : exactInterval 15 8288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8288 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8288) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8288 : oddCount 8288 15 = 6 ∧ acceleratedOrbit 15 8288 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8288 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8288) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8288.1, data_15_8288.2]

/-- Complete interval computation for depth 15, residue 8289. -/
theorem bounds_15_8289 : exactInterval 15 8289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8289 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8289) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8289 : oddCount 8289 15 = 10 ∧ acceleratedOrbit 15 8289 = 14944 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8289 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8289) = 3 ^ 10 * m + 14944 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8289.1, data_15_8289.2]

end Collatz.Research.PassageAtlas.Batch0253
