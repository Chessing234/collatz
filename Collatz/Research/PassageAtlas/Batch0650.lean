import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0650

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 21266. -/
theorem bounds_15_21266 : exactInterval 15 21266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21266 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21266) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21266 : oddCount 21266 15 = 8 ∧ acceleratedOrbit 15 21266 = 4259 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21266 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21266) = 3 ^ 8 * m + 4259 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21266.1, data_15_21266.2]

/-- Complete interval computation for depth 15, residue 21267. -/
theorem bounds_15_21267 : exactInterval 15 21267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21267 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21267) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21267 : oddCount 21267 15 = 8 ∧ acceleratedOrbit 15 21267 = 4259 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21267 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21267) = 3 ^ 8 * m + 4259 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21267.1, data_15_21267.2]

/-- Complete interval computation for depth 15, residue 21268. -/
theorem bounds_15_21268 : exactInterval 15 21268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21268 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21268) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21268 : oddCount 21268 15 = 6 ∧ acceleratedOrbit 15 21268 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21268 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21268) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21268.1, data_15_21268.2]

/-- Complete interval computation for depth 15, residue 21269. -/
theorem bounds_15_21269 : exactInterval 15 21269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21269 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21269) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21269 : oddCount 21269 15 = 6 ∧ acceleratedOrbit 15 21269 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21269 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21269) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21269.1, data_15_21269.2]

/-- Complete interval computation for depth 15, residue 21270. -/
theorem bounds_15_21270 : exactInterval 15 21270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21270 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21270) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21270 : oddCount 21270 15 = 7 ∧ acceleratedOrbit 15 21270 = 1420 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21270 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21270) = 3 ^ 7 * m + 1420 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21270.1, data_15_21270.2]

/-- Complete interval computation for depth 15, residue 21271. -/
theorem bounds_15_21271 : exactInterval 15 21271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21271 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21271) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21271 : oddCount 21271 15 = 7 ∧ acceleratedOrbit 15 21271 = 1420 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21271 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21271) = 3 ^ 7 * m + 1420 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21271.1, data_15_21271.2]

/-- Complete interval computation for depth 15, residue 21272. -/
theorem bounds_15_21272 : exactInterval 15 21272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21272 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21272) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21272 : oddCount 21272 15 = 6 ∧ acceleratedOrbit 15 21272 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21272 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21272) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21272.1, data_15_21272.2]

/-- Complete interval computation for depth 15, residue 21273. -/
theorem bounds_15_21273 : exactInterval 15 21273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21273 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21273) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21273 : oddCount 21273 15 = 7 ∧ acceleratedOrbit 15 21273 = 1420 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21273 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21273) = 3 ^ 7 * m + 1420 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21273.1, data_15_21273.2]

/-- Complete interval computation for depth 15, residue 21274. -/
theorem bounds_15_21274 : exactInterval 15 21274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21274 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21274) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21274 : oddCount 21274 15 = 6 ∧ acceleratedOrbit 15 21274 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21274 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21274) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21274.1, data_15_21274.2]

/-- Complete interval computation for depth 15, residue 21275. -/
theorem bounds_15_21275 : exactInterval 15 21275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21275 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21275) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21275 : oddCount 21275 15 = 10 ∧ acceleratedOrbit 15 21275 = 38341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21275 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21275) = 3 ^ 10 * m + 38341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21275.1, data_15_21275.2]

/-- Complete interval computation for depth 15, residue 21276. -/
theorem bounds_15_21276 : exactInterval 15 21276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21276 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21276) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21276 : oddCount 21276 15 = 7 ∧ acceleratedOrbit 15 21276 = 1421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21276 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21276) = 3 ^ 7 * m + 1421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21276.1, data_15_21276.2]

/-- Complete interval computation for depth 15, residue 21277. -/
theorem bounds_15_21277 : exactInterval 15 21277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21277 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21277) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21277 : oddCount 21277 15 = 7 ∧ acceleratedOrbit 15 21277 = 1421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21277 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21277) = 3 ^ 7 * m + 1421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21277.1, data_15_21277.2]

/-- Complete interval computation for depth 15, residue 21278. -/
theorem bounds_15_21278 : exactInterval 15 21278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21278 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21278) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21278 : oddCount 21278 15 = 7 ∧ acceleratedOrbit 15 21278 = 1421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21278 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21278) = 3 ^ 7 * m + 1421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21278.1, data_15_21278.2]

/-- Complete interval computation for depth 15, residue 21279. -/
theorem bounds_15_21279 : exactInterval 15 21279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21279 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21279) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21279 : oddCount 21279 15 = 11 ∧ acceleratedOrbit 15 21279 = 115046 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21279 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21279) = 3 ^ 11 * m + 115046 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21279.1, data_15_21279.2]

/-- Complete interval computation for depth 15, residue 21280. -/
theorem bounds_15_21280 : exactInterval 15 21280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21280 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21280) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21280 : oddCount 21280 15 = 6 ∧ acceleratedOrbit 15 21280 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21280 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21280) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21280.1, data_15_21280.2]

/-- Complete interval computation for depth 15, residue 21281. -/
theorem bounds_15_21281 : exactInterval 15 21281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21281 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21281) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21281 : oddCount 21281 15 = 9 ∧ acceleratedOrbit 15 21281 = 12788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21281 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21281) = 3 ^ 9 * m + 12788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21281.1, data_15_21281.2]

/-- Complete interval computation for depth 15, residue 21282. -/
theorem bounds_15_21282 : exactInterval 15 21282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21282 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21282) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21282 : oddCount 21282 15 = 5 ∧ acceleratedOrbit 15 21282 = 158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21282 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21282) = 3 ^ 5 * m + 158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21282.1, data_15_21282.2]

/-- Complete interval computation for depth 15, residue 21283. -/
theorem bounds_15_21283 : exactInterval 15 21283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21283 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21283) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21283 : oddCount 21283 15 = 5 ∧ acceleratedOrbit 15 21283 = 158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21283 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21283) = 3 ^ 5 * m + 158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21283.1, data_15_21283.2]

/-- Complete interval computation for depth 15, residue 21284. -/
theorem bounds_15_21284 : exactInterval 15 21284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21284 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21284) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21284 : oddCount 21284 15 = 5 ∧ acceleratedOrbit 15 21284 = 158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21284 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21284) = 3 ^ 5 * m + 158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21284.1, data_15_21284.2]

/-- Complete interval computation for depth 15, residue 21285. -/
theorem bounds_15_21285 : exactInterval 15 21285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21285 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21285) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21285 : oddCount 21285 15 = 5 ∧ acceleratedOrbit 15 21285 = 158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21285 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21285) = 3 ^ 5 * m + 158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21285.1, data_15_21285.2]

/-- Complete interval computation for depth 15, residue 21286. -/
theorem bounds_15_21286 : exactInterval 15 21286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21286 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21286) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21286 : oddCount 21286 15 = 5 ∧ acceleratedOrbit 15 21286 = 158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21286 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21286) = 3 ^ 5 * m + 158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21286.1, data_15_21286.2]

/-- Complete interval computation for depth 15, residue 21287. -/
theorem bounds_15_21287 : exactInterval 15 21287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21287 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21287) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21287 : oddCount 21287 15 = 11 ∧ acceleratedOrbit 15 21287 = 115091 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21287 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21287) = 3 ^ 11 * m + 115091 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21287.1, data_15_21287.2]

/-- Complete interval computation for depth 15, residue 21288. -/
theorem bounds_15_21288 : exactInterval 15 21288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21288 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21288) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21288 : oddCount 21288 15 = 6 ∧ acceleratedOrbit 15 21288 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21288 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21288) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21288.1, data_15_21288.2]

/-- Complete interval computation for depth 15, residue 21289. -/
theorem bounds_15_21289 : exactInterval 15 21289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21289 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21289) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21289 : oddCount 21289 15 = 7 ∧ acceleratedOrbit 15 21289 = 1421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21289 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21289) = 3 ^ 7 * m + 1421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21289.1, data_15_21289.2]

/-- Complete interval computation for depth 15, residue 21290. -/
theorem bounds_15_21290 : exactInterval 15 21290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21290 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21290) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21290 : oddCount 21290 15 = 6 ∧ acceleratedOrbit 15 21290 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21290 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21290) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21290.1, data_15_21290.2]

/-- Complete interval computation for depth 15, residue 21291. -/
theorem bounds_15_21291 : exactInterval 15 21291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21291 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21291) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21291 : oddCount 21291 15 = 8 ∧ acceleratedOrbit 15 21291 = 4265 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21291 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21291) = 3 ^ 8 * m + 4265 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21291.1, data_15_21291.2]

/-- Complete interval computation for depth 15, residue 21292. -/
theorem bounds_15_21292 : exactInterval 15 21292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21292 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21292) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21292 : oddCount 21292 15 = 5 ∧ acceleratedOrbit 15 21292 = 158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21292 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21292) = 3 ^ 5 * m + 158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21292.1, data_15_21292.2]

/-- Complete interval computation for depth 15, residue 21293. -/
theorem bounds_15_21293 : exactInterval 15 21293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21293 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21293) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21293 : oddCount 21293 15 = 5 ∧ acceleratedOrbit 15 21293 = 158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21293 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21293) = 3 ^ 5 * m + 158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21293.1, data_15_21293.2]

/-- Complete interval computation for depth 15, residue 21294. -/
theorem bounds_15_21294 : exactInterval 15 21294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21294 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21294) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21294 : oddCount 21294 15 = 5 ∧ acceleratedOrbit 15 21294 = 158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21294 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21294) = 3 ^ 5 * m + 158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21294.1, data_15_21294.2]

/-- Complete interval computation for depth 15, residue 21295. -/
theorem bounds_15_21295 : exactInterval 15 21295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21295 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21295) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21295 : oddCount 21295 15 = 9 ∧ acceleratedOrbit 15 21295 = 12793 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21295 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21295) = 3 ^ 9 * m + 12793 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21295.1, data_15_21295.2]

/-- Complete interval computation for depth 15, residue 21296. -/
theorem bounds_15_21296 : exactInterval 15 21296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21296 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21296) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21296 : oddCount 21296 15 = 6 ∧ acceleratedOrbit 15 21296 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21296 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21296) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21296.1, data_15_21296.2]

/-- Complete interval computation for depth 15, residue 21297. -/
theorem bounds_15_21297 : exactInterval 15 21297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21297 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21297) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21297 : oddCount 21297 15 = 5 ∧ acceleratedOrbit 15 21297 = 158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21297 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21297) = 3 ^ 5 * m + 158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21297.1, data_15_21297.2]

/-- Complete interval computation for depth 15, residue 21298. -/
theorem bounds_15_21298 : exactInterval 15 21298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21298 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21298) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21298 : oddCount 21298 15 = 5 ∧ acceleratedOrbit 15 21298 = 158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21298 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21298) = 3 ^ 5 * m + 158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21298.1, data_15_21298.2]

end Collatz.Research.PassageAtlas.Batch0650
