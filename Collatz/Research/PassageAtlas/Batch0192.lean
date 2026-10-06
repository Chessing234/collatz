import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0192

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 6258. -/
theorem bounds_15_6258 : exactInterval 15 6258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6258 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6258) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6258 : oddCount 6258 15 = 8 ∧ acceleratedOrbit 15 6258 = 1255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6258 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6258) = 3 ^ 8 * m + 1255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6258.1, data_15_6258.2]

/-- Complete interval computation for depth 15, residue 6259. -/
theorem bounds_15_6259 : exactInterval 15 6259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6259 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6259) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6259 : oddCount 6259 15 = 8 ∧ acceleratedOrbit 15 6259 = 1255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6259 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6259) = 3 ^ 8 * m + 1255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6259.1, data_15_6259.2]

/-- Complete interval computation for depth 15, residue 6260. -/
theorem bounds_15_6260 : exactInterval 15 6260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6260 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6260) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6260 : oddCount 6260 15 = 5 ∧ acceleratedOrbit 15 6260 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6260 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6260) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6260.1, data_15_6260.2]

/-- Complete interval computation for depth 15, residue 6261. -/
theorem bounds_15_6261 : exactInterval 15 6261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6261 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6261) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6261 : oddCount 6261 15 = 5 ∧ acceleratedOrbit 15 6261 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6261 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6261) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6261.1, data_15_6261.2]

/-- Complete interval computation for depth 15, residue 6262. -/
theorem bounds_15_6262 : exactInterval 15 6262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6262 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6262) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6262 : oddCount 6262 15 = 9 ∧ acceleratedOrbit 15 6262 = 3766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6262 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6262) = 3 ^ 9 * m + 3766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6262.1, data_15_6262.2]

/-- Complete interval computation for depth 15, residue 6263. -/
theorem bounds_15_6263 : exactInterval 15 6263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6263 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6263) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6263 : oddCount 6263 15 = 9 ∧ acceleratedOrbit 15 6263 = 3766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6263 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6263) = 3 ^ 9 * m + 3766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6263.1, data_15_6263.2]

/-- Complete interval computation for depth 15, residue 6264. -/
theorem bounds_15_6264 : exactInterval 15 6264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6264 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6264) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6264 : oddCount 6264 15 = 5 ∧ acceleratedOrbit 15 6264 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6264 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6264) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6264.1, data_15_6264.2]

/-- Complete interval computation for depth 15, residue 6265. -/
theorem bounds_15_6265 : exactInterval 15 6265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6265 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6265) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6265 : oddCount 6265 15 = 11 ∧ acceleratedOrbit 15 6265 = 33884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6265 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6265) = 3 ^ 11 * m + 33884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6265.1, data_15_6265.2]

/-- Complete interval computation for depth 15, residue 6266. -/
theorem bounds_15_6266 : exactInterval 15 6266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6266 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6266) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6266 : oddCount 6266 15 = 5 ∧ acceleratedOrbit 15 6266 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6266 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6266) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6266.1, data_15_6266.2]

/-- Complete interval computation for depth 15, residue 6267. -/
theorem bounds_15_6267 : exactInterval 15 6267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6267 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6267) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6267 : oddCount 6267 15 = 10 ∧ acceleratedOrbit 15 6267 = 11299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6267 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6267) = 3 ^ 10 * m + 11299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6267.1, data_15_6267.2]

/-- Complete interval computation for depth 15, residue 6268. -/
theorem bounds_15_6268 : exactInterval 15 6268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6268 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6268) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6268 : oddCount 6268 15 = 8 ∧ acceleratedOrbit 15 6268 = 1256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6268 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6268) = 3 ^ 8 * m + 1256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6268.1, data_15_6268.2]

/-- Complete interval computation for depth 15, residue 6269. -/
theorem bounds_15_6269 : exactInterval 15 6269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6269 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6269) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6269 : oddCount 6269 15 = 8 ∧ acceleratedOrbit 15 6269 = 1256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6269 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6269) = 3 ^ 8 * m + 1256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6269.1, data_15_6269.2]

/-- Complete interval computation for depth 15, residue 6270. -/
theorem bounds_15_6270 : exactInterval 15 6270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6270 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6270) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6270 : oddCount 6270 15 = 8 ∧ acceleratedOrbit 15 6270 = 1256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6270 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6270) = 3 ^ 8 * m + 1256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6270.1, data_15_6270.2]

/-- Complete interval computation for depth 15, residue 6271. -/
theorem bounds_15_6271 : exactInterval 15 6271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6271 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6271) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6271 : oddCount 6271 15 = 10 ∧ acceleratedOrbit 15 6271 = 11303 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6271 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6271) = 3 ^ 10 * m + 11303 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6271.1, data_15_6271.2]

/-- Complete interval computation for depth 15, residue 6272. -/
theorem bounds_15_6272 : exactInterval 15 6272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6272 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6272) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6272 : oddCount 6272 15 = 4 ∧ acceleratedOrbit 15 6272 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6272 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6272) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6272.1, data_15_6272.2]

/-- Complete interval computation for depth 15, residue 6273. -/
theorem bounds_15_6273 : exactInterval 15 6273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6273 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6273) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6273 : oddCount 6273 15 = 7 ∧ acceleratedOrbit 15 6273 = 419 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6273 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6273) = 3 ^ 7 * m + 419 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6273.1, data_15_6273.2]

/-- Complete interval computation for depth 15, residue 6274. -/
theorem bounds_15_6274 : exactInterval 15 6274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6274 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6274) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6274 : oddCount 6274 15 = 6 ∧ acceleratedOrbit 15 6274 = 140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6274 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6274) = 3 ^ 6 * m + 140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6274.1, data_15_6274.2]

/-- Complete interval computation for depth 15, residue 6275. -/
theorem bounds_15_6275 : exactInterval 15 6275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6275 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6275) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6275 : oddCount 6275 15 = 6 ∧ acceleratedOrbit 15 6275 = 140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6275 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6275) = 3 ^ 6 * m + 140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6275.1, data_15_6275.2]

/-- Complete interval computation for depth 15, residue 6276. -/
theorem bounds_15_6276 : exactInterval 15 6276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6276 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6276) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6276 : oddCount 6276 15 = 6 ∧ acceleratedOrbit 15 6276 = 140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6276 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6276) = 3 ^ 6 * m + 140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6276.1, data_15_6276.2]

/-- Complete interval computation for depth 15, residue 6277. -/
theorem bounds_15_6277 : exactInterval 15 6277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6277 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6277) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6277 : oddCount 6277 15 = 6 ∧ acceleratedOrbit 15 6277 = 140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6277 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6277) = 3 ^ 6 * m + 140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6277.1, data_15_6277.2]

/-- Complete interval computation for depth 15, residue 6278. -/
theorem bounds_15_6278 : exactInterval 15 6278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6278 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6278) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6278 : oddCount 6278 15 = 6 ∧ acceleratedOrbit 15 6278 = 140 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6278 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6278) = 3 ^ 6 * m + 140 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6278.1, data_15_6278.2]

/-- Complete interval computation for depth 15, residue 6279. -/
theorem bounds_15_6279 : exactInterval 15 6279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6279 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6279) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6279 : oddCount 6279 15 = 8 ∧ acceleratedOrbit 15 6279 = 1259 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6279 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6279) = 3 ^ 8 * m + 1259 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6279.1, data_15_6279.2]

/-- Complete interval computation for depth 15, residue 6280. -/
theorem bounds_15_6280 : exactInterval 15 6280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6280 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6280) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6280 : oddCount 6280 15 = 5 ∧ acceleratedOrbit 15 6280 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6280 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6280) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6280.1, data_15_6280.2]

/-- Complete interval computation for depth 15, residue 6281. -/
theorem bounds_15_6281 : exactInterval 15 6281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6281 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6281) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6281 : oddCount 6281 15 = 8 ∧ acceleratedOrbit 15 6281 = 1258 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6281 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6281) = 3 ^ 8 * m + 1258 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6281.1, data_15_6281.2]

/-- Complete interval computation for depth 15, residue 6282. -/
theorem bounds_15_6282 : exactInterval 15 6282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6282 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6282) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6282 : oddCount 6282 15 = 5 ∧ acceleratedOrbit 15 6282 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6282 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6282) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6282.1, data_15_6282.2]

/-- Complete interval computation for depth 15, residue 6283. -/
theorem bounds_15_6283 : exactInterval 15 6283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6283 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6283) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6283 : oddCount 6283 15 = 10 ∧ acceleratedOrbit 15 6283 = 11330 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6283 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6283) = 3 ^ 10 * m + 11330 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6283.1, data_15_6283.2]

/-- Complete interval computation for depth 15, residue 6284. -/
theorem bounds_15_6284 : exactInterval 15 6284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6284 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6284) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6284 : oddCount 6284 15 = 5 ∧ acceleratedOrbit 15 6284 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6284 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6284) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6284.1, data_15_6284.2]

/-- Complete interval computation for depth 15, residue 6285. -/
theorem bounds_15_6285 : exactInterval 15 6285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6285 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6285) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6285 : oddCount 6285 15 = 5 ∧ acceleratedOrbit 15 6285 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6285 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6285) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6285.1, data_15_6285.2]

/-- Complete interval computation for depth 15, residue 6286. -/
theorem bounds_15_6286 : exactInterval 15 6286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6286 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6286) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6286 : oddCount 6286 15 = 9 ∧ acceleratedOrbit 15 6286 = 3779 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6286 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6286) = 3 ^ 9 * m + 3779 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6286.1, data_15_6286.2]

/-- Complete interval computation for depth 15, residue 6287. -/
theorem bounds_15_6287 : exactInterval 15 6287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6287 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6287) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6287 : oddCount 6287 15 = 9 ∧ acceleratedOrbit 15 6287 = 3779 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6287 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6287) = 3 ^ 9 * m + 3779 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6287.1, data_15_6287.2]

/-- Complete interval computation for depth 15, residue 6288. -/
theorem bounds_15_6288 : exactInterval 15 6288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6288 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6288) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6288 : oddCount 6288 15 = 7 ∧ acceleratedOrbit 15 6288 = 422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6288 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6288) = 3 ^ 7 * m + 422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6288.1, data_15_6288.2]

/-- Complete interval computation for depth 15, residue 6289. -/
theorem bounds_15_6289 : exactInterval 15 6289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6289 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6289) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6289 : oddCount 6289 15 = 9 ∧ acceleratedOrbit 15 6289 = 3782 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6289 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6289) = 3 ^ 9 * m + 3782 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6289.1, data_15_6289.2]

/-- Complete interval computation for depth 15, residue 6290. -/
theorem bounds_15_6290 : exactInterval 15 6290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6290 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6290) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6290 : oddCount 6290 15 = 9 ∧ acceleratedOrbit 15 6290 = 3782 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6290 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6290) = 3 ^ 9 * m + 3782 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6290.1, data_15_6290.2]

end Collatz.Research.PassageAtlas.Batch0192
