import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0876

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6272. -/
theorem bounds_13_6272 : exactInterval 13 6272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6272 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6272) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6272 : oddCount 6272 13 = 2 ∧ acceleratedOrbit 13 6272 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6272 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6272) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6272.1, data_13_6272.2]

/-- Complete interval computation for depth 13, residue 6273. -/
theorem bounds_13_6273 : exactInterval 13 6273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6273 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6273) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6273 : oddCount 6273 13 = 7 ∧ acceleratedOrbit 13 6273 = 1676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6273 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6273) = 3 ^ 7 * m + 1676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6273.1, data_13_6273.2]

/-- Complete interval computation for depth 13, residue 6274. -/
theorem bounds_13_6274 : exactInterval 13 6274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6274 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6274) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6274 : oddCount 6274 13 = 6 ∧ acceleratedOrbit 13 6274 = 560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6274 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6274) = 3 ^ 6 * m + 560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6274.1, data_13_6274.2]

/-- Complete interval computation for depth 13, residue 6275. -/
theorem bounds_13_6275 : exactInterval 13 6275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6275 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6275) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6275 : oddCount 6275 13 = 6 ∧ acceleratedOrbit 13 6275 = 560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6275 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6275) = 3 ^ 6 * m + 560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6275.1, data_13_6275.2]

/-- Complete interval computation for depth 13, residue 6276. -/
theorem bounds_13_6276 : exactInterval 13 6276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6276 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6276) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6276 : oddCount 6276 13 = 6 ∧ acceleratedOrbit 13 6276 = 560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6276 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6276) = 3 ^ 6 * m + 560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6276.1, data_13_6276.2]

/-- Complete interval computation for depth 13, residue 6277. -/
theorem bounds_13_6277 : exactInterval 13 6277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6277 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6277) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6277 : oddCount 6277 13 = 6 ∧ acceleratedOrbit 13 6277 = 560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6277 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6277) = 3 ^ 6 * m + 560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6277.1, data_13_6277.2]

/-- Complete interval computation for depth 13, residue 6278. -/
theorem bounds_13_6278 : exactInterval 13 6278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6278 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6278) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6278 : oddCount 6278 13 = 6 ∧ acceleratedOrbit 13 6278 = 560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6278 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6278) = 3 ^ 6 * m + 560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6278.1, data_13_6278.2]

/-- Complete interval computation for depth 13, residue 6279. -/
theorem bounds_13_6279 : exactInterval 13 6279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6279 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6279) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6279 : oddCount 6279 13 = 6 ∧ acceleratedOrbit 13 6279 = 559 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6279 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6279) = 3 ^ 6 * m + 559 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6279.1, data_13_6279.2]

/-- Complete interval computation for depth 13, residue 6280. -/
theorem bounds_13_6280 : exactInterval 13 6280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6280 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6280) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6280 : oddCount 6280 13 = 5 ∧ acceleratedOrbit 13 6280 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6280 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6280) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6280.1, data_13_6280.2]

/-- Complete interval computation for depth 13, residue 6281. -/
theorem bounds_13_6281 : exactInterval 13 6281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6281 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6281) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6281 : oddCount 6281 13 = 8 ∧ acceleratedOrbit 13 6281 = 5032 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6281 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6281) = 3 ^ 8 * m + 5032 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6281.1, data_13_6281.2]

/-- Complete interval computation for depth 13, residue 6282. -/
theorem bounds_13_6282 : exactInterval 13 6282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6282 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6282) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6282 : oddCount 6282 13 = 5 ∧ acceleratedOrbit 13 6282 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6282 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6282) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6282.1, data_13_6282.2]

/-- Complete interval computation for depth 13, residue 6283. -/
theorem bounds_13_6283 : exactInterval 13 6283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6283 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6283) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6283 : oddCount 6283 13 = 8 ∧ acceleratedOrbit 13 6283 = 5035 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6283 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6283) = 3 ^ 8 * m + 5035 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6283.1, data_13_6283.2]

/-- Complete interval computation for depth 13, residue 6284. -/
theorem bounds_13_6284 : exactInterval 13 6284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6284 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6284) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6284 : oddCount 6284 13 = 5 ∧ acceleratedOrbit 13 6284 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6284 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6284) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6284.1, data_13_6284.2]

/-- Complete interval computation for depth 13, residue 6285. -/
theorem bounds_13_6285 : exactInterval 13 6285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6285 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6285) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6285 : oddCount 6285 13 = 5 ∧ acceleratedOrbit 13 6285 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6285 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6285) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6285.1, data_13_6285.2]

/-- Complete interval computation for depth 13, residue 6286. -/
theorem bounds_13_6286 : exactInterval 13 6286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6286 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6286) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6286 : oddCount 6286 13 = 7 ∧ acceleratedOrbit 13 6286 = 1679 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6286 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6286) = 3 ^ 7 * m + 1679 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6286.1, data_13_6286.2]

end Collatz.Research.StoppingAtlas.Batch0876
