import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0711

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 23265. -/
theorem bounds_15_23265 : exactInterval 15 23265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23265 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23265) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23265 : oddCount 23265 15 = 10 ∧ acceleratedOrbit 15 23265 = 41930 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23265 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23265) = 3 ^ 10 * m + 41930 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23265.1, data_15_23265.2]

/-- Complete interval computation for depth 15, residue 23266. -/
theorem bounds_15_23266 : exactInterval 15 23266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23266 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23266) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23266 : oddCount 23266 15 = 5 ∧ acceleratedOrbit 15 23266 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23266 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23266) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23266.1, data_15_23266.2]

/-- Complete interval computation for depth 15, residue 23267. -/
theorem bounds_15_23267 : exactInterval 15 23267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23267 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23267) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23267 : oddCount 23267 15 = 5 ∧ acceleratedOrbit 15 23267 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23267 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23267) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23267.1, data_15_23267.2]

/-- Complete interval computation for depth 15, residue 23268. -/
theorem bounds_15_23268 : exactInterval 15 23268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23268 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23268) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23268 : oddCount 23268 15 = 6 ∧ acceleratedOrbit 15 23268 = 518 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23268 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23268) = 3 ^ 6 * m + 518 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23268.1, data_15_23268.2]

/-- Complete interval computation for depth 15, residue 23269. -/
theorem bounds_15_23269 : exactInterval 15 23269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23269 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23269) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23269 : oddCount 23269 15 = 6 ∧ acceleratedOrbit 15 23269 = 518 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23269 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23269) = 3 ^ 6 * m + 518 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23269.1, data_15_23269.2]

/-- Complete interval computation for depth 15, residue 23270. -/
theorem bounds_15_23270 : exactInterval 15 23270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23270 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23270) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23270 : oddCount 23270 15 = 6 ∧ acceleratedOrbit 15 23270 = 518 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23270 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23270) = 3 ^ 6 * m + 518 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23270.1, data_15_23270.2]

/-- Complete interval computation for depth 15, residue 23271. -/
theorem bounds_15_23271 : exactInterval 15 23271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23271 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23271) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23271 : oddCount 23271 15 = 11 ∧ acceleratedOrbit 15 23271 = 125813 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23271 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23271) = 3 ^ 11 * m + 125813 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23271.1, data_15_23271.2]

/-- Complete interval computation for depth 15, residue 23272. -/
theorem bounds_15_23272 : exactInterval 15 23272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23272 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23272) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23272 : oddCount 23272 15 = 5 ∧ acceleratedOrbit 15 23272 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23272 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23272) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23272.1, data_15_23272.2]

/-- Complete interval computation for depth 15, residue 23273. -/
theorem bounds_15_23273 : exactInterval 15 23273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23273 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23273) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23273 : oddCount 23273 15 = 9 ∧ acceleratedOrbit 15 23273 = 13981 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23273 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23273) = 3 ^ 9 * m + 13981 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23273.1, data_15_23273.2]

/-- Complete interval computation for depth 15, residue 23274. -/
theorem bounds_15_23274 : exactInterval 15 23274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23274 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23274) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23274 : oddCount 23274 15 = 5 ∧ acceleratedOrbit 15 23274 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23274 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23274) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23274.1, data_15_23274.2]

/-- Complete interval computation for depth 15, residue 23275. -/
theorem bounds_15_23275 : exactInterval 15 23275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23275 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23275) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23275 : oddCount 23275 15 = 10 ∧ acceleratedOrbit 15 23275 = 41948 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23275 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23275) = 3 ^ 10 * m + 41948 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23275.1, data_15_23275.2]

/-- Complete interval computation for depth 15, residue 23276. -/
theorem bounds_15_23276 : exactInterval 15 23276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23276 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23276) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23276 : oddCount 23276 15 = 6 ∧ acceleratedOrbit 15 23276 = 518 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23276 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23276) = 3 ^ 6 * m + 518 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23276.1, data_15_23276.2]

/-- Complete interval computation for depth 15, residue 23277. -/
theorem bounds_15_23277 : exactInterval 15 23277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23277 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23277) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23277 : oddCount 23277 15 = 6 ∧ acceleratedOrbit 15 23277 = 518 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23277 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23277) = 3 ^ 6 * m + 518 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23277.1, data_15_23277.2]

/-- Complete interval computation for depth 15, residue 23278. -/
theorem bounds_15_23278 : exactInterval 15 23278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23278 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23278) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23278 : oddCount 23278 15 = 6 ∧ acceleratedOrbit 15 23278 = 518 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23278 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23278) = 3 ^ 6 * m + 518 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23278.1, data_15_23278.2]

/-- Complete interval computation for depth 15, residue 23279. -/
theorem bounds_15_23279 : exactInterval 15 23279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23279 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23279) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23279 : oddCount 23279 15 = 12 ∧ acceleratedOrbit 15 23279 = 377567 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23279 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23279) = 3 ^ 12 * m + 377567 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23279.1, data_15_23279.2]

/-- Complete interval computation for depth 15, residue 23280. -/
theorem bounds_15_23280 : exactInterval 15 23280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23280 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23280) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23280 : oddCount 23280 15 = 7 ∧ acceleratedOrbit 15 23280 = 1556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23280 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23280) = 3 ^ 7 * m + 1556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23280.1, data_15_23280.2]

/-- Complete interval computation for depth 15, residue 23281. -/
theorem bounds_15_23281 : exactInterval 15 23281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23281 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23281) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23281 : oddCount 23281 15 = 5 ∧ acceleratedOrbit 15 23281 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23281 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23281) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23281.1, data_15_23281.2]

/-- Complete interval computation for depth 15, residue 23282. -/
theorem bounds_15_23282 : exactInterval 15 23282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23282 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23282) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23282 : oddCount 23282 15 = 9 ∧ acceleratedOrbit 15 23282 = 13988 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23282 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23282) = 3 ^ 9 * m + 13988 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23282.1, data_15_23282.2]

/-- Complete interval computation for depth 15, residue 23283. -/
theorem bounds_15_23283 : exactInterval 15 23283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23283 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23283) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23283 : oddCount 23283 15 = 9 ∧ acceleratedOrbit 15 23283 = 13988 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23283 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23283) = 3 ^ 9 * m + 13988 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23283.1, data_15_23283.2]

/-- Complete interval computation for depth 15, residue 23284. -/
theorem bounds_15_23284 : exactInterval 15 23284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23284 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23284) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23284 : oddCount 23284 15 = 7 ∧ acceleratedOrbit 15 23284 = 1556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23284 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23284) = 3 ^ 7 * m + 1556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23284.1, data_15_23284.2]

/-- Complete interval computation for depth 15, residue 23285. -/
theorem bounds_15_23285 : exactInterval 15 23285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23285 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23285) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23285 : oddCount 23285 15 = 7 ∧ acceleratedOrbit 15 23285 = 1556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23285 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23285) = 3 ^ 7 * m + 1556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23285.1, data_15_23285.2]

/-- Complete interval computation for depth 15, residue 23286. -/
theorem bounds_15_23286 : exactInterval 15 23286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23286 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23286) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23286 : oddCount 23286 15 = 8 ∧ acceleratedOrbit 15 23286 = 4664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23286 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23286) = 3 ^ 8 * m + 4664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23286.1, data_15_23286.2]

/-- Complete interval computation for depth 15, residue 23287. -/
theorem bounds_15_23287 : exactInterval 15 23287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23287 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23287) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23287 : oddCount 23287 15 = 8 ∧ acceleratedOrbit 15 23287 = 4664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23287 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23287) = 3 ^ 8 * m + 4664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23287.1, data_15_23287.2]

/-- Complete interval computation for depth 15, residue 23288. -/
theorem bounds_15_23288 : exactInterval 15 23288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23288 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23288) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23288 : oddCount 23288 15 = 7 ∧ acceleratedOrbit 15 23288 = 1556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23288 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23288) = 3 ^ 7 * m + 1556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23288.1, data_15_23288.2]

/-- Complete interval computation for depth 15, residue 23289. -/
theorem bounds_15_23289 : exactInterval 15 23289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23289 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23289) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23289 : oddCount 23289 15 = 8 ∧ acceleratedOrbit 15 23289 = 4664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23289 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23289) = 3 ^ 8 * m + 4664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23289.1, data_15_23289.2]

/-- Complete interval computation for depth 15, residue 23290. -/
theorem bounds_15_23290 : exactInterval 15 23290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23290 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23290) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23290 : oddCount 23290 15 = 7 ∧ acceleratedOrbit 15 23290 = 1556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23290 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23290) = 3 ^ 7 * m + 1556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23290.1, data_15_23290.2]

/-- Complete interval computation for depth 15, residue 23291. -/
theorem bounds_15_23291 : exactInterval 15 23291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23291 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23291) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23291 : oddCount 23291 15 = 10 ∧ acceleratedOrbit 15 23291 = 41975 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23291 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23291) = 3 ^ 10 * m + 41975 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23291.1, data_15_23291.2]

/-- Complete interval computation for depth 15, residue 23292. -/
theorem bounds_15_23292 : exactInterval 15 23292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23292 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23292) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23292 : oddCount 23292 15 = 9 ∧ acceleratedOrbit 15 23292 = 13994 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23292 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23292) = 3 ^ 9 * m + 13994 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23292.1, data_15_23292.2]

/-- Complete interval computation for depth 15, residue 23293. -/
theorem bounds_15_23293 : exactInterval 15 23293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23293 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23293) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23293 : oddCount 23293 15 = 9 ∧ acceleratedOrbit 15 23293 = 13994 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23293 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23293) = 3 ^ 9 * m + 13994 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23293.1, data_15_23293.2]

/-- Complete interval computation for depth 15, residue 23294. -/
theorem bounds_15_23294 : exactInterval 15 23294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23294 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23294) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23294 : oddCount 23294 15 = 9 ∧ acceleratedOrbit 15 23294 = 13994 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23294 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23294) = 3 ^ 9 * m + 13994 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23294.1, data_15_23294.2]

/-- Complete interval computation for depth 15, residue 23295. -/
theorem bounds_15_23295 : exactInterval 15 23295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23295 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23295) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23295 : oddCount 23295 15 = 11 ∧ acceleratedOrbit 15 23295 = 125941 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23295 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23295) = 3 ^ 11 * m + 125941 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23295.1, data_15_23295.2]

/-- Complete interval computation for depth 15, residue 23296. -/
theorem bounds_15_23296 : exactInterval 15 23296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23296 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23296) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23296 : oddCount 23296 15 = 5 ∧ acceleratedOrbit 15 23296 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23296 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23296) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23296.1, data_15_23296.2]

/-- Complete interval computation for depth 15, residue 23297. -/
theorem bounds_15_23297 : exactInterval 15 23297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23297 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23297) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23297 : oddCount 23297 15 = 7 ∧ acceleratedOrbit 15 23297 = 1556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23297 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23297) = 3 ^ 7 * m + 1556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23297.1, data_15_23297.2]

end Collatz.Research.PassageAtlas.Batch0711
