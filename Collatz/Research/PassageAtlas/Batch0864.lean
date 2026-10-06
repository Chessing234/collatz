import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0864

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 28278. -/
theorem bounds_15_28278 : exactInterval 15 28278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28278 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28278) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28278 : oddCount 28278 15 = 7 ∧ acceleratedOrbit 15 28278 = 1889 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28278 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28278) = 3 ^ 7 * m + 1889 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28278.1, data_15_28278.2]

/-- Complete interval computation for depth 15, residue 28279. -/
theorem bounds_15_28279 : exactInterval 15 28279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28279 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28279) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28279 : oddCount 28279 15 = 7 ∧ acceleratedOrbit 15 28279 = 1889 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28279 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28279) = 3 ^ 7 * m + 1889 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28279.1, data_15_28279.2]

/-- Complete interval computation for depth 15, residue 28280. -/
theorem bounds_15_28280 : exactInterval 15 28280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28280 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28280) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28280 : oddCount 28280 15 = 8 ∧ acceleratedOrbit 15 28280 = 5665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28280 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28280) = 3 ^ 8 * m + 5665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28280.1, data_15_28280.2]

/-- Complete interval computation for depth 15, residue 28281. -/
theorem bounds_15_28281 : exactInterval 15 28281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28281 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28281) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28281 : oddCount 28281 15 = 10 ∧ acceleratedOrbit 15 28281 = 50969 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28281 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28281) = 3 ^ 10 * m + 50969 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28281.1, data_15_28281.2]

/-- Complete interval computation for depth 15, residue 28282. -/
theorem bounds_15_28282 : exactInterval 15 28282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28282 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28282) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28282 : oddCount 28282 15 = 8 ∧ acceleratedOrbit 15 28282 = 5665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28282 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28282) = 3 ^ 8 * m + 5665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28282.1, data_15_28282.2]

/-- Complete interval computation for depth 15, residue 28283. -/
theorem bounds_15_28283 : exactInterval 15 28283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28283 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28283) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28283 : oddCount 28283 15 = 7 ∧ acceleratedOrbit 15 28283 = 1889 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28283 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28283) = 3 ^ 7 * m + 1889 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28283.1, data_15_28283.2]

/-- Complete interval computation for depth 15, residue 28284. -/
theorem bounds_15_28284 : exactInterval 15 28284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28284 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28284) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28284 : oddCount 28284 15 = 7 ∧ acceleratedOrbit 15 28284 = 1888 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28284 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28284) = 3 ^ 7 * m + 1888 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28284.1, data_15_28284.2]

/-- Complete interval computation for depth 15, residue 28285. -/
theorem bounds_15_28285 : exactInterval 15 28285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28285 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28285) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28285 : oddCount 28285 15 = 7 ∧ acceleratedOrbit 15 28285 = 1888 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28285 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28285) = 3 ^ 7 * m + 1888 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28285.1, data_15_28285.2]

/-- Complete interval computation for depth 15, residue 28286. -/
theorem bounds_15_28286 : exactInterval 15 28286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28286 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28286) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28286 : oddCount 28286 15 = 7 ∧ acceleratedOrbit 15 28286 = 1888 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28286 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28286) = 3 ^ 7 * m + 1888 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28286.1, data_15_28286.2]

/-- Complete interval computation for depth 15, residue 28287. -/
theorem bounds_15_28287 : exactInterval 15 28287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28287 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28287) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28287 : oddCount 28287 15 = 14 ∧ acceleratedOrbit 15 28287 = 4129055 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28287 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28287) = 3 ^ 14 * m + 4129055 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28287.1, data_15_28287.2]

/-- Complete interval computation for depth 15, residue 28288. -/
theorem bounds_15_28288 : exactInterval 15 28288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28288 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28288) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28288 : oddCount 28288 15 = 4 ∧ acceleratedOrbit 15 28288 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28288 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28288) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28288.1, data_15_28288.2]

/-- Complete interval computation for depth 15, residue 28289. -/
theorem bounds_15_28289 : exactInterval 15 28289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28289 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28289) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28289 : oddCount 28289 15 = 11 ∧ acceleratedOrbit 15 28289 = 152954 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28289 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28289) = 3 ^ 11 * m + 152954 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28289.1, data_15_28289.2]

/-- Complete interval computation for depth 15, residue 28290. -/
theorem bounds_15_28290 : exactInterval 15 28290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28290 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28290) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28290 : oddCount 28290 15 = 4 ∧ acceleratedOrbit 15 28290 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28290 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28290) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28290.1, data_15_28290.2]

/-- Complete interval computation for depth 15, residue 28291. -/
theorem bounds_15_28291 : exactInterval 15 28291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28291 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28291) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28291 : oddCount 28291 15 = 4 ∧ acceleratedOrbit 15 28291 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28291 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28291) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28291.1, data_15_28291.2]

/-- Complete interval computation for depth 15, residue 28292. -/
theorem bounds_15_28292 : exactInterval 15 28292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28292 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28292) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28292 : oddCount 28292 15 = 8 ∧ acceleratedOrbit 15 28292 = 5669 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28292 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28292) = 3 ^ 8 * m + 5669 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28292.1, data_15_28292.2]

/-- Complete interval computation for depth 15, residue 28293. -/
theorem bounds_15_28293 : exactInterval 15 28293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28293 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28293) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28293 : oddCount 28293 15 = 8 ∧ acceleratedOrbit 15 28293 = 5669 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28293 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28293) = 3 ^ 8 * m + 5669 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28293.1, data_15_28293.2]

/-- Complete interval computation for depth 15, residue 28294. -/
theorem bounds_15_28294 : exactInterval 15 28294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28294 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28294) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28294 : oddCount 28294 15 = 8 ∧ acceleratedOrbit 15 28294 = 5669 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28294 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28294) = 3 ^ 8 * m + 5669 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28294.1, data_15_28294.2]

/-- Complete interval computation for depth 15, residue 28295. -/
theorem bounds_15_28295 : exactInterval 15 28295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28295 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28295) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28295 : oddCount 28295 15 = 9 ∧ acceleratedOrbit 15 28295 = 17000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28295 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28295) = 3 ^ 9 * m + 17000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28295.1, data_15_28295.2]

/-- Complete interval computation for depth 15, residue 28296. -/
theorem bounds_15_28296 : exactInterval 15 28296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28296 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28296) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28296 : oddCount 28296 15 = 4 ∧ acceleratedOrbit 15 28296 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28296 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28296) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28296.1, data_15_28296.2]

/-- Complete interval computation for depth 15, residue 28297. -/
theorem bounds_15_28297 : exactInterval 15 28297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28297 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28297) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28297 : oddCount 28297 15 = 10 ∧ acceleratedOrbit 15 28297 = 50996 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28297 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28297) = 3 ^ 10 * m + 50996 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28297.1, data_15_28297.2]

/-- Complete interval computation for depth 15, residue 28298. -/
theorem bounds_15_28298 : exactInterval 15 28298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28298 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28298) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28298 : oddCount 28298 15 = 4 ∧ acceleratedOrbit 15 28298 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28298 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28298) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28298.1, data_15_28298.2]

/-- Complete interval computation for depth 15, residue 28299. -/
theorem bounds_15_28299 : exactInterval 15 28299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28299 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28299) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28299 : oddCount 28299 15 = 8 ∧ acceleratedOrbit 15 28299 = 5669 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28299 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28299) = 3 ^ 8 * m + 5669 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28299.1, data_15_28299.2]

/-- Complete interval computation for depth 15, residue 28300. -/
theorem bounds_15_28300 : exactInterval 15 28300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28300 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28300) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28300 : oddCount 28300 15 = 4 ∧ acceleratedOrbit 15 28300 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28300 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28300) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28300.1, data_15_28300.2]

/-- Complete interval computation for depth 15, residue 28301. -/
theorem bounds_15_28301 : exactInterval 15 28301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28301 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28301) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28301 : oddCount 28301 15 = 4 ∧ acceleratedOrbit 15 28301 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28301 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28301) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28301.1, data_15_28301.2]

/-- Complete interval computation for depth 15, residue 28302. -/
theorem bounds_15_28302 : exactInterval 15 28302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28302 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28302) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28302 : oddCount 28302 15 = 9 ∧ acceleratedOrbit 15 28302 = 17003 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28302 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28302) = 3 ^ 9 * m + 17003 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28302.1, data_15_28302.2]

/-- Complete interval computation for depth 15, residue 28303. -/
theorem bounds_15_28303 : exactInterval 15 28303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28303 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28303) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28303 : oddCount 28303 15 = 9 ∧ acceleratedOrbit 15 28303 = 17003 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28303 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28303) = 3 ^ 9 * m + 17003 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28303.1, data_15_28303.2]

/-- Complete interval computation for depth 15, residue 28304. -/
theorem bounds_15_28304 : exactInterval 15 28304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28304 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28304) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28304 : oddCount 28304 15 = 7 ∧ acceleratedOrbit 15 28304 = 1891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28304 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28304) = 3 ^ 7 * m + 1891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28304.1, data_15_28304.2]

/-- Complete interval computation for depth 15, residue 28305. -/
theorem bounds_15_28305 : exactInterval 15 28305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28305 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28305) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28305 : oddCount 28305 15 = 9 ∧ acceleratedOrbit 15 28305 = 17009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28305 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28305) = 3 ^ 9 * m + 17009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28305.1, data_15_28305.2]

/-- Complete interval computation for depth 15, residue 28306. -/
theorem bounds_15_28306 : exactInterval 15 28306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28306 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28306) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28306 : oddCount 28306 15 = 9 ∧ acceleratedOrbit 15 28306 = 17009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28306 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28306) = 3 ^ 9 * m + 17009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28306.1, data_15_28306.2]

/-- Complete interval computation for depth 15, residue 28307. -/
theorem bounds_15_28307 : exactInterval 15 28307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28307 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28307) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28307 : oddCount 28307 15 = 9 ∧ acceleratedOrbit 15 28307 = 17009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28307 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28307) = 3 ^ 9 * m + 17009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28307.1, data_15_28307.2]

/-- Complete interval computation for depth 15, residue 28308. -/
theorem bounds_15_28308 : exactInterval 15 28308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28308 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28308) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28308 : oddCount 28308 15 = 7 ∧ acceleratedOrbit 15 28308 = 1891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28308 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28308) = 3 ^ 7 * m + 1891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28308.1, data_15_28308.2]

/-- Complete interval computation for depth 15, residue 28309. -/
theorem bounds_15_28309 : exactInterval 15 28309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28309 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28309) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28309 : oddCount 28309 15 = 7 ∧ acceleratedOrbit 15 28309 = 1891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28309 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28309) = 3 ^ 7 * m + 1891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28309.1, data_15_28309.2]

/-- Complete interval computation for depth 15, residue 28310. -/
theorem bounds_15_28310 : exactInterval 15 28310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28310 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28310) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28310 : oddCount 28310 15 = 4 ∧ acceleratedOrbit 15 28310 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28310 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28310) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28310.1, data_15_28310.2]

end Collatz.Research.PassageAtlas.Batch0864
