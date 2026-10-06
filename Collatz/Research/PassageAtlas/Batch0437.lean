import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0437

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 14286. -/
theorem bounds_15_14286 : exactInterval 15 14286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14286 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14286) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14286 : oddCount 14286 15 = 9 ∧ acceleratedOrbit 15 14286 = 8585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14286 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14286) = 3 ^ 9 * m + 8585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14286.1, data_15_14286.2]

/-- Complete interval computation for depth 15, residue 14287. -/
theorem bounds_15_14287 : exactInterval 15 14287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14287 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14287) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14287 : oddCount 14287 15 = 9 ∧ acceleratedOrbit 15 14287 = 8585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14287 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14287) = 3 ^ 9 * m + 8585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14287.1, data_15_14287.2]

/-- Complete interval computation for depth 15, residue 14288. -/
theorem bounds_15_14288 : exactInterval 15 14288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14288 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14288) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14288 : oddCount 14288 15 = 6 ∧ acceleratedOrbit 15 14288 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14288 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14288) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14288.1, data_15_14288.2]

/-- Complete interval computation for depth 15, residue 14289. -/
theorem bounds_15_14289 : exactInterval 15 14289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14289 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14289) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14289 : oddCount 14289 15 = 5 ∧ acceleratedOrbit 15 14289 = 106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14289 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14289) = 3 ^ 5 * m + 106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14289.1, data_15_14289.2]

/-- Complete interval computation for depth 15, residue 14290. -/
theorem bounds_15_14290 : exactInterval 15 14290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14290 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14290) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14290 : oddCount 14290 15 = 12 ∧ acceleratedOrbit 15 14290 = 231821 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14290 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14290) = 3 ^ 12 * m + 231821 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14290.1, data_15_14290.2]

/-- Complete interval computation for depth 15, residue 14291. -/
theorem bounds_15_14291 : exactInterval 15 14291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14291 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14291) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14291 : oddCount 14291 15 = 12 ∧ acceleratedOrbit 15 14291 = 231821 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14291 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14291) = 3 ^ 12 * m + 231821 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14291.1, data_15_14291.2]

/-- Complete interval computation for depth 15, residue 14292. -/
theorem bounds_15_14292 : exactInterval 15 14292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14292 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14292) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14292 : oddCount 14292 15 = 6 ∧ acceleratedOrbit 15 14292 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14292 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14292) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14292.1, data_15_14292.2]

/-- Complete interval computation for depth 15, residue 14293. -/
theorem bounds_15_14293 : exactInterval 15 14293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14293 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14293) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14293 : oddCount 14293 15 = 6 ∧ acceleratedOrbit 15 14293 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14293 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14293) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14293.1, data_15_14293.2]

/-- Complete interval computation for depth 15, residue 14294. -/
theorem bounds_15_14294 : exactInterval 15 14294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14294 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14294) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14294 : oddCount 14294 15 = 8 ∧ acceleratedOrbit 15 14294 = 2863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14294 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14294) = 3 ^ 8 * m + 2863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14294.1, data_15_14294.2]

/-- Complete interval computation for depth 15, residue 14295. -/
theorem bounds_15_14295 : exactInterval 15 14295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14295 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14295) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14295 : oddCount 14295 15 = 8 ∧ acceleratedOrbit 15 14295 = 2863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14295 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14295) = 3 ^ 8 * m + 2863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14295.1, data_15_14295.2]

/-- Complete interval computation for depth 15, residue 14296. -/
theorem bounds_15_14296 : exactInterval 15 14296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14296 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14296) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14296 : oddCount 14296 15 = 7 ∧ acceleratedOrbit 15 14296 = 955 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14296 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14296) = 3 ^ 7 * m + 955 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14296.1, data_15_14296.2]

/-- Complete interval computation for depth 15, residue 14297. -/
theorem bounds_15_14297 : exactInterval 15 14297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14297 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14297) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14297 : oddCount 14297 15 = 6 ∧ acceleratedOrbit 15 14297 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14297 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14297) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14297.1, data_15_14297.2]

/-- Complete interval computation for depth 15, residue 14298. -/
theorem bounds_15_14298 : exactInterval 15 14298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14298 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14298) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14298 : oddCount 14298 15 = 7 ∧ acceleratedOrbit 15 14298 = 955 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14298 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14298) = 3 ^ 7 * m + 955 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14298.1, data_15_14298.2]

/-- Complete interval computation for depth 15, residue 14299. -/
theorem bounds_15_14299 : exactInterval 15 14299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14299 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14299) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14299 : oddCount 14299 15 = 8 ∧ acceleratedOrbit 15 14299 = 2864 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14299 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14299) = 3 ^ 8 * m + 2864 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14299.1, data_15_14299.2]

/-- Complete interval computation for depth 15, residue 14300. -/
theorem bounds_15_14300 : exactInterval 15 14300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14300 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14300) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14300 : oddCount 14300 15 = 7 ∧ acceleratedOrbit 15 14300 = 955 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14300 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14300) = 3 ^ 7 * m + 955 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14300.1, data_15_14300.2]

/-- Complete interval computation for depth 15, residue 14301. -/
theorem bounds_15_14301 : exactInterval 15 14301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14301 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14301) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14301 : oddCount 14301 15 = 7 ∧ acceleratedOrbit 15 14301 = 955 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14301 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14301) = 3 ^ 7 * m + 955 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14301.1, data_15_14301.2]

/-- Complete interval computation for depth 15, residue 14302. -/
theorem bounds_15_14302 : exactInterval 15 14302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14302 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14302) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14302 : oddCount 14302 15 = 10 ∧ acceleratedOrbit 15 14302 = 25778 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14302 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14302) = 3 ^ 10 * m + 25778 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14302.1, data_15_14302.2]

/-- Complete interval computation for depth 15, residue 14303. -/
theorem bounds_15_14303 : exactInterval 15 14303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14303 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14303) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14303 : oddCount 14303 15 = 10 ∧ acceleratedOrbit 15 14303 = 25778 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14303 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14303) = 3 ^ 10 * m + 25778 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14303.1, data_15_14303.2]

/-- Complete interval computation for depth 15, residue 14304. -/
theorem bounds_15_14304 : exactInterval 15 14304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14304 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14304) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14304 : oddCount 14304 15 = 9 ∧ acceleratedOrbit 15 14304 = 8612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14304 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14304) = 3 ^ 9 * m + 8612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14304.1, data_15_14304.2]

/-- Complete interval computation for depth 15, residue 14305. -/
theorem bounds_15_14305 : exactInterval 15 14305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14305 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14305) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14305 : oddCount 14305 15 = 10 ∧ acceleratedOrbit 15 14305 = 25784 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14305 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14305) = 3 ^ 10 * m + 25784 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14305.1, data_15_14305.2]

/-- Complete interval computation for depth 15, residue 14306. -/
theorem bounds_15_14306 : exactInterval 15 14306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14306 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14306) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14306 : oddCount 14306 15 = 6 ∧ acceleratedOrbit 15 14306 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14306 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14306) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14306.1, data_15_14306.2]

/-- Complete interval computation for depth 15, residue 14307. -/
theorem bounds_15_14307 : exactInterval 15 14307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14307 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14307) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14307 : oddCount 14307 15 = 6 ∧ acceleratedOrbit 15 14307 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14307 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14307) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14307.1, data_15_14307.2]

/-- Complete interval computation for depth 15, residue 14308. -/
theorem bounds_15_14308 : exactInterval 15 14308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14308 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14308) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14308 : oddCount 14308 15 = 7 ∧ acceleratedOrbit 15 14308 = 956 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14308 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14308) = 3 ^ 7 * m + 956 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14308.1, data_15_14308.2]

/-- Complete interval computation for depth 15, residue 14309. -/
theorem bounds_15_14309 : exactInterval 15 14309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14309 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14309) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14309 : oddCount 14309 15 = 7 ∧ acceleratedOrbit 15 14309 = 956 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14309 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14309) = 3 ^ 7 * m + 956 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14309.1, data_15_14309.2]

/-- Complete interval computation for depth 15, residue 14310. -/
theorem bounds_15_14310 : exactInterval 15 14310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14310 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14310) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14310 : oddCount 14310 15 = 7 ∧ acceleratedOrbit 15 14310 = 956 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14310 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14310) = 3 ^ 7 * m + 956 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14310.1, data_15_14310.2]

/-- Complete interval computation for depth 15, residue 14311. -/
theorem bounds_15_14311 : exactInterval 15 14311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14311 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14311) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14311 : oddCount 14311 15 = 8 ∧ acceleratedOrbit 15 14311 = 2866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14311 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14311) = 3 ^ 8 * m + 2866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14311.1, data_15_14311.2]

/-- Complete interval computation for depth 15, residue 14312. -/
theorem bounds_15_14312 : exactInterval 15 14312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14312 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14312) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14312 : oddCount 14312 15 = 9 ∧ acceleratedOrbit 15 14312 = 8612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14312 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14312) = 3 ^ 9 * m + 8612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14312.1, data_15_14312.2]

/-- Complete interval computation for depth 15, residue 14313. -/
theorem bounds_15_14313 : exactInterval 15 14313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14313 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14313) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14313 : oddCount 14313 15 = 10 ∧ acceleratedOrbit 15 14313 = 25796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14313 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14313) = 3 ^ 10 * m + 25796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14313.1, data_15_14313.2]

/-- Complete interval computation for depth 15, residue 14314. -/
theorem bounds_15_14314 : exactInterval 15 14314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14314 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14314) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14314 : oddCount 14314 15 = 9 ∧ acceleratedOrbit 15 14314 = 8612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14314 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14314) = 3 ^ 9 * m + 8612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14314.1, data_15_14314.2]

/-- Complete interval computation for depth 15, residue 14315. -/
theorem bounds_15_14315 : exactInterval 15 14315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14315 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14315) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14315 : oddCount 14315 15 = 9 ∧ acceleratedOrbit 15 14315 = 8600 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14315 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14315) = 3 ^ 9 * m + 8600 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14315.1, data_15_14315.2]

/-- Complete interval computation for depth 15, residue 14316. -/
theorem bounds_15_14316 : exactInterval 15 14316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14316 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14316) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14316 : oddCount 14316 15 = 7 ∧ acceleratedOrbit 15 14316 = 956 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14316 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14316) = 3 ^ 7 * m + 956 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14316.1, data_15_14316.2]

/-- Complete interval computation for depth 15, residue 14317. -/
theorem bounds_15_14317 : exactInterval 15 14317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14317 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14317) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14317 : oddCount 14317 15 = 7 ∧ acceleratedOrbit 15 14317 = 956 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14317 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14317) = 3 ^ 7 * m + 956 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14317.1, data_15_14317.2]

/-- Complete interval computation for depth 15, residue 14318. -/
theorem bounds_15_14318 : exactInterval 15 14318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14318 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14318) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14318 : oddCount 14318 15 = 7 ∧ acceleratedOrbit 15 14318 = 956 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14318 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14318) = 3 ^ 7 * m + 956 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14318.1, data_15_14318.2]

end Collatz.Research.PassageAtlas.Batch0437
