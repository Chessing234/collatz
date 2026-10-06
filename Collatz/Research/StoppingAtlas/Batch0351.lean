import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0351

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2304. -/
theorem bounds_12_2304 : exactInterval 12 2304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2304 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2304) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2304 : oddCount 2304 12 = 3 ∧ acceleratedOrbit 12 2304 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2304 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2304) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2304.1, data_12_2304.2]

/-- Complete interval computation for depth 12, residue 2305. -/
theorem bounds_12_2305 : exactInterval 12 2305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2305 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2305) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2305 : oddCount 2305 12 = 5 ∧ acceleratedOrbit 12 2305 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2305 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2305) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2305.1, data_12_2305.2]

/-- Complete interval computation for depth 12, residue 2306. -/
theorem bounds_12_2306 : exactInterval 12 2306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2306 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2306) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2306 : oddCount 2306 12 = 7 ∧ acceleratedOrbit 12 2306 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2306 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2306) = 3 ^ 7 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2306.1, data_12_2306.2]

/-- Complete interval computation for depth 12, residue 2307. -/
theorem bounds_12_2307 : exactInterval 12 2307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2307 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2307) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2307 : oddCount 2307 12 = 7 ∧ acceleratedOrbit 12 2307 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2307 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2307) = 3 ^ 7 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2307.1, data_12_2307.2]

/-- Complete interval computation for depth 12, residue 2308. -/
theorem bounds_12_2308 : exactInterval 12 2308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2308 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2308) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2308 : oddCount 2308 12 = 4 ∧ acceleratedOrbit 12 2308 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2308 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2308) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2308.1, data_12_2308.2]

/-- Complete interval computation for depth 12, residue 2309. -/
theorem bounds_12_2309 : exactInterval 12 2309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2309 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2309) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2309 : oddCount 2309 12 = 4 ∧ acceleratedOrbit 12 2309 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2309 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2309) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2309.1, data_12_2309.2]

/-- Complete interval computation for depth 12, residue 2310. -/
theorem bounds_12_2310 : exactInterval 12 2310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2310 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2310) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2310 : oddCount 2310 12 = 4 ∧ acceleratedOrbit 12 2310 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2310 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2310) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2310.1, data_12_2310.2]

/-- Complete interval computation for depth 12, residue 2311. -/
theorem bounds_12_2311 : exactInterval 12 2311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2311 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2311) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2311 : oddCount 2311 12 = 7 ∧ acceleratedOrbit 12 2311 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2311 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2311) = 3 ^ 7 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2311.1, data_12_2311.2]

/-- Complete interval computation for depth 12, residue 2312. -/
theorem bounds_12_2312 : exactInterval 12 2312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2312 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2312) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2312 : oddCount 2312 12 = 4 ∧ acceleratedOrbit 12 2312 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2312 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2312) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2312.1, data_12_2312.2]

/-- Complete interval computation for depth 12, residue 2313. -/
theorem bounds_12_2313 : exactInterval 12 2313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2313 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2313) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2313 : oddCount 2313 12 = 6 ∧ acceleratedOrbit 12 2313 = 412 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2313 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2313) = 3 ^ 6 * m + 412 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2313.1, data_12_2313.2]

/-- Complete interval computation for depth 12, residue 2314. -/
theorem bounds_12_2314 : exactInterval 12 2314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2314 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2314) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2314 : oddCount 2314 12 = 4 ∧ acceleratedOrbit 12 2314 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2314 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2314) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2314.1, data_12_2314.2]

/-- Complete interval computation for depth 12, residue 2315. -/
theorem bounds_12_2315 : exactInterval 12 2315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2315 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2315) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2315 : oddCount 2315 12 = 6 ∧ acceleratedOrbit 12 2315 = 413 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2315 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2315) = 3 ^ 6 * m + 413 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2315.1, data_12_2315.2]

/-- Complete interval computation for depth 12, residue 2316. -/
theorem bounds_12_2316 : exactInterval 12 2316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2316 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2316) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2316 : oddCount 2316 12 = 4 ∧ acceleratedOrbit 12 2316 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2316 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2316) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2316.1, data_12_2316.2]

/-- Complete interval computation for depth 12, residue 2317. -/
theorem bounds_12_2317 : exactInterval 12 2317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2317 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2317) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2317 : oddCount 2317 12 = 4 ∧ acceleratedOrbit 12 2317 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2317 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2317) = 3 ^ 4 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2317.1, data_12_2317.2]

/-- Complete interval computation for depth 12, residue 2318. -/
theorem bounds_12_2318 : exactInterval 12 2318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2318 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2318) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2318 : oddCount 2318 12 = 7 ∧ acceleratedOrbit 12 2318 = 1241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2318 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2318) = 3 ^ 7 * m + 1241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2318.1, data_12_2318.2]

end Collatz.Research.StoppingAtlas.Batch0351
