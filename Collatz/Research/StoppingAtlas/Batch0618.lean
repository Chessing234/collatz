import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0618

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2309. -/
theorem bounds_13_2309 : exactInterval 13 2309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2309 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2309) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2309 : oddCount 2309 13 = 4 ∧ acceleratedOrbit 13 2309 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2309 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2309) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2309.1, data_13_2309.2]

/-- Complete interval computation for depth 13, residue 2310. -/
theorem bounds_13_2310 : exactInterval 13 2310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2310 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2310) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2310 : oddCount 2310 13 = 4 ∧ acceleratedOrbit 13 2310 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2310 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2310) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2310.1, data_13_2310.2]

/-- Complete interval computation for depth 13, residue 2311. -/
theorem bounds_13_2311 : exactInterval 13 2311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2311 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2311) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2311 : oddCount 2311 13 = 8 ∧ acceleratedOrbit 13 2311 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2311 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2311) = 3 ^ 8 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2311.1, data_13_2311.2]

/-- Complete interval computation for depth 13, residue 2312. -/
theorem bounds_13_2312 : exactInterval 13 2312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2312 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2312) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2312 : oddCount 2312 13 = 4 ∧ acceleratedOrbit 13 2312 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2312 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2312) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2312.1, data_13_2312.2]

/-- Complete interval computation for depth 13, residue 2313. -/
theorem bounds_13_2313 : exactInterval 13 2313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2313 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2313) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2313 : oddCount 2313 13 = 6 ∧ acceleratedOrbit 13 2313 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2313 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2313) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2313.1, data_13_2313.2]

/-- Complete interval computation for depth 13, residue 2314. -/
theorem bounds_13_2314 : exactInterval 13 2314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2314 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2314) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2314 : oddCount 2314 13 = 4 ∧ acceleratedOrbit 13 2314 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2314 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2314) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2314.1, data_13_2314.2]

/-- Complete interval computation for depth 13, residue 2315. -/
theorem bounds_13_2315 : exactInterval 13 2315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2315 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2315) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2315 : oddCount 2315 13 = 7 ∧ acceleratedOrbit 13 2315 = 620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2315 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2315) = 3 ^ 7 * m + 620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2315.1, data_13_2315.2]

/-- Complete interval computation for depth 13, residue 2316. -/
theorem bounds_13_2316 : exactInterval 13 2316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2316 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2316) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2316 : oddCount 2316 13 = 4 ∧ acceleratedOrbit 13 2316 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2316 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2316) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2316.1, data_13_2316.2]

/-- Complete interval computation for depth 13, residue 2317. -/
theorem bounds_13_2317 : exactInterval 13 2317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2317 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2317) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2317 : oddCount 2317 13 = 4 ∧ acceleratedOrbit 13 2317 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2317 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2317) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2317.1, data_13_2317.2]

/-- Complete interval computation for depth 13, residue 2318. -/
theorem bounds_13_2318 : exactInterval 13 2318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2318 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2318) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2318 : oddCount 2318 13 = 8 ∧ acceleratedOrbit 13 2318 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2318 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2318) = 3 ^ 8 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2318.1, data_13_2318.2]

/-- Complete interval computation for depth 13, residue 2319. -/
theorem bounds_13_2319 : exactInterval 13 2319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2319 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2319) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2319 : oddCount 2319 13 = 8 ∧ acceleratedOrbit 13 2319 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2319 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2319) = 3 ^ 8 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2319.1, data_13_2319.2]

/-- Complete interval computation for depth 13, residue 2320. -/
theorem bounds_13_2320 : exactInterval 13 2320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2320 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2320) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2320 : oddCount 2320 13 = 5 ∧ acceleratedOrbit 13 2320 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2320 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2320) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2320.1, data_13_2320.2]

/-- Complete interval computation for depth 13, residue 2321. -/
theorem bounds_13_2321 : exactInterval 13 2321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2321 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2321) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2321 : oddCount 2321 13 = 4 ∧ acceleratedOrbit 13 2321 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2321 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2321) = 3 ^ 4 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2321.1, data_13_2321.2]

/-- Complete interval computation for depth 13, residue 2322. -/
theorem bounds_13_2322 : exactInterval 13 2322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2322 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2322) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2322 : oddCount 2322 13 = 10 ∧ acceleratedOrbit 13 2322 = 16766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2322 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2322) = 3 ^ 10 * m + 16766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2322.1, data_13_2322.2]

/-- Complete interval computation for depth 13, residue 2323. -/
theorem bounds_13_2323 : exactInterval 13 2323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2323 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2323) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2323 : oddCount 2323 13 = 10 ∧ acceleratedOrbit 13 2323 = 16766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2323 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2323) = 3 ^ 10 * m + 16766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2323.1, data_13_2323.2]

end Collatz.Research.StoppingAtlas.Batch0618
