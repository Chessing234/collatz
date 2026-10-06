import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0834

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 27295. -/
theorem bounds_15_27295 : exactInterval 15 27295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27295 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27295) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27295 : oddCount 27295 15 = 10 ∧ acceleratedOrbit 15 27295 = 49189 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27295 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27295) = 3 ^ 10 * m + 49189 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27295.1, data_15_27295.2]

/-- Complete interval computation for depth 15, residue 27296. -/
theorem bounds_15_27296 : exactInterval 15 27296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27296 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27296) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27296 : oddCount 27296 15 = 2 ∧ acceleratedOrbit 15 27296 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27296 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27296) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27296.1, data_15_27296.2]

/-- Complete interval computation for depth 15, residue 27297. -/
theorem bounds_15_27297 : exactInterval 15 27297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27297 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27297) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27297 : oddCount 27297 15 = 9 ∧ acceleratedOrbit 15 27297 = 16399 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27297 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27297) = 3 ^ 9 * m + 16399 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27297.1, data_15_27297.2]

/-- Complete interval computation for depth 15, residue 27298. -/
theorem bounds_15_27298 : exactInterval 15 27298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27298 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27298) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27298 : oddCount 27298 15 = 10 ∧ acceleratedOrbit 15 27298 = 49207 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27298 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27298) = 3 ^ 10 * m + 49207 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27298.1, data_15_27298.2]

/-- Complete interval computation for depth 15, residue 27299. -/
theorem bounds_15_27299 : exactInterval 15 27299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27299 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27299) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27299 : oddCount 27299 15 = 10 ∧ acceleratedOrbit 15 27299 = 49207 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27299 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27299) = 3 ^ 10 * m + 49207 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27299.1, data_15_27299.2]

/-- Complete interval computation for depth 15, residue 27300. -/
theorem bounds_15_27300 : exactInterval 15 27300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27300 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27300) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27300 : oddCount 27300 15 = 11 ∧ acceleratedOrbit 15 27300 = 147622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27300 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27300) = 3 ^ 11 * m + 147622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27300.1, data_15_27300.2]

/-- Complete interval computation for depth 15, residue 27301. -/
theorem bounds_15_27301 : exactInterval 15 27301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27301 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27301) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27301 : oddCount 27301 15 = 11 ∧ acceleratedOrbit 15 27301 = 147622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27301 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27301) = 3 ^ 11 * m + 147622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27301.1, data_15_27301.2]

/-- Complete interval computation for depth 15, residue 27302. -/
theorem bounds_15_27302 : exactInterval 15 27302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27302 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27302) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27302 : oddCount 27302 15 = 11 ∧ acceleratedOrbit 15 27302 = 147622 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27302 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27302) = 3 ^ 11 * m + 147622 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27302.1, data_15_27302.2]

/-- Complete interval computation for depth 15, residue 27303. -/
theorem bounds_15_27303 : exactInterval 15 27303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27303 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27303) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27303 : oddCount 27303 15 = 10 ∧ acceleratedOrbit 15 27303 = 49204 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27303 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27303) = 3 ^ 10 * m + 49204 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27303.1, data_15_27303.2]

/-- Complete interval computation for depth 15, residue 27304. -/
theorem bounds_15_27304 : exactInterval 15 27304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27304 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27304) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27304 : oddCount 27304 15 = 2 ∧ acceleratedOrbit 15 27304 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27304 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27304) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27304.1, data_15_27304.2]

/-- Complete interval computation for depth 15, residue 27305. -/
theorem bounds_15_27305 : exactInterval 15 27305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27305 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27305) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27305 : oddCount 27305 15 = 13 ∧ acceleratedOrbit 15 27305 = 1328602 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27305 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27305) = 3 ^ 13 * m + 1328602 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27305.1, data_15_27305.2]

/-- Complete interval computation for depth 15, residue 27306. -/
theorem bounds_15_27306 : exactInterval 15 27306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27306 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27306) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27306 : oddCount 27306 15 = 2 ∧ acceleratedOrbit 15 27306 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27306 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27306) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27306.1, data_15_27306.2]

/-- Complete interval computation for depth 15, residue 27307. -/
theorem bounds_15_27307 : exactInterval 15 27307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27307 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27307) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27307 : oddCount 27307 15 = 9 ∧ acceleratedOrbit 15 27307 = 16406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27307 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27307) = 3 ^ 9 * m + 16406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27307.1, data_15_27307.2]

/-- Complete interval computation for depth 15, residue 27308. -/
theorem bounds_15_27308 : exactInterval 15 27308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27308 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27308) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27308 : oddCount 27308 15 = 8 ∧ acceleratedOrbit 15 27308 = 5471 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27308 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27308) = 3 ^ 8 * m + 5471 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27308.1, data_15_27308.2]

/-- Complete interval computation for depth 15, residue 27309. -/
theorem bounds_15_27309 : exactInterval 15 27309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27309 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27309) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27309 : oddCount 27309 15 = 8 ∧ acceleratedOrbit 15 27309 = 5471 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27309 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27309) = 3 ^ 8 * m + 5471 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27309.1, data_15_27309.2]

/-- Complete interval computation for depth 15, residue 27310. -/
theorem bounds_15_27310 : exactInterval 15 27310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27310 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27310) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27310 : oddCount 27310 15 = 8 ∧ acceleratedOrbit 15 27310 = 5471 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27310 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27310) = 3 ^ 8 * m + 5471 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27310.1, data_15_27310.2]

/-- Complete interval computation for depth 15, residue 27311. -/
theorem bounds_15_27311 : exactInterval 15 27311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27311 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27311) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27311 : oddCount 27311 15 = 7 ∧ acceleratedOrbit 15 27311 = 1823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27311 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27311) = 3 ^ 7 * m + 1823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27311.1, data_15_27311.2]

/-- Complete interval computation for depth 15, residue 27312. -/
theorem bounds_15_27312 : exactInterval 15 27312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27312 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27312) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27312 : oddCount 27312 15 = 7 ∧ acceleratedOrbit 15 27312 = 1826 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27312 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27312) = 3 ^ 7 * m + 1826 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27312.1, data_15_27312.2]

/-- Complete interval computation for depth 15, residue 27313. -/
theorem bounds_15_27313 : exactInterval 15 27313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27313 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27313) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27313 : oddCount 27313 15 = 6 ∧ acceleratedOrbit 15 27313 = 608 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27313 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27313) = 3 ^ 6 * m + 608 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27313.1, data_15_27313.2]

/-- Complete interval computation for depth 15, residue 27314. -/
theorem bounds_15_27314 : exactInterval 15 27314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27314 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27314) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27314 : oddCount 27314 15 = 6 ∧ acceleratedOrbit 15 27314 = 608 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27314 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27314) = 3 ^ 6 * m + 608 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27314.1, data_15_27314.2]

/-- Complete interval computation for depth 15, residue 27315. -/
theorem bounds_15_27315 : exactInterval 15 27315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27315 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27315) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27315 : oddCount 27315 15 = 6 ∧ acceleratedOrbit 15 27315 = 608 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27315 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27315) = 3 ^ 6 * m + 608 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27315.1, data_15_27315.2]

/-- Complete interval computation for depth 15, residue 27316. -/
theorem bounds_15_27316 : exactInterval 15 27316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27316 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27316) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27316 : oddCount 27316 15 = 7 ∧ acceleratedOrbit 15 27316 = 1826 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27316 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27316) = 3 ^ 7 * m + 1826 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27316.1, data_15_27316.2]

/-- Complete interval computation for depth 15, residue 27317. -/
theorem bounds_15_27317 : exactInterval 15 27317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27317 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27317) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27317 : oddCount 27317 15 = 7 ∧ acceleratedOrbit 15 27317 = 1826 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27317 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27317) = 3 ^ 7 * m + 1826 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27317.1, data_15_27317.2]

/-- Complete interval computation for depth 15, residue 27318. -/
theorem bounds_15_27318 : exactInterval 15 27318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27318 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27318) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27318 : oddCount 27318 15 = 8 ∧ acceleratedOrbit 15 27318 = 5471 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27318 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27318) = 3 ^ 8 * m + 5471 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27318.1, data_15_27318.2]

/-- Complete interval computation for depth 15, residue 27319. -/
theorem bounds_15_27319 : exactInterval 15 27319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27319 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27319) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27319 : oddCount 27319 15 = 8 ∧ acceleratedOrbit 15 27319 = 5471 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27319 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27319) = 3 ^ 8 * m + 5471 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27319.1, data_15_27319.2]

/-- Complete interval computation for depth 15, residue 27320. -/
theorem bounds_15_27320 : exactInterval 15 27320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27320 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27320) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27320 : oddCount 27320 15 = 7 ∧ acceleratedOrbit 15 27320 = 1826 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27320 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27320) = 3 ^ 7 * m + 1826 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27320.1, data_15_27320.2]

/-- Complete interval computation for depth 15, residue 27321. -/
theorem bounds_15_27321 : exactInterval 15 27321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27321 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27321) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27321 : oddCount 27321 15 = 6 ∧ acceleratedOrbit 15 27321 = 608 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27321 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27321) = 3 ^ 6 * m + 608 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27321.1, data_15_27321.2]

/-- Complete interval computation for depth 15, residue 27322. -/
theorem bounds_15_27322 : exactInterval 15 27322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27322 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27322) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27322 : oddCount 27322 15 = 7 ∧ acceleratedOrbit 15 27322 = 1826 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27322 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27322) = 3 ^ 7 * m + 1826 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27322.1, data_15_27322.2]

/-- Complete interval computation for depth 15, residue 27323. -/
theorem bounds_15_27323 : exactInterval 15 27323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27323 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27323) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27323 : oddCount 27323 15 = 9 ∧ acceleratedOrbit 15 27323 = 16415 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27323 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27323) = 3 ^ 9 * m + 16415 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27323.1, data_15_27323.2]

/-- Complete interval computation for depth 15, residue 27324. -/
theorem bounds_15_27324 : exactInterval 15 27324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27324 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27324) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27324 : oddCount 27324 15 = 6 ∧ acceleratedOrbit 15 27324 = 608 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27324 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27324) = 3 ^ 6 * m + 608 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27324.1, data_15_27324.2]

/-- Complete interval computation for depth 15, residue 27325. -/
theorem bounds_15_27325 : exactInterval 15 27325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27325 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27325) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27325 : oddCount 27325 15 = 6 ∧ acceleratedOrbit 15 27325 = 608 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27325 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27325) = 3 ^ 6 * m + 608 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27325.1, data_15_27325.2]

/-- Complete interval computation for depth 15, residue 27326. -/
theorem bounds_15_27326 : exactInterval 15 27326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27326 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27326) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27326 : oddCount 27326 15 = 6 ∧ acceleratedOrbit 15 27326 = 608 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27326 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27326) = 3 ^ 6 * m + 608 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27326.1, data_15_27326.2]

/-- Complete interval computation for depth 15, residue 27327. -/
theorem bounds_15_27327 : exactInterval 15 27327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27327 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27327) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27327 : oddCount 27327 15 = 11 ∧ acceleratedOrbit 15 27327 = 147739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27327 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27327) = 3 ^ 11 * m + 147739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27327.1, data_15_27327.2]

end Collatz.Research.PassageAtlas.Batch0834
