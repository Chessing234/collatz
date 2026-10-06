import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0941

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7270. -/
theorem bounds_13_7270 : exactInterval 13 7270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7270 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7270) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7270 : oddCount 7270 13 = 8 ∧ acceleratedOrbit 13 7270 = 5831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7270 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7270) = 3 ^ 8 * m + 5831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7270.1, data_13_7270.2]

/-- Complete interval computation for depth 13, residue 7271. -/
theorem bounds_13_7271 : exactInterval 13 7271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7271 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7271) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7271 : oddCount 7271 13 = 10 ∧ acceleratedOrbit 13 7271 = 52420 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7271 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7271) = 3 ^ 10 * m + 52420 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7271.1, data_13_7271.2]

/-- Complete interval computation for depth 13, residue 7272. -/
theorem bounds_13_7272 : exactInterval 13 7272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7272 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7272) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7272 : oddCount 7272 13 = 2 ∧ acceleratedOrbit 13 7272 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7272 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7272) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7272.1, data_13_7272.2]

/-- Complete interval computation for depth 13, residue 7273. -/
theorem bounds_13_7273 : exactInterval 13 7273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7273 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7273) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7273 : oddCount 7273 13 = 8 ∧ acceleratedOrbit 13 7273 = 5827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7273 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7273) = 3 ^ 8 * m + 5827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7273.1, data_13_7273.2]

/-- Complete interval computation for depth 13, residue 7274. -/
theorem bounds_13_7274 : exactInterval 13 7274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7274 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7274) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7274 : oddCount 7274 13 = 2 ∧ acceleratedOrbit 13 7274 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7274 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7274) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7274.1, data_13_7274.2]

/-- Complete interval computation for depth 13, residue 7275. -/
theorem bounds_13_7275 : exactInterval 13 7275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7275 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7275) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7275 : oddCount 7275 13 = 9 ∧ acceleratedOrbit 13 7275 = 17486 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7275 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7275) = 3 ^ 9 * m + 17486 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7275.1, data_13_7275.2]

/-- Complete interval computation for depth 13, residue 7276. -/
theorem bounds_13_7276 : exactInterval 13 7276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7276 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7276) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7276 : oddCount 7276 13 = 10 ∧ acceleratedOrbit 13 7276 = 52487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7276 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7276) = 3 ^ 10 * m + 52487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7276.1, data_13_7276.2]

/-- Complete interval computation for depth 13, residue 7277. -/
theorem bounds_13_7277 : exactInterval 13 7277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7277 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7277) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7277 : oddCount 7277 13 = 10 ∧ acceleratedOrbit 13 7277 = 52487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7277 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7277) = 3 ^ 10 * m + 52487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7277.1, data_13_7277.2]

/-- Complete interval computation for depth 13, residue 7278. -/
theorem bounds_13_7278 : exactInterval 13 7278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7278 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7278) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7278 : oddCount 7278 13 = 10 ∧ acceleratedOrbit 13 7278 = 52487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7278 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7278) = 3 ^ 10 * m + 52487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7278.1, data_13_7278.2]

/-- Complete interval computation for depth 13, residue 7279. -/
theorem bounds_13_7279 : exactInterval 13 7279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7279 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7279) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7279 : oddCount 7279 13 = 10 ∧ acceleratedOrbit 13 7279 = 52478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7279 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7279) = 3 ^ 10 * m + 52478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7279.1, data_13_7279.2]

/-- Complete interval computation for depth 13, residue 7280. -/
theorem bounds_13_7280 : exactInterval 13 7280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7280 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7280) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7280 : oddCount 7280 13 = 6 ∧ acceleratedOrbit 13 7280 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7280 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7280) = 3 ^ 6 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7280.1, data_13_7280.2]

/-- Complete interval computation for depth 13, residue 7281. -/
theorem bounds_13_7281 : exactInterval 13 7281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7281 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7281) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7281 : oddCount 7281 13 = 2 ∧ acceleratedOrbit 13 7281 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7281 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7281) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7281.1, data_13_7281.2]

/-- Complete interval computation for depth 13, residue 7282. -/
theorem bounds_13_7282 : exactInterval 13 7282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7282 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7282) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7282 : oddCount 7282 13 = 7 ∧ acceleratedOrbit 13 7282 = 1946 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7282 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7282) = 3 ^ 7 * m + 1946 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7282.1, data_13_7282.2]

/-- Complete interval computation for depth 13, residue 7283. -/
theorem bounds_13_7283 : exactInterval 13 7283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7283 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7283) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7283 : oddCount 7283 13 = 7 ∧ acceleratedOrbit 13 7283 = 1946 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7283 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7283) = 3 ^ 7 * m + 1946 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7283.1, data_13_7283.2]

/-- Complete interval computation for depth 13, residue 7284. -/
theorem bounds_13_7284 : exactInterval 13 7284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7284 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7284) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7284 : oddCount 7284 13 = 6 ∧ acceleratedOrbit 13 7284 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7284 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7284) = 3 ^ 6 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7284.1, data_13_7284.2]

end Collatz.Research.StoppingAtlas.Batch0941
