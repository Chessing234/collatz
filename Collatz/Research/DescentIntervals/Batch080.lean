import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch080

/-- Complete interval computation for depth 9, residue 297. -/
theorem bounds_9_297 : exactInterval 9 297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_297 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 297) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_297 : oddCount 297 9 = 6 ∧ acceleratedOrbit 9 297 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_297 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 297) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_297.1, data_9_297.2]

/-- Complete interval computation for depth 9, residue 298. -/
theorem bounds_9_298 : exactInterval 9 298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_298 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 298) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_298 : oddCount 298 9 = 3 ∧ acceleratedOrbit 9 298 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_298 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 298) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_298.1, data_9_298.2]

/-- Complete interval computation for depth 9, residue 299. -/
theorem bounds_9_299 : exactInterval 9 299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_299 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 299) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_299 : oddCount 299 9 = 5 ∧ acceleratedOrbit 9 299 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_299 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 299) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_299.1, data_9_299.2]

/-- Complete interval computation for depth 9, residue 300. -/
theorem bounds_9_300 : exactInterval 9 300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_300 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 300) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_300 : oddCount 300 9 = 3 ∧ acceleratedOrbit 9 300 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_300 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 300) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_300.1, data_9_300.2]

/-- Complete interval computation for depth 9, residue 301. -/
theorem bounds_9_301 : exactInterval 9 301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_301 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 301) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_301 : oddCount 301 9 = 3 ∧ acceleratedOrbit 9 301 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_301 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 301) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_301.1, data_9_301.2]

/-- Complete interval computation for depth 9, residue 302. -/
theorem bounds_9_302 : exactInterval 9 302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_302 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 302) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_302 : oddCount 302 9 = 3 ∧ acceleratedOrbit 9 302 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_302 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 302) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_302.1, data_9_302.2]

/-- Complete interval computation for depth 9, residue 303. -/
theorem bounds_9_303 : exactInterval 9 303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_303 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 303) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_303 : oddCount 303 9 = 6 ∧ acceleratedOrbit 9 303 = 433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_303 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 303) = 3 ^ 6 * m + 433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_303.1, data_9_303.2]

/-- Complete interval computation for depth 9, residue 304. -/
theorem bounds_9_304 : exactInterval 9 304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_304 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 304) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_304 : oddCount 304 9 = 3 ∧ acceleratedOrbit 9 304 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_304 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 304) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_304.1, data_9_304.2]

/-- Complete interval computation for depth 9, residue 305. -/
theorem bounds_9_305 : exactInterval 9 305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_305 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 305) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_305 : oddCount 305 9 = 4 ∧ acceleratedOrbit 9 305 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_305 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 305) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_305.1, data_9_305.2]

/-- Complete interval computation for depth 9, residue 306. -/
theorem bounds_9_306 : exactInterval 9 306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_306 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 306) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_306 : oddCount 306 9 = 4 ∧ acceleratedOrbit 9 306 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_306 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 306) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_306.1, data_9_306.2]

end Collatz.Research.DescentIntervals.Batch080
