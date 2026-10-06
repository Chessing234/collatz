import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch081

/-- Complete interval computation for depth 9, residue 307. -/
theorem bounds_9_307 : exactInterval 9 307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_307 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 307) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_307 : oddCount 307 9 = 4 ∧ acceleratedOrbit 9 307 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_307 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 307) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_307.1, data_9_307.2]

/-- Complete interval computation for depth 9, residue 308. -/
theorem bounds_9_308 : exactInterval 9 308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_308 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 308) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_308 : oddCount 308 9 = 3 ∧ acceleratedOrbit 9 308 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_308 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 308) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_308.1, data_9_308.2]

/-- Complete interval computation for depth 9, residue 309. -/
theorem bounds_9_309 : exactInterval 9 309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_309 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 309) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_309 : oddCount 309 9 = 3 ∧ acceleratedOrbit 9 309 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_309 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 309) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_309.1, data_9_309.2]

/-- Complete interval computation for depth 9, residue 310. -/
theorem bounds_9_310 : exactInterval 9 310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_310 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 310) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_310 : oddCount 310 9 = 6 ∧ acceleratedOrbit 9 310 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_310 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 310) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_310.1, data_9_310.2]

/-- Complete interval computation for depth 9, residue 311. -/
theorem bounds_9_311 : exactInterval 9 311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_311 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 311) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_311 : oddCount 311 9 = 6 ∧ acceleratedOrbit 9 311 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_311 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 311) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_311.1, data_9_311.2]

/-- Complete interval computation for depth 9, residue 312. -/
theorem bounds_9_312 : exactInterval 9 312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_312 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 312) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_312 : oddCount 312 9 = 5 ∧ acceleratedOrbit 9 312 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_312 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 312) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_312.1, data_9_312.2]

/-- Complete interval computation for depth 9, residue 313. -/
theorem bounds_9_313 : exactInterval 9 313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_313 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 313) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_313 : oddCount 313 9 = 6 ∧ acceleratedOrbit 9 313 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_313 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 313) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_313.1, data_9_313.2]

/-- Complete interval computation for depth 9, residue 314. -/
theorem bounds_9_314 : exactInterval 9 314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_314 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 314) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_314 : oddCount 314 9 = 5 ∧ acceleratedOrbit 9 314 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_314 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 314) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_314.1, data_9_314.2]

/-- Complete interval computation for depth 9, residue 315. -/
theorem bounds_9_315 : exactInterval 9 315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_315 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 315) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_315 : oddCount 315 9 = 4 ∧ acceleratedOrbit 9 315 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_315 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 315) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_315.1, data_9_315.2]

/-- Complete interval computation for depth 9, residue 316. -/
theorem bounds_9_316 : exactInterval 9 316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_316 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 316) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_316 : oddCount 316 9 = 5 ∧ acceleratedOrbit 9 316 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_316 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 316) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_316.1, data_9_316.2]

end Collatz.Research.DescentIntervals.Batch081
