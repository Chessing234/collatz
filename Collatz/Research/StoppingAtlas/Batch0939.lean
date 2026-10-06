import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0939

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7239. -/
theorem bounds_13_7239 : exactInterval 13 7239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7239 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7239) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7239 : oddCount 7239 13 = 7 ∧ acceleratedOrbit 13 7239 = 1933 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7239 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7239) = 3 ^ 7 * m + 1933 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7239.1, data_13_7239.2]

/-- Complete interval computation for depth 13, residue 7240. -/
theorem bounds_13_7240 : exactInterval 13 7240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7240 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7240) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7240 : oddCount 7240 13 = 7 ∧ acceleratedOrbit 13 7240 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7240 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7240) = 3 ^ 7 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7240.1, data_13_7240.2]

/-- Complete interval computation for depth 13, residue 7241. -/
theorem bounds_13_7241 : exactInterval 13 7241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7241 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7241) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7241 : oddCount 7241 13 = 9 ∧ acceleratedOrbit 13 7241 = 17405 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7241 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7241) = 3 ^ 9 * m + 17405 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7241.1, data_13_7241.2]

/-- Complete interval computation for depth 13, residue 7242. -/
theorem bounds_13_7242 : exactInterval 13 7242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7242 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7242) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7242 : oddCount 7242 13 = 7 ∧ acceleratedOrbit 13 7242 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7242 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7242) = 3 ^ 7 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7242.1, data_13_7242.2]

/-- Complete interval computation for depth 13, residue 7243. -/
theorem bounds_13_7243 : exactInterval 13 7243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7243 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7243) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7243 : oddCount 7243 13 = 6 ∧ acceleratedOrbit 13 7243 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7243 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7243) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7243.1, data_13_7243.2]

/-- Complete interval computation for depth 13, residue 7244. -/
theorem bounds_13_7244 : exactInterval 13 7244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7244 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7244) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7244 : oddCount 7244 13 = 7 ∧ acceleratedOrbit 13 7244 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7244 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7244) = 3 ^ 7 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7244.1, data_13_7244.2]

/-- Complete interval computation for depth 13, residue 7245. -/
theorem bounds_13_7245 : exactInterval 13 7245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7245 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7245) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7245 : oddCount 7245 13 = 7 ∧ acceleratedOrbit 13 7245 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7245 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7245) = 3 ^ 7 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7245.1, data_13_7245.2]

/-- Complete interval computation for depth 13, residue 7246. -/
theorem bounds_13_7246 : exactInterval 13 7246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7246 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7246) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7246 : oddCount 7246 13 = 5 ∧ acceleratedOrbit 13 7246 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7246 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7246) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7246.1, data_13_7246.2]

/-- Complete interval computation for depth 13, residue 7247. -/
theorem bounds_13_7247 : exactInterval 13 7247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7247 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7247) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7247 : oddCount 7247 13 = 5 ∧ acceleratedOrbit 13 7247 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7247 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7247) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7247.1, data_13_7247.2]

/-- Complete interval computation for depth 13, residue 7248. -/
theorem bounds_13_7248 : exactInterval 13 7248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7248 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7248) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7248 : oddCount 7248 13 = 2 ∧ acceleratedOrbit 13 7248 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7248 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7248) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7248.1, data_13_7248.2]

/-- Complete interval computation for depth 13, residue 7249. -/
theorem bounds_13_7249 : exactInterval 13 7249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7249 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7249) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7249 : oddCount 7249 13 = 7 ∧ acceleratedOrbit 13 7249 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7249 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7249) = 3 ^ 7 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7249.1, data_13_7249.2]

/-- Complete interval computation for depth 13, residue 7250. -/
theorem bounds_13_7250 : exactInterval 13 7250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7250 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7250) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7250 : oddCount 7250 13 = 9 ∧ acceleratedOrbit 13 7250 = 17428 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7250 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7250) = 3 ^ 9 * m + 17428 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7250.1, data_13_7250.2]

/-- Complete interval computation for depth 13, residue 7251. -/
theorem bounds_13_7251 : exactInterval 13 7251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7251 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7251) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7251 : oddCount 7251 13 = 9 ∧ acceleratedOrbit 13 7251 = 17428 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7251 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7251) = 3 ^ 9 * m + 17428 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7251.1, data_13_7251.2]

/-- Complete interval computation for depth 13, residue 7252. -/
theorem bounds_13_7252 : exactInterval 13 7252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7252 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7252) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7252 : oddCount 7252 13 = 2 ∧ acceleratedOrbit 13 7252 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7252 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7252) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7252.1, data_13_7252.2]

/-- Complete interval computation for depth 13, residue 7253. -/
theorem bounds_13_7253 : exactInterval 13 7253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7253 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7253) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7253 : oddCount 7253 13 = 2 ∧ acceleratedOrbit 13 7253 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7253 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7253) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7253.1, data_13_7253.2]

/-- Complete interval computation for depth 13, residue 7254. -/
theorem bounds_13_7254 : exactInterval 13 7254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7254 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7254) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7254 : oddCount 7254 13 = 6 ∧ acceleratedOrbit 13 7254 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7254 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7254) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7254.1, data_13_7254.2]

end Collatz.Research.StoppingAtlas.Batch0939
