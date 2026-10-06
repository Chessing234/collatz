import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0938

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7224. -/
theorem bounds_13_7224 : exactInterval 13 7224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7224 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7224) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7224 : oddCount 7224 13 = 5 ∧ acceleratedOrbit 13 7224 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7224 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7224) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7224.1, data_13_7224.2]

/-- Complete interval computation for depth 13, residue 7225. -/
theorem bounds_13_7225 : exactInterval 13 7225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7225 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7225) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7225 : oddCount 7225 13 = 7 ∧ acceleratedOrbit 13 7225 = 1930 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7225 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7225) = 3 ^ 7 * m + 1930 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7225.1, data_13_7225.2]

/-- Complete interval computation for depth 13, residue 7226. -/
theorem bounds_13_7226 : exactInterval 13 7226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7226 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7226) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7226 : oddCount 7226 13 = 5 ∧ acceleratedOrbit 13 7226 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7226 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7226) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7226.1, data_13_7226.2]

/-- Complete interval computation for depth 13, residue 7227. -/
theorem bounds_13_7227 : exactInterval 13 7227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7227 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7227) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7227 : oddCount 7227 13 = 8 ∧ acceleratedOrbit 13 7227 = 5791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7227 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7227) = 3 ^ 8 * m + 5791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7227.1, data_13_7227.2]

/-- Complete interval computation for depth 13, residue 7228. -/
theorem bounds_13_7228 : exactInterval 13 7228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7228 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7228) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7228 : oddCount 7228 13 = 5 ∧ acceleratedOrbit 13 7228 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7228 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7228) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7228.1, data_13_7228.2]

/-- Complete interval computation for depth 13, residue 7229. -/
theorem bounds_13_7229 : exactInterval 13 7229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7229 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7229) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7229 : oddCount 7229 13 = 5 ∧ acceleratedOrbit 13 7229 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7229 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7229) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7229.1, data_13_7229.2]

/-- Complete interval computation for depth 13, residue 7230. -/
theorem bounds_13_7230 : exactInterval 13 7230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7230 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7230) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7230 : oddCount 7230 13 = 9 ∧ acceleratedOrbit 13 7230 = 17378 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7230 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7230) = 3 ^ 9 * m + 17378 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7230.1, data_13_7230.2]

/-- Complete interval computation for depth 13, residue 7231. -/
theorem bounds_13_7231 : exactInterval 13 7231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7231 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7231) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7231 : oddCount 7231 13 = 9 ∧ acceleratedOrbit 13 7231 = 17378 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7231 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7231) = 3 ^ 9 * m + 17378 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7231.1, data_13_7231.2]

/-- Complete interval computation for depth 13, residue 7232. -/
theorem bounds_13_7232 : exactInterval 13 7232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7232 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7232) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7232 : oddCount 7232 13 = 2 ∧ acceleratedOrbit 13 7232 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7232 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7232) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7232.1, data_13_7232.2]

/-- Complete interval computation for depth 13, residue 7233. -/
theorem bounds_13_7233 : exactInterval 13 7233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7233 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7233) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7233 : oddCount 7233 13 = 7 ∧ acceleratedOrbit 13 7233 = 1934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7233 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7233) = 3 ^ 7 * m + 1934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7233.1, data_13_7233.2]

/-- Complete interval computation for depth 13, residue 7234. -/
theorem bounds_13_7234 : exactInterval 13 7234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7234 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7234) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7234 : oddCount 7234 13 = 7 ∧ acceleratedOrbit 13 7234 = 1934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7234 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7234) = 3 ^ 7 * m + 1934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7234.1, data_13_7234.2]

/-- Complete interval computation for depth 13, residue 7235. -/
theorem bounds_13_7235 : exactInterval 13 7235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7235 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7235) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7235 : oddCount 7235 13 = 7 ∧ acceleratedOrbit 13 7235 = 1934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7235 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7235) = 3 ^ 7 * m + 1934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7235.1, data_13_7235.2]

/-- Complete interval computation for depth 13, residue 7236. -/
theorem bounds_13_7236 : exactInterval 13 7236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7236 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7236) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7236 : oddCount 7236 13 = 6 ∧ acceleratedOrbit 13 7236 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7236 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7236) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7236.1, data_13_7236.2]

/-- Complete interval computation for depth 13, residue 7237. -/
theorem bounds_13_7237 : exactInterval 13 7237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7237 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7237) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7237 : oddCount 7237 13 = 6 ∧ acceleratedOrbit 13 7237 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7237 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7237) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7237.1, data_13_7237.2]

/-- Complete interval computation for depth 13, residue 7238. -/
theorem bounds_13_7238 : exactInterval 13 7238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7238 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7238) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7238 : oddCount 7238 13 = 6 ∧ acceleratedOrbit 13 7238 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7238 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7238) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7238.1, data_13_7238.2]

end Collatz.Research.StoppingAtlas.Batch0938
