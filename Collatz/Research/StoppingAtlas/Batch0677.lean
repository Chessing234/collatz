import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0677

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3215. -/
theorem bounds_13_3215 : exactInterval 13 3215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3215 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3215) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3215 : oddCount 3215 13 = 7 ∧ acceleratedOrbit 13 3215 = 859 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3215 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3215) = 3 ^ 7 * m + 859 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3215.1, data_13_3215.2]

/-- Complete interval computation for depth 13, residue 3216. -/
theorem bounds_13_3216 : exactInterval 13 3216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3216 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3216) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3216 : oddCount 3216 13 = 4 ∧ acceleratedOrbit 13 3216 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3216 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3216) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3216.1, data_13_3216.2]

/-- Complete interval computation for depth 13, residue 3217. -/
theorem bounds_13_3217 : exactInterval 13 3217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3217 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3217) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3217 : oddCount 3217 13 = 8 ∧ acceleratedOrbit 13 3217 = 2582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3217 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3217) = 3 ^ 8 * m + 2582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3217.1, data_13_3217.2]

/-- Complete interval computation for depth 13, residue 3218. -/
theorem bounds_13_3218 : exactInterval 13 3218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3218 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3218) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3218 : oddCount 3218 13 = 8 ∧ acceleratedOrbit 13 3218 = 2582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3218 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3218) = 3 ^ 8 * m + 2582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3218.1, data_13_3218.2]

/-- Complete interval computation for depth 13, residue 3219. -/
theorem bounds_13_3219 : exactInterval 13 3219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3219 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3219) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3219 : oddCount 3219 13 = 8 ∧ acceleratedOrbit 13 3219 = 2582 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3219 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3219) = 3 ^ 8 * m + 2582 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3219.1, data_13_3219.2]

/-- Complete interval computation for depth 13, residue 3220. -/
theorem bounds_13_3220 : exactInterval 13 3220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3220 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3220) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3220 : oddCount 3220 13 = 4 ∧ acceleratedOrbit 13 3220 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3220 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3220) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3220.1, data_13_3220.2]

/-- Complete interval computation for depth 13, residue 3221. -/
theorem bounds_13_3221 : exactInterval 13 3221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3221 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3221) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3221 : oddCount 3221 13 = 4 ∧ acceleratedOrbit 13 3221 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3221 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3221) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3221.1, data_13_3221.2]

/-- Complete interval computation for depth 13, residue 3222. -/
theorem bounds_13_3222 : exactInterval 13 3222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3222 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3222) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3222 : oddCount 3222 13 = 4 ∧ acceleratedOrbit 13 3222 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3222 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3222) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3222.1, data_13_3222.2]

/-- Complete interval computation for depth 13, residue 3223. -/
theorem bounds_13_3223 : exactInterval 13 3223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3223 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3223) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3223 : oddCount 3223 13 = 4 ∧ acceleratedOrbit 13 3223 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3223 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3223) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3223.1, data_13_3223.2]

/-- Complete interval computation for depth 13, residue 3224. -/
theorem bounds_13_3224 : exactInterval 13 3224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3224 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3224) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3224 : oddCount 3224 13 = 4 ∧ acceleratedOrbit 13 3224 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3224 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3224) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3224.1, data_13_3224.2]

/-- Complete interval computation for depth 13, residue 3225. -/
theorem bounds_13_3225 : exactInterval 13 3225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3225 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3225) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3225 : oddCount 3225 13 = 7 ∧ acceleratedOrbit 13 3225 = 863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3225 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3225) = 3 ^ 7 * m + 863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3225.1, data_13_3225.2]

/-- Complete interval computation for depth 13, residue 3226. -/
theorem bounds_13_3226 : exactInterval 13 3226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3226 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3226) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3226 : oddCount 3226 13 = 4 ∧ acceleratedOrbit 13 3226 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3226 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3226) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3226.1, data_13_3226.2]

/-- Complete interval computation for depth 13, residue 3227. -/
theorem bounds_13_3227 : exactInterval 13 3227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3227 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3227) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3227 : oddCount 3227 13 = 10 ∧ acceleratedOrbit 13 3227 = 23273 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3227 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3227) = 3 ^ 10 * m + 23273 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3227.1, data_13_3227.2]

/-- Complete interval computation for depth 13, residue 3228. -/
theorem bounds_13_3228 : exactInterval 13 3228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3228 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3228) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3228 : oddCount 3228 13 = 8 ∧ acceleratedOrbit 13 3228 = 2591 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3228 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3228) = 3 ^ 8 * m + 2591 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3228.1, data_13_3228.2]

/-- Complete interval computation for depth 13, residue 3229. -/
theorem bounds_13_3229 : exactInterval 13 3229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3229 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3229) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3229 : oddCount 3229 13 = 8 ∧ acceleratedOrbit 13 3229 = 2591 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3229 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3229) = 3 ^ 8 * m + 2591 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3229.1, data_13_3229.2]

end Collatz.Research.StoppingAtlas.Batch0677
