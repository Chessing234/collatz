import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0678

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3230. -/
theorem bounds_13_3230 : exactInterval 13 3230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3230 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3230) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3230 : oddCount 3230 13 = 8 ∧ acceleratedOrbit 13 3230 = 2591 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3230 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3230) = 3 ^ 8 * m + 2591 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3230.1, data_13_3230.2]

/-- Complete interval computation for depth 13, residue 3231. -/
theorem bounds_13_3231 : exactInterval 13 3231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3231 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3231) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3231 : oddCount 3231 13 = 11 ∧ acceleratedOrbit 13 3231 = 69893 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3231 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3231) = 3 ^ 11 * m + 69893 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3231.1, data_13_3231.2]

/-- Complete interval computation for depth 13, residue 3232. -/
theorem bounds_13_3232 : exactInterval 13 3232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3232 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3232) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3232 : oddCount 3232 13 = 3 ∧ acceleratedOrbit 13 3232 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3232 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3232) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3232.1, data_13_3232.2]

/-- Complete interval computation for depth 13, residue 3233. -/
theorem bounds_13_3233 : exactInterval 13 3233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3233 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3233) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3233 : oddCount 3233 13 = 10 ∧ acceleratedOrbit 13 3233 = 23327 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3233 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3233) = 3 ^ 10 * m + 23327 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3233.1, data_13_3233.2]

/-- Complete interval computation for depth 13, residue 3234. -/
theorem bounds_13_3234 : exactInterval 13 3234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3234 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3234) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3234 : oddCount 3234 13 = 7 ∧ acceleratedOrbit 13 3234 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3234 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3234) = 3 ^ 7 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3234.1, data_13_3234.2]

/-- Complete interval computation for depth 13, residue 3235. -/
theorem bounds_13_3235 : exactInterval 13 3235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3235 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3235) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3235 : oddCount 3235 13 = 7 ∧ acceleratedOrbit 13 3235 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3235 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3235) = 3 ^ 7 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3235.1, data_13_3235.2]

/-- Complete interval computation for depth 13, residue 3236. -/
theorem bounds_13_3236 : exactInterval 13 3236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3236 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3236) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3236 : oddCount 3236 13 = 7 ∧ acceleratedOrbit 13 3236 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3236 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3236) = 3 ^ 7 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3236.1, data_13_3236.2]

/-- Complete interval computation for depth 13, residue 3237. -/
theorem bounds_13_3237 : exactInterval 13 3237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3237 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3237) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3237 : oddCount 3237 13 = 7 ∧ acceleratedOrbit 13 3237 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3237 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3237) = 3 ^ 7 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3237.1, data_13_3237.2]

/-- Complete interval computation for depth 13, residue 3238. -/
theorem bounds_13_3238 : exactInterval 13 3238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3238 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3238) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3238 : oddCount 3238 13 = 7 ∧ acceleratedOrbit 13 3238 = 866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3238 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3238) = 3 ^ 7 * m + 866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3238.1, data_13_3238.2]

/-- Complete interval computation for depth 13, residue 3239. -/
theorem bounds_13_3239 : exactInterval 13 3239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3239 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3239) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3239 : oddCount 3239 13 = 9 ∧ acceleratedOrbit 13 3239 = 7786 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3239 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3239) = 3 ^ 9 * m + 7786 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3239.1, data_13_3239.2]

/-- Complete interval computation for depth 13, residue 3240. -/
theorem bounds_13_3240 : exactInterval 13 3240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3240 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3240) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3240 : oddCount 3240 13 = 3 ∧ acceleratedOrbit 13 3240 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3240 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3240) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3240.1, data_13_3240.2]

/-- Complete interval computation for depth 13, residue 3241. -/
theorem bounds_13_3241 : exactInterval 13 3241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3241 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3241) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3241 : oddCount 3241 13 = 8 ∧ acceleratedOrbit 13 3241 = 2597 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3241 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3241) = 3 ^ 8 * m + 2597 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3241.1, data_13_3241.2]

/-- Complete interval computation for depth 13, residue 3242. -/
theorem bounds_13_3242 : exactInterval 13 3242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3242 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3242) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3242 : oddCount 3242 13 = 3 ∧ acceleratedOrbit 13 3242 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3242 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3242) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3242.1, data_13_3242.2]

/-- Complete interval computation for depth 13, residue 3243. -/
theorem bounds_13_3243 : exactInterval 13 3243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3243 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3243) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3243 : oddCount 3243 13 = 6 ∧ acceleratedOrbit 13 3243 = 289 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3243 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3243) = 3 ^ 6 * m + 289 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3243.1, data_13_3243.2]

/-- Complete interval computation for depth 13, residue 3244. -/
theorem bounds_13_3244 : exactInterval 13 3244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3244 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3244) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3244 : oddCount 3244 13 = 6 ∧ acceleratedOrbit 13 3244 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3244 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3244) = 3 ^ 6 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3244.1, data_13_3244.2]

/-- Complete interval computation for depth 13, residue 3245. -/
theorem bounds_13_3245 : exactInterval 13 3245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3245 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3245) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3245 : oddCount 3245 13 = 6 ∧ acceleratedOrbit 13 3245 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3245 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3245) = 3 ^ 6 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3245.1, data_13_3245.2]

end Collatz.Research.StoppingAtlas.Batch0678
