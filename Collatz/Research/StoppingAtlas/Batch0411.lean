import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0411

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3225. -/
theorem bounds_12_3225 : exactInterval 12 3225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3225 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3225) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3225 : oddCount 3225 12 = 6 ∧ acceleratedOrbit 12 3225 = 575 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3225 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3225) = 3 ^ 6 * m + 575 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3225.1, data_12_3225.2]

/-- Complete interval computation for depth 12, residue 3226. -/
theorem bounds_12_3226 : exactInterval 12 3226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3226 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3226) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3226 : oddCount 3226 12 = 4 ∧ acceleratedOrbit 12 3226 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3226 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3226) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3226.1, data_12_3226.2]

/-- Complete interval computation for depth 12, residue 3227. -/
theorem bounds_12_3227 : exactInterval 12 3227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3227 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3227) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3227 : oddCount 3227 12 = 9 ∧ acceleratedOrbit 12 3227 = 15515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3227 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3227) = 3 ^ 9 * m + 15515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3227.1, data_12_3227.2]

/-- Complete interval computation for depth 12, residue 3228. -/
theorem bounds_12_3228 : exactInterval 12 3228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3228 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3228) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3228 : oddCount 3228 12 = 7 ∧ acceleratedOrbit 12 3228 = 1727 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3228 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3228) = 3 ^ 7 * m + 1727 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3228.1, data_12_3228.2]

/-- Complete interval computation for depth 12, residue 3229. -/
theorem bounds_12_3229 : exactInterval 12 3229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3229 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3229) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3229 : oddCount 3229 12 = 7 ∧ acceleratedOrbit 12 3229 = 1727 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3229 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3229) = 3 ^ 7 * m + 1727 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3229.1, data_12_3229.2]

/-- Complete interval computation for depth 12, residue 3230. -/
theorem bounds_12_3230 : exactInterval 12 3230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3230 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3230) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3230 : oddCount 3230 12 = 7 ∧ acceleratedOrbit 12 3230 = 1727 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3230 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3230) = 3 ^ 7 * m + 1727 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3230.1, data_12_3230.2]

/-- Complete interval computation for depth 12, residue 3231. -/
theorem bounds_12_3231 : exactInterval 12 3231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3231 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3231) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3231 : oddCount 3231 12 = 10 ∧ acceleratedOrbit 12 3231 = 46595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3231 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3231) = 3 ^ 10 * m + 46595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3231.1, data_12_3231.2]

/-- Complete interval computation for depth 12, residue 3232. -/
theorem bounds_12_3232 : exactInterval 12 3232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3232 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3232) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3232 : oddCount 3232 12 = 3 ∧ acceleratedOrbit 12 3232 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3232 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3232) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3232.1, data_12_3232.2]

/-- Complete interval computation for depth 12, residue 3233. -/
theorem bounds_12_3233 : exactInterval 12 3233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3233 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3233) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3233 : oddCount 3233 12 = 9 ∧ acceleratedOrbit 12 3233 = 15551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3233 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3233) = 3 ^ 9 * m + 15551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3233.1, data_12_3233.2]

/-- Complete interval computation for depth 12, residue 3234. -/
theorem bounds_12_3234 : exactInterval 12 3234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3234 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3234) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3234 : oddCount 3234 12 = 6 ∧ acceleratedOrbit 12 3234 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3234 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3234) = 3 ^ 6 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3234.1, data_12_3234.2]

/-- Complete interval computation for depth 12, residue 3235. -/
theorem bounds_12_3235 : exactInterval 12 3235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3235 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3235) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3235 : oddCount 3235 12 = 6 ∧ acceleratedOrbit 12 3235 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3235 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3235) = 3 ^ 6 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3235.1, data_12_3235.2]

/-- Complete interval computation for depth 12, residue 3236. -/
theorem bounds_12_3236 : exactInterval 12 3236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3236 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3236) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3236 : oddCount 3236 12 = 6 ∧ acceleratedOrbit 12 3236 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3236 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3236) = 3 ^ 6 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3236.1, data_12_3236.2]

/-- Complete interval computation for depth 12, residue 3237. -/
theorem bounds_12_3237 : exactInterval 12 3237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3237 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3237) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3237 : oddCount 3237 12 = 6 ∧ acceleratedOrbit 12 3237 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3237 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3237) = 3 ^ 6 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3237.1, data_12_3237.2]

/-- Complete interval computation for depth 12, residue 3238. -/
theorem bounds_12_3238 : exactInterval 12 3238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3238 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3238) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3238 : oddCount 3238 12 = 6 ∧ acceleratedOrbit 12 3238 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3238 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3238) = 3 ^ 6 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3238.1, data_12_3238.2]

/-- Complete interval computation for depth 12, residue 3239. -/
theorem bounds_12_3239 : exactInterval 12 3239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3239 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3239) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3239 : oddCount 3239 12 = 9 ∧ acceleratedOrbit 12 3239 = 15572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3239 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3239) = 3 ^ 9 * m + 15572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3239.1, data_12_3239.2]

end Collatz.Research.StoppingAtlas.Batch0411
