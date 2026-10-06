import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0743

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4229. -/
theorem bounds_13_4229 : exactInterval 13 4229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4229 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4229) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4229 : oddCount 4229 13 = 7 ∧ acceleratedOrbit 13 4229 = 1133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4229 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4229) = 3 ^ 7 * m + 1133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4229.1, data_13_4229.2]

/-- Complete interval computation for depth 13, residue 4230. -/
theorem bounds_13_4230 : exactInterval 13 4230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4230 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4230) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4230 : oddCount 4230 13 = 7 ∧ acceleratedOrbit 13 4230 = 1133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4230 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4230) = 3 ^ 7 * m + 1133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4230.1, data_13_4230.2]

/-- Complete interval computation for depth 13, residue 4231. -/
theorem bounds_13_4231 : exactInterval 13 4231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4231 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4231) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4231 : oddCount 4231 13 = 8 ∧ acceleratedOrbit 13 4231 = 3392 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4231 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4231) = 3 ^ 8 * m + 3392 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4231.1, data_13_4231.2]

/-- Complete interval computation for depth 13, residue 4232. -/
theorem bounds_13_4232 : exactInterval 13 4232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4232 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4232) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4232 : oddCount 4232 13 = 3 ∧ acceleratedOrbit 13 4232 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4232 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4232) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4232.1, data_13_4232.2]

/-- Complete interval computation for depth 13, residue 4233. -/
theorem bounds_13_4233 : exactInterval 13 4233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4233 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4233) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4233 : oddCount 4233 13 = 10 ∧ acceleratedOrbit 13 4233 = 30527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4233 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4233) = 3 ^ 10 * m + 30527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4233.1, data_13_4233.2]

/-- Complete interval computation for depth 13, residue 4234. -/
theorem bounds_13_4234 : exactInterval 13 4234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4234 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4234) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4234 : oddCount 4234 13 = 3 ∧ acceleratedOrbit 13 4234 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4234 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4234) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4234.1, data_13_4234.2]

/-- Complete interval computation for depth 13, residue 4235. -/
theorem bounds_13_4235 : exactInterval 13 4235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4235 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4235) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4235 : oddCount 4235 13 = 8 ∧ acceleratedOrbit 13 4235 = 3395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4235 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4235) = 3 ^ 8 * m + 3395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4235.1, data_13_4235.2]

/-- Complete interval computation for depth 13, residue 4236. -/
theorem bounds_13_4236 : exactInterval 13 4236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4236 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4236) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4236 : oddCount 4236 13 = 3 ∧ acceleratedOrbit 13 4236 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4236 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4236) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4236.1, data_13_4236.2]

/-- Complete interval computation for depth 13, residue 4237. -/
theorem bounds_13_4237 : exactInterval 13 4237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4237 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4237) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4237 : oddCount 4237 13 = 3 ∧ acceleratedOrbit 13 4237 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4237 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4237) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4237.1, data_13_4237.2]

/-- Complete interval computation for depth 13, residue 4238. -/
theorem bounds_13_4238 : exactInterval 13 4238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4238 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4238) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4238 : oddCount 4238 13 = 8 ∧ acceleratedOrbit 13 4238 = 3397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4238 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4238) = 3 ^ 8 * m + 3397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4238.1, data_13_4238.2]

/-- Complete interval computation for depth 13, residue 4239. -/
theorem bounds_13_4239 : exactInterval 13 4239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4239 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4239) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4239 : oddCount 4239 13 = 8 ∧ acceleratedOrbit 13 4239 = 3397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4239 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4239) = 3 ^ 8 * m + 3397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4239.1, data_13_4239.2]

/-- Complete interval computation for depth 13, residue 4240. -/
theorem bounds_13_4240 : exactInterval 13 4240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4240 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4240) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4240 : oddCount 4240 13 = 6 ∧ acceleratedOrbit 13 4240 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4240 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4240) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4240.1, data_13_4240.2]

/-- Complete interval computation for depth 13, residue 4241. -/
theorem bounds_13_4241 : exactInterval 13 4241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4241 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4241) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4241 : oddCount 4241 13 = 9 ∧ acceleratedOrbit 13 4241 = 10205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4241 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4241) = 3 ^ 9 * m + 10205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4241.1, data_13_4241.2]

/-- Complete interval computation for depth 13, residue 4242. -/
theorem bounds_13_4242 : exactInterval 13 4242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4242 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4242) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4242 : oddCount 4242 13 = 9 ∧ acceleratedOrbit 13 4242 = 10205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4242 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4242) = 3 ^ 9 * m + 10205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4242.1, data_13_4242.2]

/-- Complete interval computation for depth 13, residue 4243. -/
theorem bounds_13_4243 : exactInterval 13 4243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4243 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4243) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4243 : oddCount 4243 13 = 9 ∧ acceleratedOrbit 13 4243 = 10205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4243 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4243) = 3 ^ 9 * m + 10205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4243.1, data_13_4243.2]

end Collatz.Research.StoppingAtlas.Batch0743
