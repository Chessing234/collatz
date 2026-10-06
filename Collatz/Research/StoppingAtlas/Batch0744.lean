import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0744

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4244. -/
theorem bounds_13_4244 : exactInterval 13 4244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4244 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4244) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4244 : oddCount 4244 13 = 6 ∧ acceleratedOrbit 13 4244 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4244 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4244) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4244.1, data_13_4244.2]

/-- Complete interval computation for depth 13, residue 4245. -/
theorem bounds_13_4245 : exactInterval 13 4245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4245 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4245) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4245 : oddCount 4245 13 = 6 ∧ acceleratedOrbit 13 4245 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4245 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4245) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4245.1, data_13_4245.2]

/-- Complete interval computation for depth 13, residue 4246. -/
theorem bounds_13_4246 : exactInterval 13 4246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4246 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4246) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4246 : oddCount 4246 13 = 3 ∧ acceleratedOrbit 13 4246 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4246 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4246) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4246.1, data_13_4246.2]

/-- Complete interval computation for depth 13, residue 4247. -/
theorem bounds_13_4247 : exactInterval 13 4247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4247 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4247) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4247 : oddCount 4247 13 = 3 ∧ acceleratedOrbit 13 4247 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4247 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4247) = 3 ^ 3 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4247.1, data_13_4247.2]

/-- Complete interval computation for depth 13, residue 4248. -/
theorem bounds_13_4248 : exactInterval 13 4248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4248 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4248) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4248 : oddCount 4248 13 = 6 ∧ acceleratedOrbit 13 4248 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4248 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4248) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4248.1, data_13_4248.2]

/-- Complete interval computation for depth 13, residue 4249. -/
theorem bounds_13_4249 : exactInterval 13 4249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4249 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4249) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4249 : oddCount 4249 13 = 7 ∧ acceleratedOrbit 13 4249 = 1136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4249 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4249) = 3 ^ 7 * m + 1136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4249.1, data_13_4249.2]

/-- Complete interval computation for depth 13, residue 4250. -/
theorem bounds_13_4250 : exactInterval 13 4250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4250 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4250) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4250 : oddCount 4250 13 = 6 ∧ acceleratedOrbit 13 4250 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4250 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4250) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4250.1, data_13_4250.2]

/-- Complete interval computation for depth 13, residue 4251. -/
theorem bounds_13_4251 : exactInterval 13 4251 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4251 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4251) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4251 : oddCount 4251 13 = 8 ∧ acceleratedOrbit 13 4251 = 3406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4251 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4251) = 3 ^ 8 * m + 3406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4251.1, data_13_4251.2]

/-- Complete interval computation for depth 13, residue 4252. -/
theorem bounds_13_4252 : exactInterval 13 4252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4252 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4252) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4252 : oddCount 4252 13 = 6 ∧ acceleratedOrbit 13 4252 = 379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4252 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4252) = 3 ^ 6 * m + 379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4252.1, data_13_4252.2]

/-- Complete interval computation for depth 13, residue 4253. -/
theorem bounds_13_4253 : exactInterval 13 4253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4253 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4253) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4253 : oddCount 4253 13 = 6 ∧ acceleratedOrbit 13 4253 = 379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4253 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4253) = 3 ^ 6 * m + 379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4253.1, data_13_4253.2]

/-- Complete interval computation for depth 13, residue 4254. -/
theorem bounds_13_4254 : exactInterval 13 4254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4254 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4254) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4254 : oddCount 4254 13 = 6 ∧ acceleratedOrbit 13 4254 = 379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4254 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4254) = 3 ^ 6 * m + 379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4254.1, data_13_4254.2]

/-- Complete interval computation for depth 13, residue 4255. -/
theorem bounds_13_4255 : exactInterval 13 4255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4255 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4255) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4255 : oddCount 4255 13 = 11 ∧ acceleratedOrbit 13 4255 = 92036 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4255 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4255) = 3 ^ 11 * m + 92036 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4255.1, data_13_4255.2]

/-- Complete interval computation for depth 13, residue 4256. -/
theorem bounds_13_4256 : exactInterval 13 4256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4256 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4256) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4256 : oddCount 4256 13 = 4 ∧ acceleratedOrbit 13 4256 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4256 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4256) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4256.1, data_13_4256.2]

/-- Complete interval computation for depth 13, residue 4257. -/
theorem bounds_13_4257 : exactInterval 13 4257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4257 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4257) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4257 : oddCount 4257 13 = 8 ∧ acceleratedOrbit 13 4257 = 3412 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4257 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4257) = 3 ^ 8 * m + 3412 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4257.1, data_13_4257.2]

/-- Complete interval computation for depth 13, residue 4258. -/
theorem bounds_13_4258 : exactInterval 13 4258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4258 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4258) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4258 : oddCount 4258 13 = 6 ∧ acceleratedOrbit 13 4258 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4258 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4258) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4258.1, data_13_4258.2]

end Collatz.Research.StoppingAtlas.Batch0744
