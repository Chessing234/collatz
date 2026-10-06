import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0742

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4213. -/
theorem bounds_13_4213 : exactInterval 13 4213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4213 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4213) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4213 : oddCount 4213 13 = 6 ∧ acceleratedOrbit 13 4213 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4213 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4213) = 3 ^ 6 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4213.1, data_13_4213.2]

/-- Complete interval computation for depth 13, residue 4214. -/
theorem bounds_13_4214 : exactInterval 13 4214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4214 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4214) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4214 : oddCount 4214 13 = 7 ∧ acceleratedOrbit 13 4214 = 1127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4214 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4214) = 3 ^ 7 * m + 1127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4214.1, data_13_4214.2]

/-- Complete interval computation for depth 13, residue 4215. -/
theorem bounds_13_4215 : exactInterval 13 4215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4215 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4215) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4215 : oddCount 4215 13 = 7 ∧ acceleratedOrbit 13 4215 = 1127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4215 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4215) = 3 ^ 7 * m + 1127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4215.1, data_13_4215.2]

/-- Complete interval computation for depth 13, residue 4216. -/
theorem bounds_13_4216 : exactInterval 13 4216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4216 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4216) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4216 : oddCount 4216 13 = 6 ∧ acceleratedOrbit 13 4216 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4216 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4216) = 3 ^ 6 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4216.1, data_13_4216.2]

/-- Complete interval computation for depth 13, residue 4217. -/
theorem bounds_13_4217 : exactInterval 13 4217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4217 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4217) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4217 : oddCount 4217 13 = 9 ∧ acceleratedOrbit 13 4217 = 10138 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4217 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4217) = 3 ^ 9 * m + 10138 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4217.1, data_13_4217.2]

/-- Complete interval computation for depth 13, residue 4218. -/
theorem bounds_13_4218 : exactInterval 13 4218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4218 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4218) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4218 : oddCount 4218 13 = 6 ∧ acceleratedOrbit 13 4218 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4218 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4218) = 3 ^ 6 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4218.1, data_13_4218.2]

/-- Complete interval computation for depth 13, residue 4219. -/
theorem bounds_13_4219 : exactInterval 13 4219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4219 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4219) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4219 : oddCount 4219 13 = 7 ∧ acceleratedOrbit 13 4219 = 1127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4219 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4219) = 3 ^ 7 * m + 1127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4219.1, data_13_4219.2]

/-- Complete interval computation for depth 13, residue 4220. -/
theorem bounds_13_4220 : exactInterval 13 4220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4220 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4220) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4220 : oddCount 4220 13 = 9 ∧ acceleratedOrbit 13 4220 = 10151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4220 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4220) = 3 ^ 9 * m + 10151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4220.1, data_13_4220.2]

/-- Complete interval computation for depth 13, residue 4221. -/
theorem bounds_13_4221 : exactInterval 13 4221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4221 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4221) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4221 : oddCount 4221 13 = 9 ∧ acceleratedOrbit 13 4221 = 10151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4221 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4221) = 3 ^ 9 * m + 10151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4221.1, data_13_4221.2]

/-- Complete interval computation for depth 13, residue 4222. -/
theorem bounds_13_4222 : exactInterval 13 4222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4222 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4222) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4222 : oddCount 4222 13 = 9 ∧ acceleratedOrbit 13 4222 = 10151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4222 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4222) = 3 ^ 9 * m + 10151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4222.1, data_13_4222.2]

/-- Complete interval computation for depth 13, residue 4223. -/
theorem bounds_13_4223 : exactInterval 13 4223 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4223 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4223) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4223 : oddCount 4223 13 = 8 ∧ acceleratedOrbit 13 4223 = 3383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4223 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4223) = 3 ^ 8 * m + 3383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4223.1, data_13_4223.2]

/-- Complete interval computation for depth 13, residue 4224. -/
theorem bounds_13_4224 : exactInterval 13 4224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4224 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4224) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4224 : oddCount 4224 13 = 4 ∧ acceleratedOrbit 13 4224 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4224 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4224) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4224.1, data_13_4224.2]

/-- Complete interval computation for depth 13, residue 4225. -/
theorem bounds_13_4225 : exactInterval 13 4225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4225 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4225) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4225 : oddCount 4225 13 = 7 ∧ acceleratedOrbit 13 4225 = 1129 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4225 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4225) = 3 ^ 7 * m + 1129 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4225.1, data_13_4225.2]

/-- Complete interval computation for depth 13, residue 4226. -/
theorem bounds_13_4226 : exactInterval 13 4226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4226 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4226) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4226 : oddCount 4226 13 = 7 ∧ acceleratedOrbit 13 4226 = 1133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4226 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4226) = 3 ^ 7 * m + 1133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4226.1, data_13_4226.2]

/-- Complete interval computation for depth 13, residue 4227. -/
theorem bounds_13_4227 : exactInterval 13 4227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4227 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4227) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4227 : oddCount 4227 13 = 7 ∧ acceleratedOrbit 13 4227 = 1133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4227 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4227) = 3 ^ 7 * m + 1133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4227.1, data_13_4227.2]

/-- Complete interval computation for depth 13, residue 4228. -/
theorem bounds_13_4228 : exactInterval 13 4228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4228 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4228) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4228 : oddCount 4228 13 = 7 ∧ acceleratedOrbit 13 4228 = 1133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4228 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4228) = 3 ^ 7 * m + 1133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4228.1, data_13_4228.2]

end Collatz.Research.StoppingAtlas.Batch0742
