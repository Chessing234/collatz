import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0130

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 4227. -/
theorem bounds_15_4227 : exactInterval 15 4227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4227 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4227) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4227 : oddCount 4227 15 = 8 ∧ acceleratedOrbit 15 4227 = 850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4227 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4227) = 3 ^ 8 * m + 850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4227.1, data_15_4227.2]

/-- Complete interval computation for depth 15, residue 4228. -/
theorem bounds_15_4228 : exactInterval 15 4228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4228 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4228) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4228 : oddCount 4228 15 = 8 ∧ acceleratedOrbit 15 4228 = 850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4228 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4228) = 3 ^ 8 * m + 850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4228.1, data_15_4228.2]

/-- Complete interval computation for depth 15, residue 4229. -/
theorem bounds_15_4229 : exactInterval 15 4229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4229 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4229) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4229 : oddCount 4229 15 = 8 ∧ acceleratedOrbit 15 4229 = 850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4229 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4229) = 3 ^ 8 * m + 850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4229.1, data_15_4229.2]

/-- Complete interval computation for depth 15, residue 4230. -/
theorem bounds_15_4230 : exactInterval 15 4230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4230 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4230) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4230 : oddCount 4230 15 = 8 ∧ acceleratedOrbit 15 4230 = 850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4230 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4230) = 3 ^ 8 * m + 850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4230.1, data_15_4230.2]

/-- Complete interval computation for depth 15, residue 4231. -/
theorem bounds_15_4231 : exactInterval 15 4231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4231 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4231) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4231 : oddCount 4231 15 = 8 ∧ acceleratedOrbit 15 4231 = 848 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4231 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4231) = 3 ^ 8 * m + 848 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4231.1, data_15_4231.2]

/-- Complete interval computation for depth 15, residue 4232. -/
theorem bounds_15_4232 : exactInterval 15 4232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4232 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4232) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4232 : oddCount 4232 15 = 4 ∧ acceleratedOrbit 15 4232 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4232 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4232) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4232.1, data_15_4232.2]

/-- Complete interval computation for depth 15, residue 4233. -/
theorem bounds_15_4233 : exactInterval 15 4233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4233 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4233) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4233 : oddCount 4233 15 = 12 ∧ acceleratedOrbit 15 4233 = 68687 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4233 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4233) = 3 ^ 12 * m + 68687 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4233.1, data_15_4233.2]

/-- Complete interval computation for depth 15, residue 4234. -/
theorem bounds_15_4234 : exactInterval 15 4234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4234 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4234) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4234 : oddCount 4234 15 = 4 ∧ acceleratedOrbit 15 4234 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4234 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4234) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4234.1, data_15_4234.2]

/-- Complete interval computation for depth 15, residue 4235. -/
theorem bounds_15_4235 : exactInterval 15 4235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4235 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4235) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4235 : oddCount 4235 15 = 10 ∧ acceleratedOrbit 15 4235 = 7640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4235 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4235) = 3 ^ 10 * m + 7640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4235.1, data_15_4235.2]

/-- Complete interval computation for depth 15, residue 4236. -/
theorem bounds_15_4236 : exactInterval 15 4236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4236 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4236) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4236 : oddCount 4236 15 = 4 ∧ acceleratedOrbit 15 4236 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4236 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4236) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4236.1, data_15_4236.2]

/-- Complete interval computation for depth 15, residue 4237. -/
theorem bounds_15_4237 : exactInterval 15 4237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4237 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4237) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4237 : oddCount 4237 15 = 4 ∧ acceleratedOrbit 15 4237 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4237 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4237) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4237.1, data_15_4237.2]

/-- Complete interval computation for depth 15, residue 4238. -/
theorem bounds_15_4238 : exactInterval 15 4238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4238 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4238) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4238 : oddCount 4238 15 = 9 ∧ acceleratedOrbit 15 4238 = 2548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4238 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4238) = 3 ^ 9 * m + 2548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4238.1, data_15_4238.2]

/-- Complete interval computation for depth 15, residue 4239. -/
theorem bounds_15_4239 : exactInterval 15 4239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4239 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4239) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4239 : oddCount 4239 15 = 9 ∧ acceleratedOrbit 15 4239 = 2548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4239 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4239) = 3 ^ 9 * m + 2548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4239.1, data_15_4239.2]

/-- Complete interval computation for depth 15, residue 4240. -/
theorem bounds_15_4240 : exactInterval 15 4240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4240 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4240) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4240 : oddCount 4240 15 = 6 ∧ acceleratedOrbit 15 4240 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4240 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4240) = 3 ^ 6 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4240.1, data_15_4240.2]

/-- Complete interval computation for depth 15, residue 4241. -/
theorem bounds_15_4241 : exactInterval 15 4241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4241 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4241) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4241 : oddCount 4241 15 = 10 ∧ acceleratedOrbit 15 4241 = 7654 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4241 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4241) = 3 ^ 10 * m + 7654 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4241.1, data_15_4241.2]

/-- Complete interval computation for depth 15, residue 4242. -/
theorem bounds_15_4242 : exactInterval 15 4242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4242 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4242) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4242 : oddCount 4242 15 = 10 ∧ acceleratedOrbit 15 4242 = 7654 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4242 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4242) = 3 ^ 10 * m + 7654 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4242.1, data_15_4242.2]

/-- Complete interval computation for depth 15, residue 4243. -/
theorem bounds_15_4243 : exactInterval 15 4243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4243 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4243) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4243 : oddCount 4243 15 = 10 ∧ acceleratedOrbit 15 4243 = 7654 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4243 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4243) = 3 ^ 10 * m + 7654 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4243.1, data_15_4243.2]

/-- Complete interval computation for depth 15, residue 4244. -/
theorem bounds_15_4244 : exactInterval 15 4244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4244 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4244) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4244 : oddCount 4244 15 = 6 ∧ acceleratedOrbit 15 4244 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4244 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4244) = 3 ^ 6 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4244.1, data_15_4244.2]

/-- Complete interval computation for depth 15, residue 4245. -/
theorem bounds_15_4245 : exactInterval 15 4245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4245 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4245) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4245 : oddCount 4245 15 = 6 ∧ acceleratedOrbit 15 4245 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4245 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4245) = 3 ^ 6 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4245.1, data_15_4245.2]

/-- Complete interval computation for depth 15, residue 4246. -/
theorem bounds_15_4246 : exactInterval 15 4246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4246 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4246) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4246 : oddCount 4246 15 = 4 ∧ acceleratedOrbit 15 4246 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4246 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4246) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4246.1, data_15_4246.2]

/-- Complete interval computation for depth 15, residue 4247. -/
theorem bounds_15_4247 : exactInterval 15 4247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4247 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4247) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4247 : oddCount 4247 15 = 4 ∧ acceleratedOrbit 15 4247 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4247 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4247) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4247.1, data_15_4247.2]

/-- Complete interval computation for depth 15, residue 4248. -/
theorem bounds_15_4248 : exactInterval 15 4248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4248 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4248) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4248 : oddCount 4248 15 = 6 ∧ acceleratedOrbit 15 4248 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4248 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4248) = 3 ^ 6 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4248.1, data_15_4248.2]

/-- Complete interval computation for depth 15, residue 4249. -/
theorem bounds_15_4249 : exactInterval 15 4249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4249 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4249) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4249 : oddCount 4249 15 = 7 ∧ acceleratedOrbit 15 4249 = 284 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4249 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4249) = 3 ^ 7 * m + 284 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4249.1, data_15_4249.2]

/-- Complete interval computation for depth 15, residue 4250. -/
theorem bounds_15_4250 : exactInterval 15 4250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4250 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4250) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4250 : oddCount 4250 15 = 6 ∧ acceleratedOrbit 15 4250 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4250 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4250) = 3 ^ 6 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4250.1, data_15_4250.2]

/-- Complete interval computation for depth 15, residue 4251. -/
theorem bounds_15_4251 : exactInterval 15 4251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4251 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4251) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4251 : oddCount 4251 15 = 9 ∧ acceleratedOrbit 15 4251 = 2555 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4251 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4251) = 3 ^ 9 * m + 2555 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4251.1, data_15_4251.2]

/-- Complete interval computation for depth 15, residue 4252. -/
theorem bounds_15_4252 : exactInterval 15 4252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4252 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4252) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4252 : oddCount 4252 15 = 8 ∧ acceleratedOrbit 15 4252 = 854 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4252 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4252) = 3 ^ 8 * m + 854 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4252.1, data_15_4252.2]

/-- Complete interval computation for depth 15, residue 4253. -/
theorem bounds_15_4253 : exactInterval 15 4253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4253 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4253) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4253 : oddCount 4253 15 = 8 ∧ acceleratedOrbit 15 4253 = 854 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4253 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4253) = 3 ^ 8 * m + 854 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4253.1, data_15_4253.2]

/-- Complete interval computation for depth 15, residue 4254. -/
theorem bounds_15_4254 : exactInterval 15 4254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4254 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4254) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4254 : oddCount 4254 15 = 8 ∧ acceleratedOrbit 15 4254 = 854 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4254 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4254) = 3 ^ 8 * m + 854 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4254.1, data_15_4254.2]

/-- Complete interval computation for depth 15, residue 4255. -/
theorem bounds_15_4255 : exactInterval 15 4255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4255 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4255) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4255 : oddCount 4255 15 = 11 ∧ acceleratedOrbit 15 4255 = 23009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4255 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4255) = 3 ^ 11 * m + 23009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4255.1, data_15_4255.2]

/-- Complete interval computation for depth 15, residue 4256. -/
theorem bounds_15_4256 : exactInterval 15 4256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4256 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4256) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4256 : oddCount 4256 15 = 4 ∧ acceleratedOrbit 15 4256 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4256 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4256) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4256.1, data_15_4256.2]

/-- Complete interval computation for depth 15, residue 4257. -/
theorem bounds_15_4257 : exactInterval 15 4257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4257 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4257) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4257 : oddCount 4257 15 = 8 ∧ acceleratedOrbit 15 4257 = 853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4257 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4257) = 3 ^ 8 * m + 853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4257.1, data_15_4257.2]

/-- Complete interval computation for depth 15, residue 4258. -/
theorem bounds_15_4258 : exactInterval 15 4258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4258 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4258) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4258 : oddCount 4258 15 = 6 ∧ acceleratedOrbit 15 4258 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4258 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4258) = 3 ^ 6 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4258.1, data_15_4258.2]

end Collatz.Research.PassageAtlas.Batch0130
