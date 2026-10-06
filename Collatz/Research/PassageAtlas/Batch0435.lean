import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0435

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 14221. -/
theorem bounds_15_14221 : exactInterval 15 14221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14221 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14221) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14221 : oddCount 14221 15 = 5 ∧ acceleratedOrbit 15 14221 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14221 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14221) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14221.1, data_15_14221.2]

/-- Complete interval computation for depth 15, residue 14222. -/
theorem bounds_15_14222 : exactInterval 15 14222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14222 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14222) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14222 : oddCount 14222 15 = 10 ∧ acceleratedOrbit 15 14222 = 25636 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14222 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14222) = 3 ^ 10 * m + 25636 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14222.1, data_15_14222.2]

/-- Complete interval computation for depth 15, residue 14223. -/
theorem bounds_15_14223 : exactInterval 15 14223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14223 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14223) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14223 : oddCount 14223 15 = 10 ∧ acceleratedOrbit 15 14223 = 25636 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14223 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14223) = 3 ^ 10 * m + 25636 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14223.1, data_15_14223.2]

/-- Complete interval computation for depth 15, residue 14224. -/
theorem bounds_15_14224 : exactInterval 15 14224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14224 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14224) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14224 : oddCount 14224 15 = 8 ∧ acceleratedOrbit 15 14224 = 2855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14224 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14224) = 3 ^ 8 * m + 2855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14224.1, data_15_14224.2]

/-- Complete interval computation for depth 15, residue 14225. -/
theorem bounds_15_14225 : exactInterval 15 14225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14225 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14225) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14225 : oddCount 14225 15 = 7 ∧ acceleratedOrbit 15 14225 = 950 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14225 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14225) = 3 ^ 7 * m + 950 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14225.1, data_15_14225.2]

/-- Complete interval computation for depth 15, residue 14226. -/
theorem bounds_15_14226 : exactInterval 15 14226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14226 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14226) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14226 : oddCount 14226 15 = 7 ∧ acceleratedOrbit 15 14226 = 950 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14226 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14226) = 3 ^ 7 * m + 950 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14226.1, data_15_14226.2]

/-- Complete interval computation for depth 15, residue 14227. -/
theorem bounds_15_14227 : exactInterval 15 14227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14227 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14227) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14227 : oddCount 14227 15 = 7 ∧ acceleratedOrbit 15 14227 = 950 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14227 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14227) = 3 ^ 7 * m + 950 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14227.1, data_15_14227.2]

/-- Complete interval computation for depth 15, residue 14228. -/
theorem bounds_15_14228 : exactInterval 15 14228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14228 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14228) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14228 : oddCount 14228 15 = 8 ∧ acceleratedOrbit 15 14228 = 2855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14228 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14228) = 3 ^ 8 * m + 2855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14228.1, data_15_14228.2]

/-- Complete interval computation for depth 15, residue 14229. -/
theorem bounds_15_14229 : exactInterval 15 14229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14229 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14229) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14229 : oddCount 14229 15 = 8 ∧ acceleratedOrbit 15 14229 = 2855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14229 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14229) = 3 ^ 8 * m + 2855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14229.1, data_15_14229.2]

/-- Complete interval computation for depth 15, residue 14230. -/
theorem bounds_15_14230 : exactInterval 15 14230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14230 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14230) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14230 : oddCount 14230 15 = 6 ∧ acceleratedOrbit 15 14230 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14230 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14230) = 3 ^ 6 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14230.1, data_15_14230.2]

/-- Complete interval computation for depth 15, residue 14231. -/
theorem bounds_15_14231 : exactInterval 15 14231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14231 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14231) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14231 : oddCount 14231 15 = 6 ∧ acceleratedOrbit 15 14231 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14231 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14231) = 3 ^ 6 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14231.1, data_15_14231.2]

/-- Complete interval computation for depth 15, residue 14232. -/
theorem bounds_15_14232 : exactInterval 15 14232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14232 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14232) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14232 : oddCount 14232 15 = 8 ∧ acceleratedOrbit 15 14232 = 2855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14232 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14232) = 3 ^ 8 * m + 2855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14232.1, data_15_14232.2]

/-- Complete interval computation for depth 15, residue 14233. -/
theorem bounds_15_14233 : exactInterval 15 14233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14233 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14233) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14233 : oddCount 14233 15 = 6 ∧ acceleratedOrbit 15 14233 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14233 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14233) = 3 ^ 6 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14233.1, data_15_14233.2]

/-- Complete interval computation for depth 15, residue 14234. -/
theorem bounds_15_14234 : exactInterval 15 14234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14234 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14234) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14234 : oddCount 14234 15 = 8 ∧ acceleratedOrbit 15 14234 = 2855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14234 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14234) = 3 ^ 8 * m + 2855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14234.1, data_15_14234.2]

/-- Complete interval computation for depth 15, residue 14235. -/
theorem bounds_15_14235 : exactInterval 15 14235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14235 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14235) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14235 : oddCount 14235 15 = 9 ∧ acceleratedOrbit 15 14235 = 8552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14235 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14235) = 3 ^ 9 * m + 8552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14235.1, data_15_14235.2]

/-- Complete interval computation for depth 15, residue 14236. -/
theorem bounds_15_14236 : exactInterval 15 14236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14236 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14236) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14236 : oddCount 14236 15 = 8 ∧ acceleratedOrbit 15 14236 = 2852 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14236 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14236) = 3 ^ 8 * m + 2852 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14236.1, data_15_14236.2]

/-- Complete interval computation for depth 15, residue 14237. -/
theorem bounds_15_14237 : exactInterval 15 14237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14237 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14237) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14237 : oddCount 14237 15 = 8 ∧ acceleratedOrbit 15 14237 = 2852 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14237 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14237) = 3 ^ 8 * m + 2852 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14237.1, data_15_14237.2]

/-- Complete interval computation for depth 15, residue 14238. -/
theorem bounds_15_14238 : exactInterval 15 14238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14238 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14238) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14238 : oddCount 14238 15 = 8 ∧ acceleratedOrbit 15 14238 = 2852 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14238 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14238) = 3 ^ 8 * m + 2852 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14238.1, data_15_14238.2]

/-- Complete interval computation for depth 15, residue 14239. -/
theorem bounds_15_14239 : exactInterval 15 14239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14239 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14239) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14239 : oddCount 14239 15 = 9 ∧ acceleratedOrbit 15 14239 = 8554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14239 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14239) = 3 ^ 9 * m + 8554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14239.1, data_15_14239.2]

/-- Complete interval computation for depth 15, residue 14240. -/
theorem bounds_15_14240 : exactInterval 15 14240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14240 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14240) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14240 : oddCount 14240 15 = 6 ∧ acceleratedOrbit 15 14240 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14240 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14240) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14240.1, data_15_14240.2]

/-- Complete interval computation for depth 15, residue 14241. -/
theorem bounds_15_14241 : exactInterval 15 14241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14241 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14241) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14241 : oddCount 14241 15 = 6 ∧ acceleratedOrbit 15 14241 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14241 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14241) = 3 ^ 6 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14241.1, data_15_14241.2]

/-- Complete interval computation for depth 15, residue 14242. -/
theorem bounds_15_14242 : exactInterval 15 14242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14242 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14242) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14242 : oddCount 14242 15 = 8 ∧ acceleratedOrbit 15 14242 = 2855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14242 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14242) = 3 ^ 8 * m + 2855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14242.1, data_15_14242.2]

/-- Complete interval computation for depth 15, residue 14243. -/
theorem bounds_15_14243 : exactInterval 15 14243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14243 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14243) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14243 : oddCount 14243 15 = 8 ∧ acceleratedOrbit 15 14243 = 2855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14243 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14243) = 3 ^ 8 * m + 2855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14243.1, data_15_14243.2]

/-- Complete interval computation for depth 15, residue 14244. -/
theorem bounds_15_14244 : exactInterval 15 14244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14244 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14244) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14244 : oddCount 14244 15 = 9 ∧ acceleratedOrbit 15 14244 = 8561 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14244 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14244) = 3 ^ 9 * m + 8561 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14244.1, data_15_14244.2]

/-- Complete interval computation for depth 15, residue 14245. -/
theorem bounds_15_14245 : exactInterval 15 14245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14245 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14245) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14245 : oddCount 14245 15 = 9 ∧ acceleratedOrbit 15 14245 = 8561 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14245 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14245) = 3 ^ 9 * m + 8561 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14245.1, data_15_14245.2]

/-- Complete interval computation for depth 15, residue 14246. -/
theorem bounds_15_14246 : exactInterval 15 14246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14246 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14246) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14246 : oddCount 14246 15 = 9 ∧ acceleratedOrbit 15 14246 = 8561 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14246 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14246) = 3 ^ 9 * m + 8561 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14246.1, data_15_14246.2]

/-- Complete interval computation for depth 15, residue 14247. -/
theorem bounds_15_14247 : exactInterval 15 14247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14247 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14247) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14247 : oddCount 14247 15 = 12 ∧ acceleratedOrbit 15 14247 = 231092 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14247 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14247) = 3 ^ 12 * m + 231092 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14247.1, data_15_14247.2]

/-- Complete interval computation for depth 15, residue 14248. -/
theorem bounds_15_14248 : exactInterval 15 14248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14248 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14248) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14248 : oddCount 14248 15 = 6 ∧ acceleratedOrbit 15 14248 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14248 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14248) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14248.1, data_15_14248.2]

/-- Complete interval computation for depth 15, residue 14249. -/
theorem bounds_15_14249 : exactInterval 15 14249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14249 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14249) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14249 : oddCount 14249 15 = 11 ∧ acceleratedOrbit 15 14249 = 77041 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14249 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14249) = 3 ^ 11 * m + 77041 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14249.1, data_15_14249.2]

/-- Complete interval computation for depth 15, residue 14250. -/
theorem bounds_15_14250 : exactInterval 15 14250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14250 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14250) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14250 : oddCount 14250 15 = 6 ∧ acceleratedOrbit 15 14250 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14250 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14250) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14250.1, data_15_14250.2]

/-- Complete interval computation for depth 15, residue 14251. -/
theorem bounds_15_14251 : exactInterval 15 14251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14251 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14251) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14251 : oddCount 14251 15 = 8 ∧ acceleratedOrbit 15 14251 = 2854 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14251 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14251) = 3 ^ 8 * m + 2854 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14251.1, data_15_14251.2]

/-- Complete interval computation for depth 15, residue 14252. -/
theorem bounds_15_14252 : exactInterval 15 14252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14252 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14252) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14252 : oddCount 14252 15 = 10 ∧ acceleratedOrbit 15 14252 = 25697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14252 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14252) = 3 ^ 10 * m + 25697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14252.1, data_15_14252.2]

/-- Complete interval computation for depth 15, residue 14253. -/
theorem bounds_15_14253 : exactInterval 15 14253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14253 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14253) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14253 : oddCount 14253 15 = 10 ∧ acceleratedOrbit 15 14253 = 25697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14253 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14253) = 3 ^ 10 * m + 25697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14253.1, data_15_14253.2]

end Collatz.Research.PassageAtlas.Batch0435
