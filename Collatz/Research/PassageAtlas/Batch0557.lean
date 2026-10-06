import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0557

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 18219. -/
theorem bounds_15_18219 : exactInterval 15 18219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18219 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18219) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18219 : oddCount 18219 15 = 7 ∧ acceleratedOrbit 15 18219 = 1217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18219 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18219) = 3 ^ 7 * m + 1217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18219.1, data_15_18219.2]

/-- Complete interval computation for depth 15, residue 18220. -/
theorem bounds_15_18220 : exactInterval 15 18220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18220 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18220) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18220 : oddCount 18220 15 = 6 ∧ acceleratedOrbit 15 18220 = 406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18220 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18220) = 3 ^ 6 * m + 406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18220.1, data_15_18220.2]

/-- Complete interval computation for depth 15, residue 18221. -/
theorem bounds_15_18221 : exactInterval 15 18221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18221 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18221) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18221 : oddCount 18221 15 = 6 ∧ acceleratedOrbit 15 18221 = 406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18221 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18221) = 3 ^ 6 * m + 406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18221.1, data_15_18221.2]

/-- Complete interval computation for depth 15, residue 18222. -/
theorem bounds_15_18222 : exactInterval 15 18222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18222 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18222) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18222 : oddCount 18222 15 = 6 ∧ acceleratedOrbit 15 18222 = 406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18222 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18222) = 3 ^ 6 * m + 406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18222.1, data_15_18222.2]

/-- Complete interval computation for depth 15, residue 18223. -/
theorem bounds_15_18223 : exactInterval 15 18223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18223 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18223) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18223 : oddCount 18223 15 = 9 ∧ acceleratedOrbit 15 18223 = 10948 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18223 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18223) = 3 ^ 9 * m + 10948 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18223.1, data_15_18223.2]

/-- Complete interval computation for depth 15, residue 18224. -/
theorem bounds_15_18224 : exactInterval 15 18224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18224 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18224) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18224 : oddCount 18224 15 = 6 ∧ acceleratedOrbit 15 18224 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18224 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18224) = 3 ^ 6 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18224.1, data_15_18224.2]

/-- Complete interval computation for depth 15, residue 18225. -/
theorem bounds_15_18225 : exactInterval 15 18225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18225 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18225) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18225 : oddCount 18225 15 = 6 ∧ acceleratedOrbit 15 18225 = 406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18225 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18225) = 3 ^ 6 * m + 406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18225.1, data_15_18225.2]

/-- Complete interval computation for depth 15, residue 18226. -/
theorem bounds_15_18226 : exactInterval 15 18226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18226 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18226) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18226 : oddCount 18226 15 = 6 ∧ acceleratedOrbit 15 18226 = 406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18226 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18226) = 3 ^ 6 * m + 406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18226.1, data_15_18226.2]

/-- Complete interval computation for depth 15, residue 18227. -/
theorem bounds_15_18227 : exactInterval 15 18227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18227 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18227) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18227 : oddCount 18227 15 = 6 ∧ acceleratedOrbit 15 18227 = 406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18227 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18227) = 3 ^ 6 * m + 406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18227.1, data_15_18227.2]

/-- Complete interval computation for depth 15, residue 18228. -/
theorem bounds_15_18228 : exactInterval 15 18228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18228 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18228) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18228 : oddCount 18228 15 = 6 ∧ acceleratedOrbit 15 18228 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18228 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18228) = 3 ^ 6 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18228.1, data_15_18228.2]

/-- Complete interval computation for depth 15, residue 18229. -/
theorem bounds_15_18229 : exactInterval 15 18229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18229 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18229) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18229 : oddCount 18229 15 = 6 ∧ acceleratedOrbit 15 18229 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18229 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18229) = 3 ^ 6 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18229.1, data_15_18229.2]

/-- Complete interval computation for depth 15, residue 18230. -/
theorem bounds_15_18230 : exactInterval 15 18230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18230 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18230) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18230 : oddCount 18230 15 = 7 ∧ acceleratedOrbit 15 18230 = 1217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18230 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18230) = 3 ^ 7 * m + 1217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18230.1, data_15_18230.2]

/-- Complete interval computation for depth 15, residue 18231. -/
theorem bounds_15_18231 : exactInterval 15 18231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18231 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18231) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18231 : oddCount 18231 15 = 7 ∧ acceleratedOrbit 15 18231 = 1217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18231 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18231) = 3 ^ 7 * m + 1217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18231.1, data_15_18231.2]

/-- Complete interval computation for depth 15, residue 18232. -/
theorem bounds_15_18232 : exactInterval 15 18232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18232 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18232) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18232 : oddCount 18232 15 = 8 ∧ acceleratedOrbit 15 18232 = 3653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18232 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18232) = 3 ^ 8 * m + 3653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18232.1, data_15_18232.2]

/-- Complete interval computation for depth 15, residue 18233. -/
theorem bounds_15_18233 : exactInterval 15 18233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18233 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18233) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18233 : oddCount 18233 15 = 9 ∧ acceleratedOrbit 15 18233 = 10955 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18233 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18233) = 3 ^ 9 * m + 10955 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18233.1, data_15_18233.2]

/-- Complete interval computation for depth 15, residue 18234. -/
theorem bounds_15_18234 : exactInterval 15 18234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18234 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18234) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18234 : oddCount 18234 15 = 8 ∧ acceleratedOrbit 15 18234 = 3653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18234 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18234) = 3 ^ 8 * m + 3653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18234.1, data_15_18234.2]

/-- Complete interval computation for depth 15, residue 18235. -/
theorem bounds_15_18235 : exactInterval 15 18235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18235 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18235) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18235 : oddCount 18235 15 = 6 ∧ acceleratedOrbit 15 18235 = 406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18235 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18235) = 3 ^ 6 * m + 406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18235.1, data_15_18235.2]

/-- Complete interval computation for depth 15, residue 18236. -/
theorem bounds_15_18236 : exactInterval 15 18236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18236 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18236) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18236 : oddCount 18236 15 = 8 ∧ acceleratedOrbit 15 18236 = 3653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18236 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18236) = 3 ^ 8 * m + 3653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18236.1, data_15_18236.2]

/-- Complete interval computation for depth 15, residue 18237. -/
theorem bounds_15_18237 : exactInterval 15 18237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18237 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18237) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18237 : oddCount 18237 15 = 8 ∧ acceleratedOrbit 15 18237 = 3653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18237 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18237) = 3 ^ 8 * m + 3653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18237.1, data_15_18237.2]

/-- Complete interval computation for depth 15, residue 18238. -/
theorem bounds_15_18238 : exactInterval 15 18238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18238 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18238) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18238 : oddCount 18238 15 = 9 ∧ acceleratedOrbit 15 18238 = 10957 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18238 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18238) = 3 ^ 9 * m + 10957 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18238.1, data_15_18238.2]

/-- Complete interval computation for depth 15, residue 18239. -/
theorem bounds_15_18239 : exactInterval 15 18239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18239 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18239) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18239 : oddCount 18239 15 = 9 ∧ acceleratedOrbit 15 18239 = 10957 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18239 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18239) = 3 ^ 9 * m + 10957 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18239.1, data_15_18239.2]

/-- Complete interval computation for depth 15, residue 18240. -/
theorem bounds_15_18240 : exactInterval 15 18240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18240 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18240) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18240 : oddCount 18240 15 = 5 ∧ acceleratedOrbit 15 18240 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18240 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18240) = 3 ^ 5 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18240.1, data_15_18240.2]

/-- Complete interval computation for depth 15, residue 18241. -/
theorem bounds_15_18241 : exactInterval 15 18241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18241 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18241) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18241 : oddCount 18241 15 = 6 ∧ acceleratedOrbit 15 18241 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18241 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18241) = 3 ^ 6 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18241.1, data_15_18241.2]

/-- Complete interval computation for depth 15, residue 18242. -/
theorem bounds_15_18242 : exactInterval 15 18242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18242 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18242) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18242 : oddCount 18242 15 = 6 ∧ acceleratedOrbit 15 18242 = 406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18242 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18242) = 3 ^ 6 * m + 406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18242.1, data_15_18242.2]

/-- Complete interval computation for depth 15, residue 18243. -/
theorem bounds_15_18243 : exactInterval 15 18243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18243 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18243) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18243 : oddCount 18243 15 = 6 ∧ acceleratedOrbit 15 18243 = 406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18243 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18243) = 3 ^ 6 * m + 406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18243.1, data_15_18243.2]

/-- Complete interval computation for depth 15, residue 18244. -/
theorem bounds_15_18244 : exactInterval 15 18244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18244 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18244) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18244 : oddCount 18244 15 = 6 ∧ acceleratedOrbit 15 18244 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18244 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18244) = 3 ^ 6 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18244.1, data_15_18244.2]

/-- Complete interval computation for depth 15, residue 18245. -/
theorem bounds_15_18245 : exactInterval 15 18245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18245 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18245) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18245 : oddCount 18245 15 = 6 ∧ acceleratedOrbit 15 18245 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18245 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18245) = 3 ^ 6 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18245.1, data_15_18245.2]

/-- Complete interval computation for depth 15, residue 18246. -/
theorem bounds_15_18246 : exactInterval 15 18246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18246 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18246) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18246 : oddCount 18246 15 = 6 ∧ acceleratedOrbit 15 18246 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18246 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18246) = 3 ^ 6 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18246.1, data_15_18246.2]

/-- Complete interval computation for depth 15, residue 18247. -/
theorem bounds_15_18247 : exactInterval 15 18247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18247 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18247) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18247 : oddCount 18247 15 = 11 ∧ acceleratedOrbit 15 18247 = 98657 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18247 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18247) = 3 ^ 11 * m + 98657 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18247.1, data_15_18247.2]

/-- Complete interval computation for depth 15, residue 18248. -/
theorem bounds_15_18248 : exactInterval 15 18248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18248 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18248) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18248 : oddCount 18248 15 = 7 ∧ acceleratedOrbit 15 18248 = 1219 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18248 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18248) = 3 ^ 7 * m + 1219 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18248.1, data_15_18248.2]

/-- Complete interval computation for depth 15, residue 18249. -/
theorem bounds_15_18249 : exactInterval 15 18249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18249 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18249) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18249 : oddCount 18249 15 = 8 ∧ acceleratedOrbit 15 18249 = 3655 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18249 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18249) = 3 ^ 8 * m + 3655 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18249.1, data_15_18249.2]

/-- Complete interval computation for depth 15, residue 18250. -/
theorem bounds_15_18250 : exactInterval 15 18250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18250 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18250) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18250 : oddCount 18250 15 = 7 ∧ acceleratedOrbit 15 18250 = 1219 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18250 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18250) = 3 ^ 7 * m + 1219 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18250.1, data_15_18250.2]

end Collatz.Research.PassageAtlas.Batch0557
