import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0771

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 25231. -/
theorem bounds_15_25231 : exactInterval 15 25231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25231 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25231) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25231 : oddCount 25231 15 = 9 ∧ acceleratedOrbit 15 25231 = 15157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25231 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25231) = 3 ^ 9 * m + 15157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25231.1, data_15_25231.2]

/-- Complete interval computation for depth 15, residue 25232. -/
theorem bounds_15_25232 : exactInterval 15 25232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25232 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25232) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25232 : oddCount 25232 15 = 9 ∧ acceleratedOrbit 15 25232 = 15173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25232 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25232) = 3 ^ 9 * m + 15173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25232.1, data_15_25232.2]

/-- Complete interval computation for depth 15, residue 25233. -/
theorem bounds_15_25233 : exactInterval 15 25233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25233 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25233) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25233 : oddCount 25233 15 = 7 ∧ acceleratedOrbit 15 25233 = 1685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25233 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25233) = 3 ^ 7 * m + 1685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25233.1, data_15_25233.2]

/-- Complete interval computation for depth 15, residue 25234. -/
theorem bounds_15_25234 : exactInterval 15 25234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25234 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25234) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25234 : oddCount 25234 15 = 7 ∧ acceleratedOrbit 15 25234 = 1685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25234 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25234) = 3 ^ 7 * m + 1685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25234.1, data_15_25234.2]

/-- Complete interval computation for depth 15, residue 25235. -/
theorem bounds_15_25235 : exactInterval 15 25235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25235 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25235) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25235 : oddCount 25235 15 = 7 ∧ acceleratedOrbit 15 25235 = 1685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25235 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25235) = 3 ^ 7 * m + 1685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25235.1, data_15_25235.2]

/-- Complete interval computation for depth 15, residue 25236. -/
theorem bounds_15_25236 : exactInterval 15 25236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25236 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25236) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25236 : oddCount 25236 15 = 9 ∧ acceleratedOrbit 15 25236 = 15173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25236 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25236) = 3 ^ 9 * m + 15173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25236.1, data_15_25236.2]

/-- Complete interval computation for depth 15, residue 25237. -/
theorem bounds_15_25237 : exactInterval 15 25237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25237 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25237) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25237 : oddCount 25237 15 = 9 ∧ acceleratedOrbit 15 25237 = 15173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25237 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25237) = 3 ^ 9 * m + 15173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25237.1, data_15_25237.2]

/-- Complete interval computation for depth 15, residue 25238. -/
theorem bounds_15_25238 : exactInterval 15 25238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25238 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25238) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25238 : oddCount 25238 15 = 6 ∧ acceleratedOrbit 15 25238 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25238 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25238) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25238.1, data_15_25238.2]

/-- Complete interval computation for depth 15, residue 25239. -/
theorem bounds_15_25239 : exactInterval 15 25239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25239 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25239) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25239 : oddCount 25239 15 = 6 ∧ acceleratedOrbit 15 25239 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25239 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25239) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25239.1, data_15_25239.2]

/-- Complete interval computation for depth 15, residue 25240. -/
theorem bounds_15_25240 : exactInterval 15 25240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25240 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25240) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25240 : oddCount 25240 15 = 9 ∧ acceleratedOrbit 15 25240 = 15173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25240 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25240) = 3 ^ 9 * m + 15173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25240.1, data_15_25240.2]

/-- Complete interval computation for depth 15, residue 25241. -/
theorem bounds_15_25241 : exactInterval 15 25241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25241 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25241) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25241 : oddCount 25241 15 = 7 ∧ acceleratedOrbit 15 25241 = 1685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25241 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25241) = 3 ^ 7 * m + 1685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25241.1, data_15_25241.2]

/-- Complete interval computation for depth 15, residue 25242. -/
theorem bounds_15_25242 : exactInterval 15 25242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25242 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25242) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25242 : oddCount 25242 15 = 9 ∧ acceleratedOrbit 15 25242 = 15173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25242 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25242) = 3 ^ 9 * m + 15173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25242.1, data_15_25242.2]

/-- Complete interval computation for depth 15, residue 25243. -/
theorem bounds_15_25243 : exactInterval 15 25243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25243 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25243) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25243 : oddCount 25243 15 = 11 ∧ acceleratedOrbit 15 25243 = 136475 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25243 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25243) = 3 ^ 11 * m + 136475 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25243.1, data_15_25243.2]

/-- Complete interval computation for depth 15, residue 25244. -/
theorem bounds_15_25244 : exactInterval 15 25244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25244 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25244) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25244 : oddCount 25244 15 = 9 ∧ acceleratedOrbit 15 25244 = 15167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25244 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25244) = 3 ^ 9 * m + 15167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25244.1, data_15_25244.2]

/-- Complete interval computation for depth 15, residue 25245. -/
theorem bounds_15_25245 : exactInterval 15 25245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25245 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25245) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25245 : oddCount 25245 15 = 9 ∧ acceleratedOrbit 15 25245 = 15167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25245 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25245) = 3 ^ 9 * m + 15167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25245.1, data_15_25245.2]

/-- Complete interval computation for depth 15, residue 25246. -/
theorem bounds_15_25246 : exactInterval 15 25246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25246 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25246) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25246 : oddCount 25246 15 = 9 ∧ acceleratedOrbit 15 25246 = 15167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25246 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25246) = 3 ^ 9 * m + 15167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25246.1, data_15_25246.2]

/-- Complete interval computation for depth 15, residue 25247. -/
theorem bounds_15_25247 : exactInterval 15 25247 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25247 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25247) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25247 : oddCount 25247 15 = 9 ∧ acceleratedOrbit 15 25247 = 15166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25247 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25247) = 3 ^ 9 * m + 15166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25247.1, data_15_25247.2]

/-- Complete interval computation for depth 15, residue 25248. -/
theorem bounds_15_25248 : exactInterval 15 25248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25248 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25248) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25248 : oddCount 25248 15 = 2 ∧ acceleratedOrbit 15 25248 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25248 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25248) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25248.1, data_15_25248.2]

/-- Complete interval computation for depth 15, residue 25249. -/
theorem bounds_15_25249 : exactInterval 15 25249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25249 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25249) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25249 : oddCount 25249 15 = 9 ∧ acceleratedOrbit 15 25249 = 15169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25249 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25249) = 3 ^ 9 * m + 15169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25249.1, data_15_25249.2]

/-- Complete interval computation for depth 15, residue 25250. -/
theorem bounds_15_25250 : exactInterval 15 25250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25250 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25250) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25250 : oddCount 25250 15 = 9 ∧ acceleratedOrbit 15 25250 = 15173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25250 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25250) = 3 ^ 9 * m + 15173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25250.1, data_15_25250.2]

/-- Complete interval computation for depth 15, residue 25251. -/
theorem bounds_15_25251 : exactInterval 15 25251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25251 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25251) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25251 : oddCount 25251 15 = 9 ∧ acceleratedOrbit 15 25251 = 15173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25251 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25251) = 3 ^ 9 * m + 15173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25251.1, data_15_25251.2]

/-- Complete interval computation for depth 15, residue 25252. -/
theorem bounds_15_25252 : exactInterval 15 25252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25252 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25252) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25252 : oddCount 25252 15 = 10 ∧ acceleratedOrbit 15 25252 = 45517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25252 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25252) = 3 ^ 10 * m + 45517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25252.1, data_15_25252.2]

/-- Complete interval computation for depth 15, residue 25253. -/
theorem bounds_15_25253 : exactInterval 15 25253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25253 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25253) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25253 : oddCount 25253 15 = 10 ∧ acceleratedOrbit 15 25253 = 45517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25253 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25253) = 3 ^ 10 * m + 45517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25253.1, data_15_25253.2]

/-- Complete interval computation for depth 15, residue 25254. -/
theorem bounds_15_25254 : exactInterval 15 25254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25254 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25254) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25254 : oddCount 25254 15 = 10 ∧ acceleratedOrbit 15 25254 = 45517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25254 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25254) = 3 ^ 10 * m + 45517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25254.1, data_15_25254.2]

/-- Complete interval computation for depth 15, residue 25255. -/
theorem bounds_15_25255 : exactInterval 15 25255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25255 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25255) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25255 : oddCount 25255 15 = 8 ∧ acceleratedOrbit 15 25255 = 5057 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25255 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25255) = 3 ^ 8 * m + 5057 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25255.1, data_15_25255.2]

/-- Complete interval computation for depth 15, residue 25256. -/
theorem bounds_15_25256 : exactInterval 15 25256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25256 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25256) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25256 : oddCount 25256 15 = 2 ∧ acceleratedOrbit 15 25256 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25256 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25256) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25256.1, data_15_25256.2]

/-- Complete interval computation for depth 15, residue 25257. -/
theorem bounds_15_25257 : exactInterval 15 25257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25257 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25257) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25257 : oddCount 25257 15 = 13 ∧ acceleratedOrbit 15 25257 = 1228958 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25257 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25257) = 3 ^ 13 * m + 1228958 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25257.1, data_15_25257.2]

/-- Complete interval computation for depth 15, residue 25258. -/
theorem bounds_15_25258 : exactInterval 15 25258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25258 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25258) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25258 : oddCount 25258 15 = 2 ∧ acceleratedOrbit 15 25258 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25258 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25258) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25258.1, data_15_25258.2]

/-- Complete interval computation for depth 15, residue 25259. -/
theorem bounds_15_25259 : exactInterval 15 25259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25259 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25259) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25259 : oddCount 25259 15 = 6 ∧ acceleratedOrbit 15 25259 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25259 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25259) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25259.1, data_15_25259.2]

/-- Complete interval computation for depth 15, residue 25260. -/
theorem bounds_15_25260 : exactInterval 15 25260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25260 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25260) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25260 : oddCount 25260 15 = 7 ∧ acceleratedOrbit 15 25260 = 1687 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25260 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25260) = 3 ^ 7 * m + 1687 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25260.1, data_15_25260.2]

/-- Complete interval computation for depth 15, residue 25261. -/
theorem bounds_15_25261 : exactInterval 15 25261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25261 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25261) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25261 : oddCount 25261 15 = 7 ∧ acceleratedOrbit 15 25261 = 1687 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25261 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25261) = 3 ^ 7 * m + 1687 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25261.1, data_15_25261.2]

/-- Complete interval computation for depth 15, residue 25262. -/
theorem bounds_15_25262 : exactInterval 15 25262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25262 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25262) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25262 : oddCount 25262 15 = 7 ∧ acceleratedOrbit 15 25262 = 1687 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25262 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25262) = 3 ^ 7 * m + 1687 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25262.1, data_15_25262.2]

/-- Complete interval computation for depth 15, residue 25263. -/
theorem bounds_15_25263 : exactInterval 15 25263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25263 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25263) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25263 : oddCount 25263 15 = 8 ∧ acceleratedOrbit 15 25263 = 5059 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25263 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25263) = 3 ^ 8 * m + 5059 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25263.1, data_15_25263.2]

end Collatz.Research.PassageAtlas.Batch0771
