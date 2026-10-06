import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0649

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 21233. -/
theorem bounds_15_21233 : exactInterval 15 21233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21233 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21233) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21233 : oddCount 21233 15 = 4 ∧ acceleratedOrbit 15 21233 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21233 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21233) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21233.1, data_15_21233.2]

/-- Complete interval computation for depth 15, residue 21234. -/
theorem bounds_15_21234 : exactInterval 15 21234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21234 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21234) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21234 : oddCount 21234 15 = 11 ∧ acceleratedOrbit 15 21234 = 114817 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21234 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21234) = 3 ^ 11 * m + 114817 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21234.1, data_15_21234.2]

/-- Complete interval computation for depth 15, residue 21235. -/
theorem bounds_15_21235 : exactInterval 15 21235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21235 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21235) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21235 : oddCount 21235 15 = 11 ∧ acceleratedOrbit 15 21235 = 114817 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21235 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21235) = 3 ^ 11 * m + 114817 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21235.1, data_15_21235.2]

/-- Complete interval computation for depth 15, residue 21236. -/
theorem bounds_15_21236 : exactInterval 15 21236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21236 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21236) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21236 : oddCount 21236 15 = 8 ∧ acceleratedOrbit 15 21236 = 4256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21236 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21236) = 3 ^ 8 * m + 4256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21236.1, data_15_21236.2]

/-- Complete interval computation for depth 15, residue 21237. -/
theorem bounds_15_21237 : exactInterval 15 21237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21237 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21237) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21237 : oddCount 21237 15 = 8 ∧ acceleratedOrbit 15 21237 = 4256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21237 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21237) = 3 ^ 8 * m + 4256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21237.1, data_15_21237.2]

/-- Complete interval computation for depth 15, residue 21238. -/
theorem bounds_15_21238 : exactInterval 15 21238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21238 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21238) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21238 : oddCount 21238 15 = 9 ∧ acceleratedOrbit 15 21238 = 12761 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21238 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21238) = 3 ^ 9 * m + 12761 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21238.1, data_15_21238.2]

/-- Complete interval computation for depth 15, residue 21239. -/
theorem bounds_15_21239 : exactInterval 15 21239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21239 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21239) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21239 : oddCount 21239 15 = 9 ∧ acceleratedOrbit 15 21239 = 12761 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21239 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21239) = 3 ^ 9 * m + 12761 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21239.1, data_15_21239.2]

/-- Complete interval computation for depth 15, residue 21240. -/
theorem bounds_15_21240 : exactInterval 15 21240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21240 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21240) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21240 : oddCount 21240 15 = 8 ∧ acceleratedOrbit 15 21240 = 4256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21240 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21240) = 3 ^ 8 * m + 4256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21240.1, data_15_21240.2]

/-- Complete interval computation for depth 15, residue 21241. -/
theorem bounds_15_21241 : exactInterval 15 21241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21241 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21241) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21241 : oddCount 21241 15 = 7 ∧ acceleratedOrbit 15 21241 = 1418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21241 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21241) = 3 ^ 7 * m + 1418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21241.1, data_15_21241.2]

/-- Complete interval computation for depth 15, residue 21242. -/
theorem bounds_15_21242 : exactInterval 15 21242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21242 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21242) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21242 : oddCount 21242 15 = 8 ∧ acceleratedOrbit 15 21242 = 4256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21242 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21242) = 3 ^ 8 * m + 4256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21242.1, data_15_21242.2]

/-- Complete interval computation for depth 15, residue 21243. -/
theorem bounds_15_21243 : exactInterval 15 21243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21243 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21243) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21243 : oddCount 21243 15 = 10 ∧ acceleratedOrbit 15 21243 = 38285 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21243 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21243) = 3 ^ 10 * m + 38285 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21243.1, data_15_21243.2]

/-- Complete interval computation for depth 15, residue 21244. -/
theorem bounds_15_21244 : exactInterval 15 21244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21244 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21244) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21244 : oddCount 21244 15 = 9 ∧ acceleratedOrbit 15 21244 = 12764 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21244 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21244) = 3 ^ 9 * m + 12764 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21244.1, data_15_21244.2]

/-- Complete interval computation for depth 15, residue 21245. -/
theorem bounds_15_21245 : exactInterval 15 21245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21245 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21245) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21245 : oddCount 21245 15 = 9 ∧ acceleratedOrbit 15 21245 = 12764 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21245 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21245) = 3 ^ 9 * m + 12764 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21245.1, data_15_21245.2]

/-- Complete interval computation for depth 15, residue 21246. -/
theorem bounds_15_21246 : exactInterval 15 21246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21246 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21246) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21246 : oddCount 21246 15 = 9 ∧ acceleratedOrbit 15 21246 = 12764 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21246 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21246) = 3 ^ 9 * m + 12764 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21246.1, data_15_21246.2]

/-- Complete interval computation for depth 15, residue 21247. -/
theorem bounds_15_21247 : exactInterval 15 21247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21247 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21247) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21247 : oddCount 21247 15 = 11 ∧ acceleratedOrbit 15 21247 = 114869 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21247 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21247) = 3 ^ 11 * m + 114869 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21247.1, data_15_21247.2]

/-- Complete interval computation for depth 15, residue 21248. -/
theorem bounds_15_21248 : exactInterval 15 21248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21248 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21248) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21248 : oddCount 21248 15 = 5 ∧ acceleratedOrbit 15 21248 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21248 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21248) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21248.1, data_15_21248.2]

/-- Complete interval computation for depth 15, residue 21249. -/
theorem bounds_15_21249 : exactInterval 15 21249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21249 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21249) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21249 : oddCount 21249 15 = 6 ∧ acceleratedOrbit 15 21249 = 473 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21249 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21249) = 3 ^ 6 * m + 473 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21249.1, data_15_21249.2]

/-- Complete interval computation for depth 15, residue 21250. -/
theorem bounds_15_21250 : exactInterval 15 21250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21250 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21250) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21250 : oddCount 21250 15 = 6 ∧ acceleratedOrbit 15 21250 = 473 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21250 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21250) = 3 ^ 6 * m + 473 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21250.1, data_15_21250.2]

/-- Complete interval computation for depth 15, residue 21251. -/
theorem bounds_15_21251 : exactInterval 15 21251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21251 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21251) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21251 : oddCount 21251 15 = 6 ∧ acceleratedOrbit 15 21251 = 473 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21251 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21251) = 3 ^ 6 * m + 473 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21251.1, data_15_21251.2]

/-- Complete interval computation for depth 15, residue 21252. -/
theorem bounds_15_21252 : exactInterval 15 21252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21252 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21252) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21252 : oddCount 21252 15 = 7 ∧ acceleratedOrbit 15 21252 = 1421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21252 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21252) = 3 ^ 7 * m + 1421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21252.1, data_15_21252.2]

/-- Complete interval computation for depth 15, residue 21253. -/
theorem bounds_15_21253 : exactInterval 15 21253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21253 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21253) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21253 : oddCount 21253 15 = 7 ∧ acceleratedOrbit 15 21253 = 1421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21253 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21253) = 3 ^ 7 * m + 1421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21253.1, data_15_21253.2]

/-- Complete interval computation for depth 15, residue 21254. -/
theorem bounds_15_21254 : exactInterval 15 21254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21254 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21254) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21254 : oddCount 21254 15 = 7 ∧ acceleratedOrbit 15 21254 = 1421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21254 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21254) = 3 ^ 7 * m + 1421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21254.1, data_15_21254.2]

/-- Complete interval computation for depth 15, residue 21255. -/
theorem bounds_15_21255 : exactInterval 15 21255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21255 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21255) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21255 : oddCount 21255 15 = 9 ∧ acceleratedOrbit 15 21255 = 12770 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21255 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21255) = 3 ^ 9 * m + 12770 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21255.1, data_15_21255.2]

/-- Complete interval computation for depth 15, residue 21256. -/
theorem bounds_15_21256 : exactInterval 15 21256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21256 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21256) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21256 : oddCount 21256 15 = 7 ∧ acceleratedOrbit 15 21256 = 1421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21256 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21256) = 3 ^ 7 * m + 1421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21256.1, data_15_21256.2]

/-- Complete interval computation for depth 15, residue 21257. -/
theorem bounds_15_21257 : exactInterval 15 21257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21257 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21257) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21257 : oddCount 21257 15 = 10 ∧ acceleratedOrbit 15 21257 = 38312 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21257 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21257) = 3 ^ 10 * m + 38312 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21257.1, data_15_21257.2]

/-- Complete interval computation for depth 15, residue 21258. -/
theorem bounds_15_21258 : exactInterval 15 21258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21258 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21258) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21258 : oddCount 21258 15 = 7 ∧ acceleratedOrbit 15 21258 = 1421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21258 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21258) = 3 ^ 7 * m + 1421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21258.1, data_15_21258.2]

/-- Complete interval computation for depth 15, residue 21259. -/
theorem bounds_15_21259 : exactInterval 15 21259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21259 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21259) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21259 : oddCount 21259 15 = 9 ∧ acceleratedOrbit 15 21259 = 12773 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21259 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21259) = 3 ^ 9 * m + 12773 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21259.1, data_15_21259.2]

/-- Complete interval computation for depth 15, residue 21260. -/
theorem bounds_15_21260 : exactInterval 15 21260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21260 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21260) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21260 : oddCount 21260 15 = 7 ∧ acceleratedOrbit 15 21260 = 1421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21260 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21260) = 3 ^ 7 * m + 1421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21260.1, data_15_21260.2]

/-- Complete interval computation for depth 15, residue 21261. -/
theorem bounds_15_21261 : exactInterval 15 21261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21261 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21261) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21261 : oddCount 21261 15 = 7 ∧ acceleratedOrbit 15 21261 = 1421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21261 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21261) = 3 ^ 7 * m + 1421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21261.1, data_15_21261.2]

/-- Complete interval computation for depth 15, residue 21262. -/
theorem bounds_15_21262 : exactInterval 15 21262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21262 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21262) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21262 : oddCount 21262 15 = 7 ∧ acceleratedOrbit 15 21262 = 1421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21262 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21262) = 3 ^ 7 * m + 1421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21262.1, data_15_21262.2]

/-- Complete interval computation for depth 15, residue 21263. -/
theorem bounds_15_21263 : exactInterval 15 21263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21263 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21263) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21263 : oddCount 21263 15 = 7 ∧ acceleratedOrbit 15 21263 = 1421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21263 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21263) = 3 ^ 7 * m + 1421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21263.1, data_15_21263.2]

/-- Complete interval computation for depth 15, residue 21264. -/
theorem bounds_15_21264 : exactInterval 15 21264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21264 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21264) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21264 : oddCount 21264 15 = 6 ∧ acceleratedOrbit 15 21264 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21264 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21264) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21264.1, data_15_21264.2]

/-- Complete interval computation for depth 15, residue 21265. -/
theorem bounds_15_21265 : exactInterval 15 21265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21265 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21265) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21265 : oddCount 21265 15 = 7 ∧ acceleratedOrbit 15 21265 = 1421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21265 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21265) = 3 ^ 7 * m + 1421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21265.1, data_15_21265.2]

end Collatz.Research.PassageAtlas.Batch0649
