import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0954

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 31227. -/
theorem bounds_15_31227 : exactInterval 15 31227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31227 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31227) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31227 : oddCount 31227 15 = 8 ∧ acceleratedOrbit 15 31227 = 6254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31227 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31227) = 3 ^ 8 * m + 6254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31227.1, data_15_31227.2]

/-- Complete interval computation for depth 15, residue 31228. -/
theorem bounds_15_31228 : exactInterval 15 31228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31228 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31228) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31228 : oddCount 31228 15 = 11 ∧ acceleratedOrbit 15 31228 = 168844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31228 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31228) = 3 ^ 11 * m + 168844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31228.1, data_15_31228.2]

/-- Complete interval computation for depth 15, residue 31229. -/
theorem bounds_15_31229 : exactInterval 15 31229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31229 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31229) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31229 : oddCount 31229 15 = 11 ∧ acceleratedOrbit 15 31229 = 168844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31229 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31229) = 3 ^ 11 * m + 168844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31229.1, data_15_31229.2]

/-- Complete interval computation for depth 15, residue 31230. -/
theorem bounds_15_31230 : exactInterval 15 31230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31230 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31230) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31230 : oddCount 31230 15 = 11 ∧ acceleratedOrbit 15 31230 = 168844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31230 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31230) = 3 ^ 11 * m + 168844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31230.1, data_15_31230.2]

/-- Complete interval computation for depth 15, residue 31231. -/
theorem bounds_15_31231 : exactInterval 15 31231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31231 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31231) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31231 : oddCount 31231 15 = 12 ∧ acceleratedOrbit 15 31231 = 506530 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31231 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31231) = 3 ^ 12 * m + 506530 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31231.1, data_15_31231.2]

/-- Complete interval computation for depth 15, residue 31232. -/
theorem bounds_15_31232 : exactInterval 15 31232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31232 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31232) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31232 : oddCount 31232 15 = 4 ∧ acceleratedOrbit 15 31232 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31232 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31232) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31232.1, data_15_31232.2]

/-- Complete interval computation for depth 15, residue 31233. -/
theorem bounds_15_31233 : exactInterval 15 31233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31233 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31233) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31233 : oddCount 31233 15 = 10 ∧ acceleratedOrbit 15 31233 = 56294 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31233 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31233) = 3 ^ 10 * m + 56294 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31233.1, data_15_31233.2]

/-- Complete interval computation for depth 15, residue 31234. -/
theorem bounds_15_31234 : exactInterval 15 31234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31234 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31234) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31234 : oddCount 31234 15 = 8 ∧ acceleratedOrbit 15 31234 = 6257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31234 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31234) = 3 ^ 8 * m + 6257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31234.1, data_15_31234.2]

/-- Complete interval computation for depth 15, residue 31235. -/
theorem bounds_15_31235 : exactInterval 15 31235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31235 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31235) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31235 : oddCount 31235 15 = 8 ∧ acceleratedOrbit 15 31235 = 6257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31235 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31235) = 3 ^ 8 * m + 6257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31235.1, data_15_31235.2]

/-- Complete interval computation for depth 15, residue 31236. -/
theorem bounds_15_31236 : exactInterval 15 31236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31236 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31236) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31236 : oddCount 31236 15 = 8 ∧ acceleratedOrbit 15 31236 = 6257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31236 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31236) = 3 ^ 8 * m + 6257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31236.1, data_15_31236.2]

/-- Complete interval computation for depth 15, residue 31237. -/
theorem bounds_15_31237 : exactInterval 15 31237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31237 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31237) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31237 : oddCount 31237 15 = 8 ∧ acceleratedOrbit 15 31237 = 6257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31237 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31237) = 3 ^ 8 * m + 6257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31237.1, data_15_31237.2]

/-- Complete interval computation for depth 15, residue 31238. -/
theorem bounds_15_31238 : exactInterval 15 31238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31238 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31238) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31238 : oddCount 31238 15 = 8 ∧ acceleratedOrbit 15 31238 = 6257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31238 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31238) = 3 ^ 8 * m + 6257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31238.1, data_15_31238.2]

/-- Complete interval computation for depth 15, residue 31239. -/
theorem bounds_15_31239 : exactInterval 15 31239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31239 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31239) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31239 : oddCount 31239 15 = 9 ∧ acceleratedOrbit 15 31239 = 18767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31239 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31239) = 3 ^ 9 * m + 18767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31239.1, data_15_31239.2]

/-- Complete interval computation for depth 15, residue 31240. -/
theorem bounds_15_31240 : exactInterval 15 31240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31240 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31240) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31240 : oddCount 31240 15 = 5 ∧ acceleratedOrbit 15 31240 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31240 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31240) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31240.1, data_15_31240.2]

/-- Complete interval computation for depth 15, residue 31241. -/
theorem bounds_15_31241 : exactInterval 15 31241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31241 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31241) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31241 : oddCount 31241 15 = 8 ∧ acceleratedOrbit 15 31241 = 6257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31241 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31241) = 3 ^ 8 * m + 6257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31241.1, data_15_31241.2]

/-- Complete interval computation for depth 15, residue 31242. -/
theorem bounds_15_31242 : exactInterval 15 31242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31242 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31242) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31242 : oddCount 31242 15 = 5 ∧ acceleratedOrbit 15 31242 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31242 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31242) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31242.1, data_15_31242.2]

/-- Complete interval computation for depth 15, residue 31243. -/
theorem bounds_15_31243 : exactInterval 15 31243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31243 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31243) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31243 : oddCount 31243 15 = 8 ∧ acceleratedOrbit 15 31243 = 6257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31243 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31243) = 3 ^ 8 * m + 6257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31243.1, data_15_31243.2]

/-- Complete interval computation for depth 15, residue 31244. -/
theorem bounds_15_31244 : exactInterval 15 31244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31244 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31244) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31244 : oddCount 31244 15 = 5 ∧ acceleratedOrbit 15 31244 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31244 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31244) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31244.1, data_15_31244.2]

/-- Complete interval computation for depth 15, residue 31245. -/
theorem bounds_15_31245 : exactInterval 15 31245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31245 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31245) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31245 : oddCount 31245 15 = 5 ∧ acceleratedOrbit 15 31245 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31245 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31245) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31245.1, data_15_31245.2]

/-- Complete interval computation for depth 15, residue 31246. -/
theorem bounds_15_31246 : exactInterval 15 31246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31246 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31246) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31246 : oddCount 31246 15 = 10 ∧ acceleratedOrbit 15 31246 = 56315 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31246 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31246) = 3 ^ 10 * m + 56315 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31246.1, data_15_31246.2]

/-- Complete interval computation for depth 15, residue 31247. -/
theorem bounds_15_31247 : exactInterval 15 31247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31247 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31247) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31247 : oddCount 31247 15 = 10 ∧ acceleratedOrbit 15 31247 = 56315 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31247 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31247) = 3 ^ 10 * m + 56315 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31247.1, data_15_31247.2]

/-- Complete interval computation for depth 15, residue 31248. -/
theorem bounds_15_31248 : exactInterval 15 31248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31248 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31248) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31248 : oddCount 31248 15 = 5 ∧ acceleratedOrbit 15 31248 = 232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31248 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31248) = 3 ^ 5 * m + 232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31248.1, data_15_31248.2]

/-- Complete interval computation for depth 15, residue 31249. -/
theorem bounds_15_31249 : exactInterval 15 31249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31249 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31249) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31249 : oddCount 31249 15 = 5 ∧ acceleratedOrbit 15 31249 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31249 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31249) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31249.1, data_15_31249.2]

/-- Complete interval computation for depth 15, residue 31250. -/
theorem bounds_15_31250 : exactInterval 15 31250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31250 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31250) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31250 : oddCount 31250 15 = 7 ∧ acceleratedOrbit 15 31250 = 2086 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31250 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31250) = 3 ^ 7 * m + 2086 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31250.1, data_15_31250.2]

/-- Complete interval computation for depth 15, residue 31251. -/
theorem bounds_15_31251 : exactInterval 15 31251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31251 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31251) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31251 : oddCount 31251 15 = 7 ∧ acceleratedOrbit 15 31251 = 2086 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31251 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31251) = 3 ^ 7 * m + 2086 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31251.1, data_15_31251.2]

/-- Complete interval computation for depth 15, residue 31252. -/
theorem bounds_15_31252 : exactInterval 15 31252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31252 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31252) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31252 : oddCount 31252 15 = 5 ∧ acceleratedOrbit 15 31252 = 232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31252 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31252) = 3 ^ 5 * m + 232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31252.1, data_15_31252.2]

/-- Complete interval computation for depth 15, residue 31253. -/
theorem bounds_15_31253 : exactInterval 15 31253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31253 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31253) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31253 : oddCount 31253 15 = 5 ∧ acceleratedOrbit 15 31253 = 232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31253 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31253) = 3 ^ 5 * m + 232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31253.1, data_15_31253.2]

/-- Complete interval computation for depth 15, residue 31254. -/
theorem bounds_15_31254 : exactInterval 15 31254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31254 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31254) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31254 : oddCount 31254 15 = 7 ∧ acceleratedOrbit 15 31254 = 2087 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31254 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31254) = 3 ^ 7 * m + 2087 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31254.1, data_15_31254.2]

/-- Complete interval computation for depth 15, residue 31255. -/
theorem bounds_15_31255 : exactInterval 15 31255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31255 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31255) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31255 : oddCount 31255 15 = 7 ∧ acceleratedOrbit 15 31255 = 2087 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31255 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31255) = 3 ^ 7 * m + 2087 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31255.1, data_15_31255.2]

/-- Complete interval computation for depth 15, residue 31256. -/
theorem bounds_15_31256 : exactInterval 15 31256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31256 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31256) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31256 : oddCount 31256 15 = 5 ∧ acceleratedOrbit 15 31256 = 232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31256 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31256) = 3 ^ 5 * m + 232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31256.1, data_15_31256.2]

/-- Complete interval computation for depth 15, residue 31257. -/
theorem bounds_15_31257 : exactInterval 15 31257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31257 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31257) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31257 : oddCount 31257 15 = 7 ∧ acceleratedOrbit 15 31257 = 2087 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31257 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31257) = 3 ^ 7 * m + 2087 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31257.1, data_15_31257.2]

/-- Complete interval computation for depth 15, residue 31258. -/
theorem bounds_15_31258 : exactInterval 15 31258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31258 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31258) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31258 : oddCount 31258 15 = 5 ∧ acceleratedOrbit 15 31258 = 232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31258 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31258) = 3 ^ 5 * m + 232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31258.1, data_15_31258.2]

/-- Complete interval computation for depth 15, residue 31259. -/
theorem bounds_15_31259 : exactInterval 15 31259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31259 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31259) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31259 : oddCount 31259 15 = 9 ∧ acceleratedOrbit 15 31259 = 18778 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31259 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31259) = 3 ^ 9 * m + 18778 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31259.1, data_15_31259.2]

end Collatz.Research.PassageAtlas.Batch0954
