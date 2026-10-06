import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0374

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 12222. -/
theorem bounds_15_12222 : exactInterval 15 12222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12222 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12222) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12222 : oddCount 12222 15 = 10 ∧ acceleratedOrbit 15 12222 = 22031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12222 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12222) = 3 ^ 10 * m + 22031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12222.1, data_15_12222.2]

/-- Complete interval computation for depth 15, residue 12223. -/
theorem bounds_15_12223 : exactInterval 15 12223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12223 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12223) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12223 : oddCount 12223 15 = 11 ∧ acceleratedOrbit 15 12223 = 66086 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12223 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12223) = 3 ^ 11 * m + 66086 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12223.1, data_15_12223.2]

/-- Complete interval computation for depth 15, residue 12224. -/
theorem bounds_15_12224 : exactInterval 15 12224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12224 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12224) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12224 : oddCount 12224 15 = 7 ∧ acceleratedOrbit 15 12224 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12224 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12224) = 3 ^ 7 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12224.1, data_15_12224.2]

/-- Complete interval computation for depth 15, residue 12225. -/
theorem bounds_15_12225 : exactInterval 15 12225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12225 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12225) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12225 : oddCount 12225 15 = 8 ∧ acceleratedOrbit 15 12225 = 2450 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12225 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12225) = 3 ^ 8 * m + 2450 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12225.1, data_15_12225.2]

/-- Complete interval computation for depth 15, residue 12226. -/
theorem bounds_15_12226 : exactInterval 15 12226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12226 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12226) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12226 : oddCount 12226 15 = 8 ∧ acceleratedOrbit 15 12226 = 2449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12226 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12226) = 3 ^ 8 * m + 2449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12226.1, data_15_12226.2]

/-- Complete interval computation for depth 15, residue 12227. -/
theorem bounds_15_12227 : exactInterval 15 12227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12227 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12227) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12227 : oddCount 12227 15 = 8 ∧ acceleratedOrbit 15 12227 = 2449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12227 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12227) = 3 ^ 8 * m + 2449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12227.1, data_15_12227.2]

/-- Complete interval computation for depth 15, residue 12228. -/
theorem bounds_15_12228 : exactInterval 15 12228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12228 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12228) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12228 : oddCount 12228 15 = 5 ∧ acceleratedOrbit 15 12228 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12228 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12228) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12228.1, data_15_12228.2]

/-- Complete interval computation for depth 15, residue 12229. -/
theorem bounds_15_12229 : exactInterval 15 12229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12229 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12229) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12229 : oddCount 12229 15 = 5 ∧ acceleratedOrbit 15 12229 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12229 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12229) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12229.1, data_15_12229.2]

/-- Complete interval computation for depth 15, residue 12230. -/
theorem bounds_15_12230 : exactInterval 15 12230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12230 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12230) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12230 : oddCount 12230 15 = 5 ∧ acceleratedOrbit 15 12230 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12230 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12230) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12230.1, data_15_12230.2]

/-- Complete interval computation for depth 15, residue 12231. -/
theorem bounds_15_12231 : exactInterval 15 12231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12231 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12231) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12231 : oddCount 12231 15 = 10 ∧ acceleratedOrbit 15 12231 = 22045 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12231 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12231) = 3 ^ 10 * m + 22045 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12231.1, data_15_12231.2]

/-- Complete interval computation for depth 15, residue 12232. -/
theorem bounds_15_12232 : exactInterval 15 12232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12232 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12232) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12232 : oddCount 12232 15 = 7 ∧ acceleratedOrbit 15 12232 = 818 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12232 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12232) = 3 ^ 7 * m + 818 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12232.1, data_15_12232.2]

/-- Complete interval computation for depth 15, residue 12233. -/
theorem bounds_15_12233 : exactInterval 15 12233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12233 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12233) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12233 : oddCount 12233 15 = 10 ∧ acceleratedOrbit 15 12233 = 22052 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12233 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12233) = 3 ^ 10 * m + 22052 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12233.1, data_15_12233.2]

/-- Complete interval computation for depth 15, residue 12234. -/
theorem bounds_15_12234 : exactInterval 15 12234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12234 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12234) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12234 : oddCount 12234 15 = 7 ∧ acceleratedOrbit 15 12234 = 818 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12234 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12234) = 3 ^ 7 * m + 818 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12234.1, data_15_12234.2]

/-- Complete interval computation for depth 15, residue 12235. -/
theorem bounds_15_12235 : exactInterval 15 12235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12235 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12235) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12235 : oddCount 12235 15 = 5 ∧ acceleratedOrbit 15 12235 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12235 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12235) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12235.1, data_15_12235.2]

/-- Complete interval computation for depth 15, residue 12236. -/
theorem bounds_15_12236 : exactInterval 15 12236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12236 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12236) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12236 : oddCount 12236 15 = 7 ∧ acceleratedOrbit 15 12236 = 818 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12236 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12236) = 3 ^ 7 * m + 818 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12236.1, data_15_12236.2]

/-- Complete interval computation for depth 15, residue 12237. -/
theorem bounds_15_12237 : exactInterval 15 12237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12237 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12237) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12237 : oddCount 12237 15 = 7 ∧ acceleratedOrbit 15 12237 = 818 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12237 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12237) = 3 ^ 7 * m + 818 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12237.1, data_15_12237.2]

/-- Complete interval computation for depth 15, residue 12238. -/
theorem bounds_15_12238 : exactInterval 15 12238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12238 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12238) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12238 : oddCount 12238 15 = 7 ∧ acceleratedOrbit 15 12238 = 817 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12238 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12238) = 3 ^ 7 * m + 817 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12238.1, data_15_12238.2]

/-- Complete interval computation for depth 15, residue 12239. -/
theorem bounds_15_12239 : exactInterval 15 12239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12239 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12239) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12239 : oddCount 12239 15 = 7 ∧ acceleratedOrbit 15 12239 = 817 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12239 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12239) = 3 ^ 7 * m + 817 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12239.1, data_15_12239.2]

/-- Complete interval computation for depth 15, residue 12240. -/
theorem bounds_15_12240 : exactInterval 15 12240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12240 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12240) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12240 : oddCount 12240 15 = 7 ∧ acceleratedOrbit 15 12240 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12240 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12240) = 3 ^ 7 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12240.1, data_15_12240.2]

/-- Complete interval computation for depth 15, residue 12241. -/
theorem bounds_15_12241 : exactInterval 15 12241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12241 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12241) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12241 : oddCount 12241 15 = 7 ∧ acceleratedOrbit 15 12241 = 818 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12241 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12241) = 3 ^ 7 * m + 818 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12241.1, data_15_12241.2]

/-- Complete interval computation for depth 15, residue 12242. -/
theorem bounds_15_12242 : exactInterval 15 12242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12242 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12242) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12242 : oddCount 12242 15 = 11 ∧ acceleratedOrbit 15 12242 = 66203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12242 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12242) = 3 ^ 11 * m + 66203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12242.1, data_15_12242.2]

/-- Complete interval computation for depth 15, residue 12243. -/
theorem bounds_15_12243 : exactInterval 15 12243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12243 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12243) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12243 : oddCount 12243 15 = 11 ∧ acceleratedOrbit 15 12243 = 66203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12243 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12243) = 3 ^ 11 * m + 66203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12243.1, data_15_12243.2]

/-- Complete interval computation for depth 15, residue 12244. -/
theorem bounds_15_12244 : exactInterval 15 12244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12244 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12244) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12244 : oddCount 12244 15 = 7 ∧ acceleratedOrbit 15 12244 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12244 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12244) = 3 ^ 7 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12244.1, data_15_12244.2]

/-- Complete interval computation for depth 15, residue 12245. -/
theorem bounds_15_12245 : exactInterval 15 12245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12245 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12245) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12245 : oddCount 12245 15 = 7 ∧ acceleratedOrbit 15 12245 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12245 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12245) = 3 ^ 7 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12245.1, data_15_12245.2]

/-- Complete interval computation for depth 15, residue 12246. -/
theorem bounds_15_12246 : exactInterval 15 12246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12246 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12246) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12246 : oddCount 12246 15 = 10 ∧ acceleratedOrbit 15 12246 = 22076 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12246 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12246) = 3 ^ 10 * m + 22076 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12246.1, data_15_12246.2]

/-- Complete interval computation for depth 15, residue 12247. -/
theorem bounds_15_12247 : exactInterval 15 12247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12247 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12247) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12247 : oddCount 12247 15 = 10 ∧ acceleratedOrbit 15 12247 = 22076 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12247 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12247) = 3 ^ 10 * m + 22076 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12247.1, data_15_12247.2]

/-- Complete interval computation for depth 15, residue 12248. -/
theorem bounds_15_12248 : exactInterval 15 12248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12248 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12248) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12248 : oddCount 12248 15 = 8 ∧ acceleratedOrbit 15 12248 = 2456 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12248 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12248) = 3 ^ 8 * m + 2456 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12248.1, data_15_12248.2]

/-- Complete interval computation for depth 15, residue 12249. -/
theorem bounds_15_12249 : exactInterval 15 12249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12249 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12249) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12249 : oddCount 12249 15 = 5 ∧ acceleratedOrbit 15 12249 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12249 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12249) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12249.1, data_15_12249.2]

/-- Complete interval computation for depth 15, residue 12250. -/
theorem bounds_15_12250 : exactInterval 15 12250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12250 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12250) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12250 : oddCount 12250 15 = 8 ∧ acceleratedOrbit 15 12250 = 2456 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12250 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12250) = 3 ^ 8 * m + 2456 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12250.1, data_15_12250.2]

/-- Complete interval computation for depth 15, residue 12251. -/
theorem bounds_15_12251 : exactInterval 15 12251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12251 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12251) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12251 : oddCount 12251 15 = 9 ∧ acceleratedOrbit 15 12251 = 7361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12251 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12251) = 3 ^ 9 * m + 7361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12251.1, data_15_12251.2]

/-- Complete interval computation for depth 15, residue 12252. -/
theorem bounds_15_12252 : exactInterval 15 12252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12252 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12252) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12252 : oddCount 12252 15 = 8 ∧ acceleratedOrbit 15 12252 = 2456 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12252 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12252) = 3 ^ 8 * m + 2456 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12252.1, data_15_12252.2]

/-- Complete interval computation for depth 15, residue 12253. -/
theorem bounds_15_12253 : exactInterval 15 12253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12253 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12253) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12253 : oddCount 12253 15 = 8 ∧ acceleratedOrbit 15 12253 = 2456 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12253 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12253) = 3 ^ 8 * m + 2456 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12253.1, data_15_12253.2]

/-- Complete interval computation for depth 15, residue 12254. -/
theorem bounds_15_12254 : exactInterval 15 12254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12254 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12254) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12254 : oddCount 12254 15 = 7 ∧ acceleratedOrbit 15 12254 = 818 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12254 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12254) = 3 ^ 7 * m + 818 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12254.1, data_15_12254.2]

end Collatz.Research.PassageAtlas.Batch0374
