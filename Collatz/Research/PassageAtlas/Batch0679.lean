import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0679

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 22216. -/
theorem bounds_15_22216 : exactInterval 15 22216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22216 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22216) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22216 : oddCount 22216 15 = 4 ∧ acceleratedOrbit 15 22216 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22216 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22216) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22216.1, data_15_22216.2]

/-- Complete interval computation for depth 15, residue 22217. -/
theorem bounds_15_22217 : exactInterval 15 22217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22217 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22217) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22217 : oddCount 22217 15 = 8 ∧ acceleratedOrbit 15 22217 = 4450 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22217 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22217) = 3 ^ 8 * m + 4450 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22217.1, data_15_22217.2]

/-- Complete interval computation for depth 15, residue 22218. -/
theorem bounds_15_22218 : exactInterval 15 22218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22218 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22218) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22218 : oddCount 22218 15 = 4 ∧ acceleratedOrbit 15 22218 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22218 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22218) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22218.1, data_15_22218.2]

/-- Complete interval computation for depth 15, residue 22219. -/
theorem bounds_15_22219 : exactInterval 15 22219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22219 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22219) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22219 : oddCount 22219 15 = 8 ∧ acceleratedOrbit 15 22219 = 4450 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22219 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22219) = 3 ^ 8 * m + 4450 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22219.1, data_15_22219.2]

/-- Complete interval computation for depth 15, residue 22220. -/
theorem bounds_15_22220 : exactInterval 15 22220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22220 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22220) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22220 : oddCount 22220 15 = 4 ∧ acceleratedOrbit 15 22220 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22220 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22220) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22220.1, data_15_22220.2]

/-- Complete interval computation for depth 15, residue 22221. -/
theorem bounds_15_22221 : exactInterval 15 22221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22221 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22221) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22221 : oddCount 22221 15 = 4 ∧ acceleratedOrbit 15 22221 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22221 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22221) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22221.1, data_15_22221.2]

/-- Complete interval computation for depth 15, residue 22222. -/
theorem bounds_15_22222 : exactInterval 15 22222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22222 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22222) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22222 : oddCount 22222 15 = 11 ∧ acceleratedOrbit 15 22222 = 120149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22222 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22222) = 3 ^ 11 * m + 120149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22222.1, data_15_22222.2]

/-- Complete interval computation for depth 15, residue 22223. -/
theorem bounds_15_22223 : exactInterval 15 22223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22223 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22223) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22223 : oddCount 22223 15 = 11 ∧ acceleratedOrbit 15 22223 = 120149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22223 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22223) = 3 ^ 11 * m + 120149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22223.1, data_15_22223.2]

/-- Complete interval computation for depth 15, residue 22224. -/
theorem bounds_15_22224 : exactInterval 15 22224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22224 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22224) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22224 : oddCount 22224 15 = 6 ∧ acceleratedOrbit 15 22224 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22224 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22224) = 3 ^ 6 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22224.1, data_15_22224.2]

/-- Complete interval computation for depth 15, residue 22225. -/
theorem bounds_15_22225 : exactInterval 15 22225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22225 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22225) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22225 : oddCount 22225 15 = 9 ∧ acceleratedOrbit 15 22225 = 13355 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22225 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22225) = 3 ^ 9 * m + 13355 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22225.1, data_15_22225.2]

/-- Complete interval computation for depth 15, residue 22226. -/
theorem bounds_15_22226 : exactInterval 15 22226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22226 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22226) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22226 : oddCount 22226 15 = 9 ∧ acceleratedOrbit 15 22226 = 13355 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22226 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22226) = 3 ^ 9 * m + 13355 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22226.1, data_15_22226.2]

/-- Complete interval computation for depth 15, residue 22227. -/
theorem bounds_15_22227 : exactInterval 15 22227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22227 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22227) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22227 : oddCount 22227 15 = 9 ∧ acceleratedOrbit 15 22227 = 13355 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22227 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22227) = 3 ^ 9 * m + 13355 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22227.1, data_15_22227.2]

/-- Complete interval computation for depth 15, residue 22228. -/
theorem bounds_15_22228 : exactInterval 15 22228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22228 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22228) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22228 : oddCount 22228 15 = 6 ∧ acceleratedOrbit 15 22228 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22228 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22228) = 3 ^ 6 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22228.1, data_15_22228.2]

/-- Complete interval computation for depth 15, residue 22229. -/
theorem bounds_15_22229 : exactInterval 15 22229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22229 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22229) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22229 : oddCount 22229 15 = 6 ∧ acceleratedOrbit 15 22229 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22229 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22229) = 3 ^ 6 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22229.1, data_15_22229.2]

/-- Complete interval computation for depth 15, residue 22230. -/
theorem bounds_15_22230 : exactInterval 15 22230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22230 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22230) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22230 : oddCount 22230 15 = 8 ∧ acceleratedOrbit 15 22230 = 4454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22230 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22230) = 3 ^ 8 * m + 4454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22230.1, data_15_22230.2]

/-- Complete interval computation for depth 15, residue 22231. -/
theorem bounds_15_22231 : exactInterval 15 22231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22231 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22231) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22231 : oddCount 22231 15 = 8 ∧ acceleratedOrbit 15 22231 = 4454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22231 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22231) = 3 ^ 8 * m + 4454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22231.1, data_15_22231.2]

/-- Complete interval computation for depth 15, residue 22232. -/
theorem bounds_15_22232 : exactInterval 15 22232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22232 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22232) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22232 : oddCount 22232 15 = 9 ∧ acceleratedOrbit 15 22232 = 13364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22232 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22232) = 3 ^ 9 * m + 13364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22232.1, data_15_22232.2]

/-- Complete interval computation for depth 15, residue 22233. -/
theorem bounds_15_22233 : exactInterval 15 22233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22233 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22233) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22233 : oddCount 22233 15 = 9 ∧ acceleratedOrbit 15 22233 = 13364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22233 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22233) = 3 ^ 9 * m + 13364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22233.1, data_15_22233.2]

/-- Complete interval computation for depth 15, residue 22234. -/
theorem bounds_15_22234 : exactInterval 15 22234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22234 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22234) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22234 : oddCount 22234 15 = 9 ∧ acceleratedOrbit 15 22234 = 13364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22234 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22234) = 3 ^ 9 * m + 13364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22234.1, data_15_22234.2]

/-- Complete interval computation for depth 15, residue 22235. -/
theorem bounds_15_22235 : exactInterval 15 22235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22235 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22235) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22235 : oddCount 22235 15 = 9 ∧ acceleratedOrbit 15 22235 = 13358 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22235 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22235) = 3 ^ 9 * m + 13358 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22235.1, data_15_22235.2]

/-- Complete interval computation for depth 15, residue 22236. -/
theorem bounds_15_22236 : exactInterval 15 22236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22236 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22236) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22236 : oddCount 22236 15 = 9 ∧ acceleratedOrbit 15 22236 = 13364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22236 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22236) = 3 ^ 9 * m + 13364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22236.1, data_15_22236.2]

/-- Complete interval computation for depth 15, residue 22237. -/
theorem bounds_15_22237 : exactInterval 15 22237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22237 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22237) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22237 : oddCount 22237 15 = 9 ∧ acceleratedOrbit 15 22237 = 13364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22237 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22237) = 3 ^ 9 * m + 13364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22237.1, data_15_22237.2]

/-- Complete interval computation for depth 15, residue 22238. -/
theorem bounds_15_22238 : exactInterval 15 22238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22238 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22238) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22238 : oddCount 22238 15 = 9 ∧ acceleratedOrbit 15 22238 = 13360 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22238 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22238) = 3 ^ 9 * m + 13360 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22238.1, data_15_22238.2]

/-- Complete interval computation for depth 15, residue 22239. -/
theorem bounds_15_22239 : exactInterval 15 22239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22239 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22239) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22239 : oddCount 22239 15 = 9 ∧ acceleratedOrbit 15 22239 = 13360 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22239 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22239) = 3 ^ 9 * m + 13360 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22239.1, data_15_22239.2]

/-- Complete interval computation for depth 15, residue 22240. -/
theorem bounds_15_22240 : exactInterval 15 22240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22240 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22240) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22240 : oddCount 22240 15 = 6 ∧ acceleratedOrbit 15 22240 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22240 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22240) = 3 ^ 6 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22240.1, data_15_22240.2]

/-- Complete interval computation for depth 15, residue 22241. -/
theorem bounds_15_22241 : exactInterval 15 22241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22241 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22241) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22241 : oddCount 22241 15 = 10 ∧ acceleratedOrbit 15 22241 = 40085 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22241 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22241) = 3 ^ 10 * m + 40085 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22241.1, data_15_22241.2]

/-- Complete interval computation for depth 15, residue 22242. -/
theorem bounds_15_22242 : exactInterval 15 22242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22242 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22242) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22242 : oddCount 22242 15 = 6 ∧ acceleratedOrbit 15 22242 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22242 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22242) = 3 ^ 6 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22242.1, data_15_22242.2]

/-- Complete interval computation for depth 15, residue 22243. -/
theorem bounds_15_22243 : exactInterval 15 22243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22243 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22243) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22243 : oddCount 22243 15 = 6 ∧ acceleratedOrbit 15 22243 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22243 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22243) = 3 ^ 6 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22243.1, data_15_22243.2]

/-- Complete interval computation for depth 15, residue 22244. -/
theorem bounds_15_22244 : exactInterval 15 22244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22244 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22244) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22244 : oddCount 22244 15 = 4 ∧ acceleratedOrbit 15 22244 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22244 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22244) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22244.1, data_15_22244.2]

/-- Complete interval computation for depth 15, residue 22245. -/
theorem bounds_15_22245 : exactInterval 15 22245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22245 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22245) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22245 : oddCount 22245 15 = 4 ∧ acceleratedOrbit 15 22245 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22245 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22245) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22245.1, data_15_22245.2]

/-- Complete interval computation for depth 15, residue 22246. -/
theorem bounds_15_22246 : exactInterval 15 22246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22246 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22246) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22246 : oddCount 22246 15 = 4 ∧ acceleratedOrbit 15 22246 = 55 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22246 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22246) = 3 ^ 4 * m + 55 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22246.1, data_15_22246.2]

/-- Complete interval computation for depth 15, residue 22247. -/
theorem bounds_15_22247 : exactInterval 15 22247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22247 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22247) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22247 : oddCount 22247 15 = 11 ∧ acceleratedOrbit 15 22247 = 120278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22247 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22247) = 3 ^ 11 * m + 120278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22247.1, data_15_22247.2]

/-- Complete interval computation for depth 15, residue 22248. -/
theorem bounds_15_22248 : exactInterval 15 22248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22248 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22248) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22248 : oddCount 22248 15 = 6 ∧ acceleratedOrbit 15 22248 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22248 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22248) = 3 ^ 6 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22248.1, data_15_22248.2]

end Collatz.Research.PassageAtlas.Batch0679
