import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0923

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 30212. -/
theorem bounds_15_30212 : exactInterval 15 30212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30212 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30212) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30212 : oddCount 30212 15 = 7 ∧ acceleratedOrbit 15 30212 = 2018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30212 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30212) = 3 ^ 7 * m + 2018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30212.1, data_15_30212.2]

/-- Complete interval computation for depth 15, residue 30213. -/
theorem bounds_15_30213 : exactInterval 15 30213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30213 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30213) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30213 : oddCount 30213 15 = 7 ∧ acceleratedOrbit 15 30213 = 2018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30213 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30213) = 3 ^ 7 * m + 2018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30213.1, data_15_30213.2]

/-- Complete interval computation for depth 15, residue 30214. -/
theorem bounds_15_30214 : exactInterval 15 30214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30214 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30214) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30214 : oddCount 30214 15 = 7 ∧ acceleratedOrbit 15 30214 = 2018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30214 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30214) = 3 ^ 7 * m + 2018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30214.1, data_15_30214.2]

/-- Complete interval computation for depth 15, residue 30215. -/
theorem bounds_15_30215 : exactInterval 15 30215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30215 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30215) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30215 : oddCount 30215 15 = 7 ∧ acceleratedOrbit 15 30215 = 2017 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30215 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30215) = 3 ^ 7 * m + 2017 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30215.1, data_15_30215.2]

/-- Complete interval computation for depth 15, residue 30216. -/
theorem bounds_15_30216 : exactInterval 15 30216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30216 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30216) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30216 : oddCount 30216 15 = 6 ∧ acceleratedOrbit 15 30216 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30216 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30216) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30216.1, data_15_30216.2]

/-- Complete interval computation for depth 15, residue 30217. -/
theorem bounds_15_30217 : exactInterval 15 30217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30217 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30217) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30217 : oddCount 30217 15 = 7 ∧ acceleratedOrbit 15 30217 = 2017 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30217 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30217) = 3 ^ 7 * m + 2017 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30217.1, data_15_30217.2]

/-- Complete interval computation for depth 15, residue 30218. -/
theorem bounds_15_30218 : exactInterval 15 30218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30218 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30218) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30218 : oddCount 30218 15 = 6 ∧ acceleratedOrbit 15 30218 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30218 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30218) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30218.1, data_15_30218.2]

/-- Complete interval computation for depth 15, residue 30219. -/
theorem bounds_15_30219 : exactInterval 15 30219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30219 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30219) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30219 : oddCount 30219 15 = 7 ∧ acceleratedOrbit 15 30219 = 2018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30219 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30219) = 3 ^ 7 * m + 2018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30219.1, data_15_30219.2]

/-- Complete interval computation for depth 15, residue 30220. -/
theorem bounds_15_30220 : exactInterval 15 30220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30220 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30220) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30220 : oddCount 30220 15 = 6 ∧ acceleratedOrbit 15 30220 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30220 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30220) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30220.1, data_15_30220.2]

/-- Complete interval computation for depth 15, residue 30221. -/
theorem bounds_15_30221 : exactInterval 15 30221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30221 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30221) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30221 : oddCount 30221 15 = 6 ∧ acceleratedOrbit 15 30221 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30221 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30221) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30221.1, data_15_30221.2]

/-- Complete interval computation for depth 15, residue 30222. -/
theorem bounds_15_30222 : exactInterval 15 30222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30222 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30222) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30222 : oddCount 30222 15 = 9 ∧ acceleratedOrbit 15 30222 = 18157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30222 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30222) = 3 ^ 9 * m + 18157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30222.1, data_15_30222.2]

/-- Complete interval computation for depth 15, residue 30223. -/
theorem bounds_15_30223 : exactInterval 15 30223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30223 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30223) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30223 : oddCount 30223 15 = 9 ∧ acceleratedOrbit 15 30223 = 18157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30223 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30223) = 3 ^ 9 * m + 18157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30223.1, data_15_30223.2]

/-- Complete interval computation for depth 15, residue 30224. -/
theorem bounds_15_30224 : exactInterval 15 30224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30224 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30224) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30224 : oddCount 30224 15 = 7 ∧ acceleratedOrbit 15 30224 = 2020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30224 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30224) = 3 ^ 7 * m + 2020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30224.1, data_15_30224.2]

/-- Complete interval computation for depth 15, residue 30225. -/
theorem bounds_15_30225 : exactInterval 15 30225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30225 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30225) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30225 : oddCount 30225 15 = 6 ∧ acceleratedOrbit 15 30225 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30225 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30225) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30225.1, data_15_30225.2]

/-- Complete interval computation for depth 15, residue 30226. -/
theorem bounds_15_30226 : exactInterval 15 30226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30226 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30226) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30226 : oddCount 30226 15 = 8 ∧ acceleratedOrbit 15 30226 = 6053 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30226 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30226) = 3 ^ 8 * m + 6053 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30226.1, data_15_30226.2]

/-- Complete interval computation for depth 15, residue 30227. -/
theorem bounds_15_30227 : exactInterval 15 30227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30227 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30227) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30227 : oddCount 30227 15 = 8 ∧ acceleratedOrbit 15 30227 = 6053 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30227 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30227) = 3 ^ 8 * m + 6053 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30227.1, data_15_30227.2]

/-- Complete interval computation for depth 15, residue 30228. -/
theorem bounds_15_30228 : exactInterval 15 30228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30228 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30228) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30228 : oddCount 30228 15 = 7 ∧ acceleratedOrbit 15 30228 = 2020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30228 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30228) = 3 ^ 7 * m + 2020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30228.1, data_15_30228.2]

/-- Complete interval computation for depth 15, residue 30229. -/
theorem bounds_15_30229 : exactInterval 15 30229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30229 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30229) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30229 : oddCount 30229 15 = 7 ∧ acceleratedOrbit 15 30229 = 2020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30229 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30229) = 3 ^ 7 * m + 2020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30229.1, data_15_30229.2]

/-- Complete interval computation for depth 15, residue 30230. -/
theorem bounds_15_30230 : exactInterval 15 30230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30230 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30230) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30230 : oddCount 30230 15 = 9 ∧ acceleratedOrbit 15 30230 = 18164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30230 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30230) = 3 ^ 9 * m + 18164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30230.1, data_15_30230.2]

/-- Complete interval computation for depth 15, residue 30231. -/
theorem bounds_15_30231 : exactInterval 15 30231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30231 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30231) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30231 : oddCount 30231 15 = 9 ∧ acceleratedOrbit 15 30231 = 18164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30231 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30231) = 3 ^ 9 * m + 18164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30231.1, data_15_30231.2]

/-- Complete interval computation for depth 15, residue 30232. -/
theorem bounds_15_30232 : exactInterval 15 30232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30232 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30232) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30232 : oddCount 30232 15 = 7 ∧ acceleratedOrbit 15 30232 = 2020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30232 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30232) = 3 ^ 7 * m + 2020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30232.1, data_15_30232.2]

/-- Complete interval computation for depth 15, residue 30233. -/
theorem bounds_15_30233 : exactInterval 15 30233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30233 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30233) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30233 : oddCount 30233 15 = 9 ∧ acceleratedOrbit 15 30233 = 18164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30233 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30233) = 3 ^ 9 * m + 18164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30233.1, data_15_30233.2]

/-- Complete interval computation for depth 15, residue 30234. -/
theorem bounds_15_30234 : exactInterval 15 30234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30234 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30234) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30234 : oddCount 30234 15 = 7 ∧ acceleratedOrbit 15 30234 = 2020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30234 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30234) = 3 ^ 7 * m + 2020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30234.1, data_15_30234.2]

/-- Complete interval computation for depth 15, residue 30235. -/
theorem bounds_15_30235 : exactInterval 15 30235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30235 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30235) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30235 : oddCount 30235 15 = 10 ∧ acceleratedOrbit 15 30235 = 54488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30235 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30235) = 3 ^ 10 * m + 54488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30235.1, data_15_30235.2]

/-- Complete interval computation for depth 15, residue 30236. -/
theorem bounds_15_30236 : exactInterval 15 30236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30236 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30236) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30236 : oddCount 30236 15 = 6 ∧ acceleratedOrbit 15 30236 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30236 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30236) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30236.1, data_15_30236.2]

/-- Complete interval computation for depth 15, residue 30237. -/
theorem bounds_15_30237 : exactInterval 15 30237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30237 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30237) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30237 : oddCount 30237 15 = 6 ∧ acceleratedOrbit 15 30237 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30237 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30237) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30237.1, data_15_30237.2]

/-- Complete interval computation for depth 15, residue 30238. -/
theorem bounds_15_30238 : exactInterval 15 30238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30238 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30238) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30238 : oddCount 30238 15 = 6 ∧ acceleratedOrbit 15 30238 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30238 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30238) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30238.1, data_15_30238.2]

/-- Complete interval computation for depth 15, residue 30239. -/
theorem bounds_15_30239 : exactInterval 15 30239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30239 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30239) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30239 : oddCount 30239 15 = 11 ∧ acceleratedOrbit 15 30239 = 163484 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30239 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30239) = 3 ^ 11 * m + 163484 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30239.1, data_15_30239.2]

/-- Complete interval computation for depth 15, residue 30240. -/
theorem bounds_15_30240 : exactInterval 15 30240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30240 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30240) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30240 : oddCount 30240 15 = 3 ∧ acceleratedOrbit 15 30240 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30240 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30240) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30240.1, data_15_30240.2]

/-- Complete interval computation for depth 15, residue 30241. -/
theorem bounds_15_30241 : exactInterval 15 30241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30241 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30241) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30241 : oddCount 30241 15 = 9 ∧ acceleratedOrbit 15 30241 = 18170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30241 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30241) = 3 ^ 9 * m + 18170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30241.1, data_15_30241.2]

/-- Complete interval computation for depth 15, residue 30242. -/
theorem bounds_15_30242 : exactInterval 15 30242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30242 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30242) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30242 : oddCount 30242 15 = 7 ∧ acceleratedOrbit 15 30242 = 2020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30242 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30242) = 3 ^ 7 * m + 2020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30242.1, data_15_30242.2]

/-- Complete interval computation for depth 15, residue 30243. -/
theorem bounds_15_30243 : exactInterval 15 30243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30243 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30243) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30243 : oddCount 30243 15 = 7 ∧ acceleratedOrbit 15 30243 = 2020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30243 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30243) = 3 ^ 7 * m + 2020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30243.1, data_15_30243.2]

end Collatz.Research.PassageAtlas.Batch0923
