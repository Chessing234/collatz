import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0740

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 24215. -/
theorem bounds_15_24215 : exactInterval 15 24215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24215 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24215) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24215 : oddCount 24215 15 = 7 ∧ acceleratedOrbit 15 24215 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24215 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24215) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24215.1, data_15_24215.2]

/-- Complete interval computation for depth 15, residue 24216. -/
theorem bounds_15_24216 : exactInterval 15 24216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24216 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24216) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24216 : oddCount 24216 15 = 8 ∧ acceleratedOrbit 15 24216 = 4853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24216 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24216) = 3 ^ 8 * m + 4853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24216.1, data_15_24216.2]

/-- Complete interval computation for depth 15, residue 24217. -/
theorem bounds_15_24217 : exactInterval 15 24217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24217 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24217) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24217 : oddCount 24217 15 = 10 ∧ acceleratedOrbit 15 24217 = 43649 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24217 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24217) = 3 ^ 10 * m + 43649 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24217.1, data_15_24217.2]

/-- Complete interval computation for depth 15, residue 24218. -/
theorem bounds_15_24218 : exactInterval 15 24218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24218 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24218) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24218 : oddCount 24218 15 = 8 ∧ acceleratedOrbit 15 24218 = 4853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24218 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24218) = 3 ^ 8 * m + 4853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24218.1, data_15_24218.2]

/-- Complete interval computation for depth 15, residue 24219. -/
theorem bounds_15_24219 : exactInterval 15 24219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24219 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24219) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24219 : oddCount 24219 15 = 11 ∧ acceleratedOrbit 15 24219 = 130940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24219 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24219) = 3 ^ 11 * m + 130940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24219.1, data_15_24219.2]

/-- Complete interval computation for depth 15, residue 24220. -/
theorem bounds_15_24220 : exactInterval 15 24220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24220 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24220) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24220 : oddCount 24220 15 = 10 ∧ acceleratedOrbit 15 24220 = 43658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24220 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24220) = 3 ^ 10 * m + 43658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24220.1, data_15_24220.2]

/-- Complete interval computation for depth 15, residue 24221. -/
theorem bounds_15_24221 : exactInterval 15 24221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24221 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24221) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24221 : oddCount 24221 15 = 10 ∧ acceleratedOrbit 15 24221 = 43658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24221 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24221) = 3 ^ 10 * m + 43658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24221.1, data_15_24221.2]

/-- Complete interval computation for depth 15, residue 24222. -/
theorem bounds_15_24222 : exactInterval 15 24222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24222 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24222) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24222 : oddCount 24222 15 = 10 ∧ acceleratedOrbit 15 24222 = 43658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24222 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24222) = 3 ^ 10 * m + 43658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24222.1, data_15_24222.2]

/-- Complete interval computation for depth 15, residue 24223. -/
theorem bounds_15_24223 : exactInterval 15 24223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24223 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24223) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24223 : oddCount 24223 15 = 12 ∧ acceleratedOrbit 15 24223 = 392876 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24223 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24223) = 3 ^ 12 * m + 392876 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24223.1, data_15_24223.2]

/-- Complete interval computation for depth 15, residue 24224. -/
theorem bounds_15_24224 : exactInterval 15 24224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24224 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24224) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24224 : oddCount 24224 15 = 5 ∧ acceleratedOrbit 15 24224 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24224 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24224) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24224.1, data_15_24224.2]

/-- Complete interval computation for depth 15, residue 24225. -/
theorem bounds_15_24225 : exactInterval 15 24225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24225 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24225) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24225 : oddCount 24225 15 = 6 ∧ acceleratedOrbit 15 24225 = 539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24225 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24225) = 3 ^ 6 * m + 539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24225.1, data_15_24225.2]

/-- Complete interval computation for depth 15, residue 24226. -/
theorem bounds_15_24226 : exactInterval 15 24226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24226 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24226) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24226 : oddCount 24226 15 = 8 ∧ acceleratedOrbit 15 24226 = 4853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24226 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24226) = 3 ^ 8 * m + 4853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24226.1, data_15_24226.2]

/-- Complete interval computation for depth 15, residue 24227. -/
theorem bounds_15_24227 : exactInterval 15 24227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24227 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24227) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24227 : oddCount 24227 15 = 8 ∧ acceleratedOrbit 15 24227 = 4853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24227 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24227) = 3 ^ 8 * m + 4853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24227.1, data_15_24227.2]

/-- Complete interval computation for depth 15, residue 24228. -/
theorem bounds_15_24228 : exactInterval 15 24228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24228 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24228) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24228 : oddCount 24228 15 = 10 ∧ acceleratedOrbit 15 24228 = 43672 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24228 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24228) = 3 ^ 10 * m + 43672 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24228.1, data_15_24228.2]

/-- Complete interval computation for depth 15, residue 24229. -/
theorem bounds_15_24229 : exactInterval 15 24229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24229 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24229) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24229 : oddCount 24229 15 = 10 ∧ acceleratedOrbit 15 24229 = 43672 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24229 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24229) = 3 ^ 10 * m + 43672 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24229.1, data_15_24229.2]

/-- Complete interval computation for depth 15, residue 24230. -/
theorem bounds_15_24230 : exactInterval 15 24230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24230 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24230) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24230 : oddCount 24230 15 = 10 ∧ acceleratedOrbit 15 24230 = 43672 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24230 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24230) = 3 ^ 10 * m + 43672 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24230.1, data_15_24230.2]

/-- Complete interval computation for depth 15, residue 24231. -/
theorem bounds_15_24231 : exactInterval 15 24231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24231 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24231) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24231 : oddCount 24231 15 = 8 ∧ acceleratedOrbit 15 24231 = 4852 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24231 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24231) = 3 ^ 8 * m + 4852 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24231.1, data_15_24231.2]

/-- Complete interval computation for depth 15, residue 24232. -/
theorem bounds_15_24232 : exactInterval 15 24232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24232 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24232) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24232 : oddCount 24232 15 = 5 ∧ acceleratedOrbit 15 24232 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24232 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24232) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24232.1, data_15_24232.2]

/-- Complete interval computation for depth 15, residue 24233. -/
theorem bounds_15_24233 : exactInterval 15 24233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24233 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24233) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24233 : oddCount 24233 15 = 11 ∧ acceleratedOrbit 15 24233 = 131015 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24233 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24233) = 3 ^ 11 * m + 131015 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24233.1, data_15_24233.2]

/-- Complete interval computation for depth 15, residue 24234. -/
theorem bounds_15_24234 : exactInterval 15 24234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24234 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24234) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24234 : oddCount 24234 15 = 5 ∧ acceleratedOrbit 15 24234 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24234 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24234) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24234.1, data_15_24234.2]

/-- Complete interval computation for depth 15, residue 24235. -/
theorem bounds_15_24235 : exactInterval 15 24235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24235 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24235) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24235 : oddCount 24235 15 = 10 ∧ acceleratedOrbit 15 24235 = 43679 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24235 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24235) = 3 ^ 10 * m + 43679 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24235.1, data_15_24235.2]

/-- Complete interval computation for depth 15, residue 24236. -/
theorem bounds_15_24236 : exactInterval 15 24236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24236 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24236) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24236 : oddCount 24236 15 = 8 ∧ acceleratedOrbit 15 24236 = 4855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24236 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24236) = 3 ^ 8 * m + 4855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24236.1, data_15_24236.2]

/-- Complete interval computation for depth 15, residue 24237. -/
theorem bounds_15_24237 : exactInterval 15 24237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24237 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24237) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24237 : oddCount 24237 15 = 8 ∧ acceleratedOrbit 15 24237 = 4855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24237 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24237) = 3 ^ 8 * m + 4855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24237.1, data_15_24237.2]

/-- Complete interval computation for depth 15, residue 24238. -/
theorem bounds_15_24238 : exactInterval 15 24238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24238 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24238) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24238 : oddCount 24238 15 = 8 ∧ acceleratedOrbit 15 24238 = 4855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24238 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24238) = 3 ^ 8 * m + 4855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24238.1, data_15_24238.2]

/-- Complete interval computation for depth 15, residue 24239. -/
theorem bounds_15_24239 : exactInterval 15 24239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24239 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24239) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24239 : oddCount 24239 15 = 10 ∧ acceleratedOrbit 15 24239 = 43685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24239 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24239) = 3 ^ 10 * m + 43685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24239.1, data_15_24239.2]

/-- Complete interval computation for depth 15, residue 24240. -/
theorem bounds_15_24240 : exactInterval 15 24240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24240 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24240) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24240 : oddCount 24240 15 = 9 ∧ acceleratedOrbit 15 24240 = 14579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24240 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24240) = 3 ^ 9 * m + 14579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24240.1, data_15_24240.2]

/-- Complete interval computation for depth 15, residue 24241. -/
theorem bounds_15_24241 : exactInterval 15 24241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24241 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24241) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24241 : oddCount 24241 15 = 8 ∧ acceleratedOrbit 15 24241 = 4859 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24241 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24241) = 3 ^ 8 * m + 4859 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24241.1, data_15_24241.2]

/-- Complete interval computation for depth 15, residue 24242. -/
theorem bounds_15_24242 : exactInterval 15 24242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24242 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24242) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24242 : oddCount 24242 15 = 8 ∧ acceleratedOrbit 15 24242 = 4859 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24242 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24242) = 3 ^ 8 * m + 4859 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24242.1, data_15_24242.2]

/-- Complete interval computation for depth 15, residue 24243. -/
theorem bounds_15_24243 : exactInterval 15 24243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24243 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24243) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24243 : oddCount 24243 15 = 8 ∧ acceleratedOrbit 15 24243 = 4859 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24243 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24243) = 3 ^ 8 * m + 4859 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24243.1, data_15_24243.2]

/-- Complete interval computation for depth 15, residue 24244. -/
theorem bounds_15_24244 : exactInterval 15 24244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24244 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24244) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24244 : oddCount 24244 15 = 9 ∧ acceleratedOrbit 15 24244 = 14579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24244 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24244) = 3 ^ 9 * m + 14579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24244.1, data_15_24244.2]

/-- Complete interval computation for depth 15, residue 24245. -/
theorem bounds_15_24245 : exactInterval 15 24245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24245 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24245) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24245 : oddCount 24245 15 = 9 ∧ acceleratedOrbit 15 24245 = 14579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24245 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24245) = 3 ^ 9 * m + 14579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24245.1, data_15_24245.2]

/-- Complete interval computation for depth 15, residue 24246. -/
theorem bounds_15_24246 : exactInterval 15 24246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24246 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24246) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24246 : oddCount 24246 15 = 10 ∧ acceleratedOrbit 15 24246 = 43699 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24246 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24246) = 3 ^ 10 * m + 43699 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24246.1, data_15_24246.2]

/-- Complete interval computation for depth 15, residue 24247. -/
theorem bounds_15_24247 : exactInterval 15 24247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24247 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24247) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24247 : oddCount 24247 15 = 10 ∧ acceleratedOrbit 15 24247 = 43699 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24247 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24247) = 3 ^ 10 * m + 43699 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24247.1, data_15_24247.2]

end Collatz.Research.PassageAtlas.Batch0740
