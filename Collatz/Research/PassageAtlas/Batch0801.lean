import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0801

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 26214. -/
theorem bounds_15_26214 : exactInterval 15 26214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26214 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26214) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26214 : oddCount 26214 15 = 6 ∧ acceleratedOrbit 15 26214 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26214 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26214) = 3 ^ 6 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26214.1, data_15_26214.2]

/-- Complete interval computation for depth 15, residue 26215. -/
theorem bounds_15_26215 : exactInterval 15 26215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26215 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26215) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26215 : oddCount 26215 15 = 10 ∧ acceleratedOrbit 15 26215 = 47243 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26215 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26215) = 3 ^ 10 * m + 47243 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26215.1, data_15_26215.2]

/-- Complete interval computation for depth 15, residue 26216. -/
theorem bounds_15_26216 : exactInterval 15 26216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26216 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26216) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26216 : oddCount 26216 15 = 4 ∧ acceleratedOrbit 15 26216 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26216 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26216) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26216.1, data_15_26216.2]

/-- Complete interval computation for depth 15, residue 26217. -/
theorem bounds_15_26217 : exactInterval 15 26217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26217 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26217) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26217 : oddCount 26217 15 = 10 ∧ acceleratedOrbit 15 26217 = 47249 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26217 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26217) = 3 ^ 10 * m + 47249 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26217.1, data_15_26217.2]

/-- Complete interval computation for depth 15, residue 26218. -/
theorem bounds_15_26218 : exactInterval 15 26218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26218 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26218) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26218 : oddCount 26218 15 = 4 ∧ acceleratedOrbit 15 26218 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26218 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26218) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26218.1, data_15_26218.2]

/-- Complete interval computation for depth 15, residue 26219. -/
theorem bounds_15_26219 : exactInterval 15 26219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26219 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26219) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26219 : oddCount 26219 15 = 9 ∧ acceleratedOrbit 15 26219 = 15751 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26219 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26219) = 3 ^ 9 * m + 15751 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26219.1, data_15_26219.2]

/-- Complete interval computation for depth 15, residue 26220. -/
theorem bounds_15_26220 : exactInterval 15 26220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26220 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26220) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26220 : oddCount 26220 15 = 9 ∧ acceleratedOrbit 15 26220 = 15754 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26220 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26220) = 3 ^ 9 * m + 15754 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26220.1, data_15_26220.2]

/-- Complete interval computation for depth 15, residue 26221. -/
theorem bounds_15_26221 : exactInterval 15 26221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26221 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26221) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26221 : oddCount 26221 15 = 9 ∧ acceleratedOrbit 15 26221 = 15754 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26221 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26221) = 3 ^ 9 * m + 15754 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26221.1, data_15_26221.2]

/-- Complete interval computation for depth 15, residue 26222. -/
theorem bounds_15_26222 : exactInterval 15 26222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26222 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26222) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26222 : oddCount 26222 15 = 9 ∧ acceleratedOrbit 15 26222 = 15754 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26222 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26222) = 3 ^ 9 * m + 15754 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26222.1, data_15_26222.2]

/-- Complete interval computation for depth 15, residue 26223. -/
theorem bounds_15_26223 : exactInterval 15 26223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26223 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26223) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26223 : oddCount 26223 15 = 8 ∧ acceleratedOrbit 15 26223 = 5251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26223 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26223) = 3 ^ 8 * m + 5251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26223.1, data_15_26223.2]

/-- Complete interval computation for depth 15, residue 26224. -/
theorem bounds_15_26224 : exactInterval 15 26224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26224 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26224) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26224 : oddCount 26224 15 = 8 ∧ acceleratedOrbit 15 26224 = 5255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26224 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26224) = 3 ^ 8 * m + 5255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26224.1, data_15_26224.2]

/-- Complete interval computation for depth 15, residue 26225. -/
theorem bounds_15_26225 : exactInterval 15 26225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26225 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26225) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26225 : oddCount 26225 15 = 4 ∧ acceleratedOrbit 15 26225 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26225 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26225) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26225.1, data_15_26225.2]

/-- Complete interval computation for depth 15, residue 26226. -/
theorem bounds_15_26226 : exactInterval 15 26226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26226 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26226) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26226 : oddCount 26226 15 = 9 ∧ acceleratedOrbit 15 26226 = 15758 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26226 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26226) = 3 ^ 9 * m + 15758 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26226.1, data_15_26226.2]

/-- Complete interval computation for depth 15, residue 26227. -/
theorem bounds_15_26227 : exactInterval 15 26227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26227 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26227) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26227 : oddCount 26227 15 = 9 ∧ acceleratedOrbit 15 26227 = 15758 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26227 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26227) = 3 ^ 9 * m + 15758 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26227.1, data_15_26227.2]

/-- Complete interval computation for depth 15, residue 26228. -/
theorem bounds_15_26228 : exactInterval 15 26228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26228 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26228) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26228 : oddCount 26228 15 = 8 ∧ acceleratedOrbit 15 26228 = 5255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26228 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26228) = 3 ^ 8 * m + 5255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26228.1, data_15_26228.2]

/-- Complete interval computation for depth 15, residue 26229. -/
theorem bounds_15_26229 : exactInterval 15 26229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26229 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26229) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26229 : oddCount 26229 15 = 8 ∧ acceleratedOrbit 15 26229 = 5255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26229 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26229) = 3 ^ 8 * m + 5255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26229.1, data_15_26229.2]

/-- Complete interval computation for depth 15, residue 26230. -/
theorem bounds_15_26230 : exactInterval 15 26230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26230 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26230) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26230 : oddCount 26230 15 = 8 ∧ acceleratedOrbit 15 26230 = 5255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26230 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26230) = 3 ^ 8 * m + 5255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26230.1, data_15_26230.2]

/-- Complete interval computation for depth 15, residue 26231. -/
theorem bounds_15_26231 : exactInterval 15 26231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26231 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26231) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26231 : oddCount 26231 15 = 8 ∧ acceleratedOrbit 15 26231 = 5255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26231 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26231) = 3 ^ 8 * m + 5255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26231.1, data_15_26231.2]

/-- Complete interval computation for depth 15, residue 26232. -/
theorem bounds_15_26232 : exactInterval 15 26232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26232 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26232) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26232 : oddCount 26232 15 = 8 ∧ acceleratedOrbit 15 26232 = 5255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26232 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26232) = 3 ^ 8 * m + 5255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26232.1, data_15_26232.2]

/-- Complete interval computation for depth 15, residue 26233. -/
theorem bounds_15_26233 : exactInterval 15 26233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26233 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26233) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26233 : oddCount 26233 15 = 7 ∧ acceleratedOrbit 15 26233 = 1751 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26233 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26233) = 3 ^ 7 * m + 1751 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26233.1, data_15_26233.2]

/-- Complete interval computation for depth 15, residue 26234. -/
theorem bounds_15_26234 : exactInterval 15 26234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26234 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26234) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26234 : oddCount 26234 15 = 8 ∧ acceleratedOrbit 15 26234 = 5255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26234 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26234) = 3 ^ 8 * m + 5255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26234.1, data_15_26234.2]

/-- Complete interval computation for depth 15, residue 26235. -/
theorem bounds_15_26235 : exactInterval 15 26235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26235 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26235) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26235 : oddCount 26235 15 = 8 ∧ acceleratedOrbit 15 26235 = 5255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26235 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26235) = 3 ^ 8 * m + 5255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26235.1, data_15_26235.2]

/-- Complete interval computation for depth 15, residue 26236. -/
theorem bounds_15_26236 : exactInterval 15 26236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26236 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26236) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26236 : oddCount 26236 15 = 8 ∧ acceleratedOrbit 15 26236 = 5254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26236 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26236) = 3 ^ 8 * m + 5254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26236.1, data_15_26236.2]

/-- Complete interval computation for depth 15, residue 26237. -/
theorem bounds_15_26237 : exactInterval 15 26237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26237 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26237) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26237 : oddCount 26237 15 = 8 ∧ acceleratedOrbit 15 26237 = 5254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26237 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26237) = 3 ^ 8 * m + 5254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26237.1, data_15_26237.2]

/-- Complete interval computation for depth 15, residue 26238. -/
theorem bounds_15_26238 : exactInterval 15 26238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26238 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26238) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26238 : oddCount 26238 15 = 8 ∧ acceleratedOrbit 15 26238 = 5254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26238 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26238) = 3 ^ 8 * m + 5254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26238.1, data_15_26238.2]

/-- Complete interval computation for depth 15, residue 26239. -/
theorem bounds_15_26239 : exactInterval 15 26239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26239 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26239) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26239 : oddCount 26239 15 = 12 ∧ acceleratedOrbit 15 26239 = 425569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26239 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26239) = 3 ^ 12 * m + 425569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26239.1, data_15_26239.2]

/-- Complete interval computation for depth 15, residue 26240. -/
theorem bounds_15_26240 : exactInterval 15 26240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26240 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26240) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26240 : oddCount 26240 15 = 3 ∧ acceleratedOrbit 15 26240 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26240 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26240) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26240.1, data_15_26240.2]

/-- Complete interval computation for depth 15, residue 26241. -/
theorem bounds_15_26241 : exactInterval 15 26241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26241 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26241) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26241 : oddCount 26241 15 = 10 ∧ acceleratedOrbit 15 26241 = 47294 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26241 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26241) = 3 ^ 10 * m + 47294 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26241.1, data_15_26241.2]

/-- Complete interval computation for depth 15, residue 26242. -/
theorem bounds_15_26242 : exactInterval 15 26242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26242 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26242) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26242 : oddCount 26242 15 = 4 ∧ acceleratedOrbit 15 26242 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26242 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26242) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26242.1, data_15_26242.2]

/-- Complete interval computation for depth 15, residue 26243. -/
theorem bounds_15_26243 : exactInterval 15 26243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26243 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26243) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26243 : oddCount 26243 15 = 4 ∧ acceleratedOrbit 15 26243 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26243 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26243) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26243.1, data_15_26243.2]

/-- Complete interval computation for depth 15, residue 26244. -/
theorem bounds_15_26244 : exactInterval 15 26244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26244 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26244) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26244 : oddCount 26244 15 = 8 ∧ acceleratedOrbit 15 26244 = 5258 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26244 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26244) = 3 ^ 8 * m + 5258 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26244.1, data_15_26244.2]

/-- Complete interval computation for depth 15, residue 26245. -/
theorem bounds_15_26245 : exactInterval 15 26245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26245 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26245) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26245 : oddCount 26245 15 = 8 ∧ acceleratedOrbit 15 26245 = 5258 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26245 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26245) = 3 ^ 8 * m + 5258 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26245.1, data_15_26245.2]

/-- Complete interval computation for depth 15, residue 26246. -/
theorem bounds_15_26246 : exactInterval 15 26246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26246 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26246) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26246 : oddCount 26246 15 = 8 ∧ acceleratedOrbit 15 26246 = 5258 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26246 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26246) = 3 ^ 8 * m + 5258 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26246.1, data_15_26246.2]

end Collatz.Research.PassageAtlas.Batch0801
