import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0099

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 3211. -/
theorem bounds_15_3211 : exactInterval 15 3211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3211 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3211) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3211 : oddCount 3211 15 = 7 ∧ acceleratedOrbit 15 3211 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3211 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3211) = 3 ^ 7 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3211.1, data_15_3211.2]

/-- Complete interval computation for depth 15, residue 3212. -/
theorem bounds_15_3212 : exactInterval 15 3212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3212 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3212) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3212 : oddCount 3212 15 = 4 ∧ acceleratedOrbit 15 3212 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3212 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3212) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3212.1, data_15_3212.2]

/-- Complete interval computation for depth 15, residue 3213. -/
theorem bounds_15_3213 : exactInterval 15 3213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3213 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3213) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3213 : oddCount 3213 15 = 4 ∧ acceleratedOrbit 15 3213 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3213 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3213) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3213.1, data_15_3213.2]

/-- Complete interval computation for depth 15, residue 3214. -/
theorem bounds_15_3214 : exactInterval 15 3214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3214 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3214) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3214 : oddCount 3214 15 = 9 ∧ acceleratedOrbit 15 3214 = 1934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3214 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3214) = 3 ^ 9 * m + 1934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3214.1, data_15_3214.2]

/-- Complete interval computation for depth 15, residue 3215. -/
theorem bounds_15_3215 : exactInterval 15 3215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3215 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3215) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3215 : oddCount 3215 15 = 9 ∧ acceleratedOrbit 15 3215 = 1934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3215 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3215) = 3 ^ 9 * m + 1934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3215.1, data_15_3215.2]

/-- Complete interval computation for depth 15, residue 3216. -/
theorem bounds_15_3216 : exactInterval 15 3216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3216 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3216) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3216 : oddCount 3216 15 = 4 ∧ acceleratedOrbit 15 3216 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3216 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3216) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3216.1, data_15_3216.2]

/-- Complete interval computation for depth 15, residue 3217. -/
theorem bounds_15_3217 : exactInterval 15 3217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3217 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3217) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3217 : oddCount 3217 15 = 9 ∧ acceleratedOrbit 15 3217 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3217 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3217) = 3 ^ 9 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3217.1, data_15_3217.2]

/-- Complete interval computation for depth 15, residue 3218. -/
theorem bounds_15_3218 : exactInterval 15 3218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3218 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3218) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3218 : oddCount 3218 15 = 9 ∧ acceleratedOrbit 15 3218 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3218 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3218) = 3 ^ 9 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3218.1, data_15_3218.2]

/-- Complete interval computation for depth 15, residue 3219. -/
theorem bounds_15_3219 : exactInterval 15 3219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3219 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3219) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3219 : oddCount 3219 15 = 9 ∧ acceleratedOrbit 15 3219 = 1937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3219 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3219) = 3 ^ 9 * m + 1937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3219.1, data_15_3219.2]

/-- Complete interval computation for depth 15, residue 3220. -/
theorem bounds_15_3220 : exactInterval 15 3220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3220 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3220) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3220 : oddCount 3220 15 = 4 ∧ acceleratedOrbit 15 3220 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3220 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3220) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3220.1, data_15_3220.2]

/-- Complete interval computation for depth 15, residue 3221. -/
theorem bounds_15_3221 : exactInterval 15 3221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3221 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3221) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3221 : oddCount 3221 15 = 4 ∧ acceleratedOrbit 15 3221 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3221 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3221) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3221.1, data_15_3221.2]

/-- Complete interval computation for depth 15, residue 3222. -/
theorem bounds_15_3222 : exactInterval 15 3222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3222 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3222) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3222 : oddCount 3222 15 = 4 ∧ acceleratedOrbit 15 3222 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3222 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3222) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3222.1, data_15_3222.2]

/-- Complete interval computation for depth 15, residue 3223. -/
theorem bounds_15_3223 : exactInterval 15 3223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3223 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3223) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3223 : oddCount 3223 15 = 4 ∧ acceleratedOrbit 15 3223 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3223 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3223) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3223.1, data_15_3223.2]

/-- Complete interval computation for depth 15, residue 3224. -/
theorem bounds_15_3224 : exactInterval 15 3224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3224 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3224) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3224 : oddCount 3224 15 = 4 ∧ acceleratedOrbit 15 3224 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3224 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3224) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3224.1, data_15_3224.2]

/-- Complete interval computation for depth 15, residue 3225. -/
theorem bounds_15_3225 : exactInterval 15 3225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3225 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3225) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3225 : oddCount 3225 15 = 9 ∧ acceleratedOrbit 15 3225 = 1943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3225 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3225) = 3 ^ 9 * m + 1943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3225.1, data_15_3225.2]

/-- Complete interval computation for depth 15, residue 3226. -/
theorem bounds_15_3226 : exactInterval 15 3226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3226 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3226) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3226 : oddCount 3226 15 = 4 ∧ acceleratedOrbit 15 3226 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3226 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3226) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3226.1, data_15_3226.2]

/-- Complete interval computation for depth 15, residue 3227. -/
theorem bounds_15_3227 : exactInterval 15 3227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3227 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3227) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3227 : oddCount 3227 15 = 11 ∧ acceleratedOrbit 15 3227 = 17455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3227 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3227) = 3 ^ 11 * m + 17455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3227.1, data_15_3227.2]

/-- Complete interval computation for depth 15, residue 3228. -/
theorem bounds_15_3228 : exactInterval 15 3228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3228 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3228) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3228 : oddCount 3228 15 = 10 ∧ acceleratedOrbit 15 3228 = 5831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3228 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3228) = 3 ^ 10 * m + 5831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3228.1, data_15_3228.2]

/-- Complete interval computation for depth 15, residue 3229. -/
theorem bounds_15_3229 : exactInterval 15 3229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3229 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3229) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3229 : oddCount 3229 15 = 10 ∧ acceleratedOrbit 15 3229 = 5831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3229 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3229) = 3 ^ 10 * m + 5831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3229.1, data_15_3229.2]

/-- Complete interval computation for depth 15, residue 3230. -/
theorem bounds_15_3230 : exactInterval 15 3230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3230 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3230) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3230 : oddCount 3230 15 = 10 ∧ acceleratedOrbit 15 3230 = 5831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3230 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3230) = 3 ^ 10 * m + 5831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3230.1, data_15_3230.2]

/-- Complete interval computation for depth 15, residue 3231. -/
theorem bounds_15_3231 : exactInterval 15 3231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3231 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3231) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3231 : oddCount 3231 15 = 12 ∧ acceleratedOrbit 15 3231 = 52420 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3231 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3231) = 3 ^ 12 * m + 52420 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3231.1, data_15_3231.2]

/-- Complete interval computation for depth 15, residue 3232. -/
theorem bounds_15_3232 : exactInterval 15 3232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3232 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3232) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3232 : oddCount 3232 15 = 5 ∧ acceleratedOrbit 15 3232 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3232 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3232) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3232.1, data_15_3232.2]

/-- Complete interval computation for depth 15, residue 3233. -/
theorem bounds_15_3233 : exactInterval 15 3233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3233 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3233) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3233 : oddCount 3233 15 = 12 ∧ acceleratedOrbit 15 3233 = 52487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3233 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3233) = 3 ^ 12 * m + 52487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3233.1, data_15_3233.2]

/-- Complete interval computation for depth 15, residue 3234. -/
theorem bounds_15_3234 : exactInterval 15 3234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3234 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3234) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3234 : oddCount 3234 15 = 8 ∧ acceleratedOrbit 15 3234 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3234 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3234) = 3 ^ 8 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3234.1, data_15_3234.2]

/-- Complete interval computation for depth 15, residue 3235. -/
theorem bounds_15_3235 : exactInterval 15 3235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3235 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3235) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3235 : oddCount 3235 15 = 8 ∧ acceleratedOrbit 15 3235 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3235 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3235) = 3 ^ 8 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3235.1, data_15_3235.2]

/-- Complete interval computation for depth 15, residue 3236. -/
theorem bounds_15_3236 : exactInterval 15 3236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3236 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3236) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3236 : oddCount 3236 15 = 8 ∧ acceleratedOrbit 15 3236 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3236 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3236) = 3 ^ 8 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3236.1, data_15_3236.2]

/-- Complete interval computation for depth 15, residue 3237. -/
theorem bounds_15_3237 : exactInterval 15 3237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3237 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3237) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3237 : oddCount 3237 15 = 8 ∧ acceleratedOrbit 15 3237 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3237 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3237) = 3 ^ 8 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3237.1, data_15_3237.2]

/-- Complete interval computation for depth 15, residue 3238. -/
theorem bounds_15_3238 : exactInterval 15 3238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3238 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3238) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3238 : oddCount 3238 15 = 8 ∧ acceleratedOrbit 15 3238 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3238 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3238) = 3 ^ 8 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3238.1, data_15_3238.2]

/-- Complete interval computation for depth 15, residue 3239. -/
theorem bounds_15_3239 : exactInterval 15 3239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3239 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3239) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3239 : oddCount 3239 15 = 10 ∧ acceleratedOrbit 15 3239 = 5840 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3239 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3239) = 3 ^ 10 * m + 5840 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3239.1, data_15_3239.2]

/-- Complete interval computation for depth 15, residue 3240. -/
theorem bounds_15_3240 : exactInterval 15 3240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3240 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3240) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3240 : oddCount 3240 15 = 5 ∧ acceleratedOrbit 15 3240 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3240 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3240) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3240.1, data_15_3240.2]

/-- Complete interval computation for depth 15, residue 3241. -/
theorem bounds_15_3241 : exactInterval 15 3241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3241 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3241) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3241 : oddCount 3241 15 = 9 ∧ acceleratedOrbit 15 3241 = 1948 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3241 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3241) = 3 ^ 9 * m + 1948 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3241.1, data_15_3241.2]

/-- Complete interval computation for depth 15, residue 3242. -/
theorem bounds_15_3242 : exactInterval 15 3242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3242 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3242) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3242 : oddCount 3242 15 = 5 ∧ acceleratedOrbit 15 3242 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3242 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3242) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3242.1, data_15_3242.2]

/-- Complete interval computation for depth 15, residue 3243. -/
theorem bounds_15_3243 : exactInterval 15 3243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3243 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3243) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3243 : oddCount 3243 15 = 7 ∧ acceleratedOrbit 15 3243 = 217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3243 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3243) = 3 ^ 7 * m + 217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3243.1, data_15_3243.2]

end Collatz.Research.PassageAtlas.Batch0099
