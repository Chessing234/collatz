import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0863

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 28246. -/
theorem bounds_15_28246 : exactInterval 15 28246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28246 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28246) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28246 : oddCount 28246 15 = 6 ∧ acceleratedOrbit 15 28246 = 629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28246 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28246) = 3 ^ 6 * m + 629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28246.1, data_15_28246.2]

/-- Complete interval computation for depth 15, residue 28247. -/
theorem bounds_15_28247 : exactInterval 15 28247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28247 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28247) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28247 : oddCount 28247 15 = 6 ∧ acceleratedOrbit 15 28247 = 629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28247 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28247) = 3 ^ 6 * m + 629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28247.1, data_15_28247.2]

/-- Complete interval computation for depth 15, residue 28248. -/
theorem bounds_15_28248 : exactInterval 15 28248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28248 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28248) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28248 : oddCount 28248 15 = 7 ∧ acceleratedOrbit 15 28248 = 1889 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28248 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28248) = 3 ^ 7 * m + 1889 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28248.1, data_15_28248.2]

/-- Complete interval computation for depth 15, residue 28249. -/
theorem bounds_15_28249 : exactInterval 15 28249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28249 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28249) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28249 : oddCount 28249 15 = 9 ∧ acceleratedOrbit 15 28249 = 16973 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28249 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28249) = 3 ^ 9 * m + 16973 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28249.1, data_15_28249.2]

/-- Complete interval computation for depth 15, residue 28250. -/
theorem bounds_15_28250 : exactInterval 15 28250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28250 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28250) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28250 : oddCount 28250 15 = 7 ∧ acceleratedOrbit 15 28250 = 1889 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28250 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28250) = 3 ^ 7 * m + 1889 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28250.1, data_15_28250.2]

/-- Complete interval computation for depth 15, residue 28251. -/
theorem bounds_15_28251 : exactInterval 15 28251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28251 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28251) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28251 : oddCount 28251 15 = 8 ∧ acceleratedOrbit 15 28251 = 5657 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28251 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28251) = 3 ^ 8 * m + 5657 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28251.1, data_15_28251.2]

/-- Complete interval computation for depth 15, residue 28252. -/
theorem bounds_15_28252 : exactInterval 15 28252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28252 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28252) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28252 : oddCount 28252 15 = 7 ∧ acceleratedOrbit 15 28252 = 1889 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28252 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28252) = 3 ^ 7 * m + 1889 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28252.1, data_15_28252.2]

/-- Complete interval computation for depth 15, residue 28253. -/
theorem bounds_15_28253 : exactInterval 15 28253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28253 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28253) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28253 : oddCount 28253 15 = 7 ∧ acceleratedOrbit 15 28253 = 1889 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28253 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28253) = 3 ^ 7 * m + 1889 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28253.1, data_15_28253.2]

/-- Complete interval computation for depth 15, residue 28254. -/
theorem bounds_15_28254 : exactInterval 15 28254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28254 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28254) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28254 : oddCount 28254 15 = 7 ∧ acceleratedOrbit 15 28254 = 1886 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28254 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28254) = 3 ^ 7 * m + 1886 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28254.1, data_15_28254.2]

/-- Complete interval computation for depth 15, residue 28255. -/
theorem bounds_15_28255 : exactInterval 15 28255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28255 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28255) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28255 : oddCount 28255 15 = 7 ∧ acceleratedOrbit 15 28255 = 1886 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28255 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28255) = 3 ^ 7 * m + 1886 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28255.1, data_15_28255.2]

/-- Complete interval computation for depth 15, residue 28256. -/
theorem bounds_15_28256 : exactInterval 15 28256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28256 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28256) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28256 : oddCount 28256 15 = 4 ∧ acceleratedOrbit 15 28256 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28256 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28256) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28256.1, data_15_28256.2]

/-- Complete interval computation for depth 15, residue 28257. -/
theorem bounds_15_28257 : exactInterval 15 28257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28257 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28257) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28257 : oddCount 28257 15 = 8 ∧ acceleratedOrbit 15 28257 = 5660 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28257 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28257) = 3 ^ 8 * m + 5660 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28257.1, data_15_28257.2]

/-- Complete interval computation for depth 15, residue 28258. -/
theorem bounds_15_28258 : exactInterval 15 28258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28258 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28258) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28258 : oddCount 28258 15 = 7 ∧ acceleratedOrbit 15 28258 = 1889 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28258 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28258) = 3 ^ 7 * m + 1889 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28258.1, data_15_28258.2]

/-- Complete interval computation for depth 15, residue 28259. -/
theorem bounds_15_28259 : exactInterval 15 28259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28259 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28259) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28259 : oddCount 28259 15 = 7 ∧ acceleratedOrbit 15 28259 = 1889 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28259 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28259) = 3 ^ 7 * m + 1889 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28259.1, data_15_28259.2]

/-- Complete interval computation for depth 15, residue 28260. -/
theorem bounds_15_28260 : exactInterval 15 28260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28260 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28260) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28260 : oddCount 28260 15 = 7 ∧ acceleratedOrbit 15 28260 = 1889 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28260 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28260) = 3 ^ 7 * m + 1889 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28260.1, data_15_28260.2]

/-- Complete interval computation for depth 15, residue 28261. -/
theorem bounds_15_28261 : exactInterval 15 28261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28261 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28261) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28261 : oddCount 28261 15 = 7 ∧ acceleratedOrbit 15 28261 = 1889 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28261 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28261) = 3 ^ 7 * m + 1889 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28261.1, data_15_28261.2]

/-- Complete interval computation for depth 15, residue 28262. -/
theorem bounds_15_28262 : exactInterval 15 28262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28262 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28262) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28262 : oddCount 28262 15 = 7 ∧ acceleratedOrbit 15 28262 = 1889 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28262 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28262) = 3 ^ 7 * m + 1889 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28262.1, data_15_28262.2]

/-- Complete interval computation for depth 15, residue 28263. -/
theorem bounds_15_28263 : exactInterval 15 28263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28263 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28263) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28263 : oddCount 28263 15 = 9 ∧ acceleratedOrbit 15 28263 = 16978 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28263 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28263) = 3 ^ 9 * m + 16978 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28263.1, data_15_28263.2]

/-- Complete interval computation for depth 15, residue 28264. -/
theorem bounds_15_28264 : exactInterval 15 28264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28264 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28264) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28264 : oddCount 28264 15 = 4 ∧ acceleratedOrbit 15 28264 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28264 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28264) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28264.1, data_15_28264.2]

/-- Complete interval computation for depth 15, residue 28265. -/
theorem bounds_15_28265 : exactInterval 15 28265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28265 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28265) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28265 : oddCount 28265 15 = 10 ∧ acceleratedOrbit 15 28265 = 50939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28265 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28265) = 3 ^ 10 * m + 50939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28265.1, data_15_28265.2]

/-- Complete interval computation for depth 15, residue 28266. -/
theorem bounds_15_28266 : exactInterval 15 28266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28266 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28266) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28266 : oddCount 28266 15 = 4 ∧ acceleratedOrbit 15 28266 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28266 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28266) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28266.1, data_15_28266.2]

/-- Complete interval computation for depth 15, residue 28267. -/
theorem bounds_15_28267 : exactInterval 15 28267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28267 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28267) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28267 : oddCount 28267 15 = 9 ∧ acceleratedOrbit 15 28267 = 16982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28267 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28267) = 3 ^ 9 * m + 16982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28267.1, data_15_28267.2]

/-- Complete interval computation for depth 15, residue 28268. -/
theorem bounds_15_28268 : exactInterval 15 28268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28268 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28268) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28268 : oddCount 28268 15 = 6 ∧ acceleratedOrbit 15 28268 = 629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28268 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28268) = 3 ^ 6 * m + 629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28268.1, data_15_28268.2]

/-- Complete interval computation for depth 15, residue 28269. -/
theorem bounds_15_28269 : exactInterval 15 28269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28269 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28269) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28269 : oddCount 28269 15 = 6 ∧ acceleratedOrbit 15 28269 = 629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28269 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28269) = 3 ^ 6 * m + 629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28269.1, data_15_28269.2]

/-- Complete interval computation for depth 15, residue 28270. -/
theorem bounds_15_28270 : exactInterval 15 28270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28270 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28270) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28270 : oddCount 28270 15 = 6 ∧ acceleratedOrbit 15 28270 = 629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28270 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28270) = 3 ^ 6 * m + 629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28270.1, data_15_28270.2]

/-- Complete interval computation for depth 15, residue 28271. -/
theorem bounds_15_28271 : exactInterval 15 28271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28271 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28271) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28271 : oddCount 28271 15 = 11 ∧ acceleratedOrbit 15 28271 = 152846 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28271 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28271) = 3 ^ 11 * m + 152846 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28271.1, data_15_28271.2]

/-- Complete interval computation for depth 15, residue 28272. -/
theorem bounds_15_28272 : exactInterval 15 28272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28272 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28272) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28272 : oddCount 28272 15 = 8 ∧ acceleratedOrbit 15 28272 = 5665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28272 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28272) = 3 ^ 8 * m + 5665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28272.1, data_15_28272.2]

/-- Complete interval computation for depth 15, residue 28273. -/
theorem bounds_15_28273 : exactInterval 15 28273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28273 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28273) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28273 : oddCount 28273 15 = 4 ∧ acceleratedOrbit 15 28273 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28273 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28273) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28273.1, data_15_28273.2]

/-- Complete interval computation for depth 15, residue 28274. -/
theorem bounds_15_28274 : exactInterval 15 28274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28274 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28274) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28274 : oddCount 28274 15 = 8 ∧ acceleratedOrbit 15 28274 = 5663 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28274 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28274) = 3 ^ 8 * m + 5663 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28274.1, data_15_28274.2]

/-- Complete interval computation for depth 15, residue 28275. -/
theorem bounds_15_28275 : exactInterval 15 28275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28275 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28275) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28275 : oddCount 28275 15 = 8 ∧ acceleratedOrbit 15 28275 = 5663 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28275 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28275) = 3 ^ 8 * m + 5663 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28275.1, data_15_28275.2]

/-- Complete interval computation for depth 15, residue 28276. -/
theorem bounds_15_28276 : exactInterval 15 28276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28276 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28276) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28276 : oddCount 28276 15 = 8 ∧ acceleratedOrbit 15 28276 = 5665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28276 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28276) = 3 ^ 8 * m + 5665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28276.1, data_15_28276.2]

/-- Complete interval computation for depth 15, residue 28277. -/
theorem bounds_15_28277 : exactInterval 15 28277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28277 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28277) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28277 : oddCount 28277 15 = 8 ∧ acceleratedOrbit 15 28277 = 5665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28277 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28277) = 3 ^ 8 * m + 5665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28277.1, data_15_28277.2]

end Collatz.Research.PassageAtlas.Batch0863
