import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0985

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 32243. -/
theorem bounds_15_32243 : exactInterval 15 32243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32243 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32243) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32243 : oddCount 32243 15 = 7 ∧ acceleratedOrbit 15 32243 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32243 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32243) = 3 ^ 7 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32243.1, data_15_32243.2]

/-- Complete interval computation for depth 15, residue 32244. -/
theorem bounds_15_32244 : exactInterval 15 32244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32244 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32244) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32244 : oddCount 32244 15 = 7 ∧ acceleratedOrbit 15 32244 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32244 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32244) = 3 ^ 7 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32244.1, data_15_32244.2]

/-- Complete interval computation for depth 15, residue 32245. -/
theorem bounds_15_32245 : exactInterval 15 32245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32245 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32245) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32245 : oddCount 32245 15 = 7 ∧ acceleratedOrbit 15 32245 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32245 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32245) = 3 ^ 7 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32245.1, data_15_32245.2]

/-- Complete interval computation for depth 15, residue 32246. -/
theorem bounds_15_32246 : exactInterval 15 32246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32246 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32246) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32246 : oddCount 32246 15 = 9 ∧ acceleratedOrbit 15 32246 = 19372 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32246 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32246) = 3 ^ 9 * m + 19372 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32246.1, data_15_32246.2]

/-- Complete interval computation for depth 15, residue 32247. -/
theorem bounds_15_32247 : exactInterval 15 32247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32247 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32247) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32247 : oddCount 32247 15 = 9 ∧ acceleratedOrbit 15 32247 = 19372 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32247 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32247) = 3 ^ 9 * m + 19372 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32247.1, data_15_32247.2]

/-- Complete interval computation for depth 15, residue 32248. -/
theorem bounds_15_32248 : exactInterval 15 32248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32248 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32248) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32248 : oddCount 32248 15 = 9 ∧ acceleratedOrbit 15 32248 = 19376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32248 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32248) = 3 ^ 9 * m + 19376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32248.1, data_15_32248.2]

/-- Complete interval computation for depth 15, residue 32249. -/
theorem bounds_15_32249 : exactInterval 15 32249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32249 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32249) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32249 : oddCount 32249 15 = 7 ∧ acceleratedOrbit 15 32249 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32249 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32249) = 3 ^ 7 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32249.1, data_15_32249.2]

/-- Complete interval computation for depth 15, residue 32250. -/
theorem bounds_15_32250 : exactInterval 15 32250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32250 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32250) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32250 : oddCount 32250 15 = 9 ∧ acceleratedOrbit 15 32250 = 19376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32250 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32250) = 3 ^ 9 * m + 19376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32250.1, data_15_32250.2]

/-- Complete interval computation for depth 15, residue 32251. -/
theorem bounds_15_32251 : exactInterval 15 32251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32251 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32251) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32251 : oddCount 32251 15 = 8 ∧ acceleratedOrbit 15 32251 = 6458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32251 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32251) = 3 ^ 8 * m + 6458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32251.1, data_15_32251.2]

/-- Complete interval computation for depth 15, residue 32252. -/
theorem bounds_15_32252 : exactInterval 15 32252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32252 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32252) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32252 : oddCount 32252 15 = 9 ∧ acceleratedOrbit 15 32252 = 19376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32252 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32252) = 3 ^ 9 * m + 19376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32252.1, data_15_32252.2]

/-- Complete interval computation for depth 15, residue 32253. -/
theorem bounds_15_32253 : exactInterval 15 32253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32253 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32253) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32253 : oddCount 32253 15 = 9 ∧ acceleratedOrbit 15 32253 = 19376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32253 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32253) = 3 ^ 9 * m + 19376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32253.1, data_15_32253.2]

/-- Complete interval computation for depth 15, residue 32254. -/
theorem bounds_15_32254 : exactInterval 15 32254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32254 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32254) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32254 : oddCount 32254 15 = 12 ∧ acceleratedOrbit 15 32254 = 523138 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32254 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32254) = 3 ^ 12 * m + 523138 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32254.1, data_15_32254.2]

/-- Complete interval computation for depth 15, residue 32255. -/
theorem bounds_15_32255 : exactInterval 15 32255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32255 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32255) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32255 : oddCount 32255 15 = 12 ∧ acceleratedOrbit 15 32255 = 523138 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32255 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32255) = 3 ^ 12 * m + 523138 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32255.1, data_15_32255.2]

/-- Complete interval computation for depth 15, residue 32256. -/
theorem bounds_15_32256 : exactInterval 15 32256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32256 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32256) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32256 : oddCount 32256 15 = 6 ∧ acceleratedOrbit 15 32256 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32256 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32256) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32256.1, data_15_32256.2]

/-- Complete interval computation for depth 15, residue 32257. -/
theorem bounds_15_32257 : exactInterval 15 32257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32257 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32257) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32257 : oddCount 32257 15 = 9 ∧ acceleratedOrbit 15 32257 = 19379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32257 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32257) = 3 ^ 9 * m + 19379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32257.1, data_15_32257.2]

/-- Complete interval computation for depth 15, residue 32258. -/
theorem bounds_15_32258 : exactInterval 15 32258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32258 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32258) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32258 : oddCount 32258 15 = 6 ∧ acceleratedOrbit 15 32258 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32258 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32258) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32258.1, data_15_32258.2]

/-- Complete interval computation for depth 15, residue 32259. -/
theorem bounds_15_32259 : exactInterval 15 32259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32259 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32259) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32259 : oddCount 32259 15 = 6 ∧ acceleratedOrbit 15 32259 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32259 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32259) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32259.1, data_15_32259.2]

/-- Complete interval computation for depth 15, residue 32260. -/
theorem bounds_15_32260 : exactInterval 15 32260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32260 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32260) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32260 : oddCount 32260 15 = 6 ∧ acceleratedOrbit 15 32260 = 718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32260 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32260) = 3 ^ 6 * m + 718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32260.1, data_15_32260.2]

/-- Complete interval computation for depth 15, residue 32261. -/
theorem bounds_15_32261 : exactInterval 15 32261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32261 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32261) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32261 : oddCount 32261 15 = 6 ∧ acceleratedOrbit 15 32261 = 718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32261 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32261) = 3 ^ 6 * m + 718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32261.1, data_15_32261.2]

/-- Complete interval computation for depth 15, residue 32262. -/
theorem bounds_15_32262 : exactInterval 15 32262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32262 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32262) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32262 : oddCount 32262 15 = 6 ∧ acceleratedOrbit 15 32262 = 718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32262 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32262) = 3 ^ 6 * m + 718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32262.1, data_15_32262.2]

/-- Complete interval computation for depth 15, residue 32263. -/
theorem bounds_15_32263 : exactInterval 15 32263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32263 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32263) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32263 : oddCount 32263 15 = 8 ∧ acceleratedOrbit 15 32263 = 6461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32263 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32263) = 3 ^ 8 * m + 6461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32263.1, data_15_32263.2]

/-- Complete interval computation for depth 15, residue 32264. -/
theorem bounds_15_32264 : exactInterval 15 32264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32264 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32264) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32264 : oddCount 32264 15 = 6 ∧ acceleratedOrbit 15 32264 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32264 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32264) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32264.1, data_15_32264.2]

/-- Complete interval computation for depth 15, residue 32265. -/
theorem bounds_15_32265 : exactInterval 15 32265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32265 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32265) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32265 : oddCount 32265 15 = 9 ∧ acceleratedOrbit 15 32265 = 19385 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32265 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32265) = 3 ^ 9 * m + 19385 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32265.1, data_15_32265.2]

/-- Complete interval computation for depth 15, residue 32266. -/
theorem bounds_15_32266 : exactInterval 15 32266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32266 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32266) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32266 : oddCount 32266 15 = 6 ∧ acceleratedOrbit 15 32266 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32266 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32266) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32266.1, data_15_32266.2]

/-- Complete interval computation for depth 15, residue 32267. -/
theorem bounds_15_32267 : exactInterval 15 32267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32267 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32267) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32267 : oddCount 32267 15 = 6 ∧ acceleratedOrbit 15 32267 = 718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32267 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32267) = 3 ^ 6 * m + 718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32267.1, data_15_32267.2]

/-- Complete interval computation for depth 15, residue 32268. -/
theorem bounds_15_32268 : exactInterval 15 32268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32268 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32268) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32268 : oddCount 32268 15 = 6 ∧ acceleratedOrbit 15 32268 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32268 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32268) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32268.1, data_15_32268.2]

/-- Complete interval computation for depth 15, residue 32269. -/
theorem bounds_15_32269 : exactInterval 15 32269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32269 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32269) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32269 : oddCount 32269 15 = 6 ∧ acceleratedOrbit 15 32269 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32269 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32269) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32269.1, data_15_32269.2]

/-- Complete interval computation for depth 15, residue 32270. -/
theorem bounds_15_32270 : exactInterval 15 32270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32270 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32270) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32270 : oddCount 32270 15 = 6 ∧ acceleratedOrbit 15 32270 = 718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32270 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32270) = 3 ^ 6 * m + 718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32270.1, data_15_32270.2]

/-- Complete interval computation for depth 15, residue 32271. -/
theorem bounds_15_32271 : exactInterval 15 32271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32271 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32271) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32271 : oddCount 32271 15 = 6 ∧ acceleratedOrbit 15 32271 = 718 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32271 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32271) = 3 ^ 6 * m + 718 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32271.1, data_15_32271.2]

/-- Complete interval computation for depth 15, residue 32272. -/
theorem bounds_15_32272 : exactInterval 15 32272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32272 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32272) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32272 : oddCount 32272 15 = 8 ∧ acceleratedOrbit 15 32272 = 6470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32272 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32272) = 3 ^ 8 * m + 6470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32272.1, data_15_32272.2]

/-- Complete interval computation for depth 15, residue 32273. -/
theorem bounds_15_32273 : exactInterval 15 32273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32273 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32273) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32273 : oddCount 32273 15 = 6 ∧ acceleratedOrbit 15 32273 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32273 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32273) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32273.1, data_15_32273.2]

/-- Complete interval computation for depth 15, residue 32274. -/
theorem bounds_15_32274 : exactInterval 15 32274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32274 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32274) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32274 : oddCount 32274 15 = 8 ∧ acceleratedOrbit 15 32274 = 6463 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32274 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32274) = 3 ^ 8 * m + 6463 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32274.1, data_15_32274.2]

/-- Complete interval computation for depth 15, residue 32275. -/
theorem bounds_15_32275 : exactInterval 15 32275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32275 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32275) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32275 : oddCount 32275 15 = 8 ∧ acceleratedOrbit 15 32275 = 6463 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32275 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32275) = 3 ^ 8 * m + 6463 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32275.1, data_15_32275.2]

end Collatz.Research.PassageAtlas.Batch0985
