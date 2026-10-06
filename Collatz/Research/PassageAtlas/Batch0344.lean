import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0344

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 11239. -/
theorem bounds_15_11239 : exactInterval 15 11239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11239 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11239) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11239 : oddCount 11239 15 = 8 ∧ acceleratedOrbit 15 11239 = 2251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11239 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11239) = 3 ^ 8 * m + 2251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11239.1, data_15_11239.2]

/-- Complete interval computation for depth 15, residue 11240. -/
theorem bounds_15_11240 : exactInterval 15 11240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11240 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11240) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11240 : oddCount 11240 15 = 6 ∧ acceleratedOrbit 15 11240 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11240 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11240) = 3 ^ 6 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11240.1, data_15_11240.2]

/-- Complete interval computation for depth 15, residue 11241. -/
theorem bounds_15_11241 : exactInterval 15 11241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11241 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11241) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11241 : oddCount 11241 15 = 10 ∧ acceleratedOrbit 15 11241 = 20260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11241 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11241) = 3 ^ 10 * m + 20260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11241.1, data_15_11241.2]

/-- Complete interval computation for depth 15, residue 11242. -/
theorem bounds_15_11242 : exactInterval 15 11242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11242 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11242) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11242 : oddCount 11242 15 = 6 ∧ acceleratedOrbit 15 11242 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11242 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11242) = 3 ^ 6 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11242.1, data_15_11242.2]

/-- Complete interval computation for depth 15, residue 11243. -/
theorem bounds_15_11243 : exactInterval 15 11243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11243 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11243) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11243 : oddCount 11243 15 = 8 ∧ acceleratedOrbit 15 11243 = 2252 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11243 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11243) = 3 ^ 8 * m + 2252 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11243.1, data_15_11243.2]

/-- Complete interval computation for depth 15, residue 11244. -/
theorem bounds_15_11244 : exactInterval 15 11244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11244 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11244) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11244 : oddCount 11244 15 = 10 ∧ acceleratedOrbit 15 11244 = 20276 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11244 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11244) = 3 ^ 10 * m + 20276 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11244.1, data_15_11244.2]

/-- Complete interval computation for depth 15, residue 11245. -/
theorem bounds_15_11245 : exactInterval 15 11245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11245 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11245) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11245 : oddCount 11245 15 = 10 ∧ acceleratedOrbit 15 11245 = 20276 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11245 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11245) = 3 ^ 10 * m + 20276 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11245.1, data_15_11245.2]

/-- Complete interval computation for depth 15, residue 11246. -/
theorem bounds_15_11246 : exactInterval 15 11246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11246 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11246) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11246 : oddCount 11246 15 = 10 ∧ acceleratedOrbit 15 11246 = 20276 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11246 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11246) = 3 ^ 10 * m + 20276 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11246.1, data_15_11246.2]

/-- Complete interval computation for depth 15, residue 11247. -/
theorem bounds_15_11247 : exactInterval 15 11247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11247 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11247) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11247 : oddCount 11247 15 = 10 ∧ acceleratedOrbit 15 11247 = 20270 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11247 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11247) = 3 ^ 10 * m + 20270 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11247.1, data_15_11247.2]

/-- Complete interval computation for depth 15, residue 11248. -/
theorem bounds_15_11248 : exactInterval 15 11248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11248 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11248) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11248 : oddCount 11248 15 = 9 ∧ acceleratedOrbit 15 11248 = 6767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11248 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11248) = 3 ^ 9 * m + 6767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11248.1, data_15_11248.2]

/-- Complete interval computation for depth 15, residue 11249. -/
theorem bounds_15_11249 : exactInterval 15 11249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11249 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11249) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11249 : oddCount 11249 15 = 6 ∧ acceleratedOrbit 15 11249 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11249 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11249) = 3 ^ 6 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11249.1, data_15_11249.2]

/-- Complete interval computation for depth 15, residue 11250. -/
theorem bounds_15_11250 : exactInterval 15 11250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11250 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11250) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11250 : oddCount 11250 15 = 8 ∧ acceleratedOrbit 15 11250 = 2254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11250 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11250) = 3 ^ 8 * m + 2254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11250.1, data_15_11250.2]

/-- Complete interval computation for depth 15, residue 11251. -/
theorem bounds_15_11251 : exactInterval 15 11251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11251 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11251) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11251 : oddCount 11251 15 = 8 ∧ acceleratedOrbit 15 11251 = 2254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11251 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11251) = 3 ^ 8 * m + 2254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11251.1, data_15_11251.2]

/-- Complete interval computation for depth 15, residue 11252. -/
theorem bounds_15_11252 : exactInterval 15 11252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11252 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11252) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11252 : oddCount 11252 15 = 9 ∧ acceleratedOrbit 15 11252 = 6767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11252 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11252) = 3 ^ 9 * m + 6767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11252.1, data_15_11252.2]

/-- Complete interval computation for depth 15, residue 11253. -/
theorem bounds_15_11253 : exactInterval 15 11253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11253 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11253) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11253 : oddCount 11253 15 = 9 ∧ acceleratedOrbit 15 11253 = 6767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11253 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11253) = 3 ^ 9 * m + 6767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11253.1, data_15_11253.2]

/-- Complete interval computation for depth 15, residue 11254. -/
theorem bounds_15_11254 : exactInterval 15 11254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11254 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11254) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11254 : oddCount 11254 15 = 9 ∧ acceleratedOrbit 15 11254 = 6763 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11254 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11254) = 3 ^ 9 * m + 6763 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11254.1, data_15_11254.2]

/-- Complete interval computation for depth 15, residue 11255. -/
theorem bounds_15_11255 : exactInterval 15 11255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11255 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11255) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11255 : oddCount 11255 15 = 9 ∧ acceleratedOrbit 15 11255 = 6763 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11255 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11255) = 3 ^ 9 * m + 6763 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11255.1, data_15_11255.2]

/-- Complete interval computation for depth 15, residue 11256. -/
theorem bounds_15_11256 : exactInterval 15 11256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11256 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11256) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11256 : oddCount 11256 15 = 9 ∧ acceleratedOrbit 15 11256 = 6767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11256 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11256) = 3 ^ 9 * m + 6767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11256.1, data_15_11256.2]

/-- Complete interval computation for depth 15, residue 11257. -/
theorem bounds_15_11257 : exactInterval 15 11257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11257 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11257) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11257 : oddCount 11257 15 = 11 ∧ acceleratedOrbit 15 11257 = 60871 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11257 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11257) = 3 ^ 11 * m + 60871 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11257.1, data_15_11257.2]

/-- Complete interval computation for depth 15, residue 11258. -/
theorem bounds_15_11258 : exactInterval 15 11258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11258 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11258) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11258 : oddCount 11258 15 = 9 ∧ acceleratedOrbit 15 11258 = 6767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11258 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11258) = 3 ^ 9 * m + 6767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11258.1, data_15_11258.2]

/-- Complete interval computation for depth 15, residue 11259. -/
theorem bounds_15_11259 : exactInterval 15 11259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11259 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11259) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11259 : oddCount 11259 15 = 10 ∧ acceleratedOrbit 15 11259 = 20294 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11259 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11259) = 3 ^ 10 * m + 20294 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11259.1, data_15_11259.2]

/-- Complete interval computation for depth 15, residue 11260. -/
theorem bounds_15_11260 : exactInterval 15 11260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11260 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11260) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11260 : oddCount 11260 15 = 9 ∧ acceleratedOrbit 15 11260 = 6766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11260 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11260) = 3 ^ 9 * m + 6766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11260.1, data_15_11260.2]

/-- Complete interval computation for depth 15, residue 11261. -/
theorem bounds_15_11261 : exactInterval 15 11261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11261 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11261) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11261 : oddCount 11261 15 = 9 ∧ acceleratedOrbit 15 11261 = 6766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11261 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11261) = 3 ^ 9 * m + 6766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11261.1, data_15_11261.2]

/-- Complete interval computation for depth 15, residue 11262. -/
theorem bounds_15_11262 : exactInterval 15 11262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11262 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11262) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11262 : oddCount 11262 15 = 9 ∧ acceleratedOrbit 15 11262 = 6766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11262 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11262) = 3 ^ 9 * m + 6766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11262.1, data_15_11262.2]

/-- Complete interval computation for depth 15, residue 11263. -/
theorem bounds_15_11263 : exactInterval 15 11263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11263 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11263) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11263 : oddCount 11263 15 = 12 ∧ acceleratedOrbit 15 11263 = 182683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11263 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11263) = 3 ^ 12 * m + 182683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11263.1, data_15_11263.2]

/-- Complete interval computation for depth 15, residue 11264. -/
theorem bounds_15_11264 : exactInterval 15 11264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11264 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11264) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11264 : oddCount 11264 15 = 3 ∧ acceleratedOrbit 15 11264 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11264 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11264) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11264.1, data_15_11264.2]

/-- Complete interval computation for depth 15, residue 11265. -/
theorem bounds_15_11265 : exactInterval 15 11265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11265 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11265) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11265 : oddCount 11265 15 = 8 ∧ acceleratedOrbit 15 11265 = 2258 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11265 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11265) = 3 ^ 8 * m + 2258 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11265.1, data_15_11265.2]

/-- Complete interval computation for depth 15, residue 11266. -/
theorem bounds_15_11266 : exactInterval 15 11266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11266 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11266) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11266 : oddCount 11266 15 = 8 ∧ acceleratedOrbit 15 11266 = 2258 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11266 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11266) = 3 ^ 8 * m + 2258 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11266.1, data_15_11266.2]

/-- Complete interval computation for depth 15, residue 11267. -/
theorem bounds_15_11267 : exactInterval 15 11267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11267 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11267) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11267 : oddCount 11267 15 = 8 ∧ acceleratedOrbit 15 11267 = 2258 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11267 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11267) = 3 ^ 8 * m + 2258 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11267.1, data_15_11267.2]

/-- Complete interval computation for depth 15, residue 11268. -/
theorem bounds_15_11268 : exactInterval 15 11268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11268 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11268) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11268 : oddCount 11268 15 = 7 ∧ acceleratedOrbit 15 11268 = 755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11268 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11268) = 3 ^ 7 * m + 755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11268.1, data_15_11268.2]

/-- Complete interval computation for depth 15, residue 11269. -/
theorem bounds_15_11269 : exactInterval 15 11269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11269 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11269) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11269 : oddCount 11269 15 = 7 ∧ acceleratedOrbit 15 11269 = 755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11269 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11269) = 3 ^ 7 * m + 755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11269.1, data_15_11269.2]

/-- Complete interval computation for depth 15, residue 11270. -/
theorem bounds_15_11270 : exactInterval 15 11270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11270 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11270) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11270 : oddCount 11270 15 = 7 ∧ acceleratedOrbit 15 11270 = 755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11270 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11270) = 3 ^ 7 * m + 755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11270.1, data_15_11270.2]

/-- Complete interval computation for depth 15, residue 11271. -/
theorem bounds_15_11271 : exactInterval 15 11271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11271 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11271) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11271 : oddCount 11271 15 = 8 ∧ acceleratedOrbit 15 11271 = 2258 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11271 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11271) = 3 ^ 8 * m + 2258 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11271.1, data_15_11271.2]

end Collatz.Research.PassageAtlas.Batch0344
