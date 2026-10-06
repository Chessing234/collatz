import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0984

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 32210. -/
theorem bounds_15_32210 : exactInterval 15 32210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32210 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32210) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32210 : oddCount 32210 15 = 7 ∧ acceleratedOrbit 15 32210 = 2150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32210 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32210) = 3 ^ 7 * m + 2150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32210.1, data_15_32210.2]

/-- Complete interval computation for depth 15, residue 32211. -/
theorem bounds_15_32211 : exactInterval 15 32211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32211 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32211) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32211 : oddCount 32211 15 = 7 ∧ acceleratedOrbit 15 32211 = 2150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32211 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32211) = 3 ^ 7 * m + 2150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32211.1, data_15_32211.2]

/-- Complete interval computation for depth 15, residue 32212. -/
theorem bounds_15_32212 : exactInterval 15 32212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32212 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32212) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32212 : oddCount 32212 15 = 6 ∧ acceleratedOrbit 15 32212 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32212 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32212) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32212.1, data_15_32212.2]

/-- Complete interval computation for depth 15, residue 32213. -/
theorem bounds_15_32213 : exactInterval 15 32213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32213 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32213) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32213 : oddCount 32213 15 = 6 ∧ acceleratedOrbit 15 32213 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32213 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32213) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32213.1, data_15_32213.2]

/-- Complete interval computation for depth 15, residue 32214. -/
theorem bounds_15_32214 : exactInterval 15 32214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32214 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32214) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32214 : oddCount 32214 15 = 8 ∧ acceleratedOrbit 15 32214 = 6452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32214 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32214) = 3 ^ 8 * m + 6452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32214.1, data_15_32214.2]

/-- Complete interval computation for depth 15, residue 32215. -/
theorem bounds_15_32215 : exactInterval 15 32215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32215 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32215) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32215 : oddCount 32215 15 = 8 ∧ acceleratedOrbit 15 32215 = 6452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32215 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32215) = 3 ^ 8 * m + 6452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32215.1, data_15_32215.2]

/-- Complete interval computation for depth 15, residue 32216. -/
theorem bounds_15_32216 : exactInterval 15 32216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32216 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32216) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32216 : oddCount 32216 15 = 5 ∧ acceleratedOrbit 15 32216 = 239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32216 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32216) = 3 ^ 5 * m + 239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32216.1, data_15_32216.2]

/-- Complete interval computation for depth 15, residue 32217. -/
theorem bounds_15_32217 : exactInterval 15 32217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32217 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32217) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32217 : oddCount 32217 15 = 5 ∧ acceleratedOrbit 15 32217 = 239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32217 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32217) = 3 ^ 5 * m + 239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32217.1, data_15_32217.2]

/-- Complete interval computation for depth 15, residue 32218. -/
theorem bounds_15_32218 : exactInterval 15 32218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32218 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32218) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32218 : oddCount 32218 15 = 5 ∧ acceleratedOrbit 15 32218 = 239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32218 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32218) = 3 ^ 5 * m + 239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32218.1, data_15_32218.2]

/-- Complete interval computation for depth 15, residue 32219. -/
theorem bounds_15_32219 : exactInterval 15 32219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32219 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32219) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32219 : oddCount 32219 15 = 9 ∧ acceleratedOrbit 15 32219 = 19358 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32219 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32219) = 3 ^ 9 * m + 19358 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32219.1, data_15_32219.2]

/-- Complete interval computation for depth 15, residue 32220. -/
theorem bounds_15_32220 : exactInterval 15 32220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32220 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32220) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32220 : oddCount 32220 15 = 5 ∧ acceleratedOrbit 15 32220 = 239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32220 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32220) = 3 ^ 5 * m + 239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32220.1, data_15_32220.2]

/-- Complete interval computation for depth 15, residue 32221. -/
theorem bounds_15_32221 : exactInterval 15 32221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32221 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32221) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32221 : oddCount 32221 15 = 5 ∧ acceleratedOrbit 15 32221 = 239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32221 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32221) = 3 ^ 5 * m + 239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32221.1, data_15_32221.2]

/-- Complete interval computation for depth 15, residue 32222. -/
theorem bounds_15_32222 : exactInterval 15 32222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32222 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32222) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32222 : oddCount 32222 15 = 10 ∧ acceleratedOrbit 15 32222 = 58070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32222 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32222) = 3 ^ 10 * m + 58070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32222.1, data_15_32222.2]

/-- Complete interval computation for depth 15, residue 32223. -/
theorem bounds_15_32223 : exactInterval 15 32223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32223 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32223) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32223 : oddCount 32223 15 = 10 ∧ acceleratedOrbit 15 32223 = 58070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32223 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32223) = 3 ^ 10 * m + 58070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32223.1, data_15_32223.2]

/-- Complete interval computation for depth 15, residue 32224. -/
theorem bounds_15_32224 : exactInterval 15 32224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32224 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32224) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32224 : oddCount 32224 15 = 7 ∧ acceleratedOrbit 15 32224 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32224 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32224) = 3 ^ 7 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32224.1, data_15_32224.2]

/-- Complete interval computation for depth 15, residue 32225. -/
theorem bounds_15_32225 : exactInterval 15 32225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32225 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32225) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32225 : oddCount 32225 15 = 11 ∧ acceleratedOrbit 15 32225 = 174230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32225 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32225) = 3 ^ 11 * m + 174230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32225.1, data_15_32225.2]

/-- Complete interval computation for depth 15, residue 32226. -/
theorem bounds_15_32226 : exactInterval 15 32226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32226 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32226) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32226 : oddCount 32226 15 = 6 ∧ acceleratedOrbit 15 32226 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32226 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32226) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32226.1, data_15_32226.2]

/-- Complete interval computation for depth 15, residue 32227. -/
theorem bounds_15_32227 : exactInterval 15 32227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32227 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32227) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32227 : oddCount 32227 15 = 6 ∧ acceleratedOrbit 15 32227 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32227 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32227) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32227.1, data_15_32227.2]

/-- Complete interval computation for depth 15, residue 32228. -/
theorem bounds_15_32228 : exactInterval 15 32228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32228 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32228) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32228 : oddCount 32228 15 = 8 ∧ acceleratedOrbit 15 32228 = 6455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32228 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32228) = 3 ^ 8 * m + 6455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32228.1, data_15_32228.2]

/-- Complete interval computation for depth 15, residue 32229. -/
theorem bounds_15_32229 : exactInterval 15 32229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32229 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32229) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32229 : oddCount 32229 15 = 8 ∧ acceleratedOrbit 15 32229 = 6455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32229 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32229) = 3 ^ 8 * m + 6455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32229.1, data_15_32229.2]

/-- Complete interval computation for depth 15, residue 32230. -/
theorem bounds_15_32230 : exactInterval 15 32230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32230 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32230) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32230 : oddCount 32230 15 = 8 ∧ acceleratedOrbit 15 32230 = 6455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32230 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32230) = 3 ^ 8 * m + 6455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32230.1, data_15_32230.2]

/-- Complete interval computation for depth 15, residue 32231. -/
theorem bounds_15_32231 : exactInterval 15 32231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32231 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32231) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32231 : oddCount 32231 15 = 8 ∧ acceleratedOrbit 15 32231 = 6454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32231 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32231) = 3 ^ 8 * m + 6454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32231.1, data_15_32231.2]

/-- Complete interval computation for depth 15, residue 32232. -/
theorem bounds_15_32232 : exactInterval 15 32232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32232 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32232) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32232 : oddCount 32232 15 = 7 ∧ acceleratedOrbit 15 32232 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32232 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32232) = 3 ^ 7 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32232.1, data_15_32232.2]

/-- Complete interval computation for depth 15, residue 32233. -/
theorem bounds_15_32233 : exactInterval 15 32233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32233 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32233) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32233 : oddCount 32233 15 = 9 ∧ acceleratedOrbit 15 32233 = 19363 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32233 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32233) = 3 ^ 9 * m + 19363 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32233.1, data_15_32233.2]

/-- Complete interval computation for depth 15, residue 32234. -/
theorem bounds_15_32234 : exactInterval 15 32234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32234 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32234) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32234 : oddCount 32234 15 = 7 ∧ acceleratedOrbit 15 32234 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32234 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32234) = 3 ^ 7 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32234.1, data_15_32234.2]

/-- Complete interval computation for depth 15, residue 32235. -/
theorem bounds_15_32235 : exactInterval 15 32235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32235 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32235) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32235 : oddCount 32235 15 = 9 ∧ acceleratedOrbit 15 32235 = 19364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32235 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32235) = 3 ^ 9 * m + 19364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32235.1, data_15_32235.2]

/-- Complete interval computation for depth 15, residue 32236. -/
theorem bounds_15_32236 : exactInterval 15 32236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32236 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32236) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32236 : oddCount 32236 15 = 7 ∧ acceleratedOrbit 15 32236 = 2152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32236 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32236) = 3 ^ 7 * m + 2152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32236.1, data_15_32236.2]

/-- Complete interval computation for depth 15, residue 32237. -/
theorem bounds_15_32237 : exactInterval 15 32237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32237 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32237) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32237 : oddCount 32237 15 = 7 ∧ acceleratedOrbit 15 32237 = 2152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32237 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32237) = 3 ^ 7 * m + 2152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32237.1, data_15_32237.2]

/-- Complete interval computation for depth 15, residue 32238. -/
theorem bounds_15_32238 : exactInterval 15 32238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32238 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32238) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32238 : oddCount 32238 15 = 7 ∧ acceleratedOrbit 15 32238 = 2152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32238 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32238) = 3 ^ 7 * m + 2152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32238.1, data_15_32238.2]

/-- Complete interval computation for depth 15, residue 32239. -/
theorem bounds_15_32239 : exactInterval 15 32239 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32239 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32239) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32239 : oddCount 32239 15 = 9 ∧ acceleratedOrbit 15 32239 = 19366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32239 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32239) = 3 ^ 9 * m + 19366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32239.1, data_15_32239.2]

/-- Complete interval computation for depth 15, residue 32240. -/
theorem bounds_15_32240 : exactInterval 15 32240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32240 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32240) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32240 : oddCount 32240 15 = 7 ∧ acceleratedOrbit 15 32240 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32240 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32240) = 3 ^ 7 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32240.1, data_15_32240.2]

/-- Complete interval computation for depth 15, residue 32241. -/
theorem bounds_15_32241 : exactInterval 15 32241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32241 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32241) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32241 : oddCount 32241 15 = 7 ∧ acceleratedOrbit 15 32241 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32241 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32241) = 3 ^ 7 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32241.1, data_15_32241.2]

/-- Complete interval computation for depth 15, residue 32242. -/
theorem bounds_15_32242 : exactInterval 15 32242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32242 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32242) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32242 : oddCount 32242 15 = 7 ∧ acceleratedOrbit 15 32242 = 2153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32242 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32242) = 3 ^ 7 * m + 2153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32242.1, data_15_32242.2]

end Collatz.Research.PassageAtlas.Batch0984
