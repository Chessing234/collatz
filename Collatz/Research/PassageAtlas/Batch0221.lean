import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0221

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 7208. -/
theorem bounds_15_7208 : exactInterval 15 7208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7208 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7208) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7208 : oddCount 7208 15 = 8 ∧ acceleratedOrbit 15 7208 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7208 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7208) = 3 ^ 8 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7208.1, data_15_7208.2]

/-- Complete interval computation for depth 15, residue 7209. -/
theorem bounds_15_7209 : exactInterval 15 7209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7209 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7209) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7209 : oddCount 7209 15 = 8 ∧ acceleratedOrbit 15 7209 = 1444 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7209 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7209) = 3 ^ 8 * m + 1444 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7209.1, data_15_7209.2]

/-- Complete interval computation for depth 15, residue 7210. -/
theorem bounds_15_7210 : exactInterval 15 7210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7210 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7210) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7210 : oddCount 7210 15 = 8 ∧ acceleratedOrbit 15 7210 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7210 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7210) = 3 ^ 8 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7210.1, data_15_7210.2]

/-- Complete interval computation for depth 15, residue 7211. -/
theorem bounds_15_7211 : exactInterval 15 7211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7211 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7211) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7211 : oddCount 7211 15 = 6 ∧ acceleratedOrbit 15 7211 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7211 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7211) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7211.1, data_15_7211.2]

/-- Complete interval computation for depth 15, residue 7212. -/
theorem bounds_15_7212 : exactInterval 15 7212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7212 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7212) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7212 : oddCount 7212 15 = 8 ∧ acceleratedOrbit 15 7212 = 1448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7212 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7212) = 3 ^ 8 * m + 1448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7212.1, data_15_7212.2]

/-- Complete interval computation for depth 15, residue 7213. -/
theorem bounds_15_7213 : exactInterval 15 7213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7213 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7213) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7213 : oddCount 7213 15 = 8 ∧ acceleratedOrbit 15 7213 = 1448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7213 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7213) = 3 ^ 8 * m + 1448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7213.1, data_15_7213.2]

/-- Complete interval computation for depth 15, residue 7214. -/
theorem bounds_15_7214 : exactInterval 15 7214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7214 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7214) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7214 : oddCount 7214 15 = 8 ∧ acceleratedOrbit 15 7214 = 1448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7214 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7214) = 3 ^ 8 * m + 1448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7214.1, data_15_7214.2]

/-- Complete interval computation for depth 15, residue 7215. -/
theorem bounds_15_7215 : exactInterval 15 7215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7215 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7215) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7215 : oddCount 7215 15 = 8 ∧ acceleratedOrbit 15 7215 = 1445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7215 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7215) = 3 ^ 8 * m + 1445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7215.1, data_15_7215.2]

/-- Complete interval computation for depth 15, residue 7216. -/
theorem bounds_15_7216 : exactInterval 15 7216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7216 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7216) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7216 : oddCount 7216 15 = 8 ∧ acceleratedOrbit 15 7216 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7216 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7216) = 3 ^ 8 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7216.1, data_15_7216.2]

/-- Complete interval computation for depth 15, residue 7217. -/
theorem bounds_15_7217 : exactInterval 15 7217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7217 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7217) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7217 : oddCount 7217 15 = 8 ∧ acceleratedOrbit 15 7217 = 1448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7217 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7217) = 3 ^ 8 * m + 1448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7217.1, data_15_7217.2]

/-- Complete interval computation for depth 15, residue 7218. -/
theorem bounds_15_7218 : exactInterval 15 7218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7218 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7218) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7218 : oddCount 7218 15 = 8 ∧ acceleratedOrbit 15 7218 = 1448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7218 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7218) = 3 ^ 8 * m + 1448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7218.1, data_15_7218.2]

/-- Complete interval computation for depth 15, residue 7219. -/
theorem bounds_15_7219 : exactInterval 15 7219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7219 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7219) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7219 : oddCount 7219 15 = 8 ∧ acceleratedOrbit 15 7219 = 1448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7219 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7219) = 3 ^ 8 * m + 1448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7219.1, data_15_7219.2]

/-- Complete interval computation for depth 15, residue 7220. -/
theorem bounds_15_7220 : exactInterval 15 7220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7220 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7220) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7220 : oddCount 7220 15 = 8 ∧ acceleratedOrbit 15 7220 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7220 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7220) = 3 ^ 8 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7220.1, data_15_7220.2]

/-- Complete interval computation for depth 15, residue 7221. -/
theorem bounds_15_7221 : exactInterval 15 7221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7221 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7221) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7221 : oddCount 7221 15 = 8 ∧ acceleratedOrbit 15 7221 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7221 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7221) = 3 ^ 8 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7221.1, data_15_7221.2]

/-- Complete interval computation for depth 15, residue 7222. -/
theorem bounds_15_7222 : exactInterval 15 7222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7222 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7222) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7222 : oddCount 7222 15 = 9 ∧ acceleratedOrbit 15 7222 = 4340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7222 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7222) = 3 ^ 9 * m + 4340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7222.1, data_15_7222.2]

/-- Complete interval computation for depth 15, residue 7223. -/
theorem bounds_15_7223 : exactInterval 15 7223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7223 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7223) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7223 : oddCount 7223 15 = 9 ∧ acceleratedOrbit 15 7223 = 4340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7223 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7223) = 3 ^ 9 * m + 4340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7223.1, data_15_7223.2]

/-- Complete interval computation for depth 15, residue 7224. -/
theorem bounds_15_7224 : exactInterval 15 7224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7224 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7224) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7224 : oddCount 7224 15 = 7 ∧ acceleratedOrbit 15 7224 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7224 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7224) = 3 ^ 7 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7224.1, data_15_7224.2]

/-- Complete interval computation for depth 15, residue 7225. -/
theorem bounds_15_7225 : exactInterval 15 7225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7225 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7225) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7225 : oddCount 7225 15 = 8 ∧ acceleratedOrbit 15 7225 = 1448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7225 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7225) = 3 ^ 8 * m + 1448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7225.1, data_15_7225.2]

/-- Complete interval computation for depth 15, residue 7226. -/
theorem bounds_15_7226 : exactInterval 15 7226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7226 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7226) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7226 : oddCount 7226 15 = 7 ∧ acceleratedOrbit 15 7226 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7226 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7226) = 3 ^ 7 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7226.1, data_15_7226.2]

/-- Complete interval computation for depth 15, residue 7227. -/
theorem bounds_15_7227 : exactInterval 15 7227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7227 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7227) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7227 : oddCount 7227 15 = 10 ∧ acceleratedOrbit 15 7227 = 13031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7227 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7227) = 3 ^ 10 * m + 13031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7227.1, data_15_7227.2]

/-- Complete interval computation for depth 15, residue 7228. -/
theorem bounds_15_7228 : exactInterval 15 7228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7228 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7228) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7228 : oddCount 7228 15 = 7 ∧ acceleratedOrbit 15 7228 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7228 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7228) = 3 ^ 7 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7228.1, data_15_7228.2]

/-- Complete interval computation for depth 15, residue 7229. -/
theorem bounds_15_7229 : exactInterval 15 7229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7229 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7229) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7229 : oddCount 7229 15 = 7 ∧ acceleratedOrbit 15 7229 = 485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7229 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7229) = 3 ^ 7 * m + 485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7229.1, data_15_7229.2]

/-- Complete interval computation for depth 15, residue 7230. -/
theorem bounds_15_7230 : exactInterval 15 7230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7230 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7230) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7230 : oddCount 7230 15 = 10 ∧ acceleratedOrbit 15 7230 = 13034 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7230 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7230) = 3 ^ 10 * m + 13034 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7230.1, data_15_7230.2]

/-- Complete interval computation for depth 15, residue 7231. -/
theorem bounds_15_7231 : exactInterval 15 7231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7231 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7231) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7231 : oddCount 7231 15 = 10 ∧ acceleratedOrbit 15 7231 = 13034 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7231 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7231) = 3 ^ 10 * m + 13034 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7231.1, data_15_7231.2]

/-- Complete interval computation for depth 15, residue 7232. -/
theorem bounds_15_7232 : exactInterval 15 7232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7232 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7232) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7232 : oddCount 7232 15 = 2 ∧ acceleratedOrbit 15 7232 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7232 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7232) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7232.1, data_15_7232.2]

/-- Complete interval computation for depth 15, residue 7233. -/
theorem bounds_15_7233 : exactInterval 15 7233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7233 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7233) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7233 : oddCount 7233 15 = 8 ∧ acceleratedOrbit 15 7233 = 1451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7233 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7233) = 3 ^ 8 * m + 1451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7233.1, data_15_7233.2]

/-- Complete interval computation for depth 15, residue 7234. -/
theorem bounds_15_7234 : exactInterval 15 7234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7234 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7234) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7234 : oddCount 7234 15 = 8 ∧ acceleratedOrbit 15 7234 = 1451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7234 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7234) = 3 ^ 8 * m + 1451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7234.1, data_15_7234.2]

/-- Complete interval computation for depth 15, residue 7235. -/
theorem bounds_15_7235 : exactInterval 15 7235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7235 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7235) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7235 : oddCount 7235 15 = 8 ∧ acceleratedOrbit 15 7235 = 1451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7235 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7235) = 3 ^ 8 * m + 1451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7235.1, data_15_7235.2]

/-- Complete interval computation for depth 15, residue 7236. -/
theorem bounds_15_7236 : exactInterval 15 7236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7236 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7236) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7236 : oddCount 7236 15 = 8 ∧ acceleratedOrbit 15 7236 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7236 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7236) = 3 ^ 8 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7236.1, data_15_7236.2]

/-- Complete interval computation for depth 15, residue 7237. -/
theorem bounds_15_7237 : exactInterval 15 7237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7237 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7237) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7237 : oddCount 7237 15 = 8 ∧ acceleratedOrbit 15 7237 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7237 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7237) = 3 ^ 8 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7237.1, data_15_7237.2]

/-- Complete interval computation for depth 15, residue 7238. -/
theorem bounds_15_7238 : exactInterval 15 7238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7238 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7238) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7238 : oddCount 7238 15 = 8 ∧ acceleratedOrbit 15 7238 = 1457 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7238 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7238) = 3 ^ 8 * m + 1457 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7238.1, data_15_7238.2]

/-- Complete interval computation for depth 15, residue 7239. -/
theorem bounds_15_7239 : exactInterval 15 7239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7239 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7239) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7239 : oddCount 7239 15 = 8 ∧ acceleratedOrbit 15 7239 = 1450 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7239 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7239) = 3 ^ 8 * m + 1450 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7239.1, data_15_7239.2]

/-- Complete interval computation for depth 15, residue 7240. -/
theorem bounds_15_7240 : exactInterval 15 7240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7240 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7240) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7240 : oddCount 7240 15 = 8 ∧ acceleratedOrbit 15 7240 = 1453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7240 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7240) = 3 ^ 8 * m + 1453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7240.1, data_15_7240.2]

end Collatz.Research.PassageAtlas.Batch0221
