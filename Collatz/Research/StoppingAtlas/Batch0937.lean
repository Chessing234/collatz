import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0937

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7208. -/
theorem bounds_13_7208 : exactInterval 13 7208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7208 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7208) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7208 : oddCount 7208 13 = 6 ∧ acceleratedOrbit 13 7208 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7208 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7208) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7208.1, data_13_7208.2]

/-- Complete interval computation for depth 13, residue 7209. -/
theorem bounds_13_7209 : exactInterval 13 7209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7209 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7209) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7209 : oddCount 7209 13 = 7 ∧ acceleratedOrbit 13 7209 = 1925 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7209 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7209) = 3 ^ 7 * m + 1925 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7209.1, data_13_7209.2]

/-- Complete interval computation for depth 13, residue 7210. -/
theorem bounds_13_7210 : exactInterval 13 7210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7210 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7210) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7210 : oddCount 7210 13 = 6 ∧ acceleratedOrbit 13 7210 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7210 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7210) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7210.1, data_13_7210.2]

/-- Complete interval computation for depth 13, residue 7211. -/
theorem bounds_13_7211 : exactInterval 13 7211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7211 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7211) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7211 : oddCount 7211 13 = 5 ∧ acceleratedOrbit 13 7211 = 214 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7211 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7211) = 3 ^ 5 * m + 214 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7211.1, data_13_7211.2]

/-- Complete interval computation for depth 13, residue 7212. -/
theorem bounds_13_7212 : exactInterval 13 7212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7212 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7212) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7212 : oddCount 7212 13 = 6 ∧ acceleratedOrbit 13 7212 = 643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7212 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7212) = 3 ^ 6 * m + 643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7212.1, data_13_7212.2]

/-- Complete interval computation for depth 13, residue 7213. -/
theorem bounds_13_7213 : exactInterval 13 7213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7213 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7213) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7213 : oddCount 7213 13 = 6 ∧ acceleratedOrbit 13 7213 = 643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7213 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7213) = 3 ^ 6 * m + 643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7213.1, data_13_7213.2]

/-- Complete interval computation for depth 13, residue 7214. -/
theorem bounds_13_7214 : exactInterval 13 7214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7214 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7214) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7214 : oddCount 7214 13 = 6 ∧ acceleratedOrbit 13 7214 = 643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7214 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7214) = 3 ^ 6 * m + 643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7214.1, data_13_7214.2]

/-- Complete interval computation for depth 13, residue 7215. -/
theorem bounds_13_7215 : exactInterval 13 7215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7215 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7215) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7215 : oddCount 7215 13 = 8 ∧ acceleratedOrbit 13 7215 = 5780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7215 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7215) = 3 ^ 8 * m + 5780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7215.1, data_13_7215.2]

/-- Complete interval computation for depth 13, residue 7216. -/
theorem bounds_13_7216 : exactInterval 13 7216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7216 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7216) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7216 : oddCount 7216 13 = 6 ∧ acceleratedOrbit 13 7216 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7216 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7216) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7216.1, data_13_7216.2]

/-- Complete interval computation for depth 13, residue 7217. -/
theorem bounds_13_7217 : exactInterval 13 7217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7217 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7217) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7217 : oddCount 7217 13 = 6 ∧ acceleratedOrbit 13 7217 = 643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7217 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7217) = 3 ^ 6 * m + 643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7217.1, data_13_7217.2]

/-- Complete interval computation for depth 13, residue 7218. -/
theorem bounds_13_7218 : exactInterval 13 7218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7218 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7218) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7218 : oddCount 7218 13 = 6 ∧ acceleratedOrbit 13 7218 = 643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7218 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7218) = 3 ^ 6 * m + 643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7218.1, data_13_7218.2]

/-- Complete interval computation for depth 13, residue 7219. -/
theorem bounds_13_7219 : exactInterval 13 7219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7219 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7219) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7219 : oddCount 7219 13 = 6 ∧ acceleratedOrbit 13 7219 = 643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7219 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7219) = 3 ^ 6 * m + 643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7219.1, data_13_7219.2]

/-- Complete interval computation for depth 13, residue 7220. -/
theorem bounds_13_7220 : exactInterval 13 7220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7220 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7220) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7220 : oddCount 7220 13 = 6 ∧ acceleratedOrbit 13 7220 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7220 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7220) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7220.1, data_13_7220.2]

/-- Complete interval computation for depth 13, residue 7221. -/
theorem bounds_13_7221 : exactInterval 13 7221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7221 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7221) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7221 : oddCount 7221 13 = 6 ∧ acceleratedOrbit 13 7221 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7221 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7221) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7221.1, data_13_7221.2]

/-- Complete interval computation for depth 13, residue 7222. -/
theorem bounds_13_7222 : exactInterval 13 7222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7222 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7222) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7222 : oddCount 7222 13 = 9 ∧ acceleratedOrbit 13 7222 = 17360 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7222 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7222) = 3 ^ 9 * m + 17360 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7222.1, data_13_7222.2]

/-- Complete interval computation for depth 13, residue 7223. -/
theorem bounds_13_7223 : exactInterval 13 7223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7223 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7223) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7223 : oddCount 7223 13 = 9 ∧ acceleratedOrbit 13 7223 = 17360 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7223 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7223) = 3 ^ 9 * m + 17360 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7223.1, data_13_7223.2]

end Collatz.Research.StoppingAtlas.Batch0937
