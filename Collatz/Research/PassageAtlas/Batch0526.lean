import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0526

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 17203. -/
theorem bounds_15_17203 : exactInterval 15 17203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17203 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17203) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17203 : oddCount 17203 15 = 6 ∧ acceleratedOrbit 15 17203 = 383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17203 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17203) = 3 ^ 6 * m + 383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17203.1, data_15_17203.2]

/-- Complete interval computation for depth 15, residue 17204. -/
theorem bounds_15_17204 : exactInterval 15 17204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17204 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17204) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17204 : oddCount 17204 15 = 5 ∧ acceleratedOrbit 15 17204 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17204 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17204) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17204.1, data_15_17204.2]

/-- Complete interval computation for depth 15, residue 17205. -/
theorem bounds_15_17205 : exactInterval 15 17205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17205 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17205) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17205 : oddCount 17205 15 = 5 ∧ acceleratedOrbit 15 17205 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17205 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17205) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17205.1, data_15_17205.2]

/-- Complete interval computation for depth 15, residue 17206. -/
theorem bounds_15_17206 : exactInterval 15 17206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17206 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17206) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17206 : oddCount 17206 15 = 10 ∧ acceleratedOrbit 15 17206 = 31013 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17206 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17206) = 3 ^ 10 * m + 31013 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17206.1, data_15_17206.2]

/-- Complete interval computation for depth 15, residue 17207. -/
theorem bounds_15_17207 : exactInterval 15 17207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17207 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17207) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17207 : oddCount 17207 15 = 10 ∧ acceleratedOrbit 15 17207 = 31013 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17207 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17207) = 3 ^ 10 * m + 31013 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17207.1, data_15_17207.2]

/-- Complete interval computation for depth 15, residue 17208. -/
theorem bounds_15_17208 : exactInterval 15 17208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17208 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17208) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17208 : oddCount 17208 15 = 9 ∧ acceleratedOrbit 15 17208 = 10343 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17208 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17208) = 3 ^ 9 * m + 10343 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17208.1, data_15_17208.2]

/-- Complete interval computation for depth 15, residue 17209. -/
theorem bounds_15_17209 : exactInterval 15 17209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17209 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17209) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17209 : oddCount 17209 15 = 9 ∧ acceleratedOrbit 15 17209 = 10340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17209 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17209) = 3 ^ 9 * m + 10340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17209.1, data_15_17209.2]

/-- Complete interval computation for depth 15, residue 17210. -/
theorem bounds_15_17210 : exactInterval 15 17210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17210 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17210) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17210 : oddCount 17210 15 = 9 ∧ acceleratedOrbit 15 17210 = 10343 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17210 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17210) = 3 ^ 9 * m + 10343 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17210.1, data_15_17210.2]

/-- Complete interval computation for depth 15, residue 17211. -/
theorem bounds_15_17211 : exactInterval 15 17211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17211 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17211) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17211 : oddCount 17211 15 = 6 ∧ acceleratedOrbit 15 17211 = 383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17211 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17211) = 3 ^ 6 * m + 383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17211.1, data_15_17211.2]

/-- Complete interval computation for depth 15, residue 17212. -/
theorem bounds_15_17212 : exactInterval 15 17212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17212 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17212) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17212 : oddCount 17212 15 = 9 ∧ acceleratedOrbit 15 17212 = 10343 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17212 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17212) = 3 ^ 9 * m + 10343 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17212.1, data_15_17212.2]

/-- Complete interval computation for depth 15, residue 17213. -/
theorem bounds_15_17213 : exactInterval 15 17213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17213 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17213) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17213 : oddCount 17213 15 = 9 ∧ acceleratedOrbit 15 17213 = 10343 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17213 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17213) = 3 ^ 9 * m + 10343 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17213.1, data_15_17213.2]

/-- Complete interval computation for depth 15, residue 17214. -/
theorem bounds_15_17214 : exactInterval 15 17214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17214 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17214) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17214 : oddCount 17214 15 = 10 ∧ acceleratedOrbit 15 17214 = 31025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17214 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17214) = 3 ^ 10 * m + 31025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17214.1, data_15_17214.2]

/-- Complete interval computation for depth 15, residue 17215. -/
theorem bounds_15_17215 : exactInterval 15 17215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17215 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17215) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17215 : oddCount 17215 15 = 10 ∧ acceleratedOrbit 15 17215 = 31025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17215 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17215) = 3 ^ 10 * m + 31025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17215.1, data_15_17215.2]

/-- Complete interval computation for depth 15, residue 17216. -/
theorem bounds_15_17216 : exactInterval 15 17216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17216 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17216) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17216 : oddCount 17216 15 = 4 ∧ acceleratedOrbit 15 17216 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17216 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17216) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17216.1, data_15_17216.2]

/-- Complete interval computation for depth 15, residue 17217. -/
theorem bounds_15_17217 : exactInterval 15 17217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17217 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17217) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17217 : oddCount 17217 15 = 5 ∧ acceleratedOrbit 15 17217 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17217 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17217) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17217.1, data_15_17217.2]

/-- Complete interval computation for depth 15, residue 17218. -/
theorem bounds_15_17218 : exactInterval 15 17218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17218 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17218) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17218 : oddCount 17218 15 = 8 ∧ acceleratedOrbit 15 17218 = 3449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17218 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17218) = 3 ^ 8 * m + 3449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17218.1, data_15_17218.2]

/-- Complete interval computation for depth 15, residue 17219. -/
theorem bounds_15_17219 : exactInterval 15 17219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17219 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17219) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17219 : oddCount 17219 15 = 8 ∧ acceleratedOrbit 15 17219 = 3449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17219 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17219) = 3 ^ 8 * m + 3449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17219.1, data_15_17219.2]

/-- Complete interval computation for depth 15, residue 17220. -/
theorem bounds_15_17220 : exactInterval 15 17220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17220 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17220) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17220 : oddCount 17220 15 = 7 ∧ acceleratedOrbit 15 17220 = 1151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17220 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17220) = 3 ^ 7 * m + 1151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17220.1, data_15_17220.2]

/-- Complete interval computation for depth 15, residue 17221. -/
theorem bounds_15_17221 : exactInterval 15 17221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17221 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17221) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17221 : oddCount 17221 15 = 7 ∧ acceleratedOrbit 15 17221 = 1151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17221 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17221) = 3 ^ 7 * m + 1151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17221.1, data_15_17221.2]

/-- Complete interval computation for depth 15, residue 17222. -/
theorem bounds_15_17222 : exactInterval 15 17222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17222 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17222) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17222 : oddCount 17222 15 = 7 ∧ acceleratedOrbit 15 17222 = 1151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17222 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17222) = 3 ^ 7 * m + 1151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17222.1, data_15_17222.2]

/-- Complete interval computation for depth 15, residue 17223. -/
theorem bounds_15_17223 : exactInterval 15 17223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17223 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17223) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17223 : oddCount 17223 15 = 10 ∧ acceleratedOrbit 15 17223 = 31040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17223 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17223) = 3 ^ 10 * m + 31040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17223.1, data_15_17223.2]

/-- Complete interval computation for depth 15, residue 17224. -/
theorem bounds_15_17224 : exactInterval 15 17224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17224 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17224) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17224 : oddCount 17224 15 = 7 ∧ acceleratedOrbit 15 17224 = 1151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17224 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17224) = 3 ^ 7 * m + 1151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17224.1, data_15_17224.2]

/-- Complete interval computation for depth 15, residue 17225. -/
theorem bounds_15_17225 : exactInterval 15 17225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17225 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17225) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17225 : oddCount 17225 15 = 7 ∧ acceleratedOrbit 15 17225 = 1151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17225 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17225) = 3 ^ 7 * m + 1151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17225.1, data_15_17225.2]

/-- Complete interval computation for depth 15, residue 17226. -/
theorem bounds_15_17226 : exactInterval 15 17226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17226 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17226) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17226 : oddCount 17226 15 = 7 ∧ acceleratedOrbit 15 17226 = 1151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17226 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17226) = 3 ^ 7 * m + 1151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17226.1, data_15_17226.2]

/-- Complete interval computation for depth 15, residue 17227. -/
theorem bounds_15_17227 : exactInterval 15 17227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17227 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17227) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17227 : oddCount 17227 15 = 7 ∧ acceleratedOrbit 15 17227 = 1151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17227 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17227) = 3 ^ 7 * m + 1151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17227.1, data_15_17227.2]

/-- Complete interval computation for depth 15, residue 17228. -/
theorem bounds_15_17228 : exactInterval 15 17228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17228 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17228) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17228 : oddCount 17228 15 = 7 ∧ acceleratedOrbit 15 17228 = 1151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17228 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17228) = 3 ^ 7 * m + 1151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17228.1, data_15_17228.2]

/-- Complete interval computation for depth 15, residue 17229. -/
theorem bounds_15_17229 : exactInterval 15 17229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17229 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17229) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17229 : oddCount 17229 15 = 7 ∧ acceleratedOrbit 15 17229 = 1151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17229 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17229) = 3 ^ 7 * m + 1151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17229.1, data_15_17229.2]

/-- Complete interval computation for depth 15, residue 17230. -/
theorem bounds_15_17230 : exactInterval 15 17230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17230 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17230) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17230 : oddCount 17230 15 = 8 ∧ acceleratedOrbit 15 17230 = 3451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17230 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17230) = 3 ^ 8 * m + 3451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17230.1, data_15_17230.2]

/-- Complete interval computation for depth 15, residue 17231. -/
theorem bounds_15_17231 : exactInterval 15 17231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17231 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17231) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17231 : oddCount 17231 15 = 8 ∧ acceleratedOrbit 15 17231 = 3451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17231 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17231) = 3 ^ 8 * m + 3451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17231.1, data_15_17231.2]

/-- Complete interval computation for depth 15, residue 17232. -/
theorem bounds_15_17232 : exactInterval 15 17232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17232 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17232) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17232 : oddCount 17232 15 = 4 ∧ acceleratedOrbit 15 17232 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17232 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17232) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17232.1, data_15_17232.2]

/-- Complete interval computation for depth 15, residue 17233. -/
theorem bounds_15_17233 : exactInterval 15 17233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17233 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17233) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17233 : oddCount 17233 15 = 10 ∧ acceleratedOrbit 15 17233 = 31063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17233 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17233) = 3 ^ 10 * m + 31063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17233.1, data_15_17233.2]

/-- Complete interval computation for depth 15, residue 17234. -/
theorem bounds_15_17234 : exactInterval 15 17234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17234 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17234) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17234 : oddCount 17234 15 = 10 ∧ acceleratedOrbit 15 17234 = 31063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17234 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17234) = 3 ^ 10 * m + 31063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17234.1, data_15_17234.2]

end Collatz.Research.PassageAtlas.Batch0526
