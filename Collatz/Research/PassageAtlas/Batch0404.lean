import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0404

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 13205. -/
theorem bounds_15_13205 : exactInterval 15 13205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13205 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13205) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13205 : oddCount 13205 15 = 7 ∧ acceleratedOrbit 15 13205 = 884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13205 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13205) = 3 ^ 7 * m + 884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13205.1, data_15_13205.2]

/-- Complete interval computation for depth 15, residue 13206. -/
theorem bounds_15_13206 : exactInterval 15 13206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13206 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13206) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13206 : oddCount 13206 15 = 5 ∧ acceleratedOrbit 15 13206 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13206 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13206) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13206.1, data_15_13206.2]

/-- Complete interval computation for depth 15, residue 13207. -/
theorem bounds_15_13207 : exactInterval 15 13207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13207 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13207) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13207 : oddCount 13207 15 = 5 ∧ acceleratedOrbit 15 13207 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13207 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13207) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13207.1, data_15_13207.2]

/-- Complete interval computation for depth 15, residue 13208. -/
theorem bounds_15_13208 : exactInterval 15 13208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13208 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13208) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13208 : oddCount 13208 15 = 7 ∧ acceleratedOrbit 15 13208 = 884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13208 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13208) = 3 ^ 7 * m + 884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13208.1, data_15_13208.2]

/-- Complete interval computation for depth 15, residue 13209. -/
theorem bounds_15_13209 : exactInterval 15 13209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13209 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13209) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13209 : oddCount 13209 15 = 5 ∧ acceleratedOrbit 15 13209 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13209 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13209) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13209.1, data_15_13209.2]

/-- Complete interval computation for depth 15, residue 13210. -/
theorem bounds_15_13210 : exactInterval 15 13210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13210 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13210) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13210 : oddCount 13210 15 = 7 ∧ acceleratedOrbit 15 13210 = 884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13210 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13210) = 3 ^ 7 * m + 884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13210.1, data_15_13210.2]

/-- Complete interval computation for depth 15, residue 13211. -/
theorem bounds_15_13211 : exactInterval 15 13211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13211 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13211) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13211 : oddCount 13211 15 = 10 ∧ acceleratedOrbit 15 13211 = 23813 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13211 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13211) = 3 ^ 10 * m + 23813 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13211.1, data_15_13211.2]

/-- Complete interval computation for depth 15, residue 13212. -/
theorem bounds_15_13212 : exactInterval 15 13212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13212 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13212) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13212 : oddCount 13212 15 = 9 ∧ acceleratedOrbit 15 13212 = 7940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13212 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13212) = 3 ^ 9 * m + 7940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13212.1, data_15_13212.2]

/-- Complete interval computation for depth 15, residue 13213. -/
theorem bounds_15_13213 : exactInterval 15 13213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13213 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13213) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13213 : oddCount 13213 15 = 9 ∧ acceleratedOrbit 15 13213 = 7940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13213 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13213) = 3 ^ 9 * m + 7940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13213.1, data_15_13213.2]

/-- Complete interval computation for depth 15, residue 13214. -/
theorem bounds_15_13214 : exactInterval 15 13214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13214 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13214) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13214 : oddCount 13214 15 = 9 ∧ acceleratedOrbit 15 13214 = 7940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13214 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13214) = 3 ^ 9 * m + 7940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13214.1, data_15_13214.2]

/-- Complete interval computation for depth 15, residue 13215. -/
theorem bounds_15_13215 : exactInterval 15 13215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13215 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13215) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13215 : oddCount 13215 15 = 9 ∧ acceleratedOrbit 15 13215 = 7939 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13215 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13215) = 3 ^ 9 * m + 7939 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13215.1, data_15_13215.2]

/-- Complete interval computation for depth 15, residue 13216. -/
theorem bounds_15_13216 : exactInterval 15 13216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13216 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13216) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13216 : oddCount 13216 15 = 7 ∧ acceleratedOrbit 15 13216 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13216 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13216) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13216.1, data_15_13216.2]

/-- Complete interval computation for depth 15, residue 13217. -/
theorem bounds_15_13217 : exactInterval 15 13217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13217 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13217) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13217 : oddCount 13217 15 = 8 ∧ acceleratedOrbit 15 13217 = 2648 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13217 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13217) = 3 ^ 8 * m + 2648 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13217.1, data_15_13217.2]

/-- Complete interval computation for depth 15, residue 13218. -/
theorem bounds_15_13218 : exactInterval 15 13218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13218 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13218) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13218 : oddCount 13218 15 = 7 ∧ acceleratedOrbit 15 13218 = 884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13218 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13218) = 3 ^ 7 * m + 884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13218.1, data_15_13218.2]

/-- Complete interval computation for depth 15, residue 13219. -/
theorem bounds_15_13219 : exactInterval 15 13219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13219 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13219) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13219 : oddCount 13219 15 = 7 ∧ acceleratedOrbit 15 13219 = 884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13219 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13219) = 3 ^ 7 * m + 884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13219.1, data_15_13219.2]

/-- Complete interval computation for depth 15, residue 13220. -/
theorem bounds_15_13220 : exactInterval 15 13220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13220 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13220) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13220 : oddCount 13220 15 = 7 ∧ acceleratedOrbit 15 13220 = 883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13220 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13220) = 3 ^ 7 * m + 883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13220.1, data_15_13220.2]

/-- Complete interval computation for depth 15, residue 13221. -/
theorem bounds_15_13221 : exactInterval 15 13221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13221 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13221) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13221 : oddCount 13221 15 = 7 ∧ acceleratedOrbit 15 13221 = 883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13221 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13221) = 3 ^ 7 * m + 883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13221.1, data_15_13221.2]

/-- Complete interval computation for depth 15, residue 13222. -/
theorem bounds_15_13222 : exactInterval 15 13222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13222 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13222) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13222 : oddCount 13222 15 = 7 ∧ acceleratedOrbit 15 13222 = 883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13222 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13222) = 3 ^ 7 * m + 883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13222.1, data_15_13222.2]

/-- Complete interval computation for depth 15, residue 13223. -/
theorem bounds_15_13223 : exactInterval 15 13223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13223 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13223) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13223 : oddCount 13223 15 = 8 ∧ acceleratedOrbit 15 13223 = 2648 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13223 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13223) = 3 ^ 8 * m + 2648 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13223.1, data_15_13223.2]

/-- Complete interval computation for depth 15, residue 13224. -/
theorem bounds_15_13224 : exactInterval 15 13224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13224 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13224) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13224 : oddCount 13224 15 = 7 ∧ acceleratedOrbit 15 13224 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13224 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13224) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13224.1, data_15_13224.2]

/-- Complete interval computation for depth 15, residue 13225. -/
theorem bounds_15_13225 : exactInterval 15 13225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13225 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13225) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13225 : oddCount 13225 15 = 9 ∧ acceleratedOrbit 15 13225 = 7945 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13225 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13225) = 3 ^ 9 * m + 7945 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13225.1, data_15_13225.2]

/-- Complete interval computation for depth 15, residue 13226. -/
theorem bounds_15_13226 : exactInterval 15 13226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13226 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13226) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13226 : oddCount 13226 15 = 7 ∧ acceleratedOrbit 15 13226 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13226 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13226) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13226.1, data_15_13226.2]

/-- Complete interval computation for depth 15, residue 13227. -/
theorem bounds_15_13227 : exactInterval 15 13227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13227 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13227) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13227 : oddCount 13227 15 = 7 ∧ acceleratedOrbit 15 13227 = 883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13227 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13227) = 3 ^ 7 * m + 883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13227.1, data_15_13227.2]

/-- Complete interval computation for depth 15, residue 13228. -/
theorem bounds_15_13228 : exactInterval 15 13228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13228 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13228) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13228 : oddCount 13228 15 = 9 ∧ acceleratedOrbit 15 13228 = 7951 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13228 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13228) = 3 ^ 9 * m + 7951 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13228.1, data_15_13228.2]

/-- Complete interval computation for depth 15, residue 13229. -/
theorem bounds_15_13229 : exactInterval 15 13229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13229 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13229) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13229 : oddCount 13229 15 = 9 ∧ acceleratedOrbit 15 13229 = 7951 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13229 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13229) = 3 ^ 9 * m + 7951 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13229.1, data_15_13229.2]

/-- Complete interval computation for depth 15, residue 13230. -/
theorem bounds_15_13230 : exactInterval 15 13230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13230 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13230) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13230 : oddCount 13230 15 = 9 ∧ acceleratedOrbit 15 13230 = 7951 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13230 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13230) = 3 ^ 9 * m + 7951 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13230.1, data_15_13230.2]

/-- Complete interval computation for depth 15, residue 13231. -/
theorem bounds_15_13231 : exactInterval 15 13231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13231 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13231) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13231 : oddCount 13231 15 = 7 ∧ acceleratedOrbit 15 13231 = 884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13231 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13231) = 3 ^ 7 * m + 884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13231.1, data_15_13231.2]

/-- Complete interval computation for depth 15, residue 13232. -/
theorem bounds_15_13232 : exactInterval 15 13232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13232 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13232) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13232 : oddCount 13232 15 = 6 ∧ acceleratedOrbit 15 13232 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13232 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13232) = 3 ^ 6 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13232.1, data_15_13232.2]

/-- Complete interval computation for depth 15, residue 13233. -/
theorem bounds_15_13233 : exactInterval 15 13233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13233 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13233) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13233 : oddCount 13233 15 = 6 ∧ acceleratedOrbit 15 13233 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13233 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13233) = 3 ^ 6 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13233.1, data_15_13233.2]

/-- Complete interval computation for depth 15, residue 13234. -/
theorem bounds_15_13234 : exactInterval 15 13234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13234 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13234) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13234 : oddCount 13234 15 = 6 ∧ acceleratedOrbit 15 13234 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13234 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13234) = 3 ^ 6 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13234.1, data_15_13234.2]

/-- Complete interval computation for depth 15, residue 13235. -/
theorem bounds_15_13235 : exactInterval 15 13235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13235 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13235) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13235 : oddCount 13235 15 = 6 ∧ acceleratedOrbit 15 13235 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13235 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13235) = 3 ^ 6 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13235.1, data_15_13235.2]

/-- Complete interval computation for depth 15, residue 13236. -/
theorem bounds_15_13236 : exactInterval 15 13236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13236 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13236) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13236 : oddCount 13236 15 = 6 ∧ acceleratedOrbit 15 13236 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13236 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13236) = 3 ^ 6 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13236.1, data_15_13236.2]

/-- Complete interval computation for depth 15, residue 13237. -/
theorem bounds_15_13237 : exactInterval 15 13237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13237 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13237) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13237 : oddCount 13237 15 = 6 ∧ acceleratedOrbit 15 13237 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13237 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13237) = 3 ^ 6 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13237.1, data_15_13237.2]

end Collatz.Research.PassageAtlas.Batch0404
