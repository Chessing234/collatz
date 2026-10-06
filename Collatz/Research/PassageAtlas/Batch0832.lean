import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0832

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 27230. -/
theorem bounds_15_27230 : exactInterval 15 27230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27230 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27230) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27230 : oddCount 27230 15 = 10 ∧ acceleratedOrbit 15 27230 = 49076 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27230 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27230) = 3 ^ 10 * m + 49076 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27230.1, data_15_27230.2]

/-- Complete interval computation for depth 15, residue 27231. -/
theorem bounds_15_27231 : exactInterval 15 27231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27231 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27231) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27231 : oddCount 27231 15 = 10 ∧ acceleratedOrbit 15 27231 = 49076 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27231 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27231) = 3 ^ 10 * m + 49076 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27231.1, data_15_27231.2]

/-- Complete interval computation for depth 15, residue 27232. -/
theorem bounds_15_27232 : exactInterval 15 27232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27232 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27232) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27232 : oddCount 27232 15 = 7 ∧ acceleratedOrbit 15 27232 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27232 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27232) = 3 ^ 7 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27232.1, data_15_27232.2]

/-- Complete interval computation for depth 15, residue 27233. -/
theorem bounds_15_27233 : exactInterval 15 27233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27233 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27233) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27233 : oddCount 27233 15 = 10 ∧ acceleratedOrbit 15 27233 = 49085 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27233 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27233) = 3 ^ 10 * m + 49085 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27233.1, data_15_27233.2]

/-- Complete interval computation for depth 15, residue 27234. -/
theorem bounds_15_27234 : exactInterval 15 27234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27234 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27234) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27234 : oddCount 27234 15 = 7 ∧ acceleratedOrbit 15 27234 = 1819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27234 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27234) = 3 ^ 7 * m + 1819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27234.1, data_15_27234.2]

/-- Complete interval computation for depth 15, residue 27235. -/
theorem bounds_15_27235 : exactInterval 15 27235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27235 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27235) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27235 : oddCount 27235 15 = 7 ∧ acceleratedOrbit 15 27235 = 1819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27235 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27235) = 3 ^ 7 * m + 1819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27235.1, data_15_27235.2]

/-- Complete interval computation for depth 15, residue 27236. -/
theorem bounds_15_27236 : exactInterval 15 27236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27236 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27236) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27236 : oddCount 27236 15 = 7 ∧ acceleratedOrbit 15 27236 = 1819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27236 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27236) = 3 ^ 7 * m + 1819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27236.1, data_15_27236.2]

/-- Complete interval computation for depth 15, residue 27237. -/
theorem bounds_15_27237 : exactInterval 15 27237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27237 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27237) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27237 : oddCount 27237 15 = 7 ∧ acceleratedOrbit 15 27237 = 1819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27237 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27237) = 3 ^ 7 * m + 1819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27237.1, data_15_27237.2]

/-- Complete interval computation for depth 15, residue 27238. -/
theorem bounds_15_27238 : exactInterval 15 27238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27238 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27238) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27238 : oddCount 27238 15 = 7 ∧ acceleratedOrbit 15 27238 = 1819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27238 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27238) = 3 ^ 7 * m + 1819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27238.1, data_15_27238.2]

/-- Complete interval computation for depth 15, residue 27239. -/
theorem bounds_15_27239 : exactInterval 15 27239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27239 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27239) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27239 : oddCount 27239 15 = 9 ∧ acceleratedOrbit 15 27239 = 16363 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27239 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27239) = 3 ^ 9 * m + 16363 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27239.1, data_15_27239.2]

/-- Complete interval computation for depth 15, residue 27240. -/
theorem bounds_15_27240 : exactInterval 15 27240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27240 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27240) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27240 : oddCount 27240 15 = 7 ∧ acceleratedOrbit 15 27240 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27240 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27240) = 3 ^ 7 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27240.1, data_15_27240.2]

/-- Complete interval computation for depth 15, residue 27241. -/
theorem bounds_15_27241 : exactInterval 15 27241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27241 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27241) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27241 : oddCount 27241 15 = 8 ∧ acceleratedOrbit 15 27241 = 5455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27241 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27241) = 3 ^ 8 * m + 5455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27241.1, data_15_27241.2]

/-- Complete interval computation for depth 15, residue 27242. -/
theorem bounds_15_27242 : exactInterval 15 27242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27242 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27242) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27242 : oddCount 27242 15 = 7 ∧ acceleratedOrbit 15 27242 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27242 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27242) = 3 ^ 7 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27242.1, data_15_27242.2]

/-- Complete interval computation for depth 15, residue 27243. -/
theorem bounds_15_27243 : exactInterval 15 27243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27243 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27243) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27243 : oddCount 27243 15 = 8 ∧ acceleratedOrbit 15 27243 = 5456 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27243 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27243) = 3 ^ 8 * m + 5456 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27243.1, data_15_27243.2]

/-- Complete interval computation for depth 15, residue 27244. -/
theorem bounds_15_27244 : exactInterval 15 27244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27244 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27244) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27244 : oddCount 27244 15 = 10 ∧ acceleratedOrbit 15 27244 = 49106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27244 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27244) = 3 ^ 10 * m + 49106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27244.1, data_15_27244.2]

/-- Complete interval computation for depth 15, residue 27245. -/
theorem bounds_15_27245 : exactInterval 15 27245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27245 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27245) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27245 : oddCount 27245 15 = 10 ∧ acceleratedOrbit 15 27245 = 49106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27245 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27245) = 3 ^ 10 * m + 49106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27245.1, data_15_27245.2]

/-- Complete interval computation for depth 15, residue 27246. -/
theorem bounds_15_27246 : exactInterval 15 27246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27246 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27246) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27246 : oddCount 27246 15 = 10 ∧ acceleratedOrbit 15 27246 = 49106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27246 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27246) = 3 ^ 10 * m + 49106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27246.1, data_15_27246.2]

/-- Complete interval computation for depth 15, residue 27247. -/
theorem bounds_15_27247 : exactInterval 15 27247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27247 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27247) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27247 : oddCount 27247 15 = 10 ∧ acceleratedOrbit 15 27247 = 49103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27247 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27247) = 3 ^ 10 * m + 49103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27247.1, data_15_27247.2]

/-- Complete interval computation for depth 15, residue 27248. -/
theorem bounds_15_27248 : exactInterval 15 27248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27248 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27248) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27248 : oddCount 27248 15 = 7 ∧ acceleratedOrbit 15 27248 = 1820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27248 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27248) = 3 ^ 7 * m + 1820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27248.1, data_15_27248.2]

/-- Complete interval computation for depth 15, residue 27249. -/
theorem bounds_15_27249 : exactInterval 15 27249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27249 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27249) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27249 : oddCount 27249 15 = 7 ∧ acceleratedOrbit 15 27249 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27249 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27249) = 3 ^ 7 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27249.1, data_15_27249.2]

/-- Complete interval computation for depth 15, residue 27250. -/
theorem bounds_15_27250 : exactInterval 15 27250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27250 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27250) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27250 : oddCount 27250 15 = 9 ∧ acceleratedOrbit 15 27250 = 16372 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27250 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27250) = 3 ^ 9 * m + 16372 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27250.1, data_15_27250.2]

/-- Complete interval computation for depth 15, residue 27251. -/
theorem bounds_15_27251 : exactInterval 15 27251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27251 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27251) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27251 : oddCount 27251 15 = 9 ∧ acceleratedOrbit 15 27251 = 16372 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27251 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27251) = 3 ^ 9 * m + 16372 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27251.1, data_15_27251.2]

/-- Complete interval computation for depth 15, residue 27252. -/
theorem bounds_15_27252 : exactInterval 15 27252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27252 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27252) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27252 : oddCount 27252 15 = 7 ∧ acceleratedOrbit 15 27252 = 1820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27252 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27252) = 3 ^ 7 * m + 1820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27252.1, data_15_27252.2]

/-- Complete interval computation for depth 15, residue 27253. -/
theorem bounds_15_27253 : exactInterval 15 27253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27253 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27253) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27253 : oddCount 27253 15 = 7 ∧ acceleratedOrbit 15 27253 = 1820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27253 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27253) = 3 ^ 7 * m + 1820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27253.1, data_15_27253.2]

/-- Complete interval computation for depth 15, residue 27254. -/
theorem bounds_15_27254 : exactInterval 15 27254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27254 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27254) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27254 : oddCount 27254 15 = 6 ∧ acceleratedOrbit 15 27254 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27254 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27254) = 3 ^ 6 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27254.1, data_15_27254.2]

/-- Complete interval computation for depth 15, residue 27255. -/
theorem bounds_15_27255 : exactInterval 15 27255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27255 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27255) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27255 : oddCount 27255 15 = 6 ∧ acceleratedOrbit 15 27255 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27255 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27255) = 3 ^ 6 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27255.1, data_15_27255.2]

/-- Complete interval computation for depth 15, residue 27256. -/
theorem bounds_15_27256 : exactInterval 15 27256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27256 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27256) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27256 : oddCount 27256 15 = 7 ∧ acceleratedOrbit 15 27256 = 1820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27256 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27256) = 3 ^ 7 * m + 1820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27256.1, data_15_27256.2]

/-- Complete interval computation for depth 15, residue 27257. -/
theorem bounds_15_27257 : exactInterval 15 27257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27257 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27257) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27257 : oddCount 27257 15 = 9 ∧ acceleratedOrbit 15 27257 = 16375 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27257 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27257) = 3 ^ 9 * m + 16375 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27257.1, data_15_27257.2]

/-- Complete interval computation for depth 15, residue 27258. -/
theorem bounds_15_27258 : exactInterval 15 27258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27258 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27258) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27258 : oddCount 27258 15 = 7 ∧ acceleratedOrbit 15 27258 = 1820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27258 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27258) = 3 ^ 7 * m + 1820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27258.1, data_15_27258.2]

/-- Complete interval computation for depth 15, residue 27259. -/
theorem bounds_15_27259 : exactInterval 15 27259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27259 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27259) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27259 : oddCount 27259 15 = 7 ∧ acceleratedOrbit 15 27259 = 1820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27259 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27259) = 3 ^ 7 * m + 1820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27259.1, data_15_27259.2]

/-- Complete interval computation for depth 15, residue 27260. -/
theorem bounds_15_27260 : exactInterval 15 27260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27260 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27260) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27260 : oddCount 27260 15 = 8 ∧ acceleratedOrbit 15 27260 = 5459 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27260 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27260) = 3 ^ 8 * m + 5459 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27260.1, data_15_27260.2]

/-- Complete interval computation for depth 15, residue 27261. -/
theorem bounds_15_27261 : exactInterval 15 27261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27261 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27261) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27261 : oddCount 27261 15 = 8 ∧ acceleratedOrbit 15 27261 = 5459 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27261 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27261) = 3 ^ 8 * m + 5459 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27261.1, data_15_27261.2]

end Collatz.Research.PassageAtlas.Batch0832
