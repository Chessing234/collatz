import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0252

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 8224. -/
theorem bounds_15_8224 : exactInterval 15 8224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8224 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8224) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8224 : oddCount 8224 15 = 5 ∧ acceleratedOrbit 15 8224 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8224 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8224) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8224.1, data_15_8224.2]

/-- Complete interval computation for depth 15, residue 8225. -/
theorem bounds_15_8225 : exactInterval 15 8225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8225 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8225) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8225 : oddCount 8225 15 = 8 ∧ acceleratedOrbit 15 8225 = 1648 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8225 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8225) = 3 ^ 8 * m + 1648 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8225.1, data_15_8225.2]

/-- Complete interval computation for depth 15, residue 8226. -/
theorem bounds_15_8226 : exactInterval 15 8226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8226 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8226) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8226 : oddCount 8226 15 = 6 ∧ acceleratedOrbit 15 8226 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8226 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8226) = 3 ^ 6 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8226.1, data_15_8226.2]

/-- Complete interval computation for depth 15, residue 8227. -/
theorem bounds_15_8227 : exactInterval 15 8227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8227 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8227) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8227 : oddCount 8227 15 = 6 ∧ acceleratedOrbit 15 8227 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8227 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8227) = 3 ^ 6 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8227.1, data_15_8227.2]

/-- Complete interval computation for depth 15, residue 8228. -/
theorem bounds_15_8228 : exactInterval 15 8228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8228 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8228) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8228 : oddCount 8228 15 = 7 ∧ acceleratedOrbit 15 8228 = 550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8228 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8228) = 3 ^ 7 * m + 550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8228.1, data_15_8228.2]

/-- Complete interval computation for depth 15, residue 8229. -/
theorem bounds_15_8229 : exactInterval 15 8229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8229 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8229) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8229 : oddCount 8229 15 = 7 ∧ acceleratedOrbit 15 8229 = 550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8229 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8229) = 3 ^ 7 * m + 550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8229.1, data_15_8229.2]

/-- Complete interval computation for depth 15, residue 8230. -/
theorem bounds_15_8230 : exactInterval 15 8230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8230 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8230) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8230 : oddCount 8230 15 = 7 ∧ acceleratedOrbit 15 8230 = 550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8230 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8230) = 3 ^ 7 * m + 550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8230.1, data_15_8230.2]

/-- Complete interval computation for depth 15, residue 8231. -/
theorem bounds_15_8231 : exactInterval 15 8231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8231 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8231) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8231 : oddCount 8231 15 = 8 ∧ acceleratedOrbit 15 8231 = 1649 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8231 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8231) = 3 ^ 8 * m + 1649 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8231.1, data_15_8231.2]

/-- Complete interval computation for depth 15, residue 8232. -/
theorem bounds_15_8232 : exactInterval 15 8232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8232 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8232) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8232 : oddCount 8232 15 = 5 ∧ acceleratedOrbit 15 8232 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8232 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8232) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8232.1, data_15_8232.2]

/-- Complete interval computation for depth 15, residue 8233. -/
theorem bounds_15_8233 : exactInterval 15 8233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8233 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8233) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8233 : oddCount 8233 15 = 10 ∧ acceleratedOrbit 15 8233 = 14840 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8233 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8233) = 3 ^ 10 * m + 14840 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8233.1, data_15_8233.2]

/-- Complete interval computation for depth 15, residue 8234. -/
theorem bounds_15_8234 : exactInterval 15 8234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8234 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8234) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8234 : oddCount 8234 15 = 5 ∧ acceleratedOrbit 15 8234 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8234 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8234) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8234.1, data_15_8234.2]

/-- Complete interval computation for depth 15, residue 8235. -/
theorem bounds_15_8235 : exactInterval 15 8235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8235 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8235) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8235 : oddCount 8235 15 = 7 ∧ acceleratedOrbit 15 8235 = 550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8235 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8235) = 3 ^ 7 * m + 550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8235.1, data_15_8235.2]

/-- Complete interval computation for depth 15, residue 8236. -/
theorem bounds_15_8236 : exactInterval 15 8236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8236 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8236) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8236 : oddCount 8236 15 = 6 ∧ acceleratedOrbit 15 8236 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8236 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8236) = 3 ^ 6 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8236.1, data_15_8236.2]

/-- Complete interval computation for depth 15, residue 8237. -/
theorem bounds_15_8237 : exactInterval 15 8237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8237 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8237) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8237 : oddCount 8237 15 = 6 ∧ acceleratedOrbit 15 8237 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8237 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8237) = 3 ^ 6 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8237.1, data_15_8237.2]

/-- Complete interval computation for depth 15, residue 8238. -/
theorem bounds_15_8238 : exactInterval 15 8238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8238 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8238) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8238 : oddCount 8238 15 = 6 ∧ acceleratedOrbit 15 8238 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8238 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8238) = 3 ^ 6 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8238.1, data_15_8238.2]

/-- Complete interval computation for depth 15, residue 8239. -/
theorem bounds_15_8239 : exactInterval 15 8239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8239 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8239) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8239 : oddCount 8239 15 = 12 ∧ acceleratedOrbit 15 8239 = 133649 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8239 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8239) = 3 ^ 12 * m + 133649 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8239.1, data_15_8239.2]

/-- Complete interval computation for depth 15, residue 8240. -/
theorem bounds_15_8240 : exactInterval 15 8240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8240 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8240) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8240 : oddCount 8240 15 = 5 ∧ acceleratedOrbit 15 8240 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8240 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8240) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8240.1, data_15_8240.2]

/-- Complete interval computation for depth 15, residue 8241. -/
theorem bounds_15_8241 : exactInterval 15 8241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8241 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8241) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8241 : oddCount 8241 15 = 7 ∧ acceleratedOrbit 15 8241 = 551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8241 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8241) = 3 ^ 7 * m + 551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8241.1, data_15_8241.2]

/-- Complete interval computation for depth 15, residue 8242. -/
theorem bounds_15_8242 : exactInterval 15 8242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8242 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8242) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8242 : oddCount 8242 15 = 7 ∧ acceleratedOrbit 15 8242 = 551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8242 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8242) = 3 ^ 7 * m + 551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8242.1, data_15_8242.2]

/-- Complete interval computation for depth 15, residue 8243. -/
theorem bounds_15_8243 : exactInterval 15 8243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8243 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8243) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8243 : oddCount 8243 15 = 7 ∧ acceleratedOrbit 15 8243 = 551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8243 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8243) = 3 ^ 7 * m + 551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8243.1, data_15_8243.2]

/-- Complete interval computation for depth 15, residue 8244. -/
theorem bounds_15_8244 : exactInterval 15 8244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8244 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8244) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8244 : oddCount 8244 15 = 5 ∧ acceleratedOrbit 15 8244 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8244 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8244) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8244.1, data_15_8244.2]

/-- Complete interval computation for depth 15, residue 8245. -/
theorem bounds_15_8245 : exactInterval 15 8245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8245 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8245) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8245 : oddCount 8245 15 = 5 ∧ acceleratedOrbit 15 8245 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8245 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8245) = 3 ^ 5 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8245.1, data_15_8245.2]

/-- Complete interval computation for depth 15, residue 8246. -/
theorem bounds_15_8246 : exactInterval 15 8246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8246 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8246) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8246 : oddCount 8246 15 = 9 ∧ acceleratedOrbit 15 8246 = 4955 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8246 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8246) = 3 ^ 9 * m + 4955 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8246.1, data_15_8246.2]

/-- Complete interval computation for depth 15, residue 8247. -/
theorem bounds_15_8247 : exactInterval 15 8247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8247 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8247) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8247 : oddCount 8247 15 = 9 ∧ acceleratedOrbit 15 8247 = 4955 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8247 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8247) = 3 ^ 9 * m + 4955 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8247.1, data_15_8247.2]

/-- Complete interval computation for depth 15, residue 8248. -/
theorem bounds_15_8248 : exactInterval 15 8248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8248 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8248) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8248 : oddCount 8248 15 = 6 ∧ acceleratedOrbit 15 8248 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8248 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8248) = 3 ^ 6 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8248.1, data_15_8248.2]

/-- Complete interval computation for depth 15, residue 8249. -/
theorem bounds_15_8249 : exactInterval 15 8249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8249 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8249) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8249 : oddCount 8249 15 = 7 ∧ acceleratedOrbit 15 8249 = 551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8249 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8249) = 3 ^ 7 * m + 551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8249.1, data_15_8249.2]

/-- Complete interval computation for depth 15, residue 8250. -/
theorem bounds_15_8250 : exactInterval 15 8250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8250 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8250) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8250 : oddCount 8250 15 = 6 ∧ acceleratedOrbit 15 8250 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8250 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8250) = 3 ^ 6 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8250.1, data_15_8250.2]

/-- Complete interval computation for depth 15, residue 8251. -/
theorem bounds_15_8251 : exactInterval 15 8251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8251 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8251) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8251 : oddCount 8251 15 = 7 ∧ acceleratedOrbit 15 8251 = 551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8251 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8251) = 3 ^ 7 * m + 551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8251.1, data_15_8251.2]

/-- Complete interval computation for depth 15, residue 8252. -/
theorem bounds_15_8252 : exactInterval 15 8252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8252 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8252) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8252 : oddCount 8252 15 = 6 ∧ acceleratedOrbit 15 8252 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8252 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8252) = 3 ^ 6 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8252.1, data_15_8252.2]

/-- Complete interval computation for depth 15, residue 8253. -/
theorem bounds_15_8253 : exactInterval 15 8253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8253 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8253) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8253 : oddCount 8253 15 = 6 ∧ acceleratedOrbit 15 8253 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8253 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8253) = 3 ^ 6 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8253.1, data_15_8253.2]

/-- Complete interval computation for depth 15, residue 8254. -/
theorem bounds_15_8254 : exactInterval 15 8254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8254 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8254) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8254 : oddCount 8254 15 = 10 ∧ acceleratedOrbit 15 8254 = 14879 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8254 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8254) = 3 ^ 10 * m + 14879 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8254.1, data_15_8254.2]

/-- Complete interval computation for depth 15, residue 8255. -/
theorem bounds_15_8255 : exactInterval 15 8255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8255 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8255) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8255 : oddCount 8255 15 = 10 ∧ acceleratedOrbit 15 8255 = 14879 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8255 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8255) = 3 ^ 10 * m + 14879 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8255.1, data_15_8255.2]

/-- Complete interval computation for depth 15, residue 8256. -/
theorem bounds_15_8256 : exactInterval 15 8256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8256 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8256) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8256 : oddCount 8256 15 = 6 ∧ acceleratedOrbit 15 8256 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8256 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8256) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8256.1, data_15_8256.2]

end Collatz.Research.PassageAtlas.Batch0252
