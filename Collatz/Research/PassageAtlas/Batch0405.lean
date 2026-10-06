import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0405

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 13238. -/
theorem bounds_15_13238 : exactInterval 15 13238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13238 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13238) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13238 : oddCount 13238 15 = 7 ∧ acceleratedOrbit 15 13238 = 884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13238 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13238) = 3 ^ 7 * m + 884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13238.1, data_15_13238.2]

/-- Complete interval computation for depth 15, residue 13239. -/
theorem bounds_15_13239 : exactInterval 15 13239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13239 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13239) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13239 : oddCount 13239 15 = 7 ∧ acceleratedOrbit 15 13239 = 884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13239 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13239) = 3 ^ 7 * m + 884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13239.1, data_15_13239.2]

/-- Complete interval computation for depth 15, residue 13240. -/
theorem bounds_15_13240 : exactInterval 15 13240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13240 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13240) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13240 : oddCount 13240 15 = 6 ∧ acceleratedOrbit 15 13240 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13240 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13240) = 3 ^ 6 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13240.1, data_15_13240.2]

/-- Complete interval computation for depth 15, residue 13241. -/
theorem bounds_15_13241 : exactInterval 15 13241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13241 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13241) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13241 : oddCount 13241 15 = 9 ∧ acceleratedOrbit 15 13241 = 7958 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13241 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13241) = 3 ^ 9 * m + 7958 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13241.1, data_15_13241.2]

/-- Complete interval computation for depth 15, residue 13242. -/
theorem bounds_15_13242 : exactInterval 15 13242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13242 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13242) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13242 : oddCount 13242 15 = 6 ∧ acceleratedOrbit 15 13242 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13242 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13242) = 3 ^ 6 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13242.1, data_15_13242.2]

/-- Complete interval computation for depth 15, residue 13243. -/
theorem bounds_15_13243 : exactInterval 15 13243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13243 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13243) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13243 : oddCount 13243 15 = 9 ∧ acceleratedOrbit 15 13243 = 7958 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13243 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13243) = 3 ^ 9 * m + 7958 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13243.1, data_15_13243.2]

/-- Complete interval computation for depth 15, residue 13244. -/
theorem bounds_15_13244 : exactInterval 15 13244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13244 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13244) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13244 : oddCount 13244 15 = 11 ∧ acceleratedOrbit 15 13244 = 71624 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13244 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13244) = 3 ^ 11 * m + 71624 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13244.1, data_15_13244.2]

/-- Complete interval computation for depth 15, residue 13245. -/
theorem bounds_15_13245 : exactInterval 15 13245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13245 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13245) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13245 : oddCount 13245 15 = 11 ∧ acceleratedOrbit 15 13245 = 71624 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13245 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13245) = 3 ^ 11 * m + 71624 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13245.1, data_15_13245.2]

/-- Complete interval computation for depth 15, residue 13246. -/
theorem bounds_15_13246 : exactInterval 15 13246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13246 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13246) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13246 : oddCount 13246 15 = 11 ∧ acceleratedOrbit 15 13246 = 71624 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13246 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13246) = 3 ^ 11 * m + 71624 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13246.1, data_15_13246.2]

/-- Complete interval computation for depth 15, residue 13247. -/
theorem bounds_15_13247 : exactInterval 15 13247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13247 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13247) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13247 : oddCount 13247 15 = 11 ∧ acceleratedOrbit 15 13247 = 71621 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13247 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13247) = 3 ^ 11 * m + 71621 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13247.1, data_15_13247.2]

/-- Complete interval computation for depth 15, residue 13248. -/
theorem bounds_15_13248 : exactInterval 15 13248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13248 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13248) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13248 : oddCount 13248 15 = 7 ∧ acceleratedOrbit 15 13248 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13248 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13248) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13248.1, data_15_13248.2]

/-- Complete interval computation for depth 15, residue 13249. -/
theorem bounds_15_13249 : exactInterval 15 13249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13249 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13249) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13249 : oddCount 13249 15 = 9 ∧ acceleratedOrbit 15 13249 = 7964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13249 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13249) = 3 ^ 9 * m + 7964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13249.1, data_15_13249.2]

/-- Complete interval computation for depth 15, residue 13250. -/
theorem bounds_15_13250 : exactInterval 15 13250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13250 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13250) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13250 : oddCount 13250 15 = 9 ∧ acceleratedOrbit 15 13250 = 7964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13250 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13250) = 3 ^ 9 * m + 7964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13250.1, data_15_13250.2]

/-- Complete interval computation for depth 15, residue 13251. -/
theorem bounds_15_13251 : exactInterval 15 13251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13251 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13251) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13251 : oddCount 13251 15 = 9 ∧ acceleratedOrbit 15 13251 = 7964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13251 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13251) = 3 ^ 9 * m + 7964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13251.1, data_15_13251.2]

/-- Complete interval computation for depth 15, residue 13252. -/
theorem bounds_15_13252 : exactInterval 15 13252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13252 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13252) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13252 : oddCount 13252 15 = 7 ∧ acceleratedOrbit 15 13252 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13252 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13252) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13252.1, data_15_13252.2]

/-- Complete interval computation for depth 15, residue 13253. -/
theorem bounds_15_13253 : exactInterval 15 13253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13253 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13253) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13253 : oddCount 13253 15 = 7 ∧ acceleratedOrbit 15 13253 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13253 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13253) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13253.1, data_15_13253.2]

/-- Complete interval computation for depth 15, residue 13254. -/
theorem bounds_15_13254 : exactInterval 15 13254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13254 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13254) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13254 : oddCount 13254 15 = 7 ∧ acceleratedOrbit 15 13254 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13254 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13254) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13254.1, data_15_13254.2]

/-- Complete interval computation for depth 15, residue 13255. -/
theorem bounds_15_13255 : exactInterval 15 13255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13255 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13255) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13255 : oddCount 13255 15 = 10 ∧ acceleratedOrbit 15 13255 = 23890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13255 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13255) = 3 ^ 10 * m + 23890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13255.1, data_15_13255.2]

/-- Complete interval computation for depth 15, residue 13256. -/
theorem bounds_15_13256 : exactInterval 15 13256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13256 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13256) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13256 : oddCount 13256 15 = 7 ∧ acceleratedOrbit 15 13256 = 886 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13256 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13256) = 3 ^ 7 * m + 886 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13256.1, data_15_13256.2]

/-- Complete interval computation for depth 15, residue 13257. -/
theorem bounds_15_13257 : exactInterval 15 13257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13257 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13257) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13257 : oddCount 13257 15 = 6 ∧ acceleratedOrbit 15 13257 = 295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13257 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13257) = 3 ^ 6 * m + 295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13257.1, data_15_13257.2]

/-- Complete interval computation for depth 15, residue 13258. -/
theorem bounds_15_13258 : exactInterval 15 13258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13258 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13258) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13258 : oddCount 13258 15 = 7 ∧ acceleratedOrbit 15 13258 = 886 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13258 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13258) = 3 ^ 7 * m + 886 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13258.1, data_15_13258.2]

/-- Complete interval computation for depth 15, residue 13259. -/
theorem bounds_15_13259 : exactInterval 15 13259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13259 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13259) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13259 : oddCount 13259 15 = 7 ∧ acceleratedOrbit 15 13259 = 886 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13259 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13259) = 3 ^ 7 * m + 886 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13259.1, data_15_13259.2]

/-- Complete interval computation for depth 15, residue 13260. -/
theorem bounds_15_13260 : exactInterval 15 13260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13260 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13260) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13260 : oddCount 13260 15 = 7 ∧ acceleratedOrbit 15 13260 = 886 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13260 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13260) = 3 ^ 7 * m + 886 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13260.1, data_15_13260.2]

/-- Complete interval computation for depth 15, residue 13261. -/
theorem bounds_15_13261 : exactInterval 15 13261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13261 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13261) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13261 : oddCount 13261 15 = 7 ∧ acceleratedOrbit 15 13261 = 886 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13261 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13261) = 3 ^ 7 * m + 886 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13261.1, data_15_13261.2]

/-- Complete interval computation for depth 15, residue 13262. -/
theorem bounds_15_13262 : exactInterval 15 13262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13262 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13262) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13262 : oddCount 13262 15 = 8 ∧ acceleratedOrbit 15 13262 = 2656 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13262 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13262) = 3 ^ 8 * m + 2656 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13262.1, data_15_13262.2]

/-- Complete interval computation for depth 15, residue 13263. -/
theorem bounds_15_13263 : exactInterval 15 13263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13263 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13263) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13263 : oddCount 13263 15 = 8 ∧ acceleratedOrbit 15 13263 = 2656 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13263 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13263) = 3 ^ 8 * m + 2656 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13263.1, data_15_13263.2]

/-- Complete interval computation for depth 15, residue 13264. -/
theorem bounds_15_13264 : exactInterval 15 13264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13264 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13264) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13264 : oddCount 13264 15 = 7 ∧ acceleratedOrbit 15 13264 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13264 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13264) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13264.1, data_15_13264.2]

/-- Complete interval computation for depth 15, residue 13265. -/
theorem bounds_15_13265 : exactInterval 15 13265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13265 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13265) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13265 : oddCount 13265 15 = 7 ∧ acceleratedOrbit 15 13265 = 886 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13265 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13265) = 3 ^ 7 * m + 886 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13265.1, data_15_13265.2]

/-- Complete interval computation for depth 15, residue 13266. -/
theorem bounds_15_13266 : exactInterval 15 13266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13266 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13266) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13266 : oddCount 13266 15 = 8 ∧ acceleratedOrbit 15 13266 = 2657 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13266 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13266) = 3 ^ 8 * m + 2657 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13266.1, data_15_13266.2]

/-- Complete interval computation for depth 15, residue 13267. -/
theorem bounds_15_13267 : exactInterval 15 13267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13267 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13267) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13267 : oddCount 13267 15 = 8 ∧ acceleratedOrbit 15 13267 = 2657 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13267 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13267) = 3 ^ 8 * m + 2657 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13267.1, data_15_13267.2]

/-- Complete interval computation for depth 15, residue 13268. -/
theorem bounds_15_13268 : exactInterval 15 13268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13268 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13268) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13268 : oddCount 13268 15 = 7 ∧ acceleratedOrbit 15 13268 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13268 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13268) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13268.1, data_15_13268.2]

/-- Complete interval computation for depth 15, residue 13269. -/
theorem bounds_15_13269 : exactInterval 15 13269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13269 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13269) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13269 : oddCount 13269 15 = 7 ∧ acceleratedOrbit 15 13269 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13269 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13269) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13269.1, data_15_13269.2]

/-- Complete interval computation for depth 15, residue 13270. -/
theorem bounds_15_13270 : exactInterval 15 13270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13270 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13270) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13270 : oddCount 13270 15 = 10 ∧ acceleratedOrbit 15 13270 = 23921 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13270 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13270) = 3 ^ 10 * m + 23921 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13270.1, data_15_13270.2]

end Collatz.Research.PassageAtlas.Batch0405
