import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0214

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 199. -/
theorem bounds_12_199 : exactInterval 12 199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_199 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 199) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_199 : oddCount 199 12 = 8 ∧ acceleratedOrbit 12 199 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_199 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 199) = 3 ^ 8 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_199.1, data_12_199.2]

/-- Complete interval computation for depth 12, residue 200. -/
theorem bounds_12_200 : exactInterval 12 200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_200 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 200) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_200 : oddCount 200 12 = 5 ∧ acceleratedOrbit 12 200 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_200 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 200) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_200.1, data_12_200.2]

/-- Complete interval computation for depth 12, residue 201. -/
theorem bounds_12_201 : exactInterval 12 201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_201 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 201) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_201 : oddCount 201 12 = 4 ∧ acceleratedOrbit 12 201 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_201 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 201) = 3 ^ 4 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_201.1, data_12_201.2]

/-- Complete interval computation for depth 12, residue 202. -/
theorem bounds_12_202 : exactInterval 12 202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_202 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 202) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_202 : oddCount 202 12 = 5 ∧ acceleratedOrbit 12 202 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_202 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 202) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_202.1, data_12_202.2]

/-- Complete interval computation for depth 12, residue 203. -/
theorem bounds_12_203 : exactInterval 12 203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_203 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 203) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_203 : oddCount 203 12 = 6 ∧ acceleratedOrbit 12 203 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_203 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 203) = 3 ^ 6 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_203.1, data_12_203.2]

/-- Complete interval computation for depth 12, residue 204. -/
theorem bounds_12_204 : exactInterval 12 204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_204 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 204) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_204 : oddCount 204 12 = 5 ∧ acceleratedOrbit 12 204 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_204 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 204) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_204.1, data_12_204.2]

/-- Complete interval computation for depth 12, residue 205. -/
theorem bounds_12_205 : exactInterval 12 205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_205 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 205) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_205 : oddCount 205 12 = 5 ∧ acceleratedOrbit 12 205 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_205 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 205) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_205.1, data_12_205.2]

/-- Complete interval computation for depth 12, residue 206. -/
theorem bounds_12_206 : exactInterval 12 206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_206 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 206) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_206 : oddCount 206 12 = 8 ∧ acceleratedOrbit 12 206 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_206 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 206) = 3 ^ 8 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_206.1, data_12_206.2]

/-- Complete interval computation for depth 12, residue 207. -/
theorem bounds_12_207 : exactInterval 12 207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_207 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 207) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_207 : oddCount 207 12 = 8 ∧ acceleratedOrbit 12 207 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_207 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 207) = 3 ^ 8 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_207.1, data_12_207.2]

/-- Complete interval computation for depth 12, residue 208. -/
theorem bounds_12_208 : exactInterval 12 208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_208 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 208) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_208 : oddCount 208 12 = 3 ∧ acceleratedOrbit 12 208 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_208 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 208) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_208.1, data_12_208.2]

/-- Complete interval computation for depth 12, residue 209. -/
theorem bounds_12_209 : exactInterval 12 209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_209 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 209) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_209 : oddCount 209 12 = 6 ∧ acceleratedOrbit 12 209 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_209 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 209) = 3 ^ 6 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_209.1, data_12_209.2]

/-- Complete interval computation for depth 12, residue 210. -/
theorem bounds_12_210 : exactInterval 12 210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_210 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 210) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_210 : oddCount 210 12 = 6 ∧ acceleratedOrbit 12 210 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_210 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 210) = 3 ^ 6 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_210.1, data_12_210.2]

/-- Complete interval computation for depth 12, residue 211. -/
theorem bounds_12_211 : exactInterval 12 211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_211 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 211) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_211 : oddCount 211 12 = 6 ∧ acceleratedOrbit 12 211 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_211 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 211) = 3 ^ 6 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_211.1, data_12_211.2]

/-- Complete interval computation for depth 12, residue 212. -/
theorem bounds_12_212 : exactInterval 12 212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_212 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 212) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_212 : oddCount 212 12 = 3 ∧ acceleratedOrbit 12 212 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_212 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 212) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_212.1, data_12_212.2]

/-- Complete interval computation for depth 12, residue 213. -/
theorem bounds_12_213 : exactInterval 12 213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_213 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 213) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_213 : oddCount 213 12 = 3 ∧ acceleratedOrbit 12 213 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_213 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 213) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_213.1, data_12_213.2]

/-- Complete interval computation for depth 12, residue 214. -/
theorem bounds_12_214 : exactInterval 12 214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_214 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 214) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_214 : oddCount 214 12 = 8 ∧ acceleratedOrbit 12 214 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_214 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 214) = 3 ^ 8 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_214.1, data_12_214.2]

end Collatz.Research.StoppingAtlas.Batch0214
