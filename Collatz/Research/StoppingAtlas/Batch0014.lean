import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0014

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 199. -/
theorem bounds_10_199 : exactInterval 10 199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_199 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 199) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_199 : oddCount 199 10 = 6 ∧ acceleratedOrbit 10 199 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_199 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 199) = 3 ^ 6 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_199.1, data_10_199.2]

/-- Complete interval computation for depth 10, residue 200. -/
theorem bounds_10_200 : exactInterval 10 200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_200 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 200) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_200 : oddCount 200 10 = 4 ∧ acceleratedOrbit 10 200 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_200 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 200) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_200.1, data_10_200.2]

/-- Complete interval computation for depth 10, residue 201. -/
theorem bounds_10_201 : exactInterval 10 201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_201 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 201) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_201 : oddCount 201 10 = 4 ∧ acceleratedOrbit 10 201 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_201 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 201) = 3 ^ 4 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_201.1, data_10_201.2]

/-- Complete interval computation for depth 10, residue 202. -/
theorem bounds_10_202 : exactInterval 10 202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_202 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 202) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_202 : oddCount 202 10 = 4 ∧ acceleratedOrbit 10 202 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_202 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 202) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_202.1, data_10_202.2]

/-- Complete interval computation for depth 10, residue 203. -/
theorem bounds_10_203 : exactInterval 10 203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_203 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 203) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_203 : oddCount 203 10 = 5 ∧ acceleratedOrbit 10 203 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_203 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 203) = 3 ^ 5 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_203.1, data_10_203.2]

/-- Complete interval computation for depth 10, residue 204. -/
theorem bounds_10_204 : exactInterval 10 204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_204 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 204) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_204 : oddCount 204 10 = 4 ∧ acceleratedOrbit 10 204 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_204 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 204) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_204.1, data_10_204.2]

/-- Complete interval computation for depth 10, residue 205. -/
theorem bounds_10_205 : exactInterval 10 205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_205 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 205) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_205 : oddCount 205 10 = 4 ∧ acceleratedOrbit 10 205 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_205 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 205) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_205.1, data_10_205.2]

/-- Complete interval computation for depth 10, residue 206. -/
theorem bounds_10_206 : exactInterval 10 206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_206 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 206) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_206 : oddCount 206 10 = 7 ∧ acceleratedOrbit 10 206 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_206 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 206) = 3 ^ 7 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_206.1, data_10_206.2]

/-- Complete interval computation for depth 10, residue 207. -/
theorem bounds_10_207 : exactInterval 10 207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_207 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 207) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_207 : oddCount 207 10 = 7 ∧ acceleratedOrbit 10 207 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_207 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 207) = 3 ^ 7 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_207.1, data_10_207.2]

/-- Complete interval computation for depth 10, residue 208. -/
theorem bounds_10_208 : exactInterval 10 208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_208 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 208) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_208 : oddCount 208 10 = 2 ∧ acceleratedOrbit 10 208 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_208 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 208) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_208.1, data_10_208.2]

/-- Complete interval computation for depth 10, residue 209. -/
theorem bounds_10_209 : exactInterval 10 209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_209 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 209) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_209 : oddCount 209 10 = 6 ∧ acceleratedOrbit 10 209 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_209 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 209) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_209.1, data_10_209.2]

/-- Complete interval computation for depth 10, residue 210. -/
theorem bounds_10_210 : exactInterval 10 210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_210 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 210) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_210 : oddCount 210 10 = 6 ∧ acceleratedOrbit 10 210 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_210 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 210) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_210.1, data_10_210.2]

/-- Complete interval computation for depth 10, residue 211. -/
theorem bounds_10_211 : exactInterval 10 211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_211 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 211) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_211 : oddCount 211 10 = 6 ∧ acceleratedOrbit 10 211 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_211 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 211) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_211.1, data_10_211.2]

/-- Complete interval computation for depth 10, residue 212. -/
theorem bounds_10_212 : exactInterval 10 212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_212 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 212) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_212 : oddCount 212 10 = 2 ∧ acceleratedOrbit 10 212 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_212 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 212) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_212.1, data_10_212.2]

/-- Complete interval computation for depth 10, residue 213. -/
theorem bounds_10_213 : exactInterval 10 213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_213 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 213) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_213 : oddCount 213 10 = 2 ∧ acceleratedOrbit 10 213 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_213 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 213) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_213.1, data_10_213.2]

/-- Complete interval computation for depth 10, residue 214. -/
theorem bounds_10_214 : exactInterval 10 214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_214 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 214) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_214 : oddCount 214 10 = 6 ∧ acceleratedOrbit 10 214 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_214 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 214) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_214.1, data_10_214.2]

end Collatz.Research.StoppingAtlas.Batch0014
