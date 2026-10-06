import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0587

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 19202. -/
theorem bounds_15_19202 : exactInterval 15 19202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19202 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19202) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19202 : oddCount 19202 15 = 8 ∧ acceleratedOrbit 15 19202 = 3847 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19202 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19202) = 3 ^ 8 * m + 3847 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19202.1, data_15_19202.2]

/-- Complete interval computation for depth 15, residue 19203. -/
theorem bounds_15_19203 : exactInterval 15 19203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19203 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19203) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19203 : oddCount 19203 15 = 8 ∧ acceleratedOrbit 15 19203 = 3847 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19203 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19203) = 3 ^ 8 * m + 3847 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19203.1, data_15_19203.2]

/-- Complete interval computation for depth 15, residue 19204. -/
theorem bounds_15_19204 : exactInterval 15 19204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19204 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19204) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19204 : oddCount 19204 15 = 5 ∧ acceleratedOrbit 15 19204 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19204 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19204) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19204.1, data_15_19204.2]

/-- Complete interval computation for depth 15, residue 19205. -/
theorem bounds_15_19205 : exactInterval 15 19205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19205 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19205) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19205 : oddCount 19205 15 = 5 ∧ acceleratedOrbit 15 19205 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19205 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19205) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19205.1, data_15_19205.2]

/-- Complete interval computation for depth 15, residue 19206. -/
theorem bounds_15_19206 : exactInterval 15 19206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19206 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19206) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19206 : oddCount 19206 15 = 5 ∧ acceleratedOrbit 15 19206 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19206 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19206) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19206.1, data_15_19206.2]

/-- Complete interval computation for depth 15, residue 19207. -/
theorem bounds_15_19207 : exactInterval 15 19207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19207 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19207) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19207 : oddCount 19207 15 = 9 ∧ acceleratedOrbit 15 19207 = 11539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19207 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19207) = 3 ^ 9 * m + 11539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19207.1, data_15_19207.2]

/-- Complete interval computation for depth 15, residue 19208. -/
theorem bounds_15_19208 : exactInterval 15 19208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19208 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19208) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19208 : oddCount 19208 15 = 8 ∧ acceleratedOrbit 15 19208 = 3851 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19208 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19208) = 3 ^ 8 * m + 3851 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19208.1, data_15_19208.2]

/-- Complete interval computation for depth 15, residue 19209. -/
theorem bounds_15_19209 : exactInterval 15 19209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19209 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19209) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19209 : oddCount 19209 15 = 9 ∧ acceleratedOrbit 15 19209 = 11540 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19209 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19209) = 3 ^ 9 * m + 11540 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19209.1, data_15_19209.2]

/-- Complete interval computation for depth 15, residue 19210. -/
theorem bounds_15_19210 : exactInterval 15 19210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19210 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19210) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19210 : oddCount 19210 15 = 8 ∧ acceleratedOrbit 15 19210 = 3851 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19210 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19210) = 3 ^ 8 * m + 3851 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19210.1, data_15_19210.2]

/-- Complete interval computation for depth 15, residue 19211. -/
theorem bounds_15_19211 : exactInterval 15 19211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19211 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19211) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19211 : oddCount 19211 15 = 10 ∧ acceleratedOrbit 15 19211 = 34627 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19211 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19211) = 3 ^ 10 * m + 34627 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19211.1, data_15_19211.2]

/-- Complete interval computation for depth 15, residue 19212. -/
theorem bounds_15_19212 : exactInterval 15 19212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19212 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19212) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19212 : oddCount 19212 15 = 8 ∧ acceleratedOrbit 15 19212 = 3851 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19212 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19212) = 3 ^ 8 * m + 3851 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19212.1, data_15_19212.2]

/-- Complete interval computation for depth 15, residue 19213. -/
theorem bounds_15_19213 : exactInterval 15 19213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19213 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19213) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19213 : oddCount 19213 15 = 8 ∧ acceleratedOrbit 15 19213 = 3851 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19213 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19213) = 3 ^ 8 * m + 3851 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19213.1, data_15_19213.2]

/-- Complete interval computation for depth 15, residue 19214. -/
theorem bounds_15_19214 : exactInterval 15 19214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19214 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19214) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19214 : oddCount 19214 15 = 5 ∧ acceleratedOrbit 15 19214 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19214 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19214) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19214.1, data_15_19214.2]

/-- Complete interval computation for depth 15, residue 19215. -/
theorem bounds_15_19215 : exactInterval 15 19215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19215 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19215) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19215 : oddCount 19215 15 = 5 ∧ acceleratedOrbit 15 19215 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19215 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19215) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19215.1, data_15_19215.2]

/-- Complete interval computation for depth 15, residue 19216. -/
theorem bounds_15_19216 : exactInterval 15 19216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19216 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19216) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19216 : oddCount 19216 15 = 6 ∧ acceleratedOrbit 15 19216 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19216 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19216) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19216.1, data_15_19216.2]

/-- Complete interval computation for depth 15, residue 19217. -/
theorem bounds_15_19217 : exactInterval 15 19217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19217 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19217) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19217 : oddCount 19217 15 = 8 ∧ acceleratedOrbit 15 19217 = 3851 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19217 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19217) = 3 ^ 8 * m + 3851 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19217.1, data_15_19217.2]

/-- Complete interval computation for depth 15, residue 19218. -/
theorem bounds_15_19218 : exactInterval 15 19218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19218 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19218) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19218 : oddCount 19218 15 = 7 ∧ acceleratedOrbit 15 19218 = 1283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19218 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19218) = 3 ^ 7 * m + 1283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19218.1, data_15_19218.2]

/-- Complete interval computation for depth 15, residue 19219. -/
theorem bounds_15_19219 : exactInterval 15 19219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19219 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19219) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19219 : oddCount 19219 15 = 7 ∧ acceleratedOrbit 15 19219 = 1283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19219 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19219) = 3 ^ 7 * m + 1283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19219.1, data_15_19219.2]

/-- Complete interval computation for depth 15, residue 19220. -/
theorem bounds_15_19220 : exactInterval 15 19220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19220 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19220) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19220 : oddCount 19220 15 = 6 ∧ acceleratedOrbit 15 19220 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19220 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19220) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19220.1, data_15_19220.2]

/-- Complete interval computation for depth 15, residue 19221. -/
theorem bounds_15_19221 : exactInterval 15 19221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19221 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19221) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19221 : oddCount 19221 15 = 6 ∧ acceleratedOrbit 15 19221 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19221 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19221) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19221.1, data_15_19221.2]

/-- Complete interval computation for depth 15, residue 19222. -/
theorem bounds_15_19222 : exactInterval 15 19222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19222 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19222) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19222 : oddCount 19222 15 = 8 ∧ acceleratedOrbit 15 19222 = 3851 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19222 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19222) = 3 ^ 8 * m + 3851 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19222.1, data_15_19222.2]

/-- Complete interval computation for depth 15, residue 19223. -/
theorem bounds_15_19223 : exactInterval 15 19223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19223 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19223) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19223 : oddCount 19223 15 = 8 ∧ acceleratedOrbit 15 19223 = 3851 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19223 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19223) = 3 ^ 8 * m + 3851 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19223.1, data_15_19223.2]

/-- Complete interval computation for depth 15, residue 19224. -/
theorem bounds_15_19224 : exactInterval 15 19224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19224 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19224) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19224 : oddCount 19224 15 = 6 ∧ acceleratedOrbit 15 19224 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19224 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19224) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19224.1, data_15_19224.2]

/-- Complete interval computation for depth 15, residue 19225. -/
theorem bounds_15_19225 : exactInterval 15 19225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19225 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19225) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19225 : oddCount 19225 15 = 8 ∧ acceleratedOrbit 15 19225 = 3850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19225 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19225) = 3 ^ 8 * m + 3850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19225.1, data_15_19225.2]

/-- Complete interval computation for depth 15, residue 19226. -/
theorem bounds_15_19226 : exactInterval 15 19226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19226 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19226) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19226 : oddCount 19226 15 = 6 ∧ acceleratedOrbit 15 19226 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19226 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19226) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19226.1, data_15_19226.2]

/-- Complete interval computation for depth 15, residue 19227. -/
theorem bounds_15_19227 : exactInterval 15 19227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19227 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19227) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19227 : oddCount 19227 15 = 11 ∧ acceleratedOrbit 15 19227 = 103951 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19227 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19227) = 3 ^ 11 * m + 103951 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19227.1, data_15_19227.2]

/-- Complete interval computation for depth 15, residue 19228. -/
theorem bounds_15_19228 : exactInterval 15 19228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19228 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19228) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19228 : oddCount 19228 15 = 6 ∧ acceleratedOrbit 15 19228 = 428 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19228 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19228) = 3 ^ 6 * m + 428 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19228.1, data_15_19228.2]

/-- Complete interval computation for depth 15, residue 19229. -/
theorem bounds_15_19229 : exactInterval 15 19229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19229 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19229) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19229 : oddCount 19229 15 = 6 ∧ acceleratedOrbit 15 19229 = 428 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19229 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19229) = 3 ^ 6 * m + 428 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19229.1, data_15_19229.2]

/-- Complete interval computation for depth 15, residue 19230. -/
theorem bounds_15_19230 : exactInterval 15 19230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19230 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19230) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19230 : oddCount 19230 15 = 6 ∧ acceleratedOrbit 15 19230 = 428 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19230 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19230) = 3 ^ 6 * m + 428 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19230.1, data_15_19230.2]

/-- Complete interval computation for depth 15, residue 19231. -/
theorem bounds_15_19231 : exactInterval 15 19231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19231 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19231) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19231 : oddCount 19231 15 = 10 ∧ acceleratedOrbit 15 19231 = 34658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19231 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19231) = 3 ^ 10 * m + 34658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19231.1, data_15_19231.2]

/-- Complete interval computation for depth 15, residue 19232. -/
theorem bounds_15_19232 : exactInterval 15 19232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19232 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19232) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19232 : oddCount 19232 15 = 6 ∧ acceleratedOrbit 15 19232 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19232 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19232) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19232.1, data_15_19232.2]

/-- Complete interval computation for depth 15, residue 19233. -/
theorem bounds_15_19233 : exactInterval 15 19233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19233 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19233) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19233 : oddCount 19233 15 = 6 ∧ acceleratedOrbit 15 19233 = 428 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19233 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19233) = 3 ^ 6 * m + 428 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19233.1, data_15_19233.2]

end Collatz.Research.PassageAtlas.Batch0587
