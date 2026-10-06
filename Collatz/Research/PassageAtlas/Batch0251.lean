import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0251

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 8192. -/
theorem bounds_15_8192 : exactInterval 15 8192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8192 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8192) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8192 : oddCount 8192 15 = 1 ∧ acceleratedOrbit 15 8192 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8192 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8192) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8192.1, data_15_8192.2]

/-- Complete interval computation for depth 15, residue 8193. -/
theorem bounds_15_8193 : exactInterval 15 8193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8193 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8193) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8193 : oddCount 8193 15 = 8 ∧ acceleratedOrbit 15 8193 = 1642 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8193 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8193) = 3 ^ 8 * m + 1642 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8193.1, data_15_8193.2]

/-- Complete interval computation for depth 15, residue 8194. -/
theorem bounds_15_8194 : exactInterval 15 8194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8194 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8194) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8194 : oddCount 8194 15 = 7 ∧ acceleratedOrbit 15 8194 = 548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8194 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8194) = 3 ^ 7 * m + 548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8194.1, data_15_8194.2]

/-- Complete interval computation for depth 15, residue 8195. -/
theorem bounds_15_8195 : exactInterval 15 8195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8195 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8195) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8195 : oddCount 8195 15 = 7 ∧ acceleratedOrbit 15 8195 = 548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8195 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8195) = 3 ^ 7 * m + 548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8195.1, data_15_8195.2]

/-- Complete interval computation for depth 15, residue 8196. -/
theorem bounds_15_8196 : exactInterval 15 8196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8196 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8196) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8196 : oddCount 8196 15 = 8 ∧ acceleratedOrbit 15 8196 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8196 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8196) = 3 ^ 8 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8196.1, data_15_8196.2]

/-- Complete interval computation for depth 15, residue 8197. -/
theorem bounds_15_8197 : exactInterval 15 8197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8197 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8197) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8197 : oddCount 8197 15 = 8 ∧ acceleratedOrbit 15 8197 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8197 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8197) = 3 ^ 8 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8197.1, data_15_8197.2]

/-- Complete interval computation for depth 15, residue 8198. -/
theorem bounds_15_8198 : exactInterval 15 8198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8198 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8198) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8198 : oddCount 8198 15 = 8 ∧ acceleratedOrbit 15 8198 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8198 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8198) = 3 ^ 8 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8198.1, data_15_8198.2]

/-- Complete interval computation for depth 15, residue 8199. -/
theorem bounds_15_8199 : exactInterval 15 8199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8199 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8199) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8199 : oddCount 8199 15 = 7 ∧ acceleratedOrbit 15 8199 = 548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8199 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8199) = 3 ^ 7 * m + 548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8199.1, data_15_8199.2]

/-- Complete interval computation for depth 15, residue 8200. -/
theorem bounds_15_8200 : exactInterval 15 8200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8200 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8200) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8200 : oddCount 8200 15 = 5 ∧ acceleratedOrbit 15 8200 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8200 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8200) = 3 ^ 5 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8200.1, data_15_8200.2]

/-- Complete interval computation for depth 15, residue 8201. -/
theorem bounds_15_8201 : exactInterval 15 8201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8201 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8201) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8201 : oddCount 8201 15 = 7 ∧ acceleratedOrbit 15 8201 = 548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8201 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8201) = 3 ^ 7 * m + 548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8201.1, data_15_8201.2]

/-- Complete interval computation for depth 15, residue 8202. -/
theorem bounds_15_8202 : exactInterval 15 8202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8202 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8202) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8202 : oddCount 8202 15 = 5 ∧ acceleratedOrbit 15 8202 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8202 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8202) = 3 ^ 5 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8202.1, data_15_8202.2]

/-- Complete interval computation for depth 15, residue 8203. -/
theorem bounds_15_8203 : exactInterval 15 8203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8203 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8203) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8203 : oddCount 8203 15 = 8 ∧ acceleratedOrbit 15 8203 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8203 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8203) = 3 ^ 8 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8203.1, data_15_8203.2]

/-- Complete interval computation for depth 15, residue 8204. -/
theorem bounds_15_8204 : exactInterval 15 8204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8204 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8204) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8204 : oddCount 8204 15 = 5 ∧ acceleratedOrbit 15 8204 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8204 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8204) = 3 ^ 5 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8204.1, data_15_8204.2]

/-- Complete interval computation for depth 15, residue 8205. -/
theorem bounds_15_8205 : exactInterval 15 8205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8205 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8205) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8205 : oddCount 8205 15 = 5 ∧ acceleratedOrbit 15 8205 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8205 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8205) = 3 ^ 5 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8205.1, data_15_8205.2]

/-- Complete interval computation for depth 15, residue 8206. -/
theorem bounds_15_8206 : exactInterval 15 8206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8206 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8206) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8206 : oddCount 8206 15 = 8 ∧ acceleratedOrbit 15 8206 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8206 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8206) = 3 ^ 8 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8206.1, data_15_8206.2]

/-- Complete interval computation for depth 15, residue 8207. -/
theorem bounds_15_8207 : exactInterval 15 8207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8207 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8207) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8207 : oddCount 8207 15 = 8 ∧ acceleratedOrbit 15 8207 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8207 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8207) = 3 ^ 8 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8207.1, data_15_8207.2]

/-- Complete interval computation for depth 15, residue 8208. -/
theorem bounds_15_8208 : exactInterval 15 8208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8208 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8208) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8208 : oddCount 8208 15 = 6 ∧ acceleratedOrbit 15 8208 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8208 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8208) = 3 ^ 6 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8208.1, data_15_8208.2]

/-- Complete interval computation for depth 15, residue 8209. -/
theorem bounds_15_8209 : exactInterval 15 8209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8209 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8209) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8209 : oddCount 8209 15 = 5 ∧ acceleratedOrbit 15 8209 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8209 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8209) = 3 ^ 5 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8209.1, data_15_8209.2]

/-- Complete interval computation for depth 15, residue 8210. -/
theorem bounds_15_8210 : exactInterval 15 8210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8210 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8210) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8210 : oddCount 8210 15 = 8 ∧ acceleratedOrbit 15 8210 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8210 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8210) = 3 ^ 8 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8210.1, data_15_8210.2]

/-- Complete interval computation for depth 15, residue 8211. -/
theorem bounds_15_8211 : exactInterval 15 8211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8211 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8211) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8211 : oddCount 8211 15 = 8 ∧ acceleratedOrbit 15 8211 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8211 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8211) = 3 ^ 8 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8211.1, data_15_8211.2]

/-- Complete interval computation for depth 15, residue 8212. -/
theorem bounds_15_8212 : exactInterval 15 8212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8212 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8212) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8212 : oddCount 8212 15 = 6 ∧ acceleratedOrbit 15 8212 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8212 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8212) = 3 ^ 6 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8212.1, data_15_8212.2]

/-- Complete interval computation for depth 15, residue 8213. -/
theorem bounds_15_8213 : exactInterval 15 8213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8213 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8213) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8213 : oddCount 8213 15 = 6 ∧ acceleratedOrbit 15 8213 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8213 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8213) = 3 ^ 6 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8213.1, data_15_8213.2]

/-- Complete interval computation for depth 15, residue 8214. -/
theorem bounds_15_8214 : exactInterval 15 8214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8214 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8214) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8214 : oddCount 8214 15 = 5 ∧ acceleratedOrbit 15 8214 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8214 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8214) = 3 ^ 5 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8214.1, data_15_8214.2]

/-- Complete interval computation for depth 15, residue 8215. -/
theorem bounds_15_8215 : exactInterval 15 8215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8215 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8215) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8215 : oddCount 8215 15 = 5 ∧ acceleratedOrbit 15 8215 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8215 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8215) = 3 ^ 5 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8215.1, data_15_8215.2]

/-- Complete interval computation for depth 15, residue 8216. -/
theorem bounds_15_8216 : exactInterval 15 8216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8216 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8216) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8216 : oddCount 8216 15 = 6 ∧ acceleratedOrbit 15 8216 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8216 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8216) = 3 ^ 6 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8216.1, data_15_8216.2]

/-- Complete interval computation for depth 15, residue 8217. -/
theorem bounds_15_8217 : exactInterval 15 8217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8217 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8217) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8217 : oddCount 8217 15 = 9 ∧ acceleratedOrbit 15 8217 = 4940 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8217 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8217) = 3 ^ 9 * m + 4940 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8217.1, data_15_8217.2]

/-- Complete interval computation for depth 15, residue 8218. -/
theorem bounds_15_8218 : exactInterval 15 8218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8218 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8218) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8218 : oddCount 8218 15 = 6 ∧ acceleratedOrbit 15 8218 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8218 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8218) = 3 ^ 6 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8218.1, data_15_8218.2]

/-- Complete interval computation for depth 15, residue 8219. -/
theorem bounds_15_8219 : exactInterval 15 8219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8219 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8219) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8219 : oddCount 8219 15 = 12 ∧ acceleratedOrbit 15 8219 = 133325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8219 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8219) = 3 ^ 12 * m + 133325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8219.1, data_15_8219.2]

/-- Complete interval computation for depth 15, residue 8220. -/
theorem bounds_15_8220 : exactInterval 15 8220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8220 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8220) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8220 : oddCount 8220 15 = 5 ∧ acceleratedOrbit 15 8220 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8220 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8220) = 3 ^ 5 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8220.1, data_15_8220.2]

/-- Complete interval computation for depth 15, residue 8221. -/
theorem bounds_15_8221 : exactInterval 15 8221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8221 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8221) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8221 : oddCount 8221 15 = 5 ∧ acceleratedOrbit 15 8221 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8221 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8221) = 3 ^ 5 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8221.1, data_15_8221.2]

/-- Complete interval computation for depth 15, residue 8222. -/
theorem bounds_15_8222 : exactInterval 15 8222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8222 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8222) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8222 : oddCount 8222 15 = 5 ∧ acceleratedOrbit 15 8222 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8222 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8222) = 3 ^ 5 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8222.1, data_15_8222.2]

/-- Complete interval computation for depth 15, residue 8223. -/
theorem bounds_15_8223 : exactInterval 15 8223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8223 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8223) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8223 : oddCount 8223 15 = 11 ∧ acceleratedOrbit 15 8223 = 44462 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8223 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8223) = 3 ^ 11 * m + 44462 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8223.1, data_15_8223.2]

end Collatz.Research.PassageAtlas.Batch0251
