import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0495

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 16187. -/
theorem bounds_15_16187 : exactInterval 15 16187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16187 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16187) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16187 : oddCount 16187 15 = 7 ∧ acceleratedOrbit 15 16187 = 1081 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16187 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16187) = 3 ^ 7 * m + 1081 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16187.1, data_15_16187.2]

/-- Complete interval computation for depth 15, residue 16188. -/
theorem bounds_15_16188 : exactInterval 15 16188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16188 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16188) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16188 : oddCount 16188 15 = 7 ∧ acceleratedOrbit 15 16188 = 1081 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16188 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16188) = 3 ^ 7 * m + 1081 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16188.1, data_15_16188.2]

/-- Complete interval computation for depth 15, residue 16189. -/
theorem bounds_15_16189 : exactInterval 15 16189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16189 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16189) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16189 : oddCount 16189 15 = 7 ∧ acceleratedOrbit 15 16189 = 1081 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16189 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16189) = 3 ^ 7 * m + 1081 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16189.1, data_15_16189.2]

/-- Complete interval computation for depth 15, residue 16190. -/
theorem bounds_15_16190 : exactInterval 15 16190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16190 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16190) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16190 : oddCount 16190 15 = 10 ∧ acceleratedOrbit 15 16190 = 29180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16190 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16190) = 3 ^ 10 * m + 29180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16190.1, data_15_16190.2]

/-- Complete interval computation for depth 15, residue 16191. -/
theorem bounds_15_16191 : exactInterval 15 16191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16191 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16191) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16191 : oddCount 16191 15 = 10 ∧ acceleratedOrbit 15 16191 = 29180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16191 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16191) = 3 ^ 10 * m + 29180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16191.1, data_15_16191.2]

/-- Complete interval computation for depth 15, residue 16192. -/
theorem bounds_15_16192 : exactInterval 15 16192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16192 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16192) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16192 : oddCount 16192 15 = 6 ∧ acceleratedOrbit 15 16192 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16192 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16192) = 3 ^ 6 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16192.1, data_15_16192.2]

/-- Complete interval computation for depth 15, residue 16193. -/
theorem bounds_15_16193 : exactInterval 15 16193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16193 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16193) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16193 : oddCount 16193 15 = 6 ∧ acceleratedOrbit 15 16193 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16193 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16193) = 3 ^ 6 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16193.1, data_15_16193.2]

/-- Complete interval computation for depth 15, residue 16194. -/
theorem bounds_15_16194 : exactInterval 15 16194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16194 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16194) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16194 : oddCount 16194 15 = 7 ∧ acceleratedOrbit 15 16194 = 1082 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16194 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16194) = 3 ^ 7 * m + 1082 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16194.1, data_15_16194.2]

/-- Complete interval computation for depth 15, residue 16195. -/
theorem bounds_15_16195 : exactInterval 15 16195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16195 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16195) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16195 : oddCount 16195 15 = 7 ∧ acceleratedOrbit 15 16195 = 1082 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16195 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16195) = 3 ^ 7 * m + 1082 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16195.1, data_15_16195.2]

/-- Complete interval computation for depth 15, residue 16196. -/
theorem bounds_15_16196 : exactInterval 15 16196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16196 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16196) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16196 : oddCount 16196 15 = 6 ∧ acceleratedOrbit 15 16196 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16196 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16196) = 3 ^ 6 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16196.1, data_15_16196.2]

/-- Complete interval computation for depth 15, residue 16197. -/
theorem bounds_15_16197 : exactInterval 15 16197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16197 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16197) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16197 : oddCount 16197 15 = 6 ∧ acceleratedOrbit 15 16197 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16197 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16197) = 3 ^ 6 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16197.1, data_15_16197.2]

/-- Complete interval computation for depth 15, residue 16198. -/
theorem bounds_15_16198 : exactInterval 15 16198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16198 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16198) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16198 : oddCount 16198 15 = 6 ∧ acceleratedOrbit 15 16198 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16198 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16198) = 3 ^ 6 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16198.1, data_15_16198.2]

/-- Complete interval computation for depth 15, residue 16199. -/
theorem bounds_15_16199 : exactInterval 15 16199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16199 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16199) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16199 : oddCount 16199 15 = 8 ∧ acceleratedOrbit 15 16199 = 3244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16199 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16199) = 3 ^ 8 * m + 3244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16199.1, data_15_16199.2]

/-- Complete interval computation for depth 15, residue 16200. -/
theorem bounds_15_16200 : exactInterval 15 16200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16200 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16200) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16200 : oddCount 16200 15 = 9 ∧ acceleratedOrbit 15 16200 = 9740 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16200 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16200) = 3 ^ 9 * m + 9740 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16200.1, data_15_16200.2]

/-- Complete interval computation for depth 15, residue 16201. -/
theorem bounds_15_16201 : exactInterval 15 16201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16201 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16201) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16201 : oddCount 16201 15 = 7 ∧ acceleratedOrbit 15 16201 = 1082 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16201 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16201) = 3 ^ 7 * m + 1082 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16201.1, data_15_16201.2]

/-- Complete interval computation for depth 15, residue 16202. -/
theorem bounds_15_16202 : exactInterval 15 16202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16202 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16202) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16202 : oddCount 16202 15 = 9 ∧ acceleratedOrbit 15 16202 = 9740 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16202 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16202) = 3 ^ 9 * m + 9740 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16202.1, data_15_16202.2]

/-- Complete interval computation for depth 15, residue 16203. -/
theorem bounds_15_16203 : exactInterval 15 16203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16203 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16203) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16203 : oddCount 16203 15 = 6 ∧ acceleratedOrbit 15 16203 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16203 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16203) = 3 ^ 6 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16203.1, data_15_16203.2]

/-- Complete interval computation for depth 15, residue 16204. -/
theorem bounds_15_16204 : exactInterval 15 16204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16204 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16204) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16204 : oddCount 16204 15 = 9 ∧ acceleratedOrbit 15 16204 = 9740 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16204 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16204) = 3 ^ 9 * m + 9740 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16204.1, data_15_16204.2]

/-- Complete interval computation for depth 15, residue 16205. -/
theorem bounds_15_16205 : exactInterval 15 16205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16205 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16205) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16205 : oddCount 16205 15 = 9 ∧ acceleratedOrbit 15 16205 = 9740 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16205 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16205) = 3 ^ 9 * m + 9740 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16205.1, data_15_16205.2]

/-- Complete interval computation for depth 15, residue 16206. -/
theorem bounds_15_16206 : exactInterval 15 16206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16206 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16206) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16206 : oddCount 16206 15 = 9 ∧ acceleratedOrbit 15 16206 = 9737 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16206 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16206) = 3 ^ 9 * m + 9737 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16206.1, data_15_16206.2]

/-- Complete interval computation for depth 15, residue 16207. -/
theorem bounds_15_16207 : exactInterval 15 16207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16207 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16207) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16207 : oddCount 16207 15 = 9 ∧ acceleratedOrbit 15 16207 = 9737 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16207 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16207) = 3 ^ 9 * m + 9737 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16207.1, data_15_16207.2]

/-- Complete interval computation for depth 15, residue 16208. -/
theorem bounds_15_16208 : exactInterval 15 16208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16208 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16208) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16208 : oddCount 16208 15 = 6 ∧ acceleratedOrbit 15 16208 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16208 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16208) = 3 ^ 6 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16208.1, data_15_16208.2]

/-- Complete interval computation for depth 15, residue 16209. -/
theorem bounds_15_16209 : exactInterval 15 16209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16209 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16209) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16209 : oddCount 16209 15 = 9 ∧ acceleratedOrbit 15 16209 = 9740 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16209 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16209) = 3 ^ 9 * m + 9740 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16209.1, data_15_16209.2]

/-- Complete interval computation for depth 15, residue 16210. -/
theorem bounds_15_16210 : exactInterval 15 16210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16210 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16210) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16210 : oddCount 16210 15 = 9 ∧ acceleratedOrbit 15 16210 = 9739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16210 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16210) = 3 ^ 9 * m + 9739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16210.1, data_15_16210.2]

/-- Complete interval computation for depth 15, residue 16211. -/
theorem bounds_15_16211 : exactInterval 15 16211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16211 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16211) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16211 : oddCount 16211 15 = 9 ∧ acceleratedOrbit 15 16211 = 9739 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16211 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16211) = 3 ^ 9 * m + 9739 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16211.1, data_15_16211.2]

/-- Complete interval computation for depth 15, residue 16212. -/
theorem bounds_15_16212 : exactInterval 15 16212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16212 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16212) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16212 : oddCount 16212 15 = 6 ∧ acceleratedOrbit 15 16212 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16212 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16212) = 3 ^ 6 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16212.1, data_15_16212.2]

/-- Complete interval computation for depth 15, residue 16213. -/
theorem bounds_15_16213 : exactInterval 15 16213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16213 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16213) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16213 : oddCount 16213 15 = 6 ∧ acceleratedOrbit 15 16213 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16213 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16213) = 3 ^ 6 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16213.1, data_15_16213.2]

/-- Complete interval computation for depth 15, residue 16214. -/
theorem bounds_15_16214 : exactInterval 15 16214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16214 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16214) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16214 : oddCount 16214 15 = 8 ∧ acceleratedOrbit 15 16214 = 3248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16214 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16214) = 3 ^ 8 * m + 3248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16214.1, data_15_16214.2]

/-- Complete interval computation for depth 15, residue 16215. -/
theorem bounds_15_16215 : exactInterval 15 16215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16215 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16215) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16215 : oddCount 16215 15 = 8 ∧ acceleratedOrbit 15 16215 = 3248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16215 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16215) = 3 ^ 8 * m + 3248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16215.1, data_15_16215.2]

/-- Complete interval computation for depth 15, residue 16216. -/
theorem bounds_15_16216 : exactInterval 15 16216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16216 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16216) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16216 : oddCount 16216 15 = 8 ∧ acceleratedOrbit 15 16216 = 3250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16216 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16216) = 3 ^ 8 * m + 3250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16216.1, data_15_16216.2]

/-- Complete interval computation for depth 15, residue 16217. -/
theorem bounds_15_16217 : exactInterval 15 16217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16217 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16217) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16217 : oddCount 16217 15 = 6 ∧ acceleratedOrbit 15 16217 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16217 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16217) = 3 ^ 6 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16217.1, data_15_16217.2]

/-- Complete interval computation for depth 15, residue 16218. -/
theorem bounds_15_16218 : exactInterval 15 16218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16218 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16218) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16218 : oddCount 16218 15 = 8 ∧ acceleratedOrbit 15 16218 = 3250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16218 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16218) = 3 ^ 8 * m + 3250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16218.1, data_15_16218.2]

/-- Complete interval computation for depth 15, residue 16219. -/
theorem bounds_15_16219 : exactInterval 15 16219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16219 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16219) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16219 : oddCount 16219 15 = 10 ∧ acceleratedOrbit 15 16219 = 29231 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16219 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16219) = 3 ^ 10 * m + 29231 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16219.1, data_15_16219.2]

end Collatz.Research.PassageAtlas.Batch0495
