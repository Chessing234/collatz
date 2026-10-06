import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0861

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 28180. -/
theorem bounds_15_28180 : exactInterval 15 28180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28180 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28180) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28180 : oddCount 28180 15 = 7 ∧ acceleratedOrbit 15 28180 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28180 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28180) = 3 ^ 7 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28180.1, data_15_28180.2]

/-- Complete interval computation for depth 15, residue 28181. -/
theorem bounds_15_28181 : exactInterval 15 28181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28181 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28181) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28181 : oddCount 28181 15 = 7 ∧ acceleratedOrbit 15 28181 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28181 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28181) = 3 ^ 7 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28181.1, data_15_28181.2]

/-- Complete interval computation for depth 15, residue 28182. -/
theorem bounds_15_28182 : exactInterval 15 28182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28182 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28182) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28182 : oddCount 28182 15 = 8 ∧ acceleratedOrbit 15 28182 = 5645 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28182 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28182) = 3 ^ 8 * m + 5645 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28182.1, data_15_28182.2]

/-- Complete interval computation for depth 15, residue 28183. -/
theorem bounds_15_28183 : exactInterval 15 28183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28183 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28183) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28183 : oddCount 28183 15 = 8 ∧ acceleratedOrbit 15 28183 = 5645 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28183 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28183) = 3 ^ 8 * m + 5645 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28183.1, data_15_28183.2]

/-- Complete interval computation for depth 15, residue 28184. -/
theorem bounds_15_28184 : exactInterval 15 28184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28184 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28184) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28184 : oddCount 28184 15 = 7 ∧ acceleratedOrbit 15 28184 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28184 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28184) = 3 ^ 7 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28184.1, data_15_28184.2]

/-- Complete interval computation for depth 15, residue 28185. -/
theorem bounds_15_28185 : exactInterval 15 28185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28185 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28185) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28185 : oddCount 28185 15 = 8 ∧ acceleratedOrbit 15 28185 = 5645 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28185 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28185) = 3 ^ 8 * m + 5645 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28185.1, data_15_28185.2]

/-- Complete interval computation for depth 15, residue 28186. -/
theorem bounds_15_28186 : exactInterval 15 28186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28186 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28186) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28186 : oddCount 28186 15 = 7 ∧ acceleratedOrbit 15 28186 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28186 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28186) = 3 ^ 7 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28186.1, data_15_28186.2]

/-- Complete interval computation for depth 15, residue 28187. -/
theorem bounds_15_28187 : exactInterval 15 28187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28187 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28187) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28187 : oddCount 28187 15 = 10 ∧ acceleratedOrbit 15 28187 = 50797 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28187 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28187) = 3 ^ 10 * m + 50797 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28187.1, data_15_28187.2]

/-- Complete interval computation for depth 15, residue 28188. -/
theorem bounds_15_28188 : exactInterval 15 28188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28188 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28188) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28188 : oddCount 28188 15 = 7 ∧ acceleratedOrbit 15 28188 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28188 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28188) = 3 ^ 7 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28188.1, data_15_28188.2]

/-- Complete interval computation for depth 15, residue 28189. -/
theorem bounds_15_28189 : exactInterval 15 28189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28189 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28189) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28189 : oddCount 28189 15 = 7 ∧ acceleratedOrbit 15 28189 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28189 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28189) = 3 ^ 7 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28189.1, data_15_28189.2]

/-- Complete interval computation for depth 15, residue 28190. -/
theorem bounds_15_28190 : exactInterval 15 28190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28190 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28190) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28190 : oddCount 28190 15 = 7 ∧ acceleratedOrbit 15 28190 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28190 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28190) = 3 ^ 7 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28190.1, data_15_28190.2]

/-- Complete interval computation for depth 15, residue 28191. -/
theorem bounds_15_28191 : exactInterval 15 28191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28191 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28191) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28191 : oddCount 28191 15 = 10 ∧ acceleratedOrbit 15 28191 = 50804 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28191 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28191) = 3 ^ 10 * m + 50804 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28191.1, data_15_28191.2]

/-- Complete interval computation for depth 15, residue 28192. -/
theorem bounds_15_28192 : exactInterval 15 28192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28192 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28192) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28192 : oddCount 28192 15 = 4 ∧ acceleratedOrbit 15 28192 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28192 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28192) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28192.1, data_15_28192.2]

/-- Complete interval computation for depth 15, residue 28193. -/
theorem bounds_15_28193 : exactInterval 15 28193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28193 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28193) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28193 : oddCount 28193 15 = 7 ∧ acceleratedOrbit 15 28193 = 1882 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28193 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28193) = 3 ^ 7 * m + 1882 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28193.1, data_15_28193.2]

/-- Complete interval computation for depth 15, residue 28194. -/
theorem bounds_15_28194 : exactInterval 15 28194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28194 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28194) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28194 : oddCount 28194 15 = 7 ∧ acceleratedOrbit 15 28194 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28194 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28194) = 3 ^ 7 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28194.1, data_15_28194.2]

/-- Complete interval computation for depth 15, residue 28195. -/
theorem bounds_15_28195 : exactInterval 15 28195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28195 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28195) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28195 : oddCount 28195 15 = 7 ∧ acceleratedOrbit 15 28195 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28195 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28195) = 3 ^ 7 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28195.1, data_15_28195.2]

/-- Complete interval computation for depth 15, residue 28196. -/
theorem bounds_15_28196 : exactInterval 15 28196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28196 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28196) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28196 : oddCount 28196 15 = 9 ∧ acceleratedOrbit 15 28196 = 16942 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28196 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28196) = 3 ^ 9 * m + 16942 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28196.1, data_15_28196.2]

/-- Complete interval computation for depth 15, residue 28197. -/
theorem bounds_15_28197 : exactInterval 15 28197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28197 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28197) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28197 : oddCount 28197 15 = 9 ∧ acceleratedOrbit 15 28197 = 16942 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28197 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28197) = 3 ^ 9 * m + 16942 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28197.1, data_15_28197.2]

/-- Complete interval computation for depth 15, residue 28198. -/
theorem bounds_15_28198 : exactInterval 15 28198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28198 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28198) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28198 : oddCount 28198 15 = 9 ∧ acceleratedOrbit 15 28198 = 16942 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28198 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28198) = 3 ^ 9 * m + 16942 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28198.1, data_15_28198.2]

/-- Complete interval computation for depth 15, residue 28199. -/
theorem bounds_15_28199 : exactInterval 15 28199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28199 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28199) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28199 : oddCount 28199 15 = 7 ∧ acceleratedOrbit 15 28199 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28199 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28199) = 3 ^ 7 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28199.1, data_15_28199.2]

/-- Complete interval computation for depth 15, residue 28200. -/
theorem bounds_15_28200 : exactInterval 15 28200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28200 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28200) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28200 : oddCount 28200 15 = 4 ∧ acceleratedOrbit 15 28200 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28200 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28200) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28200.1, data_15_28200.2]

/-- Complete interval computation for depth 15, residue 28201. -/
theorem bounds_15_28201 : exactInterval 15 28201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28201 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28201) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28201 : oddCount 28201 15 = 11 ∧ acceleratedOrbit 15 28201 = 152468 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28201 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28201) = 3 ^ 11 * m + 152468 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28201.1, data_15_28201.2]

/-- Complete interval computation for depth 15, residue 28202. -/
theorem bounds_15_28202 : exactInterval 15 28202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28202 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28202) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28202 : oddCount 28202 15 = 4 ∧ acceleratedOrbit 15 28202 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28202 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28202) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28202.1, data_15_28202.2]

/-- Complete interval computation for depth 15, residue 28203. -/
theorem bounds_15_28203 : exactInterval 15 28203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28203 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28203) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28203 : oddCount 28203 15 = 7 ∧ acceleratedOrbit 15 28203 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28203 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28203) = 3 ^ 7 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28203.1, data_15_28203.2]

/-- Complete interval computation for depth 15, residue 28204. -/
theorem bounds_15_28204 : exactInterval 15 28204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28204 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28204) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28204 : oddCount 28204 15 = 9 ∧ acceleratedOrbit 15 28204 = 16949 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28204 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28204) = 3 ^ 9 * m + 16949 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28204.1, data_15_28204.2]

/-- Complete interval computation for depth 15, residue 28205. -/
theorem bounds_15_28205 : exactInterval 15 28205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28205 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28205) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28205 : oddCount 28205 15 = 9 ∧ acceleratedOrbit 15 28205 = 16949 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28205 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28205) = 3 ^ 9 * m + 16949 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28205.1, data_15_28205.2]

/-- Complete interval computation for depth 15, residue 28206. -/
theorem bounds_15_28206 : exactInterval 15 28206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28206 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28206) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28206 : oddCount 28206 15 = 9 ∧ acceleratedOrbit 15 28206 = 16949 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28206 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28206) = 3 ^ 9 * m + 16949 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28206.1, data_15_28206.2]

/-- Complete interval computation for depth 15, residue 28207. -/
theorem bounds_15_28207 : exactInterval 15 28207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28207 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28207) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28207 : oddCount 28207 15 = 11 ∧ acceleratedOrbit 15 28207 = 152498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28207 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28207) = 3 ^ 11 * m + 152498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28207.1, data_15_28207.2]

/-- Complete interval computation for depth 15, residue 28208. -/
theorem bounds_15_28208 : exactInterval 15 28208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28208 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28208) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28208 : oddCount 28208 15 = 4 ∧ acceleratedOrbit 15 28208 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28208 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28208) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28208.1, data_15_28208.2]

/-- Complete interval computation for depth 15, residue 28209. -/
theorem bounds_15_28209 : exactInterval 15 28209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28209 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28209) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28209 : oddCount 28209 15 = 9 ∧ acceleratedOrbit 15 28209 = 16949 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28209 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28209) = 3 ^ 9 * m + 16949 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28209.1, data_15_28209.2]

/-- Complete interval computation for depth 15, residue 28210. -/
theorem bounds_15_28210 : exactInterval 15 28210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28210 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28210) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28210 : oddCount 28210 15 = 9 ∧ acceleratedOrbit 15 28210 = 16949 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28210 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28210) = 3 ^ 9 * m + 16949 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28210.1, data_15_28210.2]

/-- Complete interval computation for depth 15, residue 28211. -/
theorem bounds_15_28211 : exactInterval 15 28211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28211 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28211) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28211 : oddCount 28211 15 = 9 ∧ acceleratedOrbit 15 28211 = 16949 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28211 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28211) = 3 ^ 9 * m + 16949 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28211.1, data_15_28211.2]

/-- Complete interval computation for depth 15, residue 28212. -/
theorem bounds_15_28212 : exactInterval 15 28212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28212 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28212) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28212 : oddCount 28212 15 = 4 ∧ acceleratedOrbit 15 28212 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28212 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28212) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28212.1, data_15_28212.2]

end Collatz.Research.PassageAtlas.Batch0861
