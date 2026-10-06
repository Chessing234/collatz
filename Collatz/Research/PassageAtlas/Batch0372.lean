import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0372

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 12156. -/
theorem bounds_15_12156 : exactInterval 15 12156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12156 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12156) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12156 : oddCount 12156 15 = 8 ∧ acceleratedOrbit 15 12156 = 2435 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12156 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12156) = 3 ^ 8 * m + 2435 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12156.1, data_15_12156.2]

/-- Complete interval computation for depth 15, residue 12157. -/
theorem bounds_15_12157 : exactInterval 15 12157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12157 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12157) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12157 : oddCount 12157 15 = 8 ∧ acceleratedOrbit 15 12157 = 2435 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12157 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12157) = 3 ^ 8 * m + 2435 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12157.1, data_15_12157.2]

/-- Complete interval computation for depth 15, residue 12158. -/
theorem bounds_15_12158 : exactInterval 15 12158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12158 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12158) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12158 : oddCount 12158 15 = 10 ∧ acceleratedOrbit 15 12158 = 21914 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12158 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12158) = 3 ^ 10 * m + 21914 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12158.1, data_15_12158.2]

/-- Complete interval computation for depth 15, residue 12159. -/
theorem bounds_15_12159 : exactInterval 15 12159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12159 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12159) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12159 : oddCount 12159 15 = 10 ∧ acceleratedOrbit 15 12159 = 21914 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12159 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12159) = 3 ^ 10 * m + 21914 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12159.1, data_15_12159.2]

/-- Complete interval computation for depth 15, residue 12160. -/
theorem bounds_15_12160 : exactInterval 15 12160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12160 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12160) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12160 : oddCount 12160 15 = 5 ∧ acceleratedOrbit 15 12160 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12160 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12160) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12160.1, data_15_12160.2]

/-- Complete interval computation for depth 15, residue 12161. -/
theorem bounds_15_12161 : exactInterval 15 12161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12161 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12161) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12161 : oddCount 12161 15 = 7 ∧ acceleratedOrbit 15 12161 = 812 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12161 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12161) = 3 ^ 7 * m + 812 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12161.1, data_15_12161.2]

/-- Complete interval computation for depth 15, residue 12162. -/
theorem bounds_15_12162 : exactInterval 15 12162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12162 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12162) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12162 : oddCount 12162 15 = 6 ∧ acceleratedOrbit 15 12162 = 271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12162 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12162) = 3 ^ 6 * m + 271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12162.1, data_15_12162.2]

/-- Complete interval computation for depth 15, residue 12163. -/
theorem bounds_15_12163 : exactInterval 15 12163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12163 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12163) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12163 : oddCount 12163 15 = 6 ∧ acceleratedOrbit 15 12163 = 271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12163 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12163) = 3 ^ 6 * m + 271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12163.1, data_15_12163.2]

/-- Complete interval computation for depth 15, residue 12164. -/
theorem bounds_15_12164 : exactInterval 15 12164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12164 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12164) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12164 : oddCount 12164 15 = 8 ∧ acceleratedOrbit 15 12164 = 2438 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12164 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12164) = 3 ^ 8 * m + 2438 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12164.1, data_15_12164.2]

/-- Complete interval computation for depth 15, residue 12165. -/
theorem bounds_15_12165 : exactInterval 15 12165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12165 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12165) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12165 : oddCount 12165 15 = 8 ∧ acceleratedOrbit 15 12165 = 2438 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12165 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12165) = 3 ^ 8 * m + 2438 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12165.1, data_15_12165.2]

/-- Complete interval computation for depth 15, residue 12166. -/
theorem bounds_15_12166 : exactInterval 15 12166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12166 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12166) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12166 : oddCount 12166 15 = 8 ∧ acceleratedOrbit 15 12166 = 2438 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12166 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12166) = 3 ^ 8 * m + 2438 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12166.1, data_15_12166.2]

/-- Complete interval computation for depth 15, residue 12167. -/
theorem bounds_15_12167 : exactInterval 15 12167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12167 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12167) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12167 : oddCount 12167 15 = 6 ∧ acceleratedOrbit 15 12167 = 271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12167 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12167) = 3 ^ 6 * m + 271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12167.1, data_15_12167.2]

/-- Complete interval computation for depth 15, residue 12168. -/
theorem bounds_15_12168 : exactInterval 15 12168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12168 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12168) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12168 : oddCount 12168 15 = 5 ∧ acceleratedOrbit 15 12168 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12168 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12168) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12168.1, data_15_12168.2]

/-- Complete interval computation for depth 15, residue 12169. -/
theorem bounds_15_12169 : exactInterval 15 12169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12169 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12169) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12169 : oddCount 12169 15 = 8 ∧ acceleratedOrbit 15 12169 = 2437 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12169 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12169) = 3 ^ 8 * m + 2437 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12169.1, data_15_12169.2]

/-- Complete interval computation for depth 15, residue 12170. -/
theorem bounds_15_12170 : exactInterval 15 12170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12170 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12170) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12170 : oddCount 12170 15 = 5 ∧ acceleratedOrbit 15 12170 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12170 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12170) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12170.1, data_15_12170.2]

/-- Complete interval computation for depth 15, residue 12171. -/
theorem bounds_15_12171 : exactInterval 15 12171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12171 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12171) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12171 : oddCount 12171 15 = 8 ∧ acceleratedOrbit 15 12171 = 2438 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12171 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12171) = 3 ^ 8 * m + 2438 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12171.1, data_15_12171.2]

/-- Complete interval computation for depth 15, residue 12172. -/
theorem bounds_15_12172 : exactInterval 15 12172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12172 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12172) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12172 : oddCount 12172 15 = 5 ∧ acceleratedOrbit 15 12172 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12172 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12172) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12172.1, data_15_12172.2]

/-- Complete interval computation for depth 15, residue 12173. -/
theorem bounds_15_12173 : exactInterval 15 12173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12173 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12173) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12173 : oddCount 12173 15 = 5 ∧ acceleratedOrbit 15 12173 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12173 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12173) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12173.1, data_15_12173.2]

/-- Complete interval computation for depth 15, residue 12174. -/
theorem bounds_15_12174 : exactInterval 15 12174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12174 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12174) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12174 : oddCount 12174 15 = 9 ∧ acceleratedOrbit 15 12174 = 7316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12174 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12174) = 3 ^ 9 * m + 7316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12174.1, data_15_12174.2]

/-- Complete interval computation for depth 15, residue 12175. -/
theorem bounds_15_12175 : exactInterval 15 12175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12175 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12175) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12175 : oddCount 12175 15 = 9 ∧ acceleratedOrbit 15 12175 = 7316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12175 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12175) = 3 ^ 9 * m + 7316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12175.1, data_15_12175.2]

/-- Complete interval computation for depth 15, residue 12176. -/
theorem bounds_15_12176 : exactInterval 15 12176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12176 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12176) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12176 : oddCount 12176 15 = 6 ∧ acceleratedOrbit 15 12176 = 272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12176 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12176) = 3 ^ 6 * m + 272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12176.1, data_15_12176.2]

/-- Complete interval computation for depth 15, residue 12177. -/
theorem bounds_15_12177 : exactInterval 15 12177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12177 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12177) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12177 : oddCount 12177 15 = 8 ∧ acceleratedOrbit 15 12177 = 2440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12177 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12177) = 3 ^ 8 * m + 2440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12177.1, data_15_12177.2]

/-- Complete interval computation for depth 15, residue 12178. -/
theorem bounds_15_12178 : exactInterval 15 12178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12178 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12178) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12178 : oddCount 12178 15 = 8 ∧ acceleratedOrbit 15 12178 = 2440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12178 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12178) = 3 ^ 8 * m + 2440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12178.1, data_15_12178.2]

/-- Complete interval computation for depth 15, residue 12179. -/
theorem bounds_15_12179 : exactInterval 15 12179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12179 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12179) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12179 : oddCount 12179 15 = 8 ∧ acceleratedOrbit 15 12179 = 2440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12179 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12179) = 3 ^ 8 * m + 2440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12179.1, data_15_12179.2]

/-- Complete interval computation for depth 15, residue 12180. -/
theorem bounds_15_12180 : exactInterval 15 12180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12180 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12180) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12180 : oddCount 12180 15 = 6 ∧ acceleratedOrbit 15 12180 = 272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12180 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12180) = 3 ^ 6 * m + 272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12180.1, data_15_12180.2]

/-- Complete interval computation for depth 15, residue 12181. -/
theorem bounds_15_12181 : exactInterval 15 12181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12181 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12181) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12181 : oddCount 12181 15 = 6 ∧ acceleratedOrbit 15 12181 = 272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12181 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12181) = 3 ^ 6 * m + 272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12181.1, data_15_12181.2]

/-- Complete interval computation for depth 15, residue 12182. -/
theorem bounds_15_12182 : exactInterval 15 12182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12182 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12182) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12182 : oddCount 12182 15 = 6 ∧ acceleratedOrbit 15 12182 = 272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12182 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12182) = 3 ^ 6 * m + 272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12182.1, data_15_12182.2]

/-- Complete interval computation for depth 15, residue 12183. -/
theorem bounds_15_12183 : exactInterval 15 12183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12183 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12183) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12183 : oddCount 12183 15 = 6 ∧ acceleratedOrbit 15 12183 = 272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12183 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12183) = 3 ^ 6 * m + 272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12183.1, data_15_12183.2]

/-- Complete interval computation for depth 15, residue 12184. -/
theorem bounds_15_12184 : exactInterval 15 12184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12184 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12184) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12184 : oddCount 12184 15 = 6 ∧ acceleratedOrbit 15 12184 = 272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12184 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12184) = 3 ^ 6 * m + 272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12184.1, data_15_12184.2]

/-- Complete interval computation for depth 15, residue 12185. -/
theorem bounds_15_12185 : exactInterval 15 12185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12185 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12185) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12185 : oddCount 12185 15 = 6 ∧ acceleratedOrbit 15 12185 = 272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12185 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12185) = 3 ^ 6 * m + 272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12185.1, data_15_12185.2]

/-- Complete interval computation for depth 15, residue 12186. -/
theorem bounds_15_12186 : exactInterval 15 12186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12186 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12186) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12186 : oddCount 12186 15 = 6 ∧ acceleratedOrbit 15 12186 = 272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12186 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12186) = 3 ^ 6 * m + 272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12186.1, data_15_12186.2]

/-- Complete interval computation for depth 15, residue 12187. -/
theorem bounds_15_12187 : exactInterval 15 12187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12187 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12187) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12187 : oddCount 12187 15 = 8 ∧ acceleratedOrbit 15 12187 = 2441 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12187 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12187) = 3 ^ 8 * m + 2441 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12187.1, data_15_12187.2]

/-- Complete interval computation for depth 15, residue 12188. -/
theorem bounds_15_12188 : exactInterval 15 12188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12188 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12188) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12188 : oddCount 12188 15 = 7 ∧ acceleratedOrbit 15 12188 = 814 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12188 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12188) = 3 ^ 7 * m + 814 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12188.1, data_15_12188.2]

end Collatz.Research.PassageAtlas.Batch0372
