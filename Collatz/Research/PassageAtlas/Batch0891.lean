import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0891

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 29163. -/
theorem bounds_15_29163 : exactInterval 15 29163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29163 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29163) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29163 : oddCount 29163 15 = 11 ∧ acceleratedOrbit 15 29163 = 157670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29163 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29163) = 3 ^ 11 * m + 157670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29163.1, data_15_29163.2]

/-- Complete interval computation for depth 15, residue 29164. -/
theorem bounds_15_29164 : exactInterval 15 29164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29164 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29164) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29164 : oddCount 29164 15 = 6 ∧ acceleratedOrbit 15 29164 = 649 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29164 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29164) = 3 ^ 6 * m + 649 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29164.1, data_15_29164.2]

/-- Complete interval computation for depth 15, residue 29165. -/
theorem bounds_15_29165 : exactInterval 15 29165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29165 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29165) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29165 : oddCount 29165 15 = 6 ∧ acceleratedOrbit 15 29165 = 649 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29165 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29165) = 3 ^ 6 * m + 649 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29165.1, data_15_29165.2]

/-- Complete interval computation for depth 15, residue 29166. -/
theorem bounds_15_29166 : exactInterval 15 29166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29166 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29166) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29166 : oddCount 29166 15 = 6 ∧ acceleratedOrbit 15 29166 = 649 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29166 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29166) = 3 ^ 6 * m + 649 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29166.1, data_15_29166.2]

/-- Complete interval computation for depth 15, residue 29167. -/
theorem bounds_15_29167 : exactInterval 15 29167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29167 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29167) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29167 : oddCount 29167 15 = 12 ∧ acceleratedOrbit 15 29167 = 473060 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29167 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29167) = 3 ^ 12 * m + 473060 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29167.1, data_15_29167.2]

/-- Complete interval computation for depth 15, residue 29168. -/
theorem bounds_15_29168 : exactInterval 15 29168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29168 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29168) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29168 : oddCount 29168 15 = 7 ∧ acceleratedOrbit 15 29168 = 1948 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29168 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29168) = 3 ^ 7 * m + 1948 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29168.1, data_15_29168.2]

/-- Complete interval computation for depth 15, residue 29169. -/
theorem bounds_15_29169 : exactInterval 15 29169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29169 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29169) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29169 : oddCount 29169 15 = 6 ∧ acceleratedOrbit 15 29169 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29169 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29169) = 3 ^ 6 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29169.1, data_15_29169.2]

/-- Complete interval computation for depth 15, residue 29170. -/
theorem bounds_15_29170 : exactInterval 15 29170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29170 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29170) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29170 : oddCount 29170 15 = 8 ∧ acceleratedOrbit 15 29170 = 5842 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29170 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29170) = 3 ^ 8 * m + 5842 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29170.1, data_15_29170.2]

/-- Complete interval computation for depth 15, residue 29171. -/
theorem bounds_15_29171 : exactInterval 15 29171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29171 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29171) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29171 : oddCount 29171 15 = 8 ∧ acceleratedOrbit 15 29171 = 5842 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29171 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29171) = 3 ^ 8 * m + 5842 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29171.1, data_15_29171.2]

/-- Complete interval computation for depth 15, residue 29172. -/
theorem bounds_15_29172 : exactInterval 15 29172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29172 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29172) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29172 : oddCount 29172 15 = 7 ∧ acceleratedOrbit 15 29172 = 1948 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29172 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29172) = 3 ^ 7 * m + 1948 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29172.1, data_15_29172.2]

/-- Complete interval computation for depth 15, residue 29173. -/
theorem bounds_15_29173 : exactInterval 15 29173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29173 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29173) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29173 : oddCount 29173 15 = 7 ∧ acceleratedOrbit 15 29173 = 1948 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29173 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29173) = 3 ^ 7 * m + 1948 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29173.1, data_15_29173.2]

/-- Complete interval computation for depth 15, residue 29174. -/
theorem bounds_15_29174 : exactInterval 15 29174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29174 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29174) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29174 : oddCount 29174 15 = 10 ∧ acceleratedOrbit 15 29174 = 52579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29174 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29174) = 3 ^ 10 * m + 52579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29174.1, data_15_29174.2]

/-- Complete interval computation for depth 15, residue 29175. -/
theorem bounds_15_29175 : exactInterval 15 29175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29175 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29175) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29175 : oddCount 29175 15 = 10 ∧ acceleratedOrbit 15 29175 = 52579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29175 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29175) = 3 ^ 10 * m + 52579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29175.1, data_15_29175.2]

/-- Complete interval computation for depth 15, residue 29176. -/
theorem bounds_15_29176 : exactInterval 15 29176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29176 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29176) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29176 : oddCount 29176 15 = 7 ∧ acceleratedOrbit 15 29176 = 1948 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29176 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29176) = 3 ^ 7 * m + 1948 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29176.1, data_15_29176.2]

/-- Complete interval computation for depth 15, residue 29177. -/
theorem bounds_15_29177 : exactInterval 15 29177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29177 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29177) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29177 : oddCount 29177 15 = 8 ∧ acceleratedOrbit 15 29177 = 5843 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29177 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29177) = 3 ^ 8 * m + 5843 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29177.1, data_15_29177.2]

/-- Complete interval computation for depth 15, residue 29178. -/
theorem bounds_15_29178 : exactInterval 15 29178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29178 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29178) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29178 : oddCount 29178 15 = 7 ∧ acceleratedOrbit 15 29178 = 1948 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29178 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29178) = 3 ^ 7 * m + 1948 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29178.1, data_15_29178.2]

/-- Complete interval computation for depth 15, residue 29179. -/
theorem bounds_15_29179 : exactInterval 15 29179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29179 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29179) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29179 : oddCount 29179 15 = 8 ∧ acceleratedOrbit 15 29179 = 5843 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29179 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29179) = 3 ^ 8 * m + 5843 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29179.1, data_15_29179.2]

/-- Complete interval computation for depth 15, residue 29180. -/
theorem bounds_15_29180 : exactInterval 15 29180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29180 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29180) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29180 : oddCount 29180 15 = 10 ∧ acceleratedOrbit 15 29180 = 52591 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29180 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29180) = 3 ^ 10 * m + 52591 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29180.1, data_15_29180.2]

/-- Complete interval computation for depth 15, residue 29181. -/
theorem bounds_15_29181 : exactInterval 15 29181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29181 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29181) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29181 : oddCount 29181 15 = 10 ∧ acceleratedOrbit 15 29181 = 52591 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29181 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29181) = 3 ^ 10 * m + 52591 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29181.1, data_15_29181.2]

/-- Complete interval computation for depth 15, residue 29182. -/
theorem bounds_15_29182 : exactInterval 15 29182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29182 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29182) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29182 : oddCount 29182 15 = 10 ∧ acceleratedOrbit 15 29182 = 52591 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29182 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29182) = 3 ^ 10 * m + 52591 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29182.1, data_15_29182.2]

/-- Complete interval computation for depth 15, residue 29183. -/
theorem bounds_15_29183 : exactInterval 15 29183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29183 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29183) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29183 : oddCount 29183 15 = 11 ∧ acceleratedOrbit 15 29183 = 157772 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29183 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29183) = 3 ^ 11 * m + 157772 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29183.1, data_15_29183.2]

/-- Complete interval computation for depth 15, residue 29184. -/
theorem bounds_15_29184 : exactInterval 15 29184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29184 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29184) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29184 : oddCount 29184 15 = 4 ∧ acceleratedOrbit 15 29184 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29184 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29184) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29184.1, data_15_29184.2]

/-- Complete interval computation for depth 15, residue 29185. -/
theorem bounds_15_29185 : exactInterval 15 29185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29185 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29185) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29185 : oddCount 29185 15 = 8 ∧ acceleratedOrbit 15 29185 = 5845 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29185 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29185) = 3 ^ 8 * m + 5845 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29185.1, data_15_29185.2]

/-- Complete interval computation for depth 15, residue 29186. -/
theorem bounds_15_29186 : exactInterval 15 29186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29186 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29186) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29186 : oddCount 29186 15 = 6 ∧ acceleratedOrbit 15 29186 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29186 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29186) = 3 ^ 6 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29186.1, data_15_29186.2]

/-- Complete interval computation for depth 15, residue 29187. -/
theorem bounds_15_29187 : exactInterval 15 29187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29187 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29187) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29187 : oddCount 29187 15 = 6 ∧ acceleratedOrbit 15 29187 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29187 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29187) = 3 ^ 6 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29187.1, data_15_29187.2]

/-- Complete interval computation for depth 15, residue 29188. -/
theorem bounds_15_29188 : exactInterval 15 29188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29188 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29188) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29188 : oddCount 29188 15 = 7 ∧ acceleratedOrbit 15 29188 = 1949 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29188 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29188) = 3 ^ 7 * m + 1949 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29188.1, data_15_29188.2]

/-- Complete interval computation for depth 15, residue 29189. -/
theorem bounds_15_29189 : exactInterval 15 29189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29189 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29189) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29189 : oddCount 29189 15 = 7 ∧ acceleratedOrbit 15 29189 = 1949 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29189 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29189) = 3 ^ 7 * m + 1949 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29189.1, data_15_29189.2]

/-- Complete interval computation for depth 15, residue 29190. -/
theorem bounds_15_29190 : exactInterval 15 29190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29190 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29190) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29190 : oddCount 29190 15 = 7 ∧ acceleratedOrbit 15 29190 = 1949 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29190 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29190) = 3 ^ 7 * m + 1949 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29190.1, data_15_29190.2]

/-- Complete interval computation for depth 15, residue 29191. -/
theorem bounds_15_29191 : exactInterval 15 29191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29191 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29191) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29191 : oddCount 29191 15 = 10 ∧ acceleratedOrbit 15 29191 = 52609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29191 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29191) = 3 ^ 10 * m + 52609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29191.1, data_15_29191.2]

/-- Complete interval computation for depth 15, residue 29192. -/
theorem bounds_15_29192 : exactInterval 15 29192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29192 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29192) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29192 : oddCount 29192 15 = 5 ∧ acceleratedOrbit 15 29192 = 217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29192 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29192) = 3 ^ 5 * m + 217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29192.1, data_15_29192.2]

/-- Complete interval computation for depth 15, residue 29193. -/
theorem bounds_15_29193 : exactInterval 15 29193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29193 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29193) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29193 : oddCount 29193 15 = 6 ∧ acceleratedOrbit 15 29193 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29193 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29193) = 3 ^ 6 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29193.1, data_15_29193.2]

/-- Complete interval computation for depth 15, residue 29194. -/
theorem bounds_15_29194 : exactInterval 15 29194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29194 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29194) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29194 : oddCount 29194 15 = 5 ∧ acceleratedOrbit 15 29194 = 217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29194 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29194) = 3 ^ 5 * m + 217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29194.1, data_15_29194.2]

/-- Complete interval computation for depth 15, residue 29195. -/
theorem bounds_15_29195 : exactInterval 15 29195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29195 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29195) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29195 : oddCount 29195 15 = 7 ∧ acceleratedOrbit 15 29195 = 1949 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29195 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29195) = 3 ^ 7 * m + 1949 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29195.1, data_15_29195.2]

end Collatz.Research.PassageAtlas.Batch0891
