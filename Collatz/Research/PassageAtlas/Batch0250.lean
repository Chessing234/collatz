import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0250

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 8159. -/
theorem bounds_15_8159 : exactInterval 15 8159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8159 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8159) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8159 : oddCount 8159 15 = 8 ∧ acceleratedOrbit 15 8159 = 1634 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8159 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8159) = 3 ^ 8 * m + 1634 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8159.1, data_15_8159.2]

/-- Complete interval computation for depth 15, residue 8160. -/
theorem bounds_15_8160 : exactInterval 15 8160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8160 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8160) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8160 : oddCount 8160 15 = 8 ∧ acceleratedOrbit 15 8160 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8160 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8160) = 3 ^ 8 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8160.1, data_15_8160.2]

/-- Complete interval computation for depth 15, residue 8161. -/
theorem bounds_15_8161 : exactInterval 15 8161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8161 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8161) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8161 : oddCount 8161 15 = 11 ∧ acceleratedOrbit 15 8161 = 44135 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8161 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8161) = 3 ^ 11 * m + 44135 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8161.1, data_15_8161.2]

/-- Complete interval computation for depth 15, residue 8162. -/
theorem bounds_15_8162 : exactInterval 15 8162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8162 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8162) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8162 : oddCount 8162 15 = 8 ∧ acceleratedOrbit 15 8162 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8162 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8162) = 3 ^ 8 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8162.1, data_15_8162.2]

/-- Complete interval computation for depth 15, residue 8163. -/
theorem bounds_15_8163 : exactInterval 15 8163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8163 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8163) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8163 : oddCount 8163 15 = 8 ∧ acceleratedOrbit 15 8163 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8163 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8163) = 3 ^ 8 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8163.1, data_15_8163.2]

/-- Complete interval computation for depth 15, residue 8164. -/
theorem bounds_15_8164 : exactInterval 15 8164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8164 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8164) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8164 : oddCount 8164 15 = 8 ∧ acceleratedOrbit 15 8164 = 1637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8164 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8164) = 3 ^ 8 * m + 1637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8164.1, data_15_8164.2]

/-- Complete interval computation for depth 15, residue 8165. -/
theorem bounds_15_8165 : exactInterval 15 8165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8165 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8165) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8165 : oddCount 8165 15 = 8 ∧ acceleratedOrbit 15 8165 = 1637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8165 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8165) = 3 ^ 8 * m + 1637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8165.1, data_15_8165.2]

/-- Complete interval computation for depth 15, residue 8166. -/
theorem bounds_15_8166 : exactInterval 15 8166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8166 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8166) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8166 : oddCount 8166 15 = 8 ∧ acceleratedOrbit 15 8166 = 1637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8166 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8166) = 3 ^ 8 * m + 1637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8166.1, data_15_8166.2]

/-- Complete interval computation for depth 15, residue 8167. -/
theorem bounds_15_8167 : exactInterval 15 8167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8167 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8167) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8167 : oddCount 8167 15 = 9 ∧ acceleratedOrbit 15 8167 = 4907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8167 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8167) = 3 ^ 9 * m + 4907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8167.1, data_15_8167.2]

/-- Complete interval computation for depth 15, residue 8168. -/
theorem bounds_15_8168 : exactInterval 15 8168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8168 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8168) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8168 : oddCount 8168 15 = 8 ∧ acceleratedOrbit 15 8168 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8168 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8168) = 3 ^ 8 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8168.1, data_15_8168.2]

/-- Complete interval computation for depth 15, residue 8169. -/
theorem bounds_15_8169 : exactInterval 15 8169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8169 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8169) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8169 : oddCount 8169 15 = 8 ∧ acceleratedOrbit 15 8169 = 1636 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8169 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8169) = 3 ^ 8 * m + 1636 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8169.1, data_15_8169.2]

/-- Complete interval computation for depth 15, residue 8170. -/
theorem bounds_15_8170 : exactInterval 15 8170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8170 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8170) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8170 : oddCount 8170 15 = 8 ∧ acceleratedOrbit 15 8170 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8170 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8170) = 3 ^ 8 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8170.1, data_15_8170.2]

/-- Complete interval computation for depth 15, residue 8171. -/
theorem bounds_15_8171 : exactInterval 15 8171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8171 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8171) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8171 : oddCount 8171 15 = 11 ∧ acceleratedOrbit 15 8171 = 44185 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8171 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8171) = 3 ^ 11 * m + 44185 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8171.1, data_15_8171.2]

/-- Complete interval computation for depth 15, residue 8172. -/
theorem bounds_15_8172 : exactInterval 15 8172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8172 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8172) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8172 : oddCount 8172 15 = 10 ∧ acceleratedOrbit 15 8172 = 14741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8172 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8172) = 3 ^ 10 * m + 14741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8172.1, data_15_8172.2]

/-- Complete interval computation for depth 15, residue 8173. -/
theorem bounds_15_8173 : exactInterval 15 8173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8173 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8173) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8173 : oddCount 8173 15 = 10 ∧ acceleratedOrbit 15 8173 = 14741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8173 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8173) = 3 ^ 10 * m + 14741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8173.1, data_15_8173.2]

/-- Complete interval computation for depth 15, residue 8174. -/
theorem bounds_15_8174 : exactInterval 15 8174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8174 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8174) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8174 : oddCount 8174 15 = 10 ∧ acceleratedOrbit 15 8174 = 14741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8174 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8174) = 3 ^ 10 * m + 14741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8174.1, data_15_8174.2]

/-- Complete interval computation for depth 15, residue 8175. -/
theorem bounds_15_8175 : exactInterval 15 8175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8175 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8175) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8175 : oddCount 8175 15 = 10 ∧ acceleratedOrbit 15 8175 = 14735 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8175 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8175) = 3 ^ 10 * m + 14735 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8175.1, data_15_8175.2]

/-- Complete interval computation for depth 15, residue 8176. -/
theorem bounds_15_8176 : exactInterval 15 8176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8176 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8176) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8176 : oddCount 8176 15 = 10 ∧ acceleratedOrbit 15 8176 = 14762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8176 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8176) = 3 ^ 10 * m + 14762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8176.1, data_15_8176.2]

/-- Complete interval computation for depth 15, residue 8177. -/
theorem bounds_15_8177 : exactInterval 15 8177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8177 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8177) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8177 : oddCount 8177 15 = 8 ∧ acceleratedOrbit 15 8177 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8177 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8177) = 3 ^ 8 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8177.1, data_15_8177.2]

/-- Complete interval computation for depth 15, residue 8178. -/
theorem bounds_15_8178 : exactInterval 15 8178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8178 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8178) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8178 : oddCount 8178 15 = 9 ∧ acceleratedOrbit 15 8178 = 4916 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8178 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8178) = 3 ^ 9 * m + 4916 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8178.1, data_15_8178.2]

/-- Complete interval computation for depth 15, residue 8179. -/
theorem bounds_15_8179 : exactInterval 15 8179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8179 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8179) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8179 : oddCount 8179 15 = 9 ∧ acceleratedOrbit 15 8179 = 4916 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8179 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8179) = 3 ^ 9 * m + 4916 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8179.1, data_15_8179.2]

/-- Complete interval computation for depth 15, residue 8180. -/
theorem bounds_15_8180 : exactInterval 15 8180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8180 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8180) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8180 : oddCount 8180 15 = 10 ∧ acceleratedOrbit 15 8180 = 14762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8180 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8180) = 3 ^ 10 * m + 14762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8180.1, data_15_8180.2]

/-- Complete interval computation for depth 15, residue 8181. -/
theorem bounds_15_8181 : exactInterval 15 8181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8181 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8181) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8181 : oddCount 8181 15 = 10 ∧ acceleratedOrbit 15 8181 = 14762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8181 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8181) = 3 ^ 10 * m + 14762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8181.1, data_15_8181.2]

/-- Complete interval computation for depth 15, residue 8182. -/
theorem bounds_15_8182 : exactInterval 15 8182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8182 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8182) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8182 : oddCount 8182 15 = 8 ∧ acceleratedOrbit 15 8182 = 1639 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8182 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8182) = 3 ^ 8 * m + 1639 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8182.1, data_15_8182.2]

/-- Complete interval computation for depth 15, residue 8183. -/
theorem bounds_15_8183 : exactInterval 15 8183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8183 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8183) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8183 : oddCount 8183 15 = 8 ∧ acceleratedOrbit 15 8183 = 1639 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8183 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8183) = 3 ^ 8 * m + 1639 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8183.1, data_15_8183.2]

/-- Complete interval computation for depth 15, residue 8184. -/
theorem bounds_15_8184 : exactInterval 15 8184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8184 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8184) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8184 : oddCount 8184 15 = 10 ∧ acceleratedOrbit 15 8184 = 14762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8184 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8184) = 3 ^ 10 * m + 14762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8184.1, data_15_8184.2]

/-- Complete interval computation for depth 15, residue 8185. -/
theorem bounds_15_8185 : exactInterval 15 8185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8185 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8185) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8185 : oddCount 8185 15 = 10 ∧ acceleratedOrbit 15 8185 = 14755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8185 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8185) = 3 ^ 10 * m + 14755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8185.1, data_15_8185.2]

/-- Complete interval computation for depth 15, residue 8186. -/
theorem bounds_15_8186 : exactInterval 15 8186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8186 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8186) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8186 : oddCount 8186 15 = 10 ∧ acceleratedOrbit 15 8186 = 14762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8186 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8186) = 3 ^ 10 * m + 14762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8186.1, data_15_8186.2]

/-- Complete interval computation for depth 15, residue 8187. -/
theorem bounds_15_8187 : exactInterval 15 8187 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8187 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8187) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8187 : oddCount 8187 15 = 9 ∧ acceleratedOrbit 15 8187 = 4919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8187 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8187) = 3 ^ 9 * m + 4919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8187.1, data_15_8187.2]

/-- Complete interval computation for depth 15, residue 8188. -/
theorem bounds_15_8188 : exactInterval 15 8188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8188 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8188) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8188 : oddCount 8188 15 = 12 ∧ acceleratedOrbit 15 8188 = 132860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8188 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8188) = 3 ^ 12 * m + 132860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8188.1, data_15_8188.2]

/-- Complete interval computation for depth 15, residue 8189. -/
theorem bounds_15_8189 : exactInterval 15 8189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8189 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8189) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8189 : oddCount 8189 15 = 12 ∧ acceleratedOrbit 15 8189 = 132860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8189 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8189) = 3 ^ 12 * m + 132860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8189.1, data_15_8189.2]

/-- Complete interval computation for depth 15, residue 8190. -/
theorem bounds_15_8190 : exactInterval 15 8190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8190 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8190) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8190 : oddCount 8190 15 = 12 ∧ acceleratedOrbit 15 8190 = 132860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8190 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8190) = 3 ^ 12 * m + 132860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8190.1, data_15_8190.2]

/-- Complete interval computation for depth 15, residue 8191. -/
theorem bounds_15_8191 : exactInterval 15 8191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8191 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8191) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8191 : oddCount 8191 15 = 14 ∧ acceleratedOrbit 15 8191 = 1195742 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8191 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8191) = 3 ^ 14 * m + 1195742 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8191.1, data_15_8191.2]

end Collatz.Research.PassageAtlas.Batch0250
