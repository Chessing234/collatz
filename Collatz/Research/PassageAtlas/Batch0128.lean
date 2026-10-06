import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0128

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 4161. -/
theorem bounds_15_4161 : exactInterval 15 4161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4161 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4161) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4161 : oddCount 4161 15 = 8 ∧ acceleratedOrbit 15 4161 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4161 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4161) = 3 ^ 8 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4161.1, data_15_4161.2]

/-- Complete interval computation for depth 15, residue 4162. -/
theorem bounds_15_4162 : exactInterval 15 4162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4162 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4162) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4162 : oddCount 4162 15 = 8 ∧ acceleratedOrbit 15 4162 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4162 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4162) = 3 ^ 8 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4162.1, data_15_4162.2]

/-- Complete interval computation for depth 15, residue 4163. -/
theorem bounds_15_4163 : exactInterval 15 4163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4163 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4163) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4163 : oddCount 4163 15 = 8 ∧ acceleratedOrbit 15 4163 = 836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4163 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4163) = 3 ^ 8 * m + 836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4163.1, data_15_4163.2]

/-- Complete interval computation for depth 15, residue 4164. -/
theorem bounds_15_4164 : exactInterval 15 4164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4164 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4164) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4164 : oddCount 4164 15 = 6 ∧ acceleratedOrbit 15 4164 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4164 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4164) = 3 ^ 6 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4164.1, data_15_4164.2]

/-- Complete interval computation for depth 15, residue 4165. -/
theorem bounds_15_4165 : exactInterval 15 4165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4165 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4165) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4165 : oddCount 4165 15 = 6 ∧ acceleratedOrbit 15 4165 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4165 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4165) = 3 ^ 6 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4165.1, data_15_4165.2]

/-- Complete interval computation for depth 15, residue 4166. -/
theorem bounds_15_4166 : exactInterval 15 4166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4166 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4166) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4166 : oddCount 4166 15 = 6 ∧ acceleratedOrbit 15 4166 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4166 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4166) = 3 ^ 6 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4166.1, data_15_4166.2]

/-- Complete interval computation for depth 15, residue 4167. -/
theorem bounds_15_4167 : exactInterval 15 4167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4167 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4167) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4167 : oddCount 4167 15 = 11 ∧ acceleratedOrbit 15 4167 = 22538 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4167 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4167) = 3 ^ 11 * m + 22538 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4167.1, data_15_4167.2]

/-- Complete interval computation for depth 15, residue 4168. -/
theorem bounds_15_4168 : exactInterval 15 4168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4168 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4168) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4168 : oddCount 4168 15 = 5 ∧ acceleratedOrbit 15 4168 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4168 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4168) = 3 ^ 5 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4168.1, data_15_4168.2]

/-- Complete interval computation for depth 15, residue 4169. -/
theorem bounds_15_4169 : exactInterval 15 4169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4169 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4169) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4169 : oddCount 4169 15 = 9 ∧ acceleratedOrbit 15 4169 = 2506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4169 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4169) = 3 ^ 9 * m + 2506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4169.1, data_15_4169.2]

/-- Complete interval computation for depth 15, residue 4170. -/
theorem bounds_15_4170 : exactInterval 15 4170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4170 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4170) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4170 : oddCount 4170 15 = 5 ∧ acceleratedOrbit 15 4170 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4170 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4170) = 3 ^ 5 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4170.1, data_15_4170.2]

/-- Complete interval computation for depth 15, residue 4171. -/
theorem bounds_15_4171 : exactInterval 15 4171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4171 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4171) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4171 : oddCount 4171 15 = 6 ∧ acceleratedOrbit 15 4171 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4171 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4171) = 3 ^ 6 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4171.1, data_15_4171.2]

/-- Complete interval computation for depth 15, residue 4172. -/
theorem bounds_15_4172 : exactInterval 15 4172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4172 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4172) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4172 : oddCount 4172 15 = 5 ∧ acceleratedOrbit 15 4172 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4172 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4172) = 3 ^ 5 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4172.1, data_15_4172.2]

/-- Complete interval computation for depth 15, residue 4173. -/
theorem bounds_15_4173 : exactInterval 15 4173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4173 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4173) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4173 : oddCount 4173 15 = 5 ∧ acceleratedOrbit 15 4173 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4173 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4173) = 3 ^ 5 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4173.1, data_15_4173.2]

/-- Complete interval computation for depth 15, residue 4174. -/
theorem bounds_15_4174 : exactInterval 15 4174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4174 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4174) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4174 : oddCount 4174 15 = 10 ∧ acceleratedOrbit 15 4174 = 7532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4174 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4174) = 3 ^ 10 * m + 7532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4174.1, data_15_4174.2]

/-- Complete interval computation for depth 15, residue 4175. -/
theorem bounds_15_4175 : exactInterval 15 4175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4175 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4175) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4175 : oddCount 4175 15 = 10 ∧ acceleratedOrbit 15 4175 = 7532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4175 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4175) = 3 ^ 10 * m + 7532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4175.1, data_15_4175.2]

/-- Complete interval computation for depth 15, residue 4176. -/
theorem bounds_15_4176 : exactInterval 15 4176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4176 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4176) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4176 : oddCount 4176 15 = 4 ∧ acceleratedOrbit 15 4176 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4176 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4176) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4176.1, data_15_4176.2]

/-- Complete interval computation for depth 15, residue 4177. -/
theorem bounds_15_4177 : exactInterval 15 4177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4177 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4177) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4177 : oddCount 4177 15 = 5 ∧ acceleratedOrbit 15 4177 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4177 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4177) = 3 ^ 5 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4177.1, data_15_4177.2]

/-- Complete interval computation for depth 15, residue 4178. -/
theorem bounds_15_4178 : exactInterval 15 4178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4178 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4178) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4178 : oddCount 4178 15 = 9 ∧ acceleratedOrbit 15 4178 = 2512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4178 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4178) = 3 ^ 9 * m + 2512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4178.1, data_15_4178.2]

/-- Complete interval computation for depth 15, residue 4179. -/
theorem bounds_15_4179 : exactInterval 15 4179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4179 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4179) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4179 : oddCount 4179 15 = 9 ∧ acceleratedOrbit 15 4179 = 2512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4179 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4179) = 3 ^ 9 * m + 2512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4179.1, data_15_4179.2]

/-- Complete interval computation for depth 15, residue 4180. -/
theorem bounds_15_4180 : exactInterval 15 4180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4180 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4180) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4180 : oddCount 4180 15 = 4 ∧ acceleratedOrbit 15 4180 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4180 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4180) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4180.1, data_15_4180.2]

/-- Complete interval computation for depth 15, residue 4181. -/
theorem bounds_15_4181 : exactInterval 15 4181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4181 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4181) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4181 : oddCount 4181 15 = 4 ∧ acceleratedOrbit 15 4181 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4181 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4181) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4181.1, data_15_4181.2]

/-- Complete interval computation for depth 15, residue 4182. -/
theorem bounds_15_4182 : exactInterval 15 4182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4182 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4182) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4182 : oddCount 4182 15 = 7 ∧ acceleratedOrbit 15 4182 = 280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4182 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4182) = 3 ^ 7 * m + 280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4182.1, data_15_4182.2]

/-- Complete interval computation for depth 15, residue 4183. -/
theorem bounds_15_4183 : exactInterval 15 4183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4183 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4183) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4183 : oddCount 4183 15 = 7 ∧ acceleratedOrbit 15 4183 = 280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4183 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4183) = 3 ^ 7 * m + 280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4183.1, data_15_4183.2]

/-- Complete interval computation for depth 15, residue 4184. -/
theorem bounds_15_4184 : exactInterval 15 4184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4184 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4184) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4184 : oddCount 4184 15 = 6 ∧ acceleratedOrbit 15 4184 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4184 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4184) = 3 ^ 6 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4184.1, data_15_4184.2]

/-- Complete interval computation for depth 15, residue 4185. -/
theorem bounds_15_4185 : exactInterval 15 4185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4185 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4185) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4185 : oddCount 4185 15 = 7 ∧ acceleratedOrbit 15 4185 = 280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4185 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4185) = 3 ^ 7 * m + 280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4185.1, data_15_4185.2]

/-- Complete interval computation for depth 15, residue 4186. -/
theorem bounds_15_4186 : exactInterval 15 4186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4186 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4186) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4186 : oddCount 4186 15 = 6 ∧ acceleratedOrbit 15 4186 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4186 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4186) = 3 ^ 6 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4186.1, data_15_4186.2]

/-- Complete interval computation for depth 15, residue 4187. -/
theorem bounds_15_4187 : exactInterval 15 4187 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4187 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4187) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4187 : oddCount 4187 15 = 9 ∧ acceleratedOrbit 15 4187 = 2516 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4187 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4187) = 3 ^ 9 * m + 2516 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4187.1, data_15_4187.2]

/-- Complete interval computation for depth 15, residue 4188. -/
theorem bounds_15_4188 : exactInterval 15 4188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4188 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4188) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4188 : oddCount 4188 15 = 6 ∧ acceleratedOrbit 15 4188 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4188 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4188) = 3 ^ 6 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4188.1, data_15_4188.2]

/-- Complete interval computation for depth 15, residue 4189. -/
theorem bounds_15_4189 : exactInterval 15 4189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4189 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4189) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4189 : oddCount 4189 15 = 6 ∧ acceleratedOrbit 15 4189 = 94 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4189 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4189) = 3 ^ 6 * m + 94 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4189.1, data_15_4189.2]

/-- Complete interval computation for depth 15, residue 4190. -/
theorem bounds_15_4190 : exactInterval 15 4190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4190 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4190) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4190 : oddCount 4190 15 = 9 ∧ acceleratedOrbit 15 4190 = 2519 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4190 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4190) = 3 ^ 9 * m + 2519 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4190.1, data_15_4190.2]

/-- Complete interval computation for depth 15, residue 4191. -/
theorem bounds_15_4191 : exactInterval 15 4191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4191 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4191) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4191 : oddCount 4191 15 = 9 ∧ acceleratedOrbit 15 4191 = 2519 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4191 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4191) = 3 ^ 9 * m + 2519 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4191.1, data_15_4191.2]

/-- Complete interval computation for depth 15, residue 4192. -/
theorem bounds_15_4192 : exactInterval 15 4192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4192 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4192) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4192 : oddCount 4192 15 = 4 ∧ acceleratedOrbit 15 4192 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4192 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4192) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4192.1, data_15_4192.2]

/-- Complete interval computation for depth 15, residue 4193. -/
theorem bounds_15_4193 : exactInterval 15 4193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4193 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4193) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4193 : oddCount 4193 15 = 9 ∧ acceleratedOrbit 15 4193 = 2521 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4193 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4193) = 3 ^ 9 * m + 2521 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4193.1, data_15_4193.2]

end Collatz.Research.PassageAtlas.Batch0128
