import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0769

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 25165. -/
theorem bounds_15_25165 : exactInterval 15 25165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25165 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25165) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25165 : oddCount 25165 15 = 8 ∧ acceleratedOrbit 15 25165 = 5042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25165 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25165) = 3 ^ 8 * m + 5042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25165.1, data_15_25165.2]

/-- Complete interval computation for depth 15, residue 25166. -/
theorem bounds_15_25166 : exactInterval 15 25166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25166 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25166) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25166 : oddCount 25166 15 = 10 ∧ acceleratedOrbit 15 25166 = 45359 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25166 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25166) = 3 ^ 10 * m + 45359 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25166.1, data_15_25166.2]

/-- Complete interval computation for depth 15, residue 25167. -/
theorem bounds_15_25167 : exactInterval 15 25167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25167 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25167) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25167 : oddCount 25167 15 = 10 ∧ acceleratedOrbit 15 25167 = 45359 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25167 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25167) = 3 ^ 10 * m + 45359 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25167.1, data_15_25167.2]

/-- Complete interval computation for depth 15, residue 25168. -/
theorem bounds_15_25168 : exactInterval 15 25168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25168 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25168) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25168 : oddCount 25168 15 = 6 ∧ acceleratedOrbit 15 25168 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25168 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25168) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25168.1, data_15_25168.2]

/-- Complete interval computation for depth 15, residue 25169. -/
theorem bounds_15_25169 : exactInterval 15 25169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25169 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25169) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25169 : oddCount 25169 15 = 9 ∧ acceleratedOrbit 15 25169 = 15122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25169 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25169) = 3 ^ 9 * m + 15122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25169.1, data_15_25169.2]

/-- Complete interval computation for depth 15, residue 25170. -/
theorem bounds_15_25170 : exactInterval 15 25170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25170 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25170) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25170 : oddCount 25170 15 = 9 ∧ acceleratedOrbit 15 25170 = 15122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25170 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25170) = 3 ^ 9 * m + 15122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25170.1, data_15_25170.2]

/-- Complete interval computation for depth 15, residue 25171. -/
theorem bounds_15_25171 : exactInterval 15 25171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25171 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25171) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25171 : oddCount 25171 15 = 9 ∧ acceleratedOrbit 15 25171 = 15122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25171 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25171) = 3 ^ 9 * m + 15122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25171.1, data_15_25171.2]

/-- Complete interval computation for depth 15, residue 25172. -/
theorem bounds_15_25172 : exactInterval 15 25172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25172 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25172) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25172 : oddCount 25172 15 = 6 ∧ acceleratedOrbit 15 25172 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25172 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25172) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25172.1, data_15_25172.2]

/-- Complete interval computation for depth 15, residue 25173. -/
theorem bounds_15_25173 : exactInterval 15 25173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25173 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25173) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25173 : oddCount 25173 15 = 6 ∧ acceleratedOrbit 15 25173 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25173 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25173) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25173.1, data_15_25173.2]

/-- Complete interval computation for depth 15, residue 25174. -/
theorem bounds_15_25174 : exactInterval 15 25174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25174 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25174) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25174 : oddCount 25174 15 = 8 ∧ acceleratedOrbit 15 25174 = 5042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25174 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25174) = 3 ^ 8 * m + 5042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25174.1, data_15_25174.2]

/-- Complete interval computation for depth 15, residue 25175. -/
theorem bounds_15_25175 : exactInterval 15 25175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25175 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25175) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25175 : oddCount 25175 15 = 8 ∧ acceleratedOrbit 15 25175 = 5042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25175 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25175) = 3 ^ 8 * m + 5042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25175.1, data_15_25175.2]

/-- Complete interval computation for depth 15, residue 25176. -/
theorem bounds_15_25176 : exactInterval 15 25176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25176 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25176) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25176 : oddCount 25176 15 = 5 ∧ acceleratedOrbit 15 25176 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25176 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25176) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25176.1, data_15_25176.2]

/-- Complete interval computation for depth 15, residue 25177. -/
theorem bounds_15_25177 : exactInterval 15 25177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25177 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25177) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25177 : oddCount 25177 15 = 10 ∧ acceleratedOrbit 15 25177 = 45380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25177 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25177) = 3 ^ 10 * m + 45380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25177.1, data_15_25177.2]

/-- Complete interval computation for depth 15, residue 25178. -/
theorem bounds_15_25178 : exactInterval 15 25178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25178 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25178) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25178 : oddCount 25178 15 = 5 ∧ acceleratedOrbit 15 25178 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25178 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25178) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25178.1, data_15_25178.2]

/-- Complete interval computation for depth 15, residue 25179. -/
theorem bounds_15_25179 : exactInterval 15 25179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25179 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25179) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25179 : oddCount 25179 15 = 10 ∧ acceleratedOrbit 15 25179 = 45377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25179 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25179) = 3 ^ 10 * m + 45377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25179.1, data_15_25179.2]

/-- Complete interval computation for depth 15, residue 25180. -/
theorem bounds_15_25180 : exactInterval 15 25180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25180 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25180) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25180 : oddCount 25180 15 = 5 ∧ acceleratedOrbit 15 25180 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25180 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25180) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25180.1, data_15_25180.2]

/-- Complete interval computation for depth 15, residue 25181. -/
theorem bounds_15_25181 : exactInterval 15 25181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25181 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25181) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25181 : oddCount 25181 15 = 5 ∧ acceleratedOrbit 15 25181 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25181 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25181) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25181.1, data_15_25181.2]

/-- Complete interval computation for depth 15, residue 25182. -/
theorem bounds_15_25182 : exactInterval 15 25182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25182 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25182) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25182 : oddCount 25182 15 = 10 ∧ acceleratedOrbit 15 25182 = 45386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25182 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25182) = 3 ^ 10 * m + 45386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25182.1, data_15_25182.2]

/-- Complete interval computation for depth 15, residue 25183. -/
theorem bounds_15_25183 : exactInterval 15 25183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25183 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25183) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25183 : oddCount 25183 15 = 10 ∧ acceleratedOrbit 15 25183 = 45386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25183 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25183) = 3 ^ 10 * m + 45386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25183.1, data_15_25183.2]

/-- Complete interval computation for depth 15, residue 25184. -/
theorem bounds_15_25184 : exactInterval 15 25184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25184 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25184) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25184 : oddCount 25184 15 = 6 ∧ acceleratedOrbit 15 25184 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25184 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25184) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25184.1, data_15_25184.2]

/-- Complete interval computation for depth 15, residue 25185. -/
theorem bounds_15_25185 : exactInterval 15 25185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25185 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25185) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25185 : oddCount 25185 15 = 8 ∧ acceleratedOrbit 15 25185 = 5044 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25185 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25185) = 3 ^ 8 * m + 5044 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25185.1, data_15_25185.2]

/-- Complete interval computation for depth 15, residue 25186. -/
theorem bounds_15_25186 : exactInterval 15 25186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25186 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25186) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25186 : oddCount 25186 15 = 8 ∧ acceleratedOrbit 15 25186 = 5048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25186 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25186) = 3 ^ 8 * m + 5048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25186.1, data_15_25186.2]

/-- Complete interval computation for depth 15, residue 25187. -/
theorem bounds_15_25187 : exactInterval 15 25187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25187 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25187) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25187 : oddCount 25187 15 = 8 ∧ acceleratedOrbit 15 25187 = 5048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25187 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25187) = 3 ^ 8 * m + 5048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25187.1, data_15_25187.2]

/-- Complete interval computation for depth 15, residue 25188. -/
theorem bounds_15_25188 : exactInterval 15 25188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25188 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25188) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25188 : oddCount 25188 15 = 8 ∧ acceleratedOrbit 15 25188 = 5048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25188 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25188) = 3 ^ 8 * m + 5048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25188.1, data_15_25188.2]

/-- Complete interval computation for depth 15, residue 25189. -/
theorem bounds_15_25189 : exactInterval 15 25189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25189 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25189) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25189 : oddCount 25189 15 = 8 ∧ acceleratedOrbit 15 25189 = 5048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25189 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25189) = 3 ^ 8 * m + 5048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25189.1, data_15_25189.2]

/-- Complete interval computation for depth 15, residue 25190. -/
theorem bounds_15_25190 : exactInterval 15 25190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25190 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25190) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25190 : oddCount 25190 15 = 8 ∧ acceleratedOrbit 15 25190 = 5048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25190 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25190) = 3 ^ 8 * m + 5048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25190.1, data_15_25190.2]

/-- Complete interval computation for depth 15, residue 25191. -/
theorem bounds_15_25191 : exactInterval 15 25191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25191 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25191) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25191 : oddCount 25191 15 = 9 ∧ acceleratedOrbit 15 25191 = 15133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25191 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25191) = 3 ^ 9 * m + 15133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25191.1, data_15_25191.2]

/-- Complete interval computation for depth 15, residue 25192. -/
theorem bounds_15_25192 : exactInterval 15 25192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25192 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25192) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25192 : oddCount 25192 15 = 6 ∧ acceleratedOrbit 15 25192 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25192 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25192) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25192.1, data_15_25192.2]

/-- Complete interval computation for depth 15, residue 25193. -/
theorem bounds_15_25193 : exactInterval 15 25193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25193 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25193) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25193 : oddCount 25193 15 = 10 ∧ acceleratedOrbit 15 25193 = 45404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25193 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25193) = 3 ^ 10 * m + 45404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25193.1, data_15_25193.2]

/-- Complete interval computation for depth 15, residue 25194. -/
theorem bounds_15_25194 : exactInterval 15 25194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25194 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25194) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25194 : oddCount 25194 15 = 6 ∧ acceleratedOrbit 15 25194 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25194 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25194) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25194.1, data_15_25194.2]

/-- Complete interval computation for depth 15, residue 25195. -/
theorem bounds_15_25195 : exactInterval 15 25195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25195 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25195) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25195 : oddCount 25195 15 = 9 ∧ acceleratedOrbit 15 25195 = 15137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25195 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25195) = 3 ^ 9 * m + 15137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25195.1, data_15_25195.2]

/-- Complete interval computation for depth 15, residue 25196. -/
theorem bounds_15_25196 : exactInterval 15 25196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25196 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25196) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25196 : oddCount 25196 15 = 7 ∧ acceleratedOrbit 15 25196 = 1682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25196 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25196) = 3 ^ 7 * m + 1682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25196.1, data_15_25196.2]

/-- Complete interval computation for depth 15, residue 25197. -/
theorem bounds_15_25197 : exactInterval 15 25197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25197 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25197) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25197 : oddCount 25197 15 = 7 ∧ acceleratedOrbit 15 25197 = 1682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25197 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25197) = 3 ^ 7 * m + 1682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25197.1, data_15_25197.2]

end Collatz.Research.PassageAtlas.Batch0769
