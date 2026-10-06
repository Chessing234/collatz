import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0464

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 15171. -/
theorem bounds_15_15171 : exactInterval 15 15171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15171 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15171) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15171 : oddCount 15171 15 = 7 ∧ acceleratedOrbit 15 15171 = 1013 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15171 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15171) = 3 ^ 7 * m + 1013 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15171.1, data_15_15171.2]

/-- Complete interval computation for depth 15, residue 15172. -/
theorem bounds_15_15172 : exactInterval 15 15172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15172 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15172) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15172 : oddCount 15172 15 = 6 ∧ acceleratedOrbit 15 15172 = 338 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15172 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15172) = 3 ^ 6 * m + 338 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15172.1, data_15_15172.2]

/-- Complete interval computation for depth 15, residue 15173. -/
theorem bounds_15_15173 : exactInterval 15 15173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15173 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15173) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15173 : oddCount 15173 15 = 6 ∧ acceleratedOrbit 15 15173 = 338 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15173 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15173) = 3 ^ 6 * m + 338 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15173.1, data_15_15173.2]

/-- Complete interval computation for depth 15, residue 15174. -/
theorem bounds_15_15174 : exactInterval 15 15174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15174 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15174) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15174 : oddCount 15174 15 = 6 ∧ acceleratedOrbit 15 15174 = 338 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15174 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15174) = 3 ^ 6 * m + 338 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15174.1, data_15_15174.2]

/-- Complete interval computation for depth 15, residue 15175. -/
theorem bounds_15_15175 : exactInterval 15 15175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15175 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15175) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15175 : oddCount 15175 15 = 10 ∧ acceleratedOrbit 15 15175 = 27350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15175 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15175) = 3 ^ 10 * m + 27350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15175.1, data_15_15175.2]

/-- Complete interval computation for depth 15, residue 15176. -/
theorem bounds_15_15176 : exactInterval 15 15176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15176 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15176) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15176 : oddCount 15176 15 = 6 ∧ acceleratedOrbit 15 15176 = 338 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15176 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15176) = 3 ^ 6 * m + 338 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15176.1, data_15_15176.2]

/-- Complete interval computation for depth 15, residue 15177. -/
theorem bounds_15_15177 : exactInterval 15 15177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15177 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15177) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15177 : oddCount 15177 15 = 8 ∧ acceleratedOrbit 15 15177 = 3041 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15177 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15177) = 3 ^ 8 * m + 3041 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15177.1, data_15_15177.2]

/-- Complete interval computation for depth 15, residue 15178. -/
theorem bounds_15_15178 : exactInterval 15 15178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15178 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15178) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15178 : oddCount 15178 15 = 6 ∧ acceleratedOrbit 15 15178 = 338 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15178 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15178) = 3 ^ 6 * m + 338 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15178.1, data_15_15178.2]

/-- Complete interval computation for depth 15, residue 15179. -/
theorem bounds_15_15179 : exactInterval 15 15179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15179 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15179) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15179 : oddCount 15179 15 = 6 ∧ acceleratedOrbit 15 15179 = 338 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15179 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15179) = 3 ^ 6 * m + 338 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15179.1, data_15_15179.2]

/-- Complete interval computation for depth 15, residue 15180. -/
theorem bounds_15_15180 : exactInterval 15 15180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15180 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15180) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15180 : oddCount 15180 15 = 6 ∧ acceleratedOrbit 15 15180 = 338 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15180 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15180) = 3 ^ 6 * m + 338 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15180.1, data_15_15180.2]

/-- Complete interval computation for depth 15, residue 15181. -/
theorem bounds_15_15181 : exactInterval 15 15181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15181 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15181) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15181 : oddCount 15181 15 = 6 ∧ acceleratedOrbit 15 15181 = 338 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15181 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15181) = 3 ^ 6 * m + 338 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15181.1, data_15_15181.2]

/-- Complete interval computation for depth 15, residue 15182. -/
theorem bounds_15_15182 : exactInterval 15 15182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15182 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15182) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15182 : oddCount 15182 15 = 8 ∧ acceleratedOrbit 15 15182 = 3041 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15182 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15182) = 3 ^ 8 * m + 3041 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15182.1, data_15_15182.2]

/-- Complete interval computation for depth 15, residue 15183. -/
theorem bounds_15_15183 : exactInterval 15 15183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15183 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15183) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15183 : oddCount 15183 15 = 8 ∧ acceleratedOrbit 15 15183 = 3041 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15183 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15183) = 3 ^ 8 * m + 3041 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15183.1, data_15_15183.2]

/-- Complete interval computation for depth 15, residue 15184. -/
theorem bounds_15_15184 : exactInterval 15 15184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15184 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15184) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15184 : oddCount 15184 15 = 4 ∧ acceleratedOrbit 15 15184 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15184 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15184) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15184.1, data_15_15184.2]

/-- Complete interval computation for depth 15, residue 15185. -/
theorem bounds_15_15185 : exactInterval 15 15185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15185 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15185) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15185 : oddCount 15185 15 = 9 ∧ acceleratedOrbit 15 15185 = 9125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15185 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15185) = 3 ^ 9 * m + 9125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15185.1, data_15_15185.2]

/-- Complete interval computation for depth 15, residue 15186. -/
theorem bounds_15_15186 : exactInterval 15 15186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15186 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15186) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15186 : oddCount 15186 15 = 9 ∧ acceleratedOrbit 15 15186 = 9125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15186 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15186) = 3 ^ 9 * m + 9125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15186.1, data_15_15186.2]

/-- Complete interval computation for depth 15, residue 15187. -/
theorem bounds_15_15187 : exactInterval 15 15187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15187 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15187) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15187 : oddCount 15187 15 = 9 ∧ acceleratedOrbit 15 15187 = 9125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15187 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15187) = 3 ^ 9 * m + 9125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15187.1, data_15_15187.2]

/-- Complete interval computation for depth 15, residue 15188. -/
theorem bounds_15_15188 : exactInterval 15 15188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15188 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15188) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15188 : oddCount 15188 15 = 4 ∧ acceleratedOrbit 15 15188 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15188 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15188) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15188.1, data_15_15188.2]

/-- Complete interval computation for depth 15, residue 15189. -/
theorem bounds_15_15189 : exactInterval 15 15189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15189 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15189) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15189 : oddCount 15189 15 = 4 ∧ acceleratedOrbit 15 15189 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15189 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15189) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15189.1, data_15_15189.2]

/-- Complete interval computation for depth 15, residue 15190. -/
theorem bounds_15_15190 : exactInterval 15 15190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15190 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15190) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15190 : oddCount 15190 15 = 9 ∧ acceleratedOrbit 15 15190 = 9128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15190 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15190) = 3 ^ 9 * m + 9128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15190.1, data_15_15190.2]

/-- Complete interval computation for depth 15, residue 15191. -/
theorem bounds_15_15191 : exactInterval 15 15191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15191 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15191) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15191 : oddCount 15191 15 = 9 ∧ acceleratedOrbit 15 15191 = 9128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15191 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15191) = 3 ^ 9 * m + 9128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15191.1, data_15_15191.2]

/-- Complete interval computation for depth 15, residue 15192. -/
theorem bounds_15_15192 : exactInterval 15 15192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15192 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15192) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15192 : oddCount 15192 15 = 7 ∧ acceleratedOrbit 15 15192 = 1016 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15192 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15192) = 3 ^ 7 * m + 1016 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15192.1, data_15_15192.2]

/-- Complete interval computation for depth 15, residue 15193. -/
theorem bounds_15_15193 : exactInterval 15 15193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15193 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15193) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15193 : oddCount 15193 15 = 7 ∧ acceleratedOrbit 15 15193 = 1016 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15193 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15193) = 3 ^ 7 * m + 1016 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15193.1, data_15_15193.2]

/-- Complete interval computation for depth 15, residue 15194. -/
theorem bounds_15_15194 : exactInterval 15 15194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15194 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15194) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15194 : oddCount 15194 15 = 7 ∧ acceleratedOrbit 15 15194 = 1016 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15194 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15194) = 3 ^ 7 * m + 1016 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15194.1, data_15_15194.2]

/-- Complete interval computation for depth 15, residue 15195. -/
theorem bounds_15_15195 : exactInterval 15 15195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15195 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15195) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15195 : oddCount 15195 15 = 8 ∧ acceleratedOrbit 15 15195 = 3043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15195 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15195) = 3 ^ 8 * m + 3043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15195.1, data_15_15195.2]

/-- Complete interval computation for depth 15, residue 15196. -/
theorem bounds_15_15196 : exactInterval 15 15196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15196 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15196) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15196 : oddCount 15196 15 = 7 ∧ acceleratedOrbit 15 15196 = 1016 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15196 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15196) = 3 ^ 7 * m + 1016 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15196.1, data_15_15196.2]

/-- Complete interval computation for depth 15, residue 15197. -/
theorem bounds_15_15197 : exactInterval 15 15197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15197 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15197) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15197 : oddCount 15197 15 = 7 ∧ acceleratedOrbit 15 15197 = 1016 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15197 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15197) = 3 ^ 7 * m + 1016 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15197.1, data_15_15197.2]

/-- Complete interval computation for depth 15, residue 15198. -/
theorem bounds_15_15198 : exactInterval 15 15198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15198 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15198) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15198 : oddCount 15198 15 = 8 ∧ acceleratedOrbit 15 15198 = 3044 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15198 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15198) = 3 ^ 8 * m + 3044 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15198.1, data_15_15198.2]

/-- Complete interval computation for depth 15, residue 15199. -/
theorem bounds_15_15199 : exactInterval 15 15199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15199 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15199) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15199 : oddCount 15199 15 = 8 ∧ acceleratedOrbit 15 15199 = 3044 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15199 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15199) = 3 ^ 8 * m + 3044 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15199.1, data_15_15199.2]

/-- Complete interval computation for depth 15, residue 15200. -/
theorem bounds_15_15200 : exactInterval 15 15200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15200 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15200) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15200 : oddCount 15200 15 = 5 ∧ acceleratedOrbit 15 15200 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15200 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15200) = 3 ^ 5 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15200.1, data_15_15200.2]

/-- Complete interval computation for depth 15, residue 15201. -/
theorem bounds_15_15201 : exactInterval 15 15201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15201 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15201) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15201 : oddCount 15201 15 = 10 ∧ acceleratedOrbit 15 15201 = 27398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15201 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15201) = 3 ^ 10 * m + 27398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15201.1, data_15_15201.2]

/-- Complete interval computation for depth 15, residue 15202. -/
theorem bounds_15_15202 : exactInterval 15 15202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15202 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15202) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15202 : oddCount 15202 15 = 5 ∧ acceleratedOrbit 15 15202 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15202 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15202) = 3 ^ 5 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15202.1, data_15_15202.2]

/-- Complete interval computation for depth 15, residue 15203. -/
theorem bounds_15_15203 : exactInterval 15 15203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15203 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15203) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15203 : oddCount 15203 15 = 5 ∧ acceleratedOrbit 15 15203 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15203 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15203) = 3 ^ 5 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15203.1, data_15_15203.2]

end Collatz.Research.PassageAtlas.Batch0464
