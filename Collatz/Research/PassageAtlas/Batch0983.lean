import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0983

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 32178. -/
theorem bounds_15_32178 : exactInterval 15 32178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32178 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32178) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32178 : oddCount 32178 15 = 7 ∧ acceleratedOrbit 15 32178 = 2150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32178 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32178) = 3 ^ 7 * m + 2150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32178.1, data_15_32178.2]

/-- Complete interval computation for depth 15, residue 32179. -/
theorem bounds_15_32179 : exactInterval 15 32179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32179 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32179) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32179 : oddCount 32179 15 = 7 ∧ acceleratedOrbit 15 32179 = 2150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32179 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32179) = 3 ^ 7 * m + 2150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32179.1, data_15_32179.2]

/-- Complete interval computation for depth 15, residue 32180. -/
theorem bounds_15_32180 : exactInterval 15 32180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32180 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32180) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32180 : oddCount 32180 15 = 7 ∧ acceleratedOrbit 15 32180 = 2150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32180 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32180) = 3 ^ 7 * m + 2150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32180.1, data_15_32180.2]

/-- Complete interval computation for depth 15, residue 32181. -/
theorem bounds_15_32181 : exactInterval 15 32181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32181 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32181) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32181 : oddCount 32181 15 = 7 ∧ acceleratedOrbit 15 32181 = 2150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32181 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32181) = 3 ^ 7 * m + 2150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32181.1, data_15_32181.2]

/-- Complete interval computation for depth 15, residue 32182. -/
theorem bounds_15_32182 : exactInterval 15 32182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32182 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32182) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32182 : oddCount 32182 15 = 9 ∧ acceleratedOrbit 15 32182 = 19334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32182 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32182) = 3 ^ 9 * m + 19334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32182.1, data_15_32182.2]

/-- Complete interval computation for depth 15, residue 32183. -/
theorem bounds_15_32183 : exactInterval 15 32183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32183 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32183) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32183 : oddCount 32183 15 = 9 ∧ acceleratedOrbit 15 32183 = 19334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32183 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32183) = 3 ^ 9 * m + 19334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32183.1, data_15_32183.2]

/-- Complete interval computation for depth 15, residue 32184. -/
theorem bounds_15_32184 : exactInterval 15 32184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32184 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32184) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32184 : oddCount 32184 15 = 7 ∧ acceleratedOrbit 15 32184 = 2150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32184 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32184) = 3 ^ 7 * m + 2150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32184.1, data_15_32184.2]

/-- Complete interval computation for depth 15, residue 32185. -/
theorem bounds_15_32185 : exactInterval 15 32185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32185 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32185) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32185 : oddCount 32185 15 = 7 ∧ acceleratedOrbit 15 32185 = 2150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32185 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32185) = 3 ^ 7 * m + 2150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32185.1, data_15_32185.2]

/-- Complete interval computation for depth 15, residue 32186. -/
theorem bounds_15_32186 : exactInterval 15 32186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32186 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32186) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32186 : oddCount 32186 15 = 7 ∧ acceleratedOrbit 15 32186 = 2150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32186 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32186) = 3 ^ 7 * m + 2150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32186.1, data_15_32186.2]

/-- Complete interval computation for depth 15, residue 32187. -/
theorem bounds_15_32187 : exactInterval 15 32187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32187 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32187) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32187 : oddCount 32187 15 = 8 ∧ acceleratedOrbit 15 32187 = 6446 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32187 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32187) = 3 ^ 8 * m + 6446 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32187.1, data_15_32187.2]

/-- Complete interval computation for depth 15, residue 32188. -/
theorem bounds_15_32188 : exactInterval 15 32188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32188 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32188) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32188 : oddCount 32188 15 = 8 ∧ acceleratedOrbit 15 32188 = 6446 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32188 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32188) = 3 ^ 8 * m + 6446 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32188.1, data_15_32188.2]

/-- Complete interval computation for depth 15, residue 32189. -/
theorem bounds_15_32189 : exactInterval 15 32189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32189 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32189) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32189 : oddCount 32189 15 = 8 ∧ acceleratedOrbit 15 32189 = 6446 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32189 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32189) = 3 ^ 8 * m + 6446 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32189.1, data_15_32189.2]

/-- Complete interval computation for depth 15, residue 32190. -/
theorem bounds_15_32190 : exactInterval 15 32190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32190 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32190) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32190 : oddCount 32190 15 = 8 ∧ acceleratedOrbit 15 32190 = 6446 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32190 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32190) = 3 ^ 8 * m + 6446 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32190.1, data_15_32190.2]

/-- Complete interval computation for depth 15, residue 32191. -/
theorem bounds_15_32191 : exactInterval 15 32191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32191 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32191) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32191 : oddCount 32191 15 = 12 ∧ acceleratedOrbit 15 32191 = 522101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32191 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32191) = 3 ^ 12 * m + 522101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32191.1, data_15_32191.2]

/-- Complete interval computation for depth 15, residue 32192. -/
theorem bounds_15_32192 : exactInterval 15 32192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32192 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32192) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32192 : oddCount 32192 15 = 6 ∧ acceleratedOrbit 15 32192 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32192 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32192) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32192.1, data_15_32192.2]

/-- Complete interval computation for depth 15, residue 32193. -/
theorem bounds_15_32193 : exactInterval 15 32193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32193 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32193) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32193 : oddCount 32193 15 = 7 ∧ acceleratedOrbit 15 32193 = 2149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32193 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32193) = 3 ^ 7 * m + 2149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32193.1, data_15_32193.2]

/-- Complete interval computation for depth 15, residue 32194. -/
theorem bounds_15_32194 : exactInterval 15 32194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32194 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32194) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32194 : oddCount 32194 15 = 7 ∧ acceleratedOrbit 15 32194 = 2149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32194 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32194) = 3 ^ 7 * m + 2149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32194.1, data_15_32194.2]

/-- Complete interval computation for depth 15, residue 32195. -/
theorem bounds_15_32195 : exactInterval 15 32195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32195 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32195) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32195 : oddCount 32195 15 = 7 ∧ acceleratedOrbit 15 32195 = 2149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32195 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32195) = 3 ^ 7 * m + 2149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32195.1, data_15_32195.2]

/-- Complete interval computation for depth 15, residue 32196. -/
theorem bounds_15_32196 : exactInterval 15 32196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32196 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32196) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32196 : oddCount 32196 15 = 6 ∧ acceleratedOrbit 15 32196 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32196 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32196) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32196.1, data_15_32196.2]

/-- Complete interval computation for depth 15, residue 32197. -/
theorem bounds_15_32197 : exactInterval 15 32197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32197 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32197) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32197 : oddCount 32197 15 = 6 ∧ acceleratedOrbit 15 32197 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32197 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32197) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32197.1, data_15_32197.2]

/-- Complete interval computation for depth 15, residue 32198. -/
theorem bounds_15_32198 : exactInterval 15 32198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32198 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32198) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32198 : oddCount 32198 15 = 6 ∧ acceleratedOrbit 15 32198 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32198 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32198) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32198.1, data_15_32198.2]

/-- Complete interval computation for depth 15, residue 32199. -/
theorem bounds_15_32199 : exactInterval 15 32199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32199 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32199) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32199 : oddCount 32199 15 = 8 ∧ acceleratedOrbit 15 32199 = 6448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32199 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32199) = 3 ^ 8 * m + 6448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32199.1, data_15_32199.2]

/-- Complete interval computation for depth 15, residue 32200. -/
theorem bounds_15_32200 : exactInterval 15 32200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32200 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32200) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32200 : oddCount 32200 15 = 5 ∧ acceleratedOrbit 15 32200 = 239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32200 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32200) = 3 ^ 5 * m + 239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32200.1, data_15_32200.2]

/-- Complete interval computation for depth 15, residue 32201. -/
theorem bounds_15_32201 : exactInterval 15 32201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32201 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32201) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32201 : oddCount 32201 15 = 7 ∧ acceleratedOrbit 15 32201 = 2150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32201 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32201) = 3 ^ 7 * m + 2150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32201.1, data_15_32201.2]

/-- Complete interval computation for depth 15, residue 32202. -/
theorem bounds_15_32202 : exactInterval 15 32202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32202 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32202) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32202 : oddCount 32202 15 = 5 ∧ acceleratedOrbit 15 32202 = 239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32202 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32202) = 3 ^ 5 * m + 239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32202.1, data_15_32202.2]

/-- Complete interval computation for depth 15, residue 32203. -/
theorem bounds_15_32203 : exactInterval 15 32203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32203 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32203) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32203 : oddCount 32203 15 = 9 ∧ acceleratedOrbit 15 32203 = 19349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32203 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32203) = 3 ^ 9 * m + 19349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32203.1, data_15_32203.2]

/-- Complete interval computation for depth 15, residue 32204. -/
theorem bounds_15_32204 : exactInterval 15 32204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32204 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32204) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32204 : oddCount 32204 15 = 5 ∧ acceleratedOrbit 15 32204 = 239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32204 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32204) = 3 ^ 5 * m + 239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32204.1, data_15_32204.2]

/-- Complete interval computation for depth 15, residue 32205. -/
theorem bounds_15_32205 : exactInterval 15 32205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32205 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32205) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32205 : oddCount 32205 15 = 5 ∧ acceleratedOrbit 15 32205 = 239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32205 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32205) = 3 ^ 5 * m + 239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32205.1, data_15_32205.2]

/-- Complete interval computation for depth 15, residue 32206. -/
theorem bounds_15_32206 : exactInterval 15 32206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32206 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32206) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32206 : oddCount 32206 15 = 8 ∧ acceleratedOrbit 15 32206 = 6449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32206 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32206) = 3 ^ 8 * m + 6449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32206.1, data_15_32206.2]

/-- Complete interval computation for depth 15, residue 32207. -/
theorem bounds_15_32207 : exactInterval 15 32207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32207 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32207) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32207 : oddCount 32207 15 = 8 ∧ acceleratedOrbit 15 32207 = 6449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32207 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32207) = 3 ^ 8 * m + 6449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32207.1, data_15_32207.2]

/-- Complete interval computation for depth 15, residue 32208. -/
theorem bounds_15_32208 : exactInterval 15 32208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32208 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32208) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32208 : oddCount 32208 15 = 6 ∧ acceleratedOrbit 15 32208 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32208 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32208) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32208.1, data_15_32208.2]

/-- Complete interval computation for depth 15, residue 32209. -/
theorem bounds_15_32209 : exactInterval 15 32209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32209 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32209) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32209 : oddCount 32209 15 = 5 ∧ acceleratedOrbit 15 32209 = 239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32209 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32209) = 3 ^ 5 * m + 239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32209.1, data_15_32209.2]

end Collatz.Research.PassageAtlas.Batch0983
