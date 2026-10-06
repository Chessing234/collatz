import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0922

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 30179. -/
theorem bounds_15_30179 : exactInterval 15 30179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30179 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30179) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30179 : oddCount 30179 15 = 6 ∧ acceleratedOrbit 15 30179 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30179 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30179) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30179.1, data_15_30179.2]

/-- Complete interval computation for depth 15, residue 30180. -/
theorem bounds_15_30180 : exactInterval 15 30180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30180 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30180) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30180 : oddCount 30180 15 = 9 ∧ acceleratedOrbit 15 30180 = 18134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30180 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30180) = 3 ^ 9 * m + 18134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30180.1, data_15_30180.2]

/-- Complete interval computation for depth 15, residue 30181. -/
theorem bounds_15_30181 : exactInterval 15 30181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30181 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30181) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30181 : oddCount 30181 15 = 9 ∧ acceleratedOrbit 15 30181 = 18134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30181 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30181) = 3 ^ 9 * m + 18134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30181.1, data_15_30181.2]

/-- Complete interval computation for depth 15, residue 30182. -/
theorem bounds_15_30182 : exactInterval 15 30182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30182 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30182) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30182 : oddCount 30182 15 = 9 ∧ acceleratedOrbit 15 30182 = 18134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30182 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30182) = 3 ^ 9 * m + 18134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30182.1, data_15_30182.2]

/-- Complete interval computation for depth 15, residue 30183. -/
theorem bounds_15_30183 : exactInterval 15 30183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30183 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30183) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30183 : oddCount 30183 15 = 10 ∧ acceleratedOrbit 15 30183 = 54395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30183 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30183) = 3 ^ 10 * m + 54395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30183.1, data_15_30183.2]

/-- Complete interval computation for depth 15, residue 30184. -/
theorem bounds_15_30184 : exactInterval 15 30184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30184 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30184) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30184 : oddCount 30184 15 = 5 ∧ acceleratedOrbit 15 30184 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30184 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30184) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30184.1, data_15_30184.2]

/-- Complete interval computation for depth 15, residue 30185. -/
theorem bounds_15_30185 : exactInterval 15 30185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30185 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30185) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30185 : oddCount 30185 15 = 10 ∧ acceleratedOrbit 15 30185 = 54398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30185 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30185) = 3 ^ 10 * m + 54398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30185.1, data_15_30185.2]

/-- Complete interval computation for depth 15, residue 30186. -/
theorem bounds_15_30186 : exactInterval 15 30186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30186 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30186) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30186 : oddCount 30186 15 = 5 ∧ acceleratedOrbit 15 30186 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30186 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30186) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30186.1, data_15_30186.2]

/-- Complete interval computation for depth 15, residue 30187. -/
theorem bounds_15_30187 : exactInterval 15 30187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30187 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30187) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30187 : oddCount 30187 15 = 11 ∧ acceleratedOrbit 15 30187 = 163205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30187 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30187) = 3 ^ 11 * m + 163205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30187.1, data_15_30187.2]

/-- Complete interval computation for depth 15, residue 30188. -/
theorem bounds_15_30188 : exactInterval 15 30188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30188 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30188) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30188 : oddCount 30188 15 = 8 ∧ acceleratedOrbit 15 30188 = 6047 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30188 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30188) = 3 ^ 8 * m + 6047 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30188.1, data_15_30188.2]

/-- Complete interval computation for depth 15, residue 30189. -/
theorem bounds_15_30189 : exactInterval 15 30189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30189 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30189) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30189 : oddCount 30189 15 = 8 ∧ acceleratedOrbit 15 30189 = 6047 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30189 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30189) = 3 ^ 8 * m + 6047 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30189.1, data_15_30189.2]

/-- Complete interval computation for depth 15, residue 30190. -/
theorem bounds_15_30190 : exactInterval 15 30190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30190 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30190) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30190 : oddCount 30190 15 = 8 ∧ acceleratedOrbit 15 30190 = 6047 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30190 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30190) = 3 ^ 8 * m + 6047 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30190.1, data_15_30190.2]

/-- Complete interval computation for depth 15, residue 30191. -/
theorem bounds_15_30191 : exactInterval 15 30191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30191 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30191) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30191 : oddCount 30191 15 = 9 ∧ acceleratedOrbit 15 30191 = 18136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30191 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30191) = 3 ^ 9 * m + 18136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30191.1, data_15_30191.2]

/-- Complete interval computation for depth 15, residue 30192. -/
theorem bounds_15_30192 : exactInterval 15 30192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30192 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30192) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30192 : oddCount 30192 15 = 5 ∧ acceleratedOrbit 15 30192 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30192 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30192) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30192.1, data_15_30192.2]

/-- Complete interval computation for depth 15, residue 30193. -/
theorem bounds_15_30193 : exactInterval 15 30193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30193 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30193) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30193 : oddCount 30193 15 = 5 ∧ acceleratedOrbit 15 30193 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30193 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30193) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30193.1, data_15_30193.2]

/-- Complete interval computation for depth 15, residue 30194. -/
theorem bounds_15_30194 : exactInterval 15 30194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30194 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30194) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30194 : oddCount 30194 15 = 9 ∧ acceleratedOrbit 15 30194 = 18143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30194 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30194) = 3 ^ 9 * m + 18143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30194.1, data_15_30194.2]

/-- Complete interval computation for depth 15, residue 30195. -/
theorem bounds_15_30195 : exactInterval 15 30195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30195 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30195) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30195 : oddCount 30195 15 = 9 ∧ acceleratedOrbit 15 30195 = 18143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30195 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30195) = 3 ^ 9 * m + 18143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30195.1, data_15_30195.2]

/-- Complete interval computation for depth 15, residue 30196. -/
theorem bounds_15_30196 : exactInterval 15 30196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30196 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30196) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30196 : oddCount 30196 15 = 5 ∧ acceleratedOrbit 15 30196 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30196 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30196) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30196.1, data_15_30196.2]

/-- Complete interval computation for depth 15, residue 30197. -/
theorem bounds_15_30197 : exactInterval 15 30197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30197 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30197) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30197 : oddCount 30197 15 = 5 ∧ acceleratedOrbit 15 30197 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30197 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30197) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30197.1, data_15_30197.2]

/-- Complete interval computation for depth 15, residue 30198. -/
theorem bounds_15_30198 : exactInterval 15 30198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30198 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30198) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30198 : oddCount 30198 15 = 10 ∧ acceleratedOrbit 15 30198 = 54425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30198 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30198) = 3 ^ 10 * m + 54425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30198.1, data_15_30198.2]

/-- Complete interval computation for depth 15, residue 30199. -/
theorem bounds_15_30199 : exactInterval 15 30199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30199 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30199) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30199 : oddCount 30199 15 = 10 ∧ acceleratedOrbit 15 30199 = 54425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30199 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30199) = 3 ^ 10 * m + 54425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30199.1, data_15_30199.2]

/-- Complete interval computation for depth 15, residue 30200. -/
theorem bounds_15_30200 : exactInterval 15 30200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30200 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30200) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30200 : oddCount 30200 15 = 9 ∧ acceleratedOrbit 15 30200 = 18146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30200 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30200) = 3 ^ 9 * m + 18146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30200.1, data_15_30200.2]

/-- Complete interval computation for depth 15, residue 30201. -/
theorem bounds_15_30201 : exactInterval 15 30201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30201 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30201) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30201 : oddCount 30201 15 = 10 ∧ acceleratedOrbit 15 30201 = 54431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30201 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30201) = 3 ^ 10 * m + 54431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30201.1, data_15_30201.2]

/-- Complete interval computation for depth 15, residue 30202. -/
theorem bounds_15_30202 : exactInterval 15 30202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30202 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30202) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30202 : oddCount 30202 15 = 9 ∧ acceleratedOrbit 15 30202 = 18146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30202 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30202) = 3 ^ 9 * m + 18146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30202.1, data_15_30202.2]

/-- Complete interval computation for depth 15, residue 30203. -/
theorem bounds_15_30203 : exactInterval 15 30203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30203 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30203) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30203 : oddCount 30203 15 = 11 ∧ acceleratedOrbit 15 30203 = 163295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30203 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30203) = 3 ^ 11 * m + 163295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30203.1, data_15_30203.2]

/-- Complete interval computation for depth 15, residue 30204. -/
theorem bounds_15_30204 : exactInterval 15 30204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30204 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30204) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30204 : oddCount 30204 15 = 9 ∧ acceleratedOrbit 15 30204 = 18146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30204 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30204) = 3 ^ 9 * m + 18146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30204.1, data_15_30204.2]

/-- Complete interval computation for depth 15, residue 30205. -/
theorem bounds_15_30205 : exactInterval 15 30205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30205 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30205) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30205 : oddCount 30205 15 = 9 ∧ acceleratedOrbit 15 30205 = 18146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30205 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30205) = 3 ^ 9 * m + 18146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30205.1, data_15_30205.2]

/-- Complete interval computation for depth 15, residue 30206. -/
theorem bounds_15_30206 : exactInterval 15 30206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30206 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30206) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30206 : oddCount 30206 15 = 10 ∧ acceleratedOrbit 15 30206 = 54436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30206 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30206) = 3 ^ 10 * m + 54436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30206.1, data_15_30206.2]

/-- Complete interval computation for depth 15, residue 30207. -/
theorem bounds_15_30207 : exactInterval 15 30207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30207 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30207) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30207 : oddCount 30207 15 = 10 ∧ acceleratedOrbit 15 30207 = 54436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30207 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30207) = 3 ^ 10 * m + 54436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30207.1, data_15_30207.2]

/-- Complete interval computation for depth 15, residue 30208. -/
theorem bounds_15_30208 : exactInterval 15 30208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30208 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30208) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30208 : oddCount 30208 15 = 4 ∧ acceleratedOrbit 15 30208 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30208 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30208) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30208.1, data_15_30208.2]

/-- Complete interval computation for depth 15, residue 30209. -/
theorem bounds_15_30209 : exactInterval 15 30209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30209 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30209) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30209 : oddCount 30209 15 = 8 ∧ acceleratedOrbit 15 30209 = 6050 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30209 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30209) = 3 ^ 8 * m + 6050 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30209.1, data_15_30209.2]

/-- Complete interval computation for depth 15, residue 30210. -/
theorem bounds_15_30210 : exactInterval 15 30210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30210 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30210) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30210 : oddCount 30210 15 = 7 ∧ acceleratedOrbit 15 30210 = 2018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30210 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30210) = 3 ^ 7 * m + 2018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30210.1, data_15_30210.2]

/-- Complete interval computation for depth 15, residue 30211. -/
theorem bounds_15_30211 : exactInterval 15 30211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30211 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30211) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30211 : oddCount 30211 15 = 7 ∧ acceleratedOrbit 15 30211 = 2018 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30211 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30211) = 3 ^ 7 * m + 2018 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30211.1, data_15_30211.2]

end Collatz.Research.PassageAtlas.Batch0922
