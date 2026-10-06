import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0556

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 18186. -/
theorem bounds_15_18186 : exactInterval 15 18186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18186 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18186) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18186 : oddCount 18186 15 = 10 ∧ acceleratedOrbit 15 18186 = 32804 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18186 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18186) = 3 ^ 10 * m + 32804 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18186.1, data_15_18186.2]

/-- Complete interval computation for depth 15, residue 18187. -/
theorem bounds_15_18187 : exactInterval 15 18187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18187 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18187) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18187 : oddCount 18187 15 = 9 ∧ acceleratedOrbit 15 18187 = 10928 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18187 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18187) = 3 ^ 9 * m + 10928 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18187.1, data_15_18187.2]

/-- Complete interval computation for depth 15, residue 18188. -/
theorem bounds_15_18188 : exactInterval 15 18188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18188 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18188) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18188 : oddCount 18188 15 = 10 ∧ acceleratedOrbit 15 18188 = 32804 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18188 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18188) = 3 ^ 10 * m + 32804 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18188.1, data_15_18188.2]

/-- Complete interval computation for depth 15, residue 18189. -/
theorem bounds_15_18189 : exactInterval 15 18189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18189 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18189) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18189 : oddCount 18189 15 = 10 ∧ acceleratedOrbit 15 18189 = 32804 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18189 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18189) = 3 ^ 10 * m + 32804 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18189.1, data_15_18189.2]

/-- Complete interval computation for depth 15, residue 18190. -/
theorem bounds_15_18190 : exactInterval 15 18190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18190 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18190) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18190 : oddCount 18190 15 = 9 ∧ acceleratedOrbit 15 18190 = 10934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18190 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18190) = 3 ^ 9 * m + 10934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18190.1, data_15_18190.2]

/-- Complete interval computation for depth 15, residue 18191. -/
theorem bounds_15_18191 : exactInterval 15 18191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18191 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18191) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18191 : oddCount 18191 15 = 9 ∧ acceleratedOrbit 15 18191 = 10934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18191 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18191) = 3 ^ 9 * m + 10934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18191.1, data_15_18191.2]

/-- Complete interval computation for depth 15, residue 18192. -/
theorem bounds_15_18192 : exactInterval 15 18192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18192 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18192) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18192 : oddCount 18192 15 = 2 ∧ acceleratedOrbit 15 18192 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18192 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18192) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18192.1, data_15_18192.2]

/-- Complete interval computation for depth 15, residue 18193. -/
theorem bounds_15_18193 : exactInterval 15 18193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18193 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18193) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18193 : oddCount 18193 15 = 10 ∧ acceleratedOrbit 15 18193 = 32804 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18193 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18193) = 3 ^ 10 * m + 32804 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18193.1, data_15_18193.2]

/-- Complete interval computation for depth 15, residue 18194. -/
theorem bounds_15_18194 : exactInterval 15 18194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18194 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18194) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18194 : oddCount 18194 15 = 10 ∧ acceleratedOrbit 15 18194 = 32795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18194 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18194) = 3 ^ 10 * m + 32795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18194.1, data_15_18194.2]

/-- Complete interval computation for depth 15, residue 18195. -/
theorem bounds_15_18195 : exactInterval 15 18195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18195 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18195) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18195 : oddCount 18195 15 = 10 ∧ acceleratedOrbit 15 18195 = 32795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18195 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18195) = 3 ^ 10 * m + 32795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18195.1, data_15_18195.2]

/-- Complete interval computation for depth 15, residue 18196. -/
theorem bounds_15_18196 : exactInterval 15 18196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18196 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18196) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18196 : oddCount 18196 15 = 2 ∧ acceleratedOrbit 15 18196 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18196 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18196) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18196.1, data_15_18196.2]

/-- Complete interval computation for depth 15, residue 18197. -/
theorem bounds_15_18197 : exactInterval 15 18197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18197 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18197) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18197 : oddCount 18197 15 = 2 ∧ acceleratedOrbit 15 18197 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18197 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18197) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18197.1, data_15_18197.2]

/-- Complete interval computation for depth 15, residue 18198. -/
theorem bounds_15_18198 : exactInterval 15 18198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18198 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18198) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18198 : oddCount 18198 15 = 11 ∧ acceleratedOrbit 15 18198 = 98414 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18198 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18198) = 3 ^ 11 * m + 98414 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18198.1, data_15_18198.2]

/-- Complete interval computation for depth 15, residue 18199. -/
theorem bounds_15_18199 : exactInterval 15 18199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18199 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18199) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18199 : oddCount 18199 15 = 11 ∧ acceleratedOrbit 15 18199 = 98414 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18199 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18199) = 3 ^ 11 * m + 98414 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18199.1, data_15_18199.2]

/-- Complete interval computation for depth 15, residue 18200. -/
theorem bounds_15_18200 : exactInterval 15 18200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18200 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18200) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18200 : oddCount 18200 15 = 2 ∧ acceleratedOrbit 15 18200 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18200 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18200) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18200.1, data_15_18200.2]

/-- Complete interval computation for depth 15, residue 18201. -/
theorem bounds_15_18201 : exactInterval 15 18201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18201 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18201) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18201 : oddCount 18201 15 = 12 ∧ acceleratedOrbit 15 18201 = 295244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18201 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18201) = 3 ^ 12 * m + 295244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18201.1, data_15_18201.2]

/-- Complete interval computation for depth 15, residue 18202. -/
theorem bounds_15_18202 : exactInterval 15 18202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18202 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18202) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18202 : oddCount 18202 15 = 2 ∧ acceleratedOrbit 15 18202 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18202 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18202) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18202.1, data_15_18202.2]

/-- Complete interval computation for depth 15, residue 18203. -/
theorem bounds_15_18203 : exactInterval 15 18203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18203 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18203) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18203 : oddCount 18203 15 = 14 ∧ acceleratedOrbit 15 18203 = 2657204 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18203 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18203) = 3 ^ 14 * m + 2657204 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18203.1, data_15_18203.2]

/-- Complete interval computation for depth 15, residue 18204. -/
theorem bounds_15_18204 : exactInterval 15 18204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18204 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18204) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18204 : oddCount 18204 15 = 8 ∧ acceleratedOrbit 15 18204 = 3647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18204 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18204) = 3 ^ 8 * m + 3647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18204.1, data_15_18204.2]

/-- Complete interval computation for depth 15, residue 18205. -/
theorem bounds_15_18205 : exactInterval 15 18205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18205 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18205) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18205 : oddCount 18205 15 = 8 ∧ acceleratedOrbit 15 18205 = 3647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18205 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18205) = 3 ^ 8 * m + 3647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18205.1, data_15_18205.2]

/-- Complete interval computation for depth 15, residue 18206. -/
theorem bounds_15_18206 : exactInterval 15 18206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18206 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18206) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18206 : oddCount 18206 15 = 8 ∧ acceleratedOrbit 15 18206 = 3647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18206 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18206) = 3 ^ 8 * m + 3647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18206.1, data_15_18206.2]

/-- Complete interval computation for depth 15, residue 18207. -/
theorem bounds_15_18207 : exactInterval 15 18207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18207 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18207) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18207 : oddCount 18207 15 = 8 ∧ acceleratedOrbit 15 18207 = 3646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18207 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18207) = 3 ^ 8 * m + 3646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18207.1, data_15_18207.2]

/-- Complete interval computation for depth 15, residue 18208. -/
theorem bounds_15_18208 : exactInterval 15 18208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18208 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18208) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18208 : oddCount 18208 15 = 6 ∧ acceleratedOrbit 15 18208 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18208 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18208) = 3 ^ 6 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18208.1, data_15_18208.2]

/-- Complete interval computation for depth 15, residue 18209. -/
theorem bounds_15_18209 : exactInterval 15 18209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18209 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18209) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18209 : oddCount 18209 15 = 7 ∧ acceleratedOrbit 15 18209 = 1216 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18209 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18209) = 3 ^ 7 * m + 1216 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18209.1, data_15_18209.2]

/-- Complete interval computation for depth 15, residue 18210. -/
theorem bounds_15_18210 : exactInterval 15 18210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18210 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18210) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18210 : oddCount 18210 15 = 7 ∧ acceleratedOrbit 15 18210 = 1217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18210 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18210) = 3 ^ 7 * m + 1217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18210.1, data_15_18210.2]

/-- Complete interval computation for depth 15, residue 18211. -/
theorem bounds_15_18211 : exactInterval 15 18211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18211 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18211) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18211 : oddCount 18211 15 = 7 ∧ acceleratedOrbit 15 18211 = 1217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18211 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18211) = 3 ^ 7 * m + 1217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18211.1, data_15_18211.2]

/-- Complete interval computation for depth 15, residue 18212. -/
theorem bounds_15_18212 : exactInterval 15 18212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18212 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18212) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18212 : oddCount 18212 15 = 7 ∧ acceleratedOrbit 15 18212 = 1217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18212 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18212) = 3 ^ 7 * m + 1217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18212.1, data_15_18212.2]

/-- Complete interval computation for depth 15, residue 18213. -/
theorem bounds_15_18213 : exactInterval 15 18213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18213 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18213) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18213 : oddCount 18213 15 = 7 ∧ acceleratedOrbit 15 18213 = 1217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18213 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18213) = 3 ^ 7 * m + 1217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18213.1, data_15_18213.2]

/-- Complete interval computation for depth 15, residue 18214. -/
theorem bounds_15_18214 : exactInterval 15 18214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18214 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18214) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18214 : oddCount 18214 15 = 7 ∧ acceleratedOrbit 15 18214 = 1217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18214 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18214) = 3 ^ 7 * m + 1217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18214.1, data_15_18214.2]

/-- Complete interval computation for depth 15, residue 18215. -/
theorem bounds_15_18215 : exactInterval 15 18215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18215 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18215) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18215 : oddCount 18215 15 = 9 ∧ acceleratedOrbit 15 18215 = 10943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18215 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18215) = 3 ^ 9 * m + 10943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18215.1, data_15_18215.2]

/-- Complete interval computation for depth 15, residue 18216. -/
theorem bounds_15_18216 : exactInterval 15 18216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18216 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18216) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18216 : oddCount 18216 15 = 6 ∧ acceleratedOrbit 15 18216 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18216 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18216) = 3 ^ 6 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18216.1, data_15_18216.2]

/-- Complete interval computation for depth 15, residue 18217. -/
theorem bounds_15_18217 : exactInterval 15 18217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18217 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18217) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18217 : oddCount 18217 15 = 7 ∧ acceleratedOrbit 15 18217 = 1216 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18217 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18217) = 3 ^ 7 * m + 1216 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18217.1, data_15_18217.2]

/-- Complete interval computation for depth 15, residue 18218. -/
theorem bounds_15_18218 : exactInterval 15 18218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18218 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18218) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18218 : oddCount 18218 15 = 6 ∧ acceleratedOrbit 15 18218 = 407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18218 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18218) = 3 ^ 6 * m + 407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18218.1, data_15_18218.2]

end Collatz.Research.PassageAtlas.Batch0556
