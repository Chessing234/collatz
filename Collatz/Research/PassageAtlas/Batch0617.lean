import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0617

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 20185. -/
theorem bounds_15_20185 : exactInterval 15 20185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20185 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20185) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20185 : oddCount 20185 15 = 7 ∧ acceleratedOrbit 15 20185 = 1349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20185 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20185) = 3 ^ 7 * m + 1349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20185.1, data_15_20185.2]

/-- Complete interval computation for depth 15, residue 20186. -/
theorem bounds_15_20186 : exactInterval 15 20186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20186 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20186) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20186 : oddCount 20186 15 = 7 ∧ acceleratedOrbit 15 20186 = 1349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20186 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20186) = 3 ^ 7 * m + 1349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20186.1, data_15_20186.2]

/-- Complete interval computation for depth 15, residue 20187. -/
theorem bounds_15_20187 : exactInterval 15 20187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20187 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20187) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20187 : oddCount 20187 15 = 10 ∧ acceleratedOrbit 15 20187 = 36382 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20187 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20187) = 3 ^ 10 * m + 36382 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20187.1, data_15_20187.2]

/-- Complete interval computation for depth 15, residue 20188. -/
theorem bounds_15_20188 : exactInterval 15 20188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20188 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20188) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20188 : oddCount 20188 15 = 7 ∧ acceleratedOrbit 15 20188 = 1349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20188 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20188) = 3 ^ 7 * m + 1349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20188.1, data_15_20188.2]

/-- Complete interval computation for depth 15, residue 20189. -/
theorem bounds_15_20189 : exactInterval 15 20189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20189 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20189) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20189 : oddCount 20189 15 = 7 ∧ acceleratedOrbit 15 20189 = 1349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20189 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20189) = 3 ^ 7 * m + 1349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20189.1, data_15_20189.2]

/-- Complete interval computation for depth 15, residue 20190. -/
theorem bounds_15_20190 : exactInterval 15 20190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20190 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20190) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20190 : oddCount 20190 15 = 10 ∧ acceleratedOrbit 15 20190 = 36389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20190 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20190) = 3 ^ 10 * m + 36389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20190.1, data_15_20190.2]

/-- Complete interval computation for depth 15, residue 20191. -/
theorem bounds_15_20191 : exactInterval 15 20191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20191 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20191) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20191 : oddCount 20191 15 = 10 ∧ acceleratedOrbit 15 20191 = 36389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20191 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20191) = 3 ^ 10 * m + 36389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20191.1, data_15_20191.2]

/-- Complete interval computation for depth 15, residue 20192. -/
theorem bounds_15_20192 : exactInterval 15 20192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20192 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20192) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20192 : oddCount 20192 15 = 4 ∧ acceleratedOrbit 15 20192 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20192 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20192) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20192.1, data_15_20192.2]

/-- Complete interval computation for depth 15, residue 20193. -/
theorem bounds_15_20193 : exactInterval 15 20193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20193 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20193) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20193 : oddCount 20193 15 = 10 ∧ acceleratedOrbit 15 20193 = 36395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20193 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20193) = 3 ^ 10 * m + 36395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20193.1, data_15_20193.2]

/-- Complete interval computation for depth 15, residue 20194. -/
theorem bounds_15_20194 : exactInterval 15 20194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20194 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20194) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20194 : oddCount 20194 15 = 4 ∧ acceleratedOrbit 15 20194 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20194 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20194) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20194.1, data_15_20194.2]

/-- Complete interval computation for depth 15, residue 20195. -/
theorem bounds_15_20195 : exactInterval 15 20195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20195 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20195) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20195 : oddCount 20195 15 = 4 ∧ acceleratedOrbit 15 20195 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20195 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20195) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20195.1, data_15_20195.2]

/-- Complete interval computation for depth 15, residue 20196. -/
theorem bounds_15_20196 : exactInterval 15 20196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20196 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20196) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20196 : oddCount 20196 15 = 8 ∧ acceleratedOrbit 15 20196 = 4049 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20196 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20196) = 3 ^ 8 * m + 4049 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20196.1, data_15_20196.2]

/-- Complete interval computation for depth 15, residue 20197. -/
theorem bounds_15_20197 : exactInterval 15 20197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20197 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20197) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20197 : oddCount 20197 15 = 8 ∧ acceleratedOrbit 15 20197 = 4049 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20197 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20197) = 3 ^ 8 * m + 4049 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20197.1, data_15_20197.2]

/-- Complete interval computation for depth 15, residue 20198. -/
theorem bounds_15_20198 : exactInterval 15 20198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20198 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20198) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20198 : oddCount 20198 15 = 8 ∧ acceleratedOrbit 15 20198 = 4049 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20198 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20198) = 3 ^ 8 * m + 4049 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20198.1, data_15_20198.2]

/-- Complete interval computation for depth 15, residue 20199. -/
theorem bounds_15_20199 : exactInterval 15 20199 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20199 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20199) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20199 : oddCount 20199 15 = 9 ∧ acceleratedOrbit 15 20199 = 12134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20199 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20199) = 3 ^ 9 * m + 12134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20199.1, data_15_20199.2]

/-- Complete interval computation for depth 15, residue 20200. -/
theorem bounds_15_20200 : exactInterval 15 20200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20200 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20200) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20200 : oddCount 20200 15 = 4 ∧ acceleratedOrbit 15 20200 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20200 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20200) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20200.1, data_15_20200.2]

/-- Complete interval computation for depth 15, residue 20201. -/
theorem bounds_15_20201 : exactInterval 15 20201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20201 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20201) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20201 : oddCount 20201 15 = 9 ∧ acceleratedOrbit 15 20201 = 12136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20201 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20201) = 3 ^ 9 * m + 12136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20201.1, data_15_20201.2]

/-- Complete interval computation for depth 15, residue 20202. -/
theorem bounds_15_20202 : exactInterval 15 20202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20202 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20202) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20202 : oddCount 20202 15 = 4 ∧ acceleratedOrbit 15 20202 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20202 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20202) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20202.1, data_15_20202.2]

/-- Complete interval computation for depth 15, residue 20203. -/
theorem bounds_15_20203 : exactInterval 15 20203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20203 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20203) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20203 : oddCount 20203 15 = 7 ∧ acceleratedOrbit 15 20203 = 1349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20203 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20203) = 3 ^ 7 * m + 1349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20203.1, data_15_20203.2]

/-- Complete interval computation for depth 15, residue 20204. -/
theorem bounds_15_20204 : exactInterval 15 20204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20204 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20204) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20204 : oddCount 20204 15 = 8 ∧ acceleratedOrbit 15 20204 = 4049 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20204 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20204) = 3 ^ 8 * m + 4049 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20204.1, data_15_20204.2]

/-- Complete interval computation for depth 15, residue 20205. -/
theorem bounds_15_20205 : exactInterval 15 20205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20205 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20205) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20205 : oddCount 20205 15 = 8 ∧ acceleratedOrbit 15 20205 = 4049 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20205 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20205) = 3 ^ 8 * m + 4049 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20205.1, data_15_20205.2]

/-- Complete interval computation for depth 15, residue 20206. -/
theorem bounds_15_20206 : exactInterval 15 20206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20206 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20206) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20206 : oddCount 20206 15 = 8 ∧ acceleratedOrbit 15 20206 = 4049 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20206 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20206) = 3 ^ 8 * m + 4049 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20206.1, data_15_20206.2]

/-- Complete interval computation for depth 15, residue 20207. -/
theorem bounds_15_20207 : exactInterval 15 20207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20207 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20207) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20207 : oddCount 20207 15 = 10 ∧ acceleratedOrbit 15 20207 = 36416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20207 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20207) = 3 ^ 10 * m + 36416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20207.1, data_15_20207.2]

/-- Complete interval computation for depth 15, residue 20208. -/
theorem bounds_15_20208 : exactInterval 15 20208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20208 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20208) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20208 : oddCount 20208 15 = 10 ∧ acceleratedOrbit 15 20208 = 36449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20208 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20208) = 3 ^ 10 * m + 36449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20208.1, data_15_20208.2]

/-- Complete interval computation for depth 15, residue 20209. -/
theorem bounds_15_20209 : exactInterval 15 20209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20209 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20209) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20209 : oddCount 20209 15 = 4 ∧ acceleratedOrbit 15 20209 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20209 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20209) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20209.1, data_15_20209.2]

/-- Complete interval computation for depth 15, residue 20210. -/
theorem bounds_15_20210 : exactInterval 15 20210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20210 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20210) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20210 : oddCount 20210 15 = 9 ∧ acceleratedOrbit 15 20210 = 12143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20210 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20210) = 3 ^ 9 * m + 12143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20210.1, data_15_20210.2]

/-- Complete interval computation for depth 15, residue 20211. -/
theorem bounds_15_20211 : exactInterval 15 20211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20211 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20211) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20211 : oddCount 20211 15 = 9 ∧ acceleratedOrbit 15 20211 = 12143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20211 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20211) = 3 ^ 9 * m + 12143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20211.1, data_15_20211.2]

/-- Complete interval computation for depth 15, residue 20212. -/
theorem bounds_15_20212 : exactInterval 15 20212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20212 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20212) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20212 : oddCount 20212 15 = 10 ∧ acceleratedOrbit 15 20212 = 36449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20212 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20212) = 3 ^ 10 * m + 36449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20212.1, data_15_20212.2]

/-- Complete interval computation for depth 15, residue 20213. -/
theorem bounds_15_20213 : exactInterval 15 20213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20213 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20213) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20213 : oddCount 20213 15 = 10 ∧ acceleratedOrbit 15 20213 = 36449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20213 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20213) = 3 ^ 10 * m + 36449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20213.1, data_15_20213.2]

/-- Complete interval computation for depth 15, residue 20214. -/
theorem bounds_15_20214 : exactInterval 15 20214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20214 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20214) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20214 : oddCount 20214 15 = 9 ∧ acceleratedOrbit 15 20214 = 12145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20214 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20214) = 3 ^ 9 * m + 12145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20214.1, data_15_20214.2]

/-- Complete interval computation for depth 15, residue 20215. -/
theorem bounds_15_20215 : exactInterval 15 20215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20215 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20215) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20215 : oddCount 20215 15 = 9 ∧ acceleratedOrbit 15 20215 = 12145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20215 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20215) = 3 ^ 9 * m + 12145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20215.1, data_15_20215.2]

/-- Complete interval computation for depth 15, residue 20216. -/
theorem bounds_15_20216 : exactInterval 15 20216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20216 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20216) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20216 : oddCount 20216 15 = 10 ∧ acceleratedOrbit 15 20216 = 36449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20216 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20216) = 3 ^ 10 * m + 36449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20216.1, data_15_20216.2]

end Collatz.Research.PassageAtlas.Batch0617
