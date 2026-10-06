import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0434

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 14188. -/
theorem bounds_15_14188 : exactInterval 15 14188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14188 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14188) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14188 : oddCount 14188 15 = 6 ∧ acceleratedOrbit 15 14188 = 316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14188 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14188) = 3 ^ 6 * m + 316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14188.1, data_15_14188.2]

/-- Complete interval computation for depth 15, residue 14189. -/
theorem bounds_15_14189 : exactInterval 15 14189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14189 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14189) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14189 : oddCount 14189 15 = 6 ∧ acceleratedOrbit 15 14189 = 316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14189 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14189) = 3 ^ 6 * m + 316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14189.1, data_15_14189.2]

/-- Complete interval computation for depth 15, residue 14190. -/
theorem bounds_15_14190 : exactInterval 15 14190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14190 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14190) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14190 : oddCount 14190 15 = 6 ∧ acceleratedOrbit 15 14190 = 316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14190 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14190) = 3 ^ 6 * m + 316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14190.1, data_15_14190.2]

/-- Complete interval computation for depth 15, residue 14191. -/
theorem bounds_15_14191 : exactInterval 15 14191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14191 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14191) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14191 : oddCount 14191 15 = 11 ∧ acceleratedOrbit 15 14191 = 76727 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14191 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14191) = 3 ^ 11 * m + 76727 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14191.1, data_15_14191.2]

/-- Complete interval computation for depth 15, residue 14192. -/
theorem bounds_15_14192 : exactInterval 15 14192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14192 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14192) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14192 : oddCount 14192 15 = 6 ∧ acceleratedOrbit 15 14192 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14192 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14192) = 3 ^ 6 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14192.1, data_15_14192.2]

/-- Complete interval computation for depth 15, residue 14193. -/
theorem bounds_15_14193 : exactInterval 15 14193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14193 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14193) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14193 : oddCount 14193 15 = 6 ∧ acceleratedOrbit 15 14193 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14193 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14193) = 3 ^ 6 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14193.1, data_15_14193.2]

/-- Complete interval computation for depth 15, residue 14194. -/
theorem bounds_15_14194 : exactInterval 15 14194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14194 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14194) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14194 : oddCount 14194 15 = 6 ∧ acceleratedOrbit 15 14194 = 316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14194 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14194) = 3 ^ 6 * m + 316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14194.1, data_15_14194.2]

/-- Complete interval computation for depth 15, residue 14195. -/
theorem bounds_15_14195 : exactInterval 15 14195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14195 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14195) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14195 : oddCount 14195 15 = 6 ∧ acceleratedOrbit 15 14195 = 316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14195 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14195) = 3 ^ 6 * m + 316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14195.1, data_15_14195.2]

/-- Complete interval computation for depth 15, residue 14196. -/
theorem bounds_15_14196 : exactInterval 15 14196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14196 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14196) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14196 : oddCount 14196 15 = 6 ∧ acceleratedOrbit 15 14196 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14196 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14196) = 3 ^ 6 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14196.1, data_15_14196.2]

/-- Complete interval computation for depth 15, residue 14197. -/
theorem bounds_15_14197 : exactInterval 15 14197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14197 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14197) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14197 : oddCount 14197 15 = 6 ∧ acceleratedOrbit 15 14197 = 317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14197 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14197) = 3 ^ 6 * m + 317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14197.1, data_15_14197.2]

/-- Complete interval computation for depth 15, residue 14198. -/
theorem bounds_15_14198 : exactInterval 15 14198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14198 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14198) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14198 : oddCount 14198 15 = 6 ∧ acceleratedOrbit 15 14198 = 316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14198 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14198) = 3 ^ 6 * m + 316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14198.1, data_15_14198.2]

/-- Complete interval computation for depth 15, residue 14199. -/
theorem bounds_15_14199 : exactInterval 15 14199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14199 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14199) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14199 : oddCount 14199 15 = 6 ∧ acceleratedOrbit 15 14199 = 316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14199 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14199) = 3 ^ 6 * m + 316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14199.1, data_15_14199.2]

/-- Complete interval computation for depth 15, residue 14200. -/
theorem bounds_15_14200 : exactInterval 15 14200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14200 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14200) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14200 : oddCount 14200 15 = 8 ∧ acceleratedOrbit 15 14200 = 2845 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14200 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14200) = 3 ^ 8 * m + 2845 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14200.1, data_15_14200.2]

/-- Complete interval computation for depth 15, residue 14201. -/
theorem bounds_15_14201 : exactInterval 15 14201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14201 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14201) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14201 : oddCount 14201 15 = 11 ∧ acceleratedOrbit 15 14201 = 76787 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14201 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14201) = 3 ^ 11 * m + 76787 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14201.1, data_15_14201.2]

/-- Complete interval computation for depth 15, residue 14202. -/
theorem bounds_15_14202 : exactInterval 15 14202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14202 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14202) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14202 : oddCount 14202 15 = 8 ∧ acceleratedOrbit 15 14202 = 2845 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14202 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14202) = 3 ^ 8 * m + 2845 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14202.1, data_15_14202.2]

/-- Complete interval computation for depth 15, residue 14203. -/
theorem bounds_15_14203 : exactInterval 15 14203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14203 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14203) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14203 : oddCount 14203 15 = 9 ∧ acceleratedOrbit 15 14203 = 8533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14203 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14203) = 3 ^ 9 * m + 8533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14203.1, data_15_14203.2]

/-- Complete interval computation for depth 15, residue 14204. -/
theorem bounds_15_14204 : exactInterval 15 14204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14204 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14204) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14204 : oddCount 14204 15 = 8 ∧ acceleratedOrbit 15 14204 = 2845 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14204 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14204) = 3 ^ 8 * m + 2845 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14204.1, data_15_14204.2]

/-- Complete interval computation for depth 15, residue 14205. -/
theorem bounds_15_14205 : exactInterval 15 14205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14205 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14205) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14205 : oddCount 14205 15 = 8 ∧ acceleratedOrbit 15 14205 = 2845 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14205 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14205) = 3 ^ 8 * m + 2845 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14205.1, data_15_14205.2]

/-- Complete interval computation for depth 15, residue 14206. -/
theorem bounds_15_14206 : exactInterval 15 14206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14206 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14206) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14206 : oddCount 14206 15 = 10 ∧ acceleratedOrbit 15 14206 = 25604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14206 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14206) = 3 ^ 10 * m + 25604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14206.1, data_15_14206.2]

/-- Complete interval computation for depth 15, residue 14207. -/
theorem bounds_15_14207 : exactInterval 15 14207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14207 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14207) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14207 : oddCount 14207 15 = 10 ∧ acceleratedOrbit 15 14207 = 25604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14207 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14207) = 3 ^ 10 * m + 25604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14207.1, data_15_14207.2]

/-- Complete interval computation for depth 15, residue 14208. -/
theorem bounds_15_14208 : exactInterval 15 14208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14208 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14208) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14208 : oddCount 14208 15 = 6 ∧ acceleratedOrbit 15 14208 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14208 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14208) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14208.1, data_15_14208.2]

/-- Complete interval computation for depth 15, residue 14209. -/
theorem bounds_15_14209 : exactInterval 15 14209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14209 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14209) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14209 : oddCount 14209 15 = 8 ∧ acceleratedOrbit 15 14209 = 2846 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14209 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14209) = 3 ^ 8 * m + 2846 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14209.1, data_15_14209.2]

/-- Complete interval computation for depth 15, residue 14210. -/
theorem bounds_15_14210 : exactInterval 15 14210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14210 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14210) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14210 : oddCount 14210 15 = 8 ∧ acceleratedOrbit 15 14210 = 2848 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14210 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14210) = 3 ^ 8 * m + 2848 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14210.1, data_15_14210.2]

/-- Complete interval computation for depth 15, residue 14211. -/
theorem bounds_15_14211 : exactInterval 15 14211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14211 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14211) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14211 : oddCount 14211 15 = 8 ∧ acceleratedOrbit 15 14211 = 2848 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14211 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14211) = 3 ^ 8 * m + 2848 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14211.1, data_15_14211.2]

/-- Complete interval computation for depth 15, residue 14212. -/
theorem bounds_15_14212 : exactInterval 15 14212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14212 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14212) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14212 : oddCount 14212 15 = 8 ∧ acceleratedOrbit 15 14212 = 2848 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14212 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14212) = 3 ^ 8 * m + 2848 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14212.1, data_15_14212.2]

/-- Complete interval computation for depth 15, residue 14213. -/
theorem bounds_15_14213 : exactInterval 15 14213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14213 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14213) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14213 : oddCount 14213 15 = 8 ∧ acceleratedOrbit 15 14213 = 2848 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14213 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14213) = 3 ^ 8 * m + 2848 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14213.1, data_15_14213.2]

/-- Complete interval computation for depth 15, residue 14214. -/
theorem bounds_15_14214 : exactInterval 15 14214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14214 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14214) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14214 : oddCount 14214 15 = 8 ∧ acceleratedOrbit 15 14214 = 2848 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14214 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14214) = 3 ^ 8 * m + 2848 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14214.1, data_15_14214.2]

/-- Complete interval computation for depth 15, residue 14215. -/
theorem bounds_15_14215 : exactInterval 15 14215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14215 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14215) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14215 : oddCount 14215 15 = 8 ∧ acceleratedOrbit 15 14215 = 2848 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14215 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14215) = 3 ^ 8 * m + 2848 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14215.1, data_15_14215.2]

/-- Complete interval computation for depth 15, residue 14216. -/
theorem bounds_15_14216 : exactInterval 15 14216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14216 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14216) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14216 : oddCount 14216 15 = 5 ∧ acceleratedOrbit 15 14216 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14216 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14216) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14216.1, data_15_14216.2]

/-- Complete interval computation for depth 15, residue 14217. -/
theorem bounds_15_14217 : exactInterval 15 14217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14217 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14217) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14217 : oddCount 14217 15 = 7 ∧ acceleratedOrbit 15 14217 = 949 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14217 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14217) = 3 ^ 7 * m + 949 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14217.1, data_15_14217.2]

/-- Complete interval computation for depth 15, residue 14218. -/
theorem bounds_15_14218 : exactInterval 15 14218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14218 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14218) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14218 : oddCount 14218 15 = 5 ∧ acceleratedOrbit 15 14218 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14218 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14218) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14218.1, data_15_14218.2]

/-- Complete interval computation for depth 15, residue 14219. -/
theorem bounds_15_14219 : exactInterval 15 14219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14219 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14219) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14219 : oddCount 14219 15 = 9 ∧ acceleratedOrbit 15 14219 = 8543 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14219 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14219) = 3 ^ 9 * m + 8543 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14219.1, data_15_14219.2]

/-- Complete interval computation for depth 15, residue 14220. -/
theorem bounds_15_14220 : exactInterval 15 14220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14220 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14220) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14220 : oddCount 14220 15 = 5 ∧ acceleratedOrbit 15 14220 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14220 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14220) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14220.1, data_15_14220.2]

end Collatz.Research.PassageAtlas.Batch0434
