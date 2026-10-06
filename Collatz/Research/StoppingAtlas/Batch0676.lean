import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0676

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3200. -/
theorem bounds_13_3200 : exactInterval 13 3200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3200 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3200) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3200 : oddCount 3200 13 = 3 ∧ acceleratedOrbit 13 3200 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3200 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3200) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3200.1, data_13_3200.2]

/-- Complete interval computation for depth 13, residue 3201. -/
theorem bounds_13_3201 : exactInterval 13 3201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3201 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3201) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3201 : oddCount 3201 13 = 8 ∧ acceleratedOrbit 13 3201 = 2567 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3201 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3201) = 3 ^ 8 * m + 2567 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3201.1, data_13_3201.2]

/-- Complete interval computation for depth 13, residue 3202. -/
theorem bounds_13_3202 : exactInterval 13 3202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3202 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3202) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3202 : oddCount 3202 13 = 6 ∧ acceleratedOrbit 13 3202 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3202 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3202) = 3 ^ 6 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3202.1, data_13_3202.2]

/-- Complete interval computation for depth 13, residue 3203. -/
theorem bounds_13_3203 : exactInterval 13 3203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3203 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3203) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3203 : oddCount 3203 13 = 6 ∧ acceleratedOrbit 13 3203 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3203 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3203) = 3 ^ 6 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3203.1, data_13_3203.2]

/-- Complete interval computation for depth 13, residue 3204. -/
theorem bounds_13_3204 : exactInterval 13 3204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3204 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3204) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3204 : oddCount 3204 13 = 6 ∧ acceleratedOrbit 13 3204 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3204 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3204) = 3 ^ 6 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3204.1, data_13_3204.2]

/-- Complete interval computation for depth 13, residue 3205. -/
theorem bounds_13_3205 : exactInterval 13 3205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3205 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3205) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3205 : oddCount 3205 13 = 6 ∧ acceleratedOrbit 13 3205 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3205 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3205) = 3 ^ 6 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3205.1, data_13_3205.2]

/-- Complete interval computation for depth 13, residue 3206. -/
theorem bounds_13_3206 : exactInterval 13 3206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3206 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3206) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3206 : oddCount 3206 13 = 6 ∧ acceleratedOrbit 13 3206 = 287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3206 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3206) = 3 ^ 6 * m + 287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3206.1, data_13_3206.2]

/-- Complete interval computation for depth 13, residue 3207. -/
theorem bounds_13_3207 : exactInterval 13 3207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3207 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3207) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3207 : oddCount 3207 13 = 7 ∧ acceleratedOrbit 13 3207 = 857 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3207 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3207) = 3 ^ 7 * m + 857 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3207.1, data_13_3207.2]

/-- Complete interval computation for depth 13, residue 3208. -/
theorem bounds_13_3208 : exactInterval 13 3208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3208 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3208) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3208 : oddCount 3208 13 = 4 ∧ acceleratedOrbit 13 3208 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3208 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3208) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3208.1, data_13_3208.2]

/-- Complete interval computation for depth 13, residue 3209. -/
theorem bounds_13_3209 : exactInterval 13 3209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3209 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3209) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3209 : oddCount 3209 13 = 9 ∧ acceleratedOrbit 13 3209 = 7715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3209 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3209) = 3 ^ 9 * m + 7715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3209.1, data_13_3209.2]

/-- Complete interval computation for depth 13, residue 3210. -/
theorem bounds_13_3210 : exactInterval 13 3210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3210 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3210) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3210 : oddCount 3210 13 = 4 ∧ acceleratedOrbit 13 3210 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3210 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3210) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3210.1, data_13_3210.2]

/-- Complete interval computation for depth 13, residue 3211. -/
theorem bounds_13_3211 : exactInterval 13 3211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3211 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3211) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3211 : oddCount 3211 13 = 6 ∧ acceleratedOrbit 13 3211 = 286 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3211 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3211) = 3 ^ 6 * m + 286 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3211.1, data_13_3211.2]

/-- Complete interval computation for depth 13, residue 3212. -/
theorem bounds_13_3212 : exactInterval 13 3212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3212 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3212) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3212 : oddCount 3212 13 = 4 ∧ acceleratedOrbit 13 3212 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3212 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3212) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3212.1, data_13_3212.2]

/-- Complete interval computation for depth 13, residue 3213. -/
theorem bounds_13_3213 : exactInterval 13 3213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3213 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3213) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3213 : oddCount 3213 13 = 4 ∧ acceleratedOrbit 13 3213 = 32 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3213 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3213) = 3 ^ 4 * m + 32 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3213.1, data_13_3213.2]

/-- Complete interval computation for depth 13, residue 3214. -/
theorem bounds_13_3214 : exactInterval 13 3214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3214 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3214) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3214 : oddCount 3214 13 = 7 ∧ acceleratedOrbit 13 3214 = 859 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3214 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3214) = 3 ^ 7 * m + 859 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3214.1, data_13_3214.2]

end Collatz.Research.StoppingAtlas.Batch0676
