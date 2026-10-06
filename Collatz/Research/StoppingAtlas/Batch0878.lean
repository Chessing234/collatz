import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0878

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6302. -/
theorem bounds_13_6302 : exactInterval 13 6302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6302 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6302) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6302 : oddCount 6302 13 = 5 ∧ acceleratedOrbit 13 6302 = 187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6302 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6302) = 3 ^ 5 * m + 187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6302.1, data_13_6302.2]

/-- Complete interval computation for depth 13, residue 6303. -/
theorem bounds_13_6303 : exactInterval 13 6303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6303 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6303) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6303 : oddCount 6303 13 = 12 ∧ acceleratedOrbit 13 6303 = 408968 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6303 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6303) = 3 ^ 12 * m + 408968 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6303.1, data_13_6303.2]

/-- Complete interval computation for depth 13, residue 6304. -/
theorem bounds_13_6304 : exactInterval 13 6304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6304 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6304) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6304 : oddCount 6304 13 = 2 ∧ acceleratedOrbit 13 6304 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6304 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6304) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6304.1, data_13_6304.2]

/-- Complete interval computation for depth 13, residue 6305. -/
theorem bounds_13_6305 : exactInterval 13 6305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6305 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6305) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6305 : oddCount 6305 13 = 7 ∧ acceleratedOrbit 13 6305 = 1684 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6305 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6305) = 3 ^ 7 * m + 1684 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6305.1, data_13_6305.2]

/-- Complete interval computation for depth 13, residue 6306. -/
theorem bounds_13_6306 : exactInterval 13 6306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6306 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6306) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6306 : oddCount 6306 13 = 6 ∧ acceleratedOrbit 13 6306 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6306 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6306) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6306.1, data_13_6306.2]

/-- Complete interval computation for depth 13, residue 6307. -/
theorem bounds_13_6307 : exactInterval 13 6307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6307 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6307) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6307 : oddCount 6307 13 = 6 ∧ acceleratedOrbit 13 6307 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6307 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6307) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6307.1, data_13_6307.2]

/-- Complete interval computation for depth 13, residue 6308. -/
theorem bounds_13_6308 : exactInterval 13 6308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6308 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6308) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6308 : oddCount 6308 13 = 9 ∧ acceleratedOrbit 13 6308 = 15173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6308 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6308) = 3 ^ 9 * m + 15173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6308.1, data_13_6308.2]

/-- Complete interval computation for depth 13, residue 6309. -/
theorem bounds_13_6309 : exactInterval 13 6309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6309 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6309) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6309 : oddCount 6309 13 = 9 ∧ acceleratedOrbit 13 6309 = 15173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6309 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6309) = 3 ^ 9 * m + 15173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6309.1, data_13_6309.2]

/-- Complete interval computation for depth 13, residue 6310. -/
theorem bounds_13_6310 : exactInterval 13 6310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6310 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6310) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6310 : oddCount 6310 13 = 9 ∧ acceleratedOrbit 13 6310 = 15173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6310 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6310) = 3 ^ 9 * m + 15173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6310.1, data_13_6310.2]

/-- Complete interval computation for depth 13, residue 6311. -/
theorem bounds_13_6311 : exactInterval 13 6311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6311 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6311) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6311 : oddCount 6311 13 = 9 ∧ acceleratedOrbit 13 6311 = 15167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6311 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6311) = 3 ^ 9 * m + 15167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6311.1, data_13_6311.2]

/-- Complete interval computation for depth 13, residue 6312. -/
theorem bounds_13_6312 : exactInterval 13 6312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6312 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6312) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6312 : oddCount 6312 13 = 2 ∧ acceleratedOrbit 13 6312 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6312 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6312) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6312.1, data_13_6312.2]

/-- Complete interval computation for depth 13, residue 6313. -/
theorem bounds_13_6313 : exactInterval 13 6313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6313 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6313) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6313 : oddCount 6313 13 = 10 ∧ acceleratedOrbit 13 6313 = 45517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6313 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6313) = 3 ^ 10 * m + 45517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6313.1, data_13_6313.2]

/-- Complete interval computation for depth 13, residue 6314. -/
theorem bounds_13_6314 : exactInterval 13 6314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6314 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6314) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6314 : oddCount 6314 13 = 2 ∧ acceleratedOrbit 13 6314 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6314 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6314) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6314.1, data_13_6314.2]

/-- Complete interval computation for depth 13, residue 6315. -/
theorem bounds_13_6315 : exactInterval 13 6315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6315 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6315) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6315 : oddCount 6315 13 = 7 ∧ acceleratedOrbit 13 6315 = 1687 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6315 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6315) = 3 ^ 7 * m + 1687 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6315.1, data_13_6315.2]

/-- Complete interval computation for depth 13, residue 6316. -/
theorem bounds_13_6316 : exactInterval 13 6316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6316 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6316) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6316 : oddCount 6316 13 = 5 ∧ acceleratedOrbit 13 6316 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6316 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6316) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6316.1, data_13_6316.2]

/-- Complete interval computation for depth 13, residue 6317. -/
theorem bounds_13_6317 : exactInterval 13 6317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6317 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6317) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6317 : oddCount 6317 13 = 5 ∧ acceleratedOrbit 13 6317 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6317 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6317) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6317.1, data_13_6317.2]

end Collatz.Research.StoppingAtlas.Batch0878
