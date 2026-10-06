import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0943

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7301. -/
theorem bounds_13_7301 : exactInterval 13 7301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7301 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7301) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7301 : oddCount 7301 13 = 5 ∧ acceleratedOrbit 13 7301 = 217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7301 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7301) = 3 ^ 5 * m + 217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7301.1, data_13_7301.2]

/-- Complete interval computation for depth 13, residue 7302. -/
theorem bounds_13_7302 : exactInterval 13 7302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7302 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7302) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7302 : oddCount 7302 13 = 5 ∧ acceleratedOrbit 13 7302 = 217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7302 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7302) = 3 ^ 5 * m + 217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7302.1, data_13_7302.2]

/-- Complete interval computation for depth 13, residue 7303. -/
theorem bounds_13_7303 : exactInterval 13 7303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7303 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7303) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7303 : oddCount 7303 13 = 8 ∧ acceleratedOrbit 13 7303 = 5852 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7303 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7303) = 3 ^ 8 * m + 5852 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7303.1, data_13_7303.2]

/-- Complete interval computation for depth 13, residue 7304. -/
theorem bounds_13_7304 : exactInterval 13 7304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7304 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7304) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7304 : oddCount 7304 13 = 5 ∧ acceleratedOrbit 13 7304 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7304 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7304) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7304.1, data_13_7304.2]

/-- Complete interval computation for depth 13, residue 7305. -/
theorem bounds_13_7305 : exactInterval 13 7305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7305 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7305) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7305 : oddCount 7305 13 = 10 ∧ acceleratedOrbit 13 7305 = 52670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7305 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7305) = 3 ^ 10 * m + 52670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7305.1, data_13_7305.2]

/-- Complete interval computation for depth 13, residue 7306. -/
theorem bounds_13_7306 : exactInterval 13 7306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7306 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7306) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7306 : oddCount 7306 13 = 5 ∧ acceleratedOrbit 13 7306 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7306 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7306) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7306.1, data_13_7306.2]

/-- Complete interval computation for depth 13, residue 7307. -/
theorem bounds_13_7307 : exactInterval 13 7307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7307 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7307) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7307 : oddCount 7307 13 = 7 ∧ acceleratedOrbit 13 7307 = 1952 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7307 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7307) = 3 ^ 7 * m + 1952 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7307.1, data_13_7307.2]

/-- Complete interval computation for depth 13, residue 7308. -/
theorem bounds_13_7308 : exactInterval 13 7308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7308 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7308) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7308 : oddCount 7308 13 = 5 ∧ acceleratedOrbit 13 7308 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7308 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7308) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7308.1, data_13_7308.2]

/-- Complete interval computation for depth 13, residue 7309. -/
theorem bounds_13_7309 : exactInterval 13 7309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7309 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7309) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7309 : oddCount 7309 13 = 5 ∧ acceleratedOrbit 13 7309 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7309 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7309) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7309.1, data_13_7309.2]

/-- Complete interval computation for depth 13, residue 7310. -/
theorem bounds_13_7310 : exactInterval 13 7310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7310 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7310) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7310 : oddCount 7310 13 = 8 ∧ acceleratedOrbit 13 7310 = 5858 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7310 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7310) = 3 ^ 8 * m + 5858 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7310.1, data_13_7310.2]

/-- Complete interval computation for depth 13, residue 7311. -/
theorem bounds_13_7311 : exactInterval 13 7311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7311 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7311) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7311 : oddCount 7311 13 = 8 ∧ acceleratedOrbit 13 7311 = 5858 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7311 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7311) = 3 ^ 8 * m + 5858 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7311.1, data_13_7311.2]

/-- Complete interval computation for depth 13, residue 7312. -/
theorem bounds_13_7312 : exactInterval 13 7312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7312 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7312) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7312 : oddCount 7312 13 = 5 ∧ acceleratedOrbit 13 7312 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7312 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7312) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7312.1, data_13_7312.2]

/-- Complete interval computation for depth 13, residue 7313. -/
theorem bounds_13_7313 : exactInterval 13 7313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7313 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7313) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7313 : oddCount 7313 13 = 7 ∧ acceleratedOrbit 13 7313 = 1954 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7313 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7313) = 3 ^ 7 * m + 1954 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7313.1, data_13_7313.2]

/-- Complete interval computation for depth 13, residue 7314. -/
theorem bounds_13_7314 : exactInterval 13 7314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7314 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7314) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7314 : oddCount 7314 13 = 7 ∧ acceleratedOrbit 13 7314 = 1954 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7314 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7314) = 3 ^ 7 * m + 1954 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7314.1, data_13_7314.2]

/-- Complete interval computation for depth 13, residue 7315. -/
theorem bounds_13_7315 : exactInterval 13 7315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7315 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7315) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7315 : oddCount 7315 13 = 7 ∧ acceleratedOrbit 13 7315 = 1954 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7315 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7315) = 3 ^ 7 * m + 1954 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7315.1, data_13_7315.2]

end Collatz.Research.StoppingAtlas.Batch0943
