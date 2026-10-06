import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0874

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6241. -/
theorem bounds_13_6241 : exactInterval 13 6241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6241 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6241) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6241 : oddCount 6241 13 = 7 ∧ acceleratedOrbit 13 6241 = 1667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6241 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6241) = 3 ^ 7 * m + 1667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6241.1, data_13_6241.2]

/-- Complete interval computation for depth 13, residue 6242. -/
theorem bounds_13_6242 : exactInterval 13 6242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6242 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6242) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6242 : oddCount 6242 13 = 6 ∧ acceleratedOrbit 13 6242 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6242 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6242) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6242.1, data_13_6242.2]

/-- Complete interval computation for depth 13, residue 6243. -/
theorem bounds_13_6243 : exactInterval 13 6243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6243 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6243) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6243 : oddCount 6243 13 = 6 ∧ acceleratedOrbit 13 6243 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6243 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6243) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6243.1, data_13_6243.2]

/-- Complete interval computation for depth 13, residue 6244. -/
theorem bounds_13_6244 : exactInterval 13 6244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6244 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6244) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6244 : oddCount 6244 13 = 6 ∧ acceleratedOrbit 13 6244 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6244 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6244) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6244.1, data_13_6244.2]

/-- Complete interval computation for depth 13, residue 6245. -/
theorem bounds_13_6245 : exactInterval 13 6245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6245 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6245) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6245 : oddCount 6245 13 = 6 ∧ acceleratedOrbit 13 6245 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6245 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6245) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6245.1, data_13_6245.2]

/-- Complete interval computation for depth 13, residue 6246. -/
theorem bounds_13_6246 : exactInterval 13 6246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6246 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6246) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6246 : oddCount 6246 13 = 6 ∧ acceleratedOrbit 13 6246 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6246 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6246) = 3 ^ 6 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6246.1, data_13_6246.2]

/-- Complete interval computation for depth 13, residue 6247. -/
theorem bounds_13_6247 : exactInterval 13 6247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6247 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6247) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6247 : oddCount 6247 13 = 9 ∧ acceleratedOrbit 13 6247 = 15013 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6247 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6247) = 3 ^ 9 * m + 15013 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6247.1, data_13_6247.2]

/-- Complete interval computation for depth 13, residue 6248. -/
theorem bounds_13_6248 : exactInterval 13 6248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6248 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6248) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6248 : oddCount 6248 13 = 5 ∧ acceleratedOrbit 13 6248 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6248 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6248) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6248.1, data_13_6248.2]

/-- Complete interval computation for depth 13, residue 6249. -/
theorem bounds_13_6249 : exactInterval 13 6249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6249 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6249) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6249 : oddCount 6249 13 = 7 ∧ acceleratedOrbit 13 6249 = 1669 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6249 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6249) = 3 ^ 7 * m + 1669 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6249.1, data_13_6249.2]

/-- Complete interval computation for depth 13, residue 6250. -/
theorem bounds_13_6250 : exactInterval 13 6250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6250 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6250) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6250 : oddCount 6250 13 = 5 ∧ acceleratedOrbit 13 6250 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6250 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6250) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6250.1, data_13_6250.2]

/-- Complete interval computation for depth 13, residue 6251. -/
theorem bounds_13_6251 : exactInterval 13 6251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6251 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6251) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6251 : oddCount 6251 13 = 9 ∧ acceleratedOrbit 13 6251 = 15025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6251 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6251) = 3 ^ 9 * m + 15025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6251.1, data_13_6251.2]

/-- Complete interval computation for depth 13, residue 6252. -/
theorem bounds_13_6252 : exactInterval 13 6252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6252 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6252) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6252 : oddCount 6252 13 = 8 ∧ acceleratedOrbit 13 6252 = 5012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6252 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6252) = 3 ^ 8 * m + 5012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6252.1, data_13_6252.2]

/-- Complete interval computation for depth 13, residue 6253. -/
theorem bounds_13_6253 : exactInterval 13 6253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6253 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6253) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6253 : oddCount 6253 13 = 8 ∧ acceleratedOrbit 13 6253 = 5012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6253 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6253) = 3 ^ 8 * m + 5012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6253.1, data_13_6253.2]

/-- Complete interval computation for depth 13, residue 6254. -/
theorem bounds_13_6254 : exactInterval 13 6254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6254 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6254) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6254 : oddCount 6254 13 = 8 ∧ acceleratedOrbit 13 6254 = 5012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6254 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6254) = 3 ^ 8 * m + 5012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6254.1, data_13_6254.2]

/-- Complete interval computation for depth 13, residue 6255. -/
theorem bounds_13_6255 : exactInterval 13 6255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6255 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6255) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6255 : oddCount 6255 13 = 9 ∧ acceleratedOrbit 13 6255 = 15032 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6255 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6255) = 3 ^ 9 * m + 15032 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6255.1, data_13_6255.2]

end Collatz.Research.StoppingAtlas.Batch0874
