import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0468

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 15302. -/
theorem bounds_15_15302 : exactInterval 15 15302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15302 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15302) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15302 : oddCount 15302 15 = 4 ∧ acceleratedOrbit 15 15302 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15302 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15302) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15302.1, data_15_15302.2]

/-- Complete interval computation for depth 15, residue 15303. -/
theorem bounds_15_15303 : exactInterval 15 15303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15303 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15303) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15303 : oddCount 15303 15 = 11 ∧ acceleratedOrbit 15 15303 = 82741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15303 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15303) = 3 ^ 11 * m + 82741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15303.1, data_15_15303.2]

/-- Complete interval computation for depth 15, residue 15304. -/
theorem bounds_15_15304 : exactInterval 15 15304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15304 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15304) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15304 : oddCount 15304 15 = 8 ∧ acceleratedOrbit 15 15304 = 3068 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15304 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15304) = 3 ^ 8 * m + 3068 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15304.1, data_15_15304.2]

/-- Complete interval computation for depth 15, residue 15305. -/
theorem bounds_15_15305 : exactInterval 15 15305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15305 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15305) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15305 : oddCount 15305 15 = 9 ∧ acceleratedOrbit 15 15305 = 9197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15305 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15305) = 3 ^ 9 * m + 9197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15305.1, data_15_15305.2]

/-- Complete interval computation for depth 15, residue 15306. -/
theorem bounds_15_15306 : exactInterval 15 15306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15306 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15306) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15306 : oddCount 15306 15 = 8 ∧ acceleratedOrbit 15 15306 = 3068 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15306 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15306) = 3 ^ 8 * m + 3068 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15306.1, data_15_15306.2]

/-- Complete interval computation for depth 15, residue 15307. -/
theorem bounds_15_15307 : exactInterval 15 15307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15307 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15307) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15307 : oddCount 15307 15 = 8 ∧ acceleratedOrbit 15 15307 = 3068 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15307 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15307) = 3 ^ 8 * m + 3068 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15307.1, data_15_15307.2]

/-- Complete interval computation for depth 15, residue 15308. -/
theorem bounds_15_15308 : exactInterval 15 15308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15308 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15308) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15308 : oddCount 15308 15 = 8 ∧ acceleratedOrbit 15 15308 = 3068 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15308 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15308) = 3 ^ 8 * m + 3068 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15308.1, data_15_15308.2]

/-- Complete interval computation for depth 15, residue 15309. -/
theorem bounds_15_15309 : exactInterval 15 15309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15309 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15309) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15309 : oddCount 15309 15 = 8 ∧ acceleratedOrbit 15 15309 = 3068 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15309 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15309) = 3 ^ 8 * m + 3068 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15309.1, data_15_15309.2]

/-- Complete interval computation for depth 15, residue 15310. -/
theorem bounds_15_15310 : exactInterval 15 15310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15310 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15310) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15310 : oddCount 15310 15 = 7 ∧ acceleratedOrbit 15 15310 = 1022 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15310 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15310) = 3 ^ 7 * m + 1022 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15310.1, data_15_15310.2]

/-- Complete interval computation for depth 15, residue 15311. -/
theorem bounds_15_15311 : exactInterval 15 15311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15311 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15311) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15311 : oddCount 15311 15 = 7 ∧ acceleratedOrbit 15 15311 = 1022 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15311 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15311) = 3 ^ 7 * m + 1022 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15311.1, data_15_15311.2]

/-- Complete interval computation for depth 15, residue 15312. -/
theorem bounds_15_15312 : exactInterval 15 15312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15312 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15312) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15312 : oddCount 15312 15 = 8 ∧ acceleratedOrbit 15 15312 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15312 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15312) = 3 ^ 8 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15312.1, data_15_15312.2]

/-- Complete interval computation for depth 15, residue 15313. -/
theorem bounds_15_15313 : exactInterval 15 15313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15313 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15313) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15313 : oddCount 15313 15 = 8 ∧ acceleratedOrbit 15 15313 = 3068 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15313 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15313) = 3 ^ 8 * m + 3068 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15313.1, data_15_15313.2]

/-- Complete interval computation for depth 15, residue 15314. -/
theorem bounds_15_15314 : exactInterval 15 15314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15314 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15314) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15314 : oddCount 15314 15 = 8 ∧ acceleratedOrbit 15 15314 = 3067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15314 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15314) = 3 ^ 8 * m + 3067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15314.1, data_15_15314.2]

/-- Complete interval computation for depth 15, residue 15315. -/
theorem bounds_15_15315 : exactInterval 15 15315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15315 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15315) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15315 : oddCount 15315 15 = 8 ∧ acceleratedOrbit 15 15315 = 3067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15315 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15315) = 3 ^ 8 * m + 3067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15315.1, data_15_15315.2]

/-- Complete interval computation for depth 15, residue 15316. -/
theorem bounds_15_15316 : exactInterval 15 15316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15316 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15316) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15316 : oddCount 15316 15 = 8 ∧ acceleratedOrbit 15 15316 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15316 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15316) = 3 ^ 8 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15316.1, data_15_15316.2]

/-- Complete interval computation for depth 15, residue 15317. -/
theorem bounds_15_15317 : exactInterval 15 15317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15317 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15317) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15317 : oddCount 15317 15 = 8 ∧ acceleratedOrbit 15 15317 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15317 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15317) = 3 ^ 8 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15317.1, data_15_15317.2]

/-- Complete interval computation for depth 15, residue 15318. -/
theorem bounds_15_15318 : exactInterval 15 15318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15318 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15318) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15318 : oddCount 15318 15 = 10 ∧ acceleratedOrbit 15 15318 = 27611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15318 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15318) = 3 ^ 10 * m + 27611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15318.1, data_15_15318.2]

/-- Complete interval computation for depth 15, residue 15319. -/
theorem bounds_15_15319 : exactInterval 15 15319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15319 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15319) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15319 : oddCount 15319 15 = 10 ∧ acceleratedOrbit 15 15319 = 27611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15319 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15319) = 3 ^ 10 * m + 27611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15319.1, data_15_15319.2]

/-- Complete interval computation for depth 15, residue 15320. -/
theorem bounds_15_15320 : exactInterval 15 15320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15320 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15320) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15320 : oddCount 15320 15 = 8 ∧ acceleratedOrbit 15 15320 = 3071 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15320 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15320) = 3 ^ 8 * m + 3071 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15320.1, data_15_15320.2]

/-- Complete interval computation for depth 15, residue 15321. -/
theorem bounds_15_15321 : exactInterval 15 15321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15321 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15321) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15321 : oddCount 15321 15 = 4 ∧ acceleratedOrbit 15 15321 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15321 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15321) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15321.1, data_15_15321.2]

/-- Complete interval computation for depth 15, residue 15322. -/
theorem bounds_15_15322 : exactInterval 15 15322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15322 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15322) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15322 : oddCount 15322 15 = 8 ∧ acceleratedOrbit 15 15322 = 3071 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15322 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15322) = 3 ^ 8 * m + 3071 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15322.1, data_15_15322.2]

/-- Complete interval computation for depth 15, residue 15323. -/
theorem bounds_15_15323 : exactInterval 15 15323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15323 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15323) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15323 : oddCount 15323 15 = 10 ∧ acceleratedOrbit 15 15323 = 27620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15323 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15323) = 3 ^ 10 * m + 27620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15323.1, data_15_15323.2]

/-- Complete interval computation for depth 15, residue 15324. -/
theorem bounds_15_15324 : exactInterval 15 15324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15324 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15324) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15324 : oddCount 15324 15 = 8 ∧ acceleratedOrbit 15 15324 = 3071 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15324 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15324) = 3 ^ 8 * m + 3071 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15324.1, data_15_15324.2]

/-- Complete interval computation for depth 15, residue 15325. -/
theorem bounds_15_15325 : exactInterval 15 15325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15325 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15325) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15325 : oddCount 15325 15 = 8 ∧ acceleratedOrbit 15 15325 = 3071 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15325 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15325) = 3 ^ 8 * m + 3071 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15325.1, data_15_15325.2]

/-- Complete interval computation for depth 15, residue 15326. -/
theorem bounds_15_15326 : exactInterval 15 15326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15326 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15326) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15326 : oddCount 15326 15 = 10 ∧ acceleratedOrbit 15 15326 = 27623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15326 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15326) = 3 ^ 10 * m + 27623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15326.1, data_15_15326.2]

/-- Complete interval computation for depth 15, residue 15327. -/
theorem bounds_15_15327 : exactInterval 15 15327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15327 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15327) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15327 : oddCount 15327 15 = 10 ∧ acceleratedOrbit 15 15327 = 27623 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15327 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15327) = 3 ^ 10 * m + 27623 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15327.1, data_15_15327.2]

/-- Complete interval computation for depth 15, residue 15328. -/
theorem bounds_15_15328 : exactInterval 15 15328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15328 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15328) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15328 : oddCount 15328 15 = 8 ∧ acceleratedOrbit 15 15328 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15328 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15328) = 3 ^ 8 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15328.1, data_15_15328.2]

/-- Complete interval computation for depth 15, residue 15329. -/
theorem bounds_15_15329 : exactInterval 15 15329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15329 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15329) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15329 : oddCount 15329 15 = 8 ∧ acceleratedOrbit 15 15329 = 3070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15329 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15329) = 3 ^ 8 * m + 3070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15329.1, data_15_15329.2]

/-- Complete interval computation for depth 15, residue 15330. -/
theorem bounds_15_15330 : exactInterval 15 15330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15330 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15330) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15330 : oddCount 15330 15 = 8 ∧ acceleratedOrbit 15 15330 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15330 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15330) = 3 ^ 8 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15330.1, data_15_15330.2]

/-- Complete interval computation for depth 15, residue 15331. -/
theorem bounds_15_15331 : exactInterval 15 15331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15331 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15331) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15331 : oddCount 15331 15 = 8 ∧ acceleratedOrbit 15 15331 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15331 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15331) = 3 ^ 8 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15331.1, data_15_15331.2]

/-- Complete interval computation for depth 15, residue 15332. -/
theorem bounds_15_15332 : exactInterval 15 15332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15332 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15332) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15332 : oddCount 15332 15 = 7 ∧ acceleratedOrbit 15 15332 = 1025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15332 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15332) = 3 ^ 7 * m + 1025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15332.1, data_15_15332.2]

/-- Complete interval computation for depth 15, residue 15333. -/
theorem bounds_15_15333 : exactInterval 15 15333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15333 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15333) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15333 : oddCount 15333 15 = 7 ∧ acceleratedOrbit 15 15333 = 1025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15333 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15333) = 3 ^ 7 * m + 1025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15333.1, data_15_15333.2]

/-- Complete interval computation for depth 15, residue 15334. -/
theorem bounds_15_15334 : exactInterval 15 15334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15334 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15334) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15334 : oddCount 15334 15 = 7 ∧ acceleratedOrbit 15 15334 = 1025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15334 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15334) = 3 ^ 7 * m + 1025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15334.1, data_15_15334.2]

end Collatz.Research.PassageAtlas.Batch0468
