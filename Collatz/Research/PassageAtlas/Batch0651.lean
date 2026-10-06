import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0651

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 21299. -/
theorem bounds_15_21299 : exactInterval 15 21299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21299 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21299) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21299 : oddCount 21299 15 = 5 ∧ acceleratedOrbit 15 21299 = 158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21299 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21299) = 3 ^ 5 * m + 158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21299.1, data_15_21299.2]

/-- Complete interval computation for depth 15, residue 21300. -/
theorem bounds_15_21300 : exactInterval 15 21300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21300 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21300) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21300 : oddCount 21300 15 = 6 ∧ acceleratedOrbit 15 21300 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21300 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21300) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21300.1, data_15_21300.2]

/-- Complete interval computation for depth 15, residue 21301. -/
theorem bounds_15_21301 : exactInterval 15 21301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21301 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21301) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21301 : oddCount 21301 15 = 6 ∧ acceleratedOrbit 15 21301 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21301 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21301) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21301.1, data_15_21301.2]

/-- Complete interval computation for depth 15, residue 21302. -/
theorem bounds_15_21302 : exactInterval 15 21302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21302 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21302) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21302 : oddCount 21302 15 = 11 ∧ acceleratedOrbit 15 21302 = 115181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21302 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21302) = 3 ^ 11 * m + 115181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21302.1, data_15_21302.2]

/-- Complete interval computation for depth 15, residue 21303. -/
theorem bounds_15_21303 : exactInterval 15 21303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21303 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21303) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21303 : oddCount 21303 15 = 11 ∧ acceleratedOrbit 15 21303 = 115181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21303 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21303) = 3 ^ 11 * m + 115181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21303.1, data_15_21303.2]

/-- Complete interval computation for depth 15, residue 21304. -/
theorem bounds_15_21304 : exactInterval 15 21304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21304 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21304) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21304 : oddCount 21304 15 = 8 ∧ acceleratedOrbit 15 21304 = 4268 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21304 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21304) = 3 ^ 8 * m + 4268 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21304.1, data_15_21304.2]

/-- Complete interval computation for depth 15, residue 21305. -/
theorem bounds_15_21305 : exactInterval 15 21305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21305 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21305) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21305 : oddCount 21305 15 = 9 ∧ acceleratedOrbit 15 21305 = 12800 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21305 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21305) = 3 ^ 9 * m + 12800 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21305.1, data_15_21305.2]

/-- Complete interval computation for depth 15, residue 21306. -/
theorem bounds_15_21306 : exactInterval 15 21306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21306 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21306) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21306 : oddCount 21306 15 = 8 ∧ acceleratedOrbit 15 21306 = 4268 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21306 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21306) = 3 ^ 8 * m + 4268 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21306.1, data_15_21306.2]

/-- Complete interval computation for depth 15, residue 21307. -/
theorem bounds_15_21307 : exactInterval 15 21307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21307 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21307) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21307 : oddCount 21307 15 = 8 ∧ acceleratedOrbit 15 21307 = 4268 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21307 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21307) = 3 ^ 8 * m + 4268 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21307.1, data_15_21307.2]

/-- Complete interval computation for depth 15, residue 21308. -/
theorem bounds_15_21308 : exactInterval 15 21308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21308 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21308) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21308 : oddCount 21308 15 = 8 ∧ acceleratedOrbit 15 21308 = 4268 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21308 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21308) = 3 ^ 8 * m + 4268 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21308.1, data_15_21308.2]

/-- Complete interval computation for depth 15, residue 21309. -/
theorem bounds_15_21309 : exactInterval 15 21309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21309 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21309) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21309 : oddCount 21309 15 = 8 ∧ acceleratedOrbit 15 21309 = 4268 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21309 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21309) = 3 ^ 8 * m + 4268 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21309.1, data_15_21309.2]

/-- Complete interval computation for depth 15, residue 21310. -/
theorem bounds_15_21310 : exactInterval 15 21310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21310 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21310) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21310 : oddCount 21310 15 = 9 ∧ acceleratedOrbit 15 21310 = 12802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21310 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21310) = 3 ^ 9 * m + 12802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21310.1, data_15_21310.2]

/-- Complete interval computation for depth 15, residue 21311. -/
theorem bounds_15_21311 : exactInterval 15 21311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21311 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21311) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21311 : oddCount 21311 15 = 9 ∧ acceleratedOrbit 15 21311 = 12802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21311 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21311) = 3 ^ 9 * m + 12802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21311.1, data_15_21311.2]

/-- Complete interval computation for depth 15, residue 21312. -/
theorem bounds_15_21312 : exactInterval 15 21312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21312 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21312) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21312 : oddCount 21312 15 = 5 ∧ acceleratedOrbit 15 21312 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21312 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21312) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21312.1, data_15_21312.2]

/-- Complete interval computation for depth 15, residue 21313. -/
theorem bounds_15_21313 : exactInterval 15 21313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21313 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21313) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21313 : oddCount 21313 15 = 6 ∧ acceleratedOrbit 15 21313 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21313 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21313) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21313.1, data_15_21313.2]

/-- Complete interval computation for depth 15, residue 21314. -/
theorem bounds_15_21314 : exactInterval 15 21314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21314 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21314) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21314 : oddCount 21314 15 = 7 ∧ acceleratedOrbit 15 21314 = 1423 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21314 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21314) = 3 ^ 7 * m + 1423 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21314.1, data_15_21314.2]

/-- Complete interval computation for depth 15, residue 21315. -/
theorem bounds_15_21315 : exactInterval 15 21315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21315 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21315) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21315 : oddCount 21315 15 = 7 ∧ acceleratedOrbit 15 21315 = 1423 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21315 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21315) = 3 ^ 7 * m + 1423 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21315.1, data_15_21315.2]

/-- Complete interval computation for depth 15, residue 21316. -/
theorem bounds_15_21316 : exactInterval 15 21316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21316 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21316) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21316 : oddCount 21316 15 = 7 ∧ acceleratedOrbit 15 21316 = 1424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21316 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21316) = 3 ^ 7 * m + 1424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21316.1, data_15_21316.2]

/-- Complete interval computation for depth 15, residue 21317. -/
theorem bounds_15_21317 : exactInterval 15 21317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21317 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21317) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21317 : oddCount 21317 15 = 7 ∧ acceleratedOrbit 15 21317 = 1424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21317 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21317) = 3 ^ 7 * m + 1424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21317.1, data_15_21317.2]

/-- Complete interval computation for depth 15, residue 21318. -/
theorem bounds_15_21318 : exactInterval 15 21318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21318 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21318) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21318 : oddCount 21318 15 = 7 ∧ acceleratedOrbit 15 21318 = 1424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21318 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21318) = 3 ^ 7 * m + 1424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21318.1, data_15_21318.2]

/-- Complete interval computation for depth 15, residue 21319. -/
theorem bounds_15_21319 : exactInterval 15 21319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21319 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21319) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21319 : oddCount 21319 15 = 12 ∧ acceleratedOrbit 15 21319 = 345788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21319 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21319) = 3 ^ 12 * m + 345788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21319.1, data_15_21319.2]

/-- Complete interval computation for depth 15, residue 21320. -/
theorem bounds_15_21320 : exactInterval 15 21320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21320 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21320) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21320 : oddCount 21320 15 = 7 ∧ acceleratedOrbit 15 21320 = 1424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21320 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21320) = 3 ^ 7 * m + 1424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21320.1, data_15_21320.2]

/-- Complete interval computation for depth 15, residue 21321. -/
theorem bounds_15_21321 : exactInterval 15 21321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21321 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21321) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21321 : oddCount 21321 15 = 7 ∧ acceleratedOrbit 15 21321 = 1424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21321 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21321) = 3 ^ 7 * m + 1424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21321.1, data_15_21321.2]

/-- Complete interval computation for depth 15, residue 21322. -/
theorem bounds_15_21322 : exactInterval 15 21322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21322 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21322) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21322 : oddCount 21322 15 = 7 ∧ acceleratedOrbit 15 21322 = 1424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21322 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21322) = 3 ^ 7 * m + 1424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21322.1, data_15_21322.2]

/-- Complete interval computation for depth 15, residue 21323. -/
theorem bounds_15_21323 : exactInterval 15 21323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21323 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21323) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21323 : oddCount 21323 15 = 7 ∧ acceleratedOrbit 15 21323 = 1424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21323 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21323) = 3 ^ 7 * m + 1424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21323.1, data_15_21323.2]

/-- Complete interval computation for depth 15, residue 21324. -/
theorem bounds_15_21324 : exactInterval 15 21324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21324 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21324) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21324 : oddCount 21324 15 = 7 ∧ acceleratedOrbit 15 21324 = 1424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21324 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21324) = 3 ^ 7 * m + 1424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21324.1, data_15_21324.2]

/-- Complete interval computation for depth 15, residue 21325. -/
theorem bounds_15_21325 : exactInterval 15 21325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21325 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21325) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21325 : oddCount 21325 15 = 7 ∧ acceleratedOrbit 15 21325 = 1424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21325 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21325) = 3 ^ 7 * m + 1424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21325.1, data_15_21325.2]

/-- Complete interval computation for depth 15, residue 21326. -/
theorem bounds_15_21326 : exactInterval 15 21326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21326 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21326) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21326 : oddCount 21326 15 = 7 ∧ acceleratedOrbit 15 21326 = 1424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21326 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21326) = 3 ^ 7 * m + 1424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21326.1, data_15_21326.2]

/-- Complete interval computation for depth 15, residue 21327. -/
theorem bounds_15_21327 : exactInterval 15 21327 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21327 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21327) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21327 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21327 : oddCount 21327 15 = 7 ∧ acceleratedOrbit 15 21327 = 1424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21327 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21327) = 3 ^ 7 * m + 1424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21327.1, data_15_21327.2]

/-- Complete interval computation for depth 15, residue 21328. -/
theorem bounds_15_21328 : exactInterval 15 21328 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21328 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21328) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21328 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21328 : oddCount 21328 15 = 5 ∧ acceleratedOrbit 15 21328 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21328 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21328) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21328.1, data_15_21328.2]

/-- Complete interval computation for depth 15, residue 21329. -/
theorem bounds_15_21329 : exactInterval 15 21329 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21329 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21329) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21329 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21329 : oddCount 21329 15 = 9 ∧ acceleratedOrbit 15 21329 = 12815 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21329 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21329) = 3 ^ 9 * m + 12815 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21329.1, data_15_21329.2]

/-- Complete interval computation for depth 15, residue 21330. -/
theorem bounds_15_21330 : exactInterval 15 21330 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21330 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21330) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21330 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21330 : oddCount 21330 15 = 9 ∧ acceleratedOrbit 15 21330 = 12815 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21330 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21330) = 3 ^ 9 * m + 12815 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21330.1, data_15_21330.2]

end Collatz.Research.PassageAtlas.Batch0651
