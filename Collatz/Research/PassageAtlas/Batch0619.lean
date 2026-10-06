import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0619

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 20250. -/
theorem bounds_15_20250 : exactInterval 15 20250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20250 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20250) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20250 : oddCount 20250 15 = 5 ∧ acceleratedOrbit 15 20250 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20250 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20250) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20250.1, data_15_20250.2]

/-- Complete interval computation for depth 15, residue 20251. -/
theorem bounds_15_20251 : exactInterval 15 20251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20251 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20251) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20251 : oddCount 20251 15 = 11 ∧ acceleratedOrbit 15 20251 = 109487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20251 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20251) = 3 ^ 11 * m + 109487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20251.1, data_15_20251.2]

/-- Complete interval computation for depth 15, residue 20252. -/
theorem bounds_15_20252 : exactInterval 15 20252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20252 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20252) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20252 : oddCount 20252 15 = 9 ∧ acceleratedOrbit 15 20252 = 12170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20252 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20252) = 3 ^ 9 * m + 12170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20252.1, data_15_20252.2]

/-- Complete interval computation for depth 15, residue 20253. -/
theorem bounds_15_20253 : exactInterval 15 20253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20253 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20253) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20253 : oddCount 20253 15 = 9 ∧ acceleratedOrbit 15 20253 = 12170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20253 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20253) = 3 ^ 9 * m + 12170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20253.1, data_15_20253.2]

/-- Complete interval computation for depth 15, residue 20254. -/
theorem bounds_15_20254 : exactInterval 15 20254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20254 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20254) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20254 : oddCount 20254 15 = 9 ∧ acceleratedOrbit 15 20254 = 12170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20254 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20254) = 3 ^ 9 * m + 12170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20254.1, data_15_20254.2]

/-- Complete interval computation for depth 15, residue 20255. -/
theorem bounds_15_20255 : exactInterval 15 20255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20255 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20255) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20255 : oddCount 20255 15 = 11 ∧ acceleratedOrbit 15 20255 = 109511 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20255 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20255) = 3 ^ 11 * m + 109511 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20255.1, data_15_20255.2]

/-- Complete interval computation for depth 15, residue 20256. -/
theorem bounds_15_20256 : exactInterval 15 20256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20256 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20256) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20256 : oddCount 20256 15 = 6 ∧ acceleratedOrbit 15 20256 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20256 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20256) = 3 ^ 6 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20256.1, data_15_20256.2]

/-- Complete interval computation for depth 15, residue 20257. -/
theorem bounds_15_20257 : exactInterval 15 20257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20257 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20257) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20257 : oddCount 20257 15 = 6 ∧ acceleratedOrbit 15 20257 = 451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20257 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20257) = 3 ^ 6 * m + 451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20257.1, data_15_20257.2]

/-- Complete interval computation for depth 15, residue 20258. -/
theorem bounds_15_20258 : exactInterval 15 20258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20258 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20258) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20258 : oddCount 20258 15 = 6 ∧ acceleratedOrbit 15 20258 = 451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20258 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20258) = 3 ^ 6 * m + 451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20258.1, data_15_20258.2]

/-- Complete interval computation for depth 15, residue 20259. -/
theorem bounds_15_20259 : exactInterval 15 20259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20259 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20259) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20259 : oddCount 20259 15 = 6 ∧ acceleratedOrbit 15 20259 = 451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20259 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20259) = 3 ^ 6 * m + 451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20259.1, data_15_20259.2]

/-- Complete interval computation for depth 15, residue 20260. -/
theorem bounds_15_20260 : exactInterval 15 20260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20260 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20260) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20260 : oddCount 20260 15 = 6 ∧ acceleratedOrbit 15 20260 = 451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20260 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20260) = 3 ^ 6 * m + 451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20260.1, data_15_20260.2]

/-- Complete interval computation for depth 15, residue 20261. -/
theorem bounds_15_20261 : exactInterval 15 20261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20261 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20261) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20261 : oddCount 20261 15 = 6 ∧ acceleratedOrbit 15 20261 = 451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20261 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20261) = 3 ^ 6 * m + 451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20261.1, data_15_20261.2]

/-- Complete interval computation for depth 15, residue 20262. -/
theorem bounds_15_20262 : exactInterval 15 20262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20262 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20262) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20262 : oddCount 20262 15 = 6 ∧ acceleratedOrbit 15 20262 = 451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20262 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20262) = 3 ^ 6 * m + 451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20262.1, data_15_20262.2]

/-- Complete interval computation for depth 15, residue 20263. -/
theorem bounds_15_20263 : exactInterval 15 20263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20263 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20263) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20263 : oddCount 20263 15 = 8 ∧ acceleratedOrbit 15 20263 = 4058 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20263 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20263) = 3 ^ 8 * m + 4058 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20263.1, data_15_20263.2]

/-- Complete interval computation for depth 15, residue 20264. -/
theorem bounds_15_20264 : exactInterval 15 20264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20264 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20264) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20264 : oddCount 20264 15 = 6 ∧ acceleratedOrbit 15 20264 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20264 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20264) = 3 ^ 6 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20264.1, data_15_20264.2]

/-- Complete interval computation for depth 15, residue 20265. -/
theorem bounds_15_20265 : exactInterval 15 20265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20265 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20265) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20265 : oddCount 20265 15 = 9 ∧ acceleratedOrbit 15 20265 = 12176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20265 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20265) = 3 ^ 9 * m + 12176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20265.1, data_15_20265.2]

/-- Complete interval computation for depth 15, residue 20266. -/
theorem bounds_15_20266 : exactInterval 15 20266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20266 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20266) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20266 : oddCount 20266 15 = 6 ∧ acceleratedOrbit 15 20266 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20266 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20266) = 3 ^ 6 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20266.1, data_15_20266.2]

/-- Complete interval computation for depth 15, residue 20267. -/
theorem bounds_15_20267 : exactInterval 15 20267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20267 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20267) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20267 : oddCount 20267 15 = 6 ∧ acceleratedOrbit 15 20267 = 451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20267 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20267) = 3 ^ 6 * m + 451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20267.1, data_15_20267.2]

/-- Complete interval computation for depth 15, residue 20268. -/
theorem bounds_15_20268 : exactInterval 15 20268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20268 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20268) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20268 : oddCount 20268 15 = 6 ∧ acceleratedOrbit 15 20268 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20268 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20268) = 3 ^ 6 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20268.1, data_15_20268.2]

/-- Complete interval computation for depth 15, residue 20269. -/
theorem bounds_15_20269 : exactInterval 15 20269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20269 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20269) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20269 : oddCount 20269 15 = 6 ∧ acceleratedOrbit 15 20269 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20269 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20269) = 3 ^ 6 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20269.1, data_15_20269.2]

/-- Complete interval computation for depth 15, residue 20270. -/
theorem bounds_15_20270 : exactInterval 15 20270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20270 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20270) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20270 : oddCount 20270 15 = 6 ∧ acceleratedOrbit 15 20270 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20270 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20270) = 3 ^ 6 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20270.1, data_15_20270.2]

/-- Complete interval computation for depth 15, residue 20271. -/
theorem bounds_15_20271 : exactInterval 15 20271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20271 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20271) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20271 : oddCount 20271 15 = 6 ∧ acceleratedOrbit 15 20271 = 451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20271 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20271) = 3 ^ 6 * m + 451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20271.1, data_15_20271.2]

/-- Complete interval computation for depth 15, residue 20272. -/
theorem bounds_15_20272 : exactInterval 15 20272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20272 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20272) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20272 : oddCount 20272 15 = 6 ∧ acceleratedOrbit 15 20272 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20272 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20272) = 3 ^ 6 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20272.1, data_15_20272.2]

/-- Complete interval computation for depth 15, residue 20273. -/
theorem bounds_15_20273 : exactInterval 15 20273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20273 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20273) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20273 : oddCount 20273 15 = 6 ∧ acceleratedOrbit 15 20273 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20273 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20273) = 3 ^ 6 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20273.1, data_15_20273.2]

/-- Complete interval computation for depth 15, residue 20274. -/
theorem bounds_15_20274 : exactInterval 15 20274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20274 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20274) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20274 : oddCount 20274 15 = 6 ∧ acceleratedOrbit 15 20274 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20274 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20274) = 3 ^ 6 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20274.1, data_15_20274.2]

/-- Complete interval computation for depth 15, residue 20275. -/
theorem bounds_15_20275 : exactInterval 15 20275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20275 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20275) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20275 : oddCount 20275 15 = 6 ∧ acceleratedOrbit 15 20275 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20275 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20275) = 3 ^ 6 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20275.1, data_15_20275.2]

/-- Complete interval computation for depth 15, residue 20276. -/
theorem bounds_15_20276 : exactInterval 15 20276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20276 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20276) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20276 : oddCount 20276 15 = 6 ∧ acceleratedOrbit 15 20276 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20276 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20276) = 3 ^ 6 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20276.1, data_15_20276.2]

/-- Complete interval computation for depth 15, residue 20277. -/
theorem bounds_15_20277 : exactInterval 15 20277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20277 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20277) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20277 : oddCount 20277 15 = 6 ∧ acceleratedOrbit 15 20277 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20277 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20277) = 3 ^ 6 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20277.1, data_15_20277.2]

/-- Complete interval computation for depth 15, residue 20278. -/
theorem bounds_15_20278 : exactInterval 15 20278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20278 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20278) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20278 : oddCount 20278 15 = 8 ∧ acceleratedOrbit 15 20278 = 4061 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20278 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20278) = 3 ^ 8 * m + 4061 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20278.1, data_15_20278.2]

/-- Complete interval computation for depth 15, residue 20279. -/
theorem bounds_15_20279 : exactInterval 15 20279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20279 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20279) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20279 : oddCount 20279 15 = 8 ∧ acceleratedOrbit 15 20279 = 4061 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20279 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20279) = 3 ^ 8 * m + 4061 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20279.1, data_15_20279.2]

/-- Complete interval computation for depth 15, residue 20280. -/
theorem bounds_15_20280 : exactInterval 15 20280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20280 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20280) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20280 : oddCount 20280 15 = 8 ∧ acceleratedOrbit 15 20280 = 4063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20280 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20280) = 3 ^ 8 * m + 4063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20280.1, data_15_20280.2]

/-- Complete interval computation for depth 15, residue 20281. -/
theorem bounds_15_20281 : exactInterval 15 20281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20281 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20281) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20281 : oddCount 20281 15 = 7 ∧ acceleratedOrbit 15 20281 = 1354 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20281 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20281) = 3 ^ 7 * m + 1354 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20281.1, data_15_20281.2]

/-- Complete interval computation for depth 15, residue 20282. -/
theorem bounds_15_20282 : exactInterval 15 20282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20282 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20282) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20282 : oddCount 20282 15 = 8 ∧ acceleratedOrbit 15 20282 = 4063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20282 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20282) = 3 ^ 8 * m + 4063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20282.1, data_15_20282.2]

end Collatz.Research.PassageAtlas.Batch0619
