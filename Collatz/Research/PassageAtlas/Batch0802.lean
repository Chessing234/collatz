import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0802

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 26247. -/
theorem bounds_15_26247 : exactInterval 15 26247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26247 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26247) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26247 : oddCount 26247 15 = 6 ∧ acceleratedOrbit 15 26247 = 584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26247 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26247) = 3 ^ 6 * m + 584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26247.1, data_15_26247.2]

/-- Complete interval computation for depth 15, residue 26248. -/
theorem bounds_15_26248 : exactInterval 15 26248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26248 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26248) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26248 : oddCount 26248 15 = 8 ∧ acceleratedOrbit 15 26248 = 5264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26248 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26248) = 3 ^ 8 * m + 5264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26248.1, data_15_26248.2]

/-- Complete interval computation for depth 15, residue 26249. -/
theorem bounds_15_26249 : exactInterval 15 26249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26249 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26249) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26249 : oddCount 26249 15 = 10 ∧ acceleratedOrbit 15 26249 = 47306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26249 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26249) = 3 ^ 10 * m + 47306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26249.1, data_15_26249.2]

/-- Complete interval computation for depth 15, residue 26250. -/
theorem bounds_15_26250 : exactInterval 15 26250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26250 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26250) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26250 : oddCount 26250 15 = 8 ∧ acceleratedOrbit 15 26250 = 5264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26250 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26250) = 3 ^ 8 * m + 5264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26250.1, data_15_26250.2]

/-- Complete interval computation for depth 15, residue 26251. -/
theorem bounds_15_26251 : exactInterval 15 26251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26251 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26251) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26251 : oddCount 26251 15 = 8 ∧ acceleratedOrbit 15 26251 = 5258 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26251 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26251) = 3 ^ 8 * m + 5258 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26251.1, data_15_26251.2]

/-- Complete interval computation for depth 15, residue 26252. -/
theorem bounds_15_26252 : exactInterval 15 26252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26252 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26252) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26252 : oddCount 26252 15 = 8 ∧ acceleratedOrbit 15 26252 = 5264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26252 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26252) = 3 ^ 8 * m + 5264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26252.1, data_15_26252.2]

/-- Complete interval computation for depth 15, residue 26253. -/
theorem bounds_15_26253 : exactInterval 15 26253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26253 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26253) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26253 : oddCount 26253 15 = 8 ∧ acceleratedOrbit 15 26253 = 5264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26253 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26253) = 3 ^ 8 * m + 5264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26253.1, data_15_26253.2]

/-- Complete interval computation for depth 15, residue 26254. -/
theorem bounds_15_26254 : exactInterval 15 26254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26254 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26254) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26254 : oddCount 26254 15 = 10 ∧ acceleratedOrbit 15 26254 = 47317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26254 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26254) = 3 ^ 10 * m + 47317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26254.1, data_15_26254.2]

/-- Complete interval computation for depth 15, residue 26255. -/
theorem bounds_15_26255 : exactInterval 15 26255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26255 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26255) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26255 : oddCount 26255 15 = 10 ∧ acceleratedOrbit 15 26255 = 47317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26255 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26255) = 3 ^ 10 * m + 47317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26255.1, data_15_26255.2]

/-- Complete interval computation for depth 15, residue 26256. -/
theorem bounds_15_26256 : exactInterval 15 26256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26256 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26256) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26256 : oddCount 26256 15 = 8 ∧ acceleratedOrbit 15 26256 = 5264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26256 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26256) = 3 ^ 8 * m + 5264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26256.1, data_15_26256.2]

/-- Complete interval computation for depth 15, residue 26257. -/
theorem bounds_15_26257 : exactInterval 15 26257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26257 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26257) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26257 : oddCount 26257 15 = 7 ∧ acceleratedOrbit 15 26257 = 1754 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26257 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26257) = 3 ^ 7 * m + 1754 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26257.1, data_15_26257.2]

/-- Complete interval computation for depth 15, residue 26258. -/
theorem bounds_15_26258 : exactInterval 15 26258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26258 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26258) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26258 : oddCount 26258 15 = 7 ∧ acceleratedOrbit 15 26258 = 1754 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26258 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26258) = 3 ^ 7 * m + 1754 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26258.1, data_15_26258.2]

/-- Complete interval computation for depth 15, residue 26259. -/
theorem bounds_15_26259 : exactInterval 15 26259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26259 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26259) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26259 : oddCount 26259 15 = 7 ∧ acceleratedOrbit 15 26259 = 1754 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26259 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26259) = 3 ^ 7 * m + 1754 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26259.1, data_15_26259.2]

/-- Complete interval computation for depth 15, residue 26260. -/
theorem bounds_15_26260 : exactInterval 15 26260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26260 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26260) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26260 : oddCount 26260 15 = 8 ∧ acceleratedOrbit 15 26260 = 5264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26260 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26260) = 3 ^ 8 * m + 5264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26260.1, data_15_26260.2]

/-- Complete interval computation for depth 15, residue 26261. -/
theorem bounds_15_26261 : exactInterval 15 26261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26261 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26261) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26261 : oddCount 26261 15 = 8 ∧ acceleratedOrbit 15 26261 = 5264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26261 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26261) = 3 ^ 8 * m + 5264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26261.1, data_15_26261.2]

/-- Complete interval computation for depth 15, residue 26262. -/
theorem bounds_15_26262 : exactInterval 15 26262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26262 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26262) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26262 : oddCount 26262 15 = 8 ∧ acceleratedOrbit 15 26262 = 5264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26262 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26262) = 3 ^ 8 * m + 5264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26262.1, data_15_26262.2]

/-- Complete interval computation for depth 15, residue 26263. -/
theorem bounds_15_26263 : exactInterval 15 26263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26263 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26263) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26263 : oddCount 26263 15 = 8 ∧ acceleratedOrbit 15 26263 = 5264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26263 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26263) = 3 ^ 8 * m + 5264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26263.1, data_15_26263.2]

/-- Complete interval computation for depth 15, residue 26264. -/
theorem bounds_15_26264 : exactInterval 15 26264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26264 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26264) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26264 : oddCount 26264 15 = 8 ∧ acceleratedOrbit 15 26264 = 5264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26264 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26264) = 3 ^ 8 * m + 5264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26264.1, data_15_26264.2]

/-- Complete interval computation for depth 15, residue 26265. -/
theorem bounds_15_26265 : exactInterval 15 26265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26265 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26265) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26265 : oddCount 26265 15 = 8 ∧ acceleratedOrbit 15 26265 = 5260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26265 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26265) = 3 ^ 8 * m + 5260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26265.1, data_15_26265.2]

/-- Complete interval computation for depth 15, residue 26266. -/
theorem bounds_15_26266 : exactInterval 15 26266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26266 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26266) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26266 : oddCount 26266 15 = 8 ∧ acceleratedOrbit 15 26266 = 5264 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26266 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26266) = 3 ^ 8 * m + 5264 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26266.1, data_15_26266.2]

/-- Complete interval computation for depth 15, residue 26267. -/
theorem bounds_15_26267 : exactInterval 15 26267 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26267 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26267) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26267 : oddCount 26267 15 = 9 ∧ acceleratedOrbit 15 26267 = 15779 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26267 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26267) = 3 ^ 9 * m + 15779 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26267.1, data_15_26267.2]

/-- Complete interval computation for depth 15, residue 26268. -/
theorem bounds_15_26268 : exactInterval 15 26268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26268 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26268) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26268 : oddCount 26268 15 = 7 ∧ acceleratedOrbit 15 26268 = 1754 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26268 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26268) = 3 ^ 7 * m + 1754 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26268.1, data_15_26268.2]

/-- Complete interval computation for depth 15, residue 26269. -/
theorem bounds_15_26269 : exactInterval 15 26269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26269 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26269) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26269 : oddCount 26269 15 = 7 ∧ acceleratedOrbit 15 26269 = 1754 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26269 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26269) = 3 ^ 7 * m + 1754 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26269.1, data_15_26269.2]

/-- Complete interval computation for depth 15, residue 26270. -/
theorem bounds_15_26270 : exactInterval 15 26270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26270 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26270) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26270 : oddCount 26270 15 = 7 ∧ acceleratedOrbit 15 26270 = 1754 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26270 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26270) = 3 ^ 7 * m + 1754 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26270.1, data_15_26270.2]

/-- Complete interval computation for depth 15, residue 26271. -/
theorem bounds_15_26271 : exactInterval 15 26271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26271 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26271) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26271 : oddCount 26271 15 = 11 ∧ acceleratedOrbit 15 26271 = 142030 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26271 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26271) = 3 ^ 11 * m + 142030 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26271.1, data_15_26271.2]

/-- Complete interval computation for depth 15, residue 26272. -/
theorem bounds_15_26272 : exactInterval 15 26272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26272 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26272) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26272 : oddCount 26272 15 = 3 ∧ acceleratedOrbit 15 26272 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26272 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26272) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26272.1, data_15_26272.2]

/-- Complete interval computation for depth 15, residue 26273. -/
theorem bounds_15_26273 : exactInterval 15 26273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26273 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26273) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26273 : oddCount 26273 15 = 9 ∧ acceleratedOrbit 15 26273 = 15785 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26273 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26273) = 3 ^ 9 * m + 15785 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26273.1, data_15_26273.2]

/-- Complete interval computation for depth 15, residue 26274. -/
theorem bounds_15_26274 : exactInterval 15 26274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26274 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26274) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26274 : oddCount 26274 15 = 9 ∧ acceleratedOrbit 15 26274 = 15788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26274 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26274) = 3 ^ 9 * m + 15788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26274.1, data_15_26274.2]

/-- Complete interval computation for depth 15, residue 26275. -/
theorem bounds_15_26275 : exactInterval 15 26275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26275 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26275) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26275 : oddCount 26275 15 = 9 ∧ acceleratedOrbit 15 26275 = 15788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26275 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26275) = 3 ^ 9 * m + 15788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26275.1, data_15_26275.2]

/-- Complete interval computation for depth 15, residue 26276. -/
theorem bounds_15_26276 : exactInterval 15 26276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26276 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26276) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26276 : oddCount 26276 15 = 9 ∧ acceleratedOrbit 15 26276 = 15788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26276 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26276) = 3 ^ 9 * m + 15788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26276.1, data_15_26276.2]

/-- Complete interval computation for depth 15, residue 26277. -/
theorem bounds_15_26277 : exactInterval 15 26277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26277 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26277) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26277 : oddCount 26277 15 = 9 ∧ acceleratedOrbit 15 26277 = 15788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26277 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26277) = 3 ^ 9 * m + 15788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26277.1, data_15_26277.2]

/-- Complete interval computation for depth 15, residue 26278. -/
theorem bounds_15_26278 : exactInterval 15 26278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26278 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26278) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26278 : oddCount 26278 15 = 9 ∧ acceleratedOrbit 15 26278 = 15788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26278 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26278) = 3 ^ 9 * m + 15788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26278.1, data_15_26278.2]

end Collatz.Research.PassageAtlas.Batch0802
