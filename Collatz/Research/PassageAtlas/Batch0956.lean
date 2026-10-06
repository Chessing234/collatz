import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0956

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 31293. -/
theorem bounds_15_31293 : exactInterval 15 31293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31293 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31293) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31293 : oddCount 31293 15 = 7 ∧ acceleratedOrbit 15 31293 = 2089 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31293 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31293) = 3 ^ 7 * m + 2089 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31293.1, data_15_31293.2]

/-- Complete interval computation for depth 15, residue 31294. -/
theorem bounds_15_31294 : exactInterval 15 31294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31294 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31294) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31294 : oddCount 31294 15 = 7 ∧ acceleratedOrbit 15 31294 = 2089 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31294 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31294) = 3 ^ 7 * m + 2089 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31294.1, data_15_31294.2]

/-- Complete interval computation for depth 15, residue 31295. -/
theorem bounds_15_31295 : exactInterval 15 31295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31295 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31295) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31295 : oddCount 31295 15 = 7 ∧ acceleratedOrbit 15 31295 = 2089 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31295 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31295) = 3 ^ 7 * m + 2089 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31295.1, data_15_31295.2]

/-- Complete interval computation for depth 15, residue 31296. -/
theorem bounds_15_31296 : exactInterval 15 31296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31296 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31296) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31296 : oddCount 31296 15 = 7 ∧ acceleratedOrbit 15 31296 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31296 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31296) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31296.1, data_15_31296.2]

/-- Complete interval computation for depth 15, residue 31297. -/
theorem bounds_15_31297 : exactInterval 15 31297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31297 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31297) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31297 : oddCount 31297 15 = 6 ∧ acceleratedOrbit 15 31297 = 697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31297 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31297) = 3 ^ 6 * m + 697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31297.1, data_15_31297.2]

/-- Complete interval computation for depth 15, residue 31298. -/
theorem bounds_15_31298 : exactInterval 15 31298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31298 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31298) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31298 : oddCount 31298 15 = 6 ∧ acceleratedOrbit 15 31298 = 697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31298 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31298) = 3 ^ 6 * m + 697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31298.1, data_15_31298.2]

/-- Complete interval computation for depth 15, residue 31299. -/
theorem bounds_15_31299 : exactInterval 15 31299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31299 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31299) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31299 : oddCount 31299 15 = 6 ∧ acceleratedOrbit 15 31299 = 697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31299 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31299) = 3 ^ 6 * m + 697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31299.1, data_15_31299.2]

/-- Complete interval computation for depth 15, residue 31300. -/
theorem bounds_15_31300 : exactInterval 15 31300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31300 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31300) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31300 : oddCount 31300 15 = 6 ∧ acceleratedOrbit 15 31300 = 697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31300 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31300) = 3 ^ 6 * m + 697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31300.1, data_15_31300.2]

/-- Complete interval computation for depth 15, residue 31301. -/
theorem bounds_15_31301 : exactInterval 15 31301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31301 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31301) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31301 : oddCount 31301 15 = 6 ∧ acceleratedOrbit 15 31301 = 697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31301 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31301) = 3 ^ 6 * m + 697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31301.1, data_15_31301.2]

/-- Complete interval computation for depth 15, residue 31302. -/
theorem bounds_15_31302 : exactInterval 15 31302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31302 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31302) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31302 : oddCount 31302 15 = 6 ∧ acceleratedOrbit 15 31302 = 697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31302 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31302) = 3 ^ 6 * m + 697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31302.1, data_15_31302.2]

/-- Complete interval computation for depth 15, residue 31303. -/
theorem bounds_15_31303 : exactInterval 15 31303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31303 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31303) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31303 : oddCount 31303 15 = 9 ∧ acceleratedOrbit 15 31303 = 18805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31303 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31303) = 3 ^ 9 * m + 18805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31303.1, data_15_31303.2]

/-- Complete interval computation for depth 15, residue 31304. -/
theorem bounds_15_31304 : exactInterval 15 31304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31304 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31304) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31304 : oddCount 31304 15 = 6 ∧ acceleratedOrbit 15 31304 = 697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31304 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31304) = 3 ^ 6 * m + 697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31304.1, data_15_31304.2]

/-- Complete interval computation for depth 15, residue 31305. -/
theorem bounds_15_31305 : exactInterval 15 31305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31305 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31305) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31305 : oddCount 31305 15 = 7 ∧ acceleratedOrbit 15 31305 = 2090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31305 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31305) = 3 ^ 7 * m + 2090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31305.1, data_15_31305.2]

/-- Complete interval computation for depth 15, residue 31306. -/
theorem bounds_15_31306 : exactInterval 15 31306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31306 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31306) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31306 : oddCount 31306 15 = 6 ∧ acceleratedOrbit 15 31306 = 697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31306 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31306) = 3 ^ 6 * m + 697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31306.1, data_15_31306.2]

/-- Complete interval computation for depth 15, residue 31307. -/
theorem bounds_15_31307 : exactInterval 15 31307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31307 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31307) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31307 : oddCount 31307 15 = 6 ∧ acceleratedOrbit 15 31307 = 697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31307 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31307) = 3 ^ 6 * m + 697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31307.1, data_15_31307.2]

/-- Complete interval computation for depth 15, residue 31308. -/
theorem bounds_15_31308 : exactInterval 15 31308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31308 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31308) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31308 : oddCount 31308 15 = 6 ∧ acceleratedOrbit 15 31308 = 697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31308 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31308) = 3 ^ 6 * m + 697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31308.1, data_15_31308.2]

/-- Complete interval computation for depth 15, residue 31309. -/
theorem bounds_15_31309 : exactInterval 15 31309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31309 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31309) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31309 : oddCount 31309 15 = 6 ∧ acceleratedOrbit 15 31309 = 697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31309 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31309) = 3 ^ 6 * m + 697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31309.1, data_15_31309.2]

/-- Complete interval computation for depth 15, residue 31310. -/
theorem bounds_15_31310 : exactInterval 15 31310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31310 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31310) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31310 : oddCount 31310 15 = 7 ∧ acceleratedOrbit 15 31310 = 2090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31310 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31310) = 3 ^ 7 * m + 2090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31310.1, data_15_31310.2]

/-- Complete interval computation for depth 15, residue 31311. -/
theorem bounds_15_31311 : exactInterval 15 31311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31311 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31311) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31311 : oddCount 31311 15 = 7 ∧ acceleratedOrbit 15 31311 = 2090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31311 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31311) = 3 ^ 7 * m + 2090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31311.1, data_15_31311.2]

/-- Complete interval computation for depth 15, residue 31312. -/
theorem bounds_15_31312 : exactInterval 15 31312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31312 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31312) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31312 : oddCount 31312 15 = 7 ∧ acceleratedOrbit 15 31312 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31312 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31312) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31312.1, data_15_31312.2]

/-- Complete interval computation for depth 15, residue 31313. -/
theorem bounds_15_31313 : exactInterval 15 31313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31313 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31313) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31313 : oddCount 31313 15 = 9 ∧ acceleratedOrbit 15 31313 = 18812 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31313 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31313) = 3 ^ 9 * m + 18812 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31313.1, data_15_31313.2]

/-- Complete interval computation for depth 15, residue 31314. -/
theorem bounds_15_31314 : exactInterval 15 31314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31314 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31314) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31314 : oddCount 31314 15 = 9 ∧ acceleratedOrbit 15 31314 = 18812 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31314 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31314) = 3 ^ 9 * m + 18812 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31314.1, data_15_31314.2]

/-- Complete interval computation for depth 15, residue 31315. -/
theorem bounds_15_31315 : exactInterval 15 31315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31315 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31315) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31315 : oddCount 31315 15 = 9 ∧ acceleratedOrbit 15 31315 = 18812 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31315 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31315) = 3 ^ 9 * m + 18812 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31315.1, data_15_31315.2]

/-- Complete interval computation for depth 15, residue 31316. -/
theorem bounds_15_31316 : exactInterval 15 31316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31316 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31316) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31316 : oddCount 31316 15 = 7 ∧ acceleratedOrbit 15 31316 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31316 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31316) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31316.1, data_15_31316.2]

/-- Complete interval computation for depth 15, residue 31317. -/
theorem bounds_15_31317 : exactInterval 15 31317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31317 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31317) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31317 : oddCount 31317 15 = 7 ∧ acceleratedOrbit 15 31317 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31317 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31317) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31317.1, data_15_31317.2]

/-- Complete interval computation for depth 15, residue 31318. -/
theorem bounds_15_31318 : exactInterval 15 31318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31318 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31318) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31318 : oddCount 31318 15 = 9 ∧ acceleratedOrbit 15 31318 = 18818 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31318 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31318) = 3 ^ 9 * m + 18818 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31318.1, data_15_31318.2]

/-- Complete interval computation for depth 15, residue 31319. -/
theorem bounds_15_31319 : exactInterval 15 31319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31319 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31319) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31319 : oddCount 31319 15 = 9 ∧ acceleratedOrbit 15 31319 = 18818 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31319 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31319) = 3 ^ 9 * m + 18818 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31319.1, data_15_31319.2]

/-- Complete interval computation for depth 15, residue 31320. -/
theorem bounds_15_31320 : exactInterval 15 31320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31320 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31320) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31320 : oddCount 31320 15 = 5 ∧ acceleratedOrbit 15 31320 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31320 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31320) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31320.1, data_15_31320.2]

/-- Complete interval computation for depth 15, residue 31321. -/
theorem bounds_15_31321 : exactInterval 15 31321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31321 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31321) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31321 : oddCount 31321 15 = 9 ∧ acceleratedOrbit 15 31321 = 18818 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31321 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31321) = 3 ^ 9 * m + 18818 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31321.1, data_15_31321.2]

/-- Complete interval computation for depth 15, residue 31322. -/
theorem bounds_15_31322 : exactInterval 15 31322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31322 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31322) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31322 : oddCount 31322 15 = 5 ∧ acceleratedOrbit 15 31322 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31322 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31322) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31322.1, data_15_31322.2]

/-- Complete interval computation for depth 15, residue 31323. -/
theorem bounds_15_31323 : exactInterval 15 31323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31323 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31323) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31323 : oddCount 31323 15 = 8 ∧ acceleratedOrbit 15 31323 = 6272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31323 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31323) = 3 ^ 8 * m + 6272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31323.1, data_15_31323.2]

/-- Complete interval computation for depth 15, residue 31324. -/
theorem bounds_15_31324 : exactInterval 15 31324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31324 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31324) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31324 : oddCount 31324 15 = 5 ∧ acceleratedOrbit 15 31324 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31324 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31324) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31324.1, data_15_31324.2]

/-- Complete interval computation for depth 15, residue 31325. -/
theorem bounds_15_31325 : exactInterval 15 31325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31325 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31325) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31325 : oddCount 31325 15 = 5 ∧ acceleratedOrbit 15 31325 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31325 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31325) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31325.1, data_15_31325.2]

end Collatz.Research.PassageAtlas.Batch0956
