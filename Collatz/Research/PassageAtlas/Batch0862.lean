import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0862

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 28213. -/
theorem bounds_15_28213 : exactInterval 15 28213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28213 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28213) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28213 : oddCount 28213 15 = 4 ∧ acceleratedOrbit 15 28213 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28213 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28213) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28213.1, data_15_28213.2]

/-- Complete interval computation for depth 15, residue 28214. -/
theorem bounds_15_28214 : exactInterval 15 28214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28214 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28214) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28214 : oddCount 28214 15 = 11 ∧ acceleratedOrbit 15 28214 = 152543 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28214 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28214) = 3 ^ 11 * m + 152543 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28214.1, data_15_28214.2]

/-- Complete interval computation for depth 15, residue 28215. -/
theorem bounds_15_28215 : exactInterval 15 28215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28215 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28215) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28215 : oddCount 28215 15 = 11 ∧ acceleratedOrbit 15 28215 = 152543 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28215 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28215) = 3 ^ 11 * m + 152543 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28215.1, data_15_28215.2]

/-- Complete interval computation for depth 15, residue 28216. -/
theorem bounds_15_28216 : exactInterval 15 28216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28216 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28216) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28216 : oddCount 28216 15 = 6 ∧ acceleratedOrbit 15 28216 = 628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28216 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28216) = 3 ^ 6 * m + 628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28216.1, data_15_28216.2]

/-- Complete interval computation for depth 15, residue 28217. -/
theorem bounds_15_28217 : exactInterval 15 28217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28217 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28217) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28217 : oddCount 28217 15 = 8 ∧ acceleratedOrbit 15 28217 = 5651 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28217 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28217) = 3 ^ 8 * m + 5651 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28217.1, data_15_28217.2]

/-- Complete interval computation for depth 15, residue 28218. -/
theorem bounds_15_28218 : exactInterval 15 28218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28218 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28218) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28218 : oddCount 28218 15 = 6 ∧ acceleratedOrbit 15 28218 = 628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28218 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28218) = 3 ^ 6 * m + 628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28218.1, data_15_28218.2]

/-- Complete interval computation for depth 15, residue 28219. -/
theorem bounds_15_28219 : exactInterval 15 28219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28219 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28219) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28219 : oddCount 28219 15 = 9 ∧ acceleratedOrbit 15 28219 = 16955 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28219 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28219) = 3 ^ 9 * m + 16955 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28219.1, data_15_28219.2]

/-- Complete interval computation for depth 15, residue 28220. -/
theorem bounds_15_28220 : exactInterval 15 28220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28220 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28220) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28220 : oddCount 28220 15 = 6 ∧ acceleratedOrbit 15 28220 = 628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28220 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28220) = 3 ^ 6 * m + 628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28220.1, data_15_28220.2]

/-- Complete interval computation for depth 15, residue 28221. -/
theorem bounds_15_28221 : exactInterval 15 28221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28221 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28221) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28221 : oddCount 28221 15 = 6 ∧ acceleratedOrbit 15 28221 = 628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28221 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28221) = 3 ^ 6 * m + 628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28221.1, data_15_28221.2]

/-- Complete interval computation for depth 15, residue 28222. -/
theorem bounds_15_28222 : exactInterval 15 28222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28222 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28222) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28222 : oddCount 28222 15 = 9 ∧ acceleratedOrbit 15 28222 = 16955 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28222 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28222) = 3 ^ 9 * m + 16955 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28222.1, data_15_28222.2]

/-- Complete interval computation for depth 15, residue 28223. -/
theorem bounds_15_28223 : exactInterval 15 28223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28223 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28223) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28223 : oddCount 28223 15 = 9 ∧ acceleratedOrbit 15 28223 = 16955 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28223 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28223) = 3 ^ 9 * m + 16955 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28223.1, data_15_28223.2]

/-- Complete interval computation for depth 15, residue 28224. -/
theorem bounds_15_28224 : exactInterval 15 28224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28224 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28224) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28224 : oddCount 28224 15 = 4 ∧ acceleratedOrbit 15 28224 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28224 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28224) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28224.1, data_15_28224.2]

/-- Complete interval computation for depth 15, residue 28225. -/
theorem bounds_15_28225 : exactInterval 15 28225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28225 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28225) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28225 : oddCount 28225 15 = 7 ∧ acceleratedOrbit 15 28225 = 1885 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28225 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28225) = 3 ^ 7 * m + 1885 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28225.1, data_15_28225.2]

/-- Complete interval computation for depth 15, residue 28226. -/
theorem bounds_15_28226 : exactInterval 15 28226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28226 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28226) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28226 : oddCount 28226 15 = 7 ∧ acceleratedOrbit 15 28226 = 1885 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28226 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28226) = 3 ^ 7 * m + 1885 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28226.1, data_15_28226.2]

/-- Complete interval computation for depth 15, residue 28227. -/
theorem bounds_15_28227 : exactInterval 15 28227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28227 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28227) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28227 : oddCount 28227 15 = 7 ∧ acceleratedOrbit 15 28227 = 1885 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28227 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28227) = 3 ^ 7 * m + 1885 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28227.1, data_15_28227.2]

/-- Complete interval computation for depth 15, residue 28228. -/
theorem bounds_15_28228 : exactInterval 15 28228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28228 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28228) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28228 : oddCount 28228 15 = 6 ∧ acceleratedOrbit 15 28228 = 629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28228 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28228) = 3 ^ 6 * m + 629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28228.1, data_15_28228.2]

/-- Complete interval computation for depth 15, residue 28229. -/
theorem bounds_15_28229 : exactInterval 15 28229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28229 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28229) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28229 : oddCount 28229 15 = 6 ∧ acceleratedOrbit 15 28229 = 629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28229 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28229) = 3 ^ 6 * m + 629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28229.1, data_15_28229.2]

/-- Complete interval computation for depth 15, residue 28230. -/
theorem bounds_15_28230 : exactInterval 15 28230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28230 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28230) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28230 : oddCount 28230 15 = 6 ∧ acceleratedOrbit 15 28230 = 629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28230 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28230) = 3 ^ 6 * m + 629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28230.1, data_15_28230.2]

/-- Complete interval computation for depth 15, residue 28231. -/
theorem bounds_15_28231 : exactInterval 15 28231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28231 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28231) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28231 : oddCount 28231 15 = 8 ∧ acceleratedOrbit 15 28231 = 5653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28231 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28231) = 3 ^ 8 * m + 5653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28231.1, data_15_28231.2]

/-- Complete interval computation for depth 15, residue 28232. -/
theorem bounds_15_28232 : exactInterval 15 28232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28232 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28232) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28232 : oddCount 28232 15 = 6 ∧ acceleratedOrbit 15 28232 = 629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28232 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28232) = 3 ^ 6 * m + 629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28232.1, data_15_28232.2]

/-- Complete interval computation for depth 15, residue 28233. -/
theorem bounds_15_28233 : exactInterval 15 28233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28233 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28233) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28233 : oddCount 28233 15 = 8 ∧ acceleratedOrbit 15 28233 = 5654 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28233 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28233) = 3 ^ 8 * m + 5654 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28233.1, data_15_28233.2]

/-- Complete interval computation for depth 15, residue 28234. -/
theorem bounds_15_28234 : exactInterval 15 28234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28234 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28234) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28234 : oddCount 28234 15 = 6 ∧ acceleratedOrbit 15 28234 = 629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28234 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28234) = 3 ^ 6 * m + 629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28234.1, data_15_28234.2]

/-- Complete interval computation for depth 15, residue 28235. -/
theorem bounds_15_28235 : exactInterval 15 28235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28235 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28235) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28235 : oddCount 28235 15 = 6 ∧ acceleratedOrbit 15 28235 = 629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28235 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28235) = 3 ^ 6 * m + 629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28235.1, data_15_28235.2]

/-- Complete interval computation for depth 15, residue 28236. -/
theorem bounds_15_28236 : exactInterval 15 28236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28236 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28236) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28236 : oddCount 28236 15 = 6 ∧ acceleratedOrbit 15 28236 = 629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28236 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28236) = 3 ^ 6 * m + 629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28236.1, data_15_28236.2]

/-- Complete interval computation for depth 15, residue 28237. -/
theorem bounds_15_28237 : exactInterval 15 28237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28237 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28237) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28237 : oddCount 28237 15 = 6 ∧ acceleratedOrbit 15 28237 = 629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28237 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28237) = 3 ^ 6 * m + 629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28237.1, data_15_28237.2]

/-- Complete interval computation for depth 15, residue 28238. -/
theorem bounds_15_28238 : exactInterval 15 28238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28238 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28238) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28238 : oddCount 28238 15 = 10 ∧ acceleratedOrbit 15 28238 = 50894 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28238 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28238) = 3 ^ 10 * m + 50894 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28238.1, data_15_28238.2]

/-- Complete interval computation for depth 15, residue 28239. -/
theorem bounds_15_28239 : exactInterval 15 28239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28239 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28239) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28239 : oddCount 28239 15 = 10 ∧ acceleratedOrbit 15 28239 = 50894 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28239 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28239) = 3 ^ 10 * m + 50894 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28239.1, data_15_28239.2]

/-- Complete interval computation for depth 15, residue 28240. -/
theorem bounds_15_28240 : exactInterval 15 28240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28240 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28240) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28240 : oddCount 28240 15 = 4 ∧ acceleratedOrbit 15 28240 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28240 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28240) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28240.1, data_15_28240.2]

/-- Complete interval computation for depth 15, residue 28241. -/
theorem bounds_15_28241 : exactInterval 15 28241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28241 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28241) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28241 : oddCount 28241 15 = 8 ∧ acceleratedOrbit 15 28241 = 5656 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28241 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28241) = 3 ^ 8 * m + 5656 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28241.1, data_15_28241.2]

/-- Complete interval computation for depth 15, residue 28242. -/
theorem bounds_15_28242 : exactInterval 15 28242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28242 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28242) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28242 : oddCount 28242 15 = 8 ∧ acceleratedOrbit 15 28242 = 5656 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28242 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28242) = 3 ^ 8 * m + 5656 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28242.1, data_15_28242.2]

/-- Complete interval computation for depth 15, residue 28243. -/
theorem bounds_15_28243 : exactInterval 15 28243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28243 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28243) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28243 : oddCount 28243 15 = 8 ∧ acceleratedOrbit 15 28243 = 5656 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28243 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28243) = 3 ^ 8 * m + 5656 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28243.1, data_15_28243.2]

/-- Complete interval computation for depth 15, residue 28244. -/
theorem bounds_15_28244 : exactInterval 15 28244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28244 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28244) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28244 : oddCount 28244 15 = 4 ∧ acceleratedOrbit 15 28244 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28244 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28244) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28244.1, data_15_28244.2]

/-- Complete interval computation for depth 15, residue 28245. -/
theorem bounds_15_28245 : exactInterval 15 28245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28245 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28245) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28245 : oddCount 28245 15 = 4 ∧ acceleratedOrbit 15 28245 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28245 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28245) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28245.1, data_15_28245.2]

end Collatz.Research.PassageAtlas.Batch0862
