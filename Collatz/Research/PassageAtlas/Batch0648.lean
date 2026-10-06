import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0648

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 21200. -/
theorem bounds_15_21200 : exactInterval 15 21200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21200 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21200) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21200 : oddCount 21200 15 = 4 ∧ acceleratedOrbit 15 21200 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21200 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21200) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21200.1, data_15_21200.2]

/-- Complete interval computation for depth 15, residue 21201. -/
theorem bounds_15_21201 : exactInterval 15 21201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21201 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21201) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21201 : oddCount 21201 15 = 6 ∧ acceleratedOrbit 15 21201 = 472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21201 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21201) = 3 ^ 6 * m + 472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21201.1, data_15_21201.2]

/-- Complete interval computation for depth 15, residue 21202. -/
theorem bounds_15_21202 : exactInterval 15 21202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21202 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21202) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21202 : oddCount 21202 15 = 6 ∧ acceleratedOrbit 15 21202 = 472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21202 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21202) = 3 ^ 6 * m + 472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21202.1, data_15_21202.2]

/-- Complete interval computation for depth 15, residue 21203. -/
theorem bounds_15_21203 : exactInterval 15 21203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21203 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21203) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21203 : oddCount 21203 15 = 6 ∧ acceleratedOrbit 15 21203 = 472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21203 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21203) = 3 ^ 6 * m + 472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21203.1, data_15_21203.2]

/-- Complete interval computation for depth 15, residue 21204. -/
theorem bounds_15_21204 : exactInterval 15 21204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21204 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21204) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21204 : oddCount 21204 15 = 4 ∧ acceleratedOrbit 15 21204 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21204 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21204) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21204.1, data_15_21204.2]

/-- Complete interval computation for depth 15, residue 21205. -/
theorem bounds_15_21205 : exactInterval 15 21205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21205 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21205) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21205 : oddCount 21205 15 = 4 ∧ acceleratedOrbit 15 21205 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21205 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21205) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21205.1, data_15_21205.2]

/-- Complete interval computation for depth 15, residue 21206. -/
theorem bounds_15_21206 : exactInterval 15 21206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21206 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21206) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21206 : oddCount 21206 15 = 9 ∧ acceleratedOrbit 15 21206 = 12743 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21206 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21206) = 3 ^ 9 * m + 12743 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21206.1, data_15_21206.2]

/-- Complete interval computation for depth 15, residue 21207. -/
theorem bounds_15_21207 : exactInterval 15 21207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21207 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21207) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21207 : oddCount 21207 15 = 9 ∧ acceleratedOrbit 15 21207 = 12743 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21207 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21207) = 3 ^ 9 * m + 12743 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21207.1, data_15_21207.2]

/-- Complete interval computation for depth 15, residue 21208. -/
theorem bounds_15_21208 : exactInterval 15 21208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21208 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21208) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21208 : oddCount 21208 15 = 8 ∧ acceleratedOrbit 15 21208 = 4249 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21208 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21208) = 3 ^ 8 * m + 4249 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21208.1, data_15_21208.2]

/-- Complete interval computation for depth 15, residue 21209. -/
theorem bounds_15_21209 : exactInterval 15 21209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21209 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21209) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21209 : oddCount 21209 15 = 7 ∧ acceleratedOrbit 15 21209 = 1417 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21209 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21209) = 3 ^ 7 * m + 1417 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21209.1, data_15_21209.2]

/-- Complete interval computation for depth 15, residue 21210. -/
theorem bounds_15_21210 : exactInterval 15 21210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21210 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21210) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21210 : oddCount 21210 15 = 8 ∧ acceleratedOrbit 15 21210 = 4249 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21210 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21210) = 3 ^ 8 * m + 4249 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21210.1, data_15_21210.2]

/-- Complete interval computation for depth 15, residue 21211. -/
theorem bounds_15_21211 : exactInterval 15 21211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21211 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21211) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21211 : oddCount 21211 15 = 10 ∧ acceleratedOrbit 15 21211 = 38227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21211 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21211) = 3 ^ 10 * m + 38227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21211.1, data_15_21211.2]

/-- Complete interval computation for depth 15, residue 21212. -/
theorem bounds_15_21212 : exactInterval 15 21212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21212 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21212) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21212 : oddCount 21212 15 = 8 ∧ acceleratedOrbit 15 21212 = 4249 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21212 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21212) = 3 ^ 8 * m + 4249 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21212.1, data_15_21212.2]

/-- Complete interval computation for depth 15, residue 21213. -/
theorem bounds_15_21213 : exactInterval 15 21213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21213 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21213) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21213 : oddCount 21213 15 = 8 ∧ acceleratedOrbit 15 21213 = 4249 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21213 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21213) = 3 ^ 8 * m + 4249 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21213.1, data_15_21213.2]

/-- Complete interval computation for depth 15, residue 21214. -/
theorem bounds_15_21214 : exactInterval 15 21214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21214 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21214) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21214 : oddCount 21214 15 = 6 ∧ acceleratedOrbit 15 21214 = 472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21214 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21214) = 3 ^ 6 * m + 472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21214.1, data_15_21214.2]

/-- Complete interval computation for depth 15, residue 21215. -/
theorem bounds_15_21215 : exactInterval 15 21215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21215 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21215) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21215 : oddCount 21215 15 = 6 ∧ acceleratedOrbit 15 21215 = 472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21215 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21215) = 3 ^ 6 * m + 472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21215.1, data_15_21215.2]

/-- Complete interval computation for depth 15, residue 21216. -/
theorem bounds_15_21216 : exactInterval 15 21216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21216 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21216) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21216 : oddCount 21216 15 = 4 ∧ acceleratedOrbit 15 21216 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21216 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21216) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21216.1, data_15_21216.2]

/-- Complete interval computation for depth 15, residue 21217. -/
theorem bounds_15_21217 : exactInterval 15 21217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21217 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21217) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21217 : oddCount 21217 15 = 11 ∧ acceleratedOrbit 15 21217 = 114716 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21217 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21217) = 3 ^ 11 * m + 114716 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21217.1, data_15_21217.2]

/-- Complete interval computation for depth 15, residue 21218. -/
theorem bounds_15_21218 : exactInterval 15 21218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21218 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21218) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21218 : oddCount 21218 15 = 4 ∧ acceleratedOrbit 15 21218 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21218 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21218) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21218.1, data_15_21218.2]

/-- Complete interval computation for depth 15, residue 21219. -/
theorem bounds_15_21219 : exactInterval 15 21219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21219 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21219) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21219 : oddCount 21219 15 = 4 ∧ acceleratedOrbit 15 21219 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21219 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21219) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21219.1, data_15_21219.2]

/-- Complete interval computation for depth 15, residue 21220. -/
theorem bounds_15_21220 : exactInterval 15 21220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21220 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21220) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21220 : oddCount 21220 15 = 8 ∧ acceleratedOrbit 15 21220 = 4252 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21220 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21220) = 3 ^ 8 * m + 4252 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21220.1, data_15_21220.2]

/-- Complete interval computation for depth 15, residue 21221. -/
theorem bounds_15_21221 : exactInterval 15 21221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21221 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21221) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21221 : oddCount 21221 15 = 8 ∧ acceleratedOrbit 15 21221 = 4252 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21221 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21221) = 3 ^ 8 * m + 4252 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21221.1, data_15_21221.2]

/-- Complete interval computation for depth 15, residue 21222. -/
theorem bounds_15_21222 : exactInterval 15 21222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21222 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21222) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21222 : oddCount 21222 15 = 8 ∧ acceleratedOrbit 15 21222 = 4252 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21222 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21222) = 3 ^ 8 * m + 4252 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21222.1, data_15_21222.2]

/-- Complete interval computation for depth 15, residue 21223. -/
theorem bounds_15_21223 : exactInterval 15 21223 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21223 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21223) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21223 : oddCount 21223 15 = 9 ∧ acceleratedOrbit 15 21223 = 12749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21223 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21223) = 3 ^ 9 * m + 12749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21223.1, data_15_21223.2]

/-- Complete interval computation for depth 15, residue 21224. -/
theorem bounds_15_21224 : exactInterval 15 21224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21224 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21224) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21224 : oddCount 21224 15 = 4 ∧ acceleratedOrbit 15 21224 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21224 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21224) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21224.1, data_15_21224.2]

/-- Complete interval computation for depth 15, residue 21225. -/
theorem bounds_15_21225 : exactInterval 15 21225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21225 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21225) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21225 : oddCount 21225 15 = 10 ∧ acceleratedOrbit 15 21225 = 38252 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21225 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21225) = 3 ^ 10 * m + 38252 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21225.1, data_15_21225.2]

/-- Complete interval computation for depth 15, residue 21226. -/
theorem bounds_15_21226 : exactInterval 15 21226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21226 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21226) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21226 : oddCount 21226 15 = 4 ∧ acceleratedOrbit 15 21226 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21226 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21226) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21226.1, data_15_21226.2]

/-- Complete interval computation for depth 15, residue 21227. -/
theorem bounds_15_21227 : exactInterval 15 21227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21227 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21227) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21227 : oddCount 21227 15 = 10 ∧ acceleratedOrbit 15 21227 = 38258 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21227 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21227) = 3 ^ 10 * m + 38258 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21227.1, data_15_21227.2]

/-- Complete interval computation for depth 15, residue 21228. -/
theorem bounds_15_21228 : exactInterval 15 21228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21228 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21228) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21228 : oddCount 21228 15 = 9 ∧ acceleratedOrbit 15 21228 = 12757 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21228 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21228) = 3 ^ 9 * m + 12757 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21228.1, data_15_21228.2]

/-- Complete interval computation for depth 15, residue 21229. -/
theorem bounds_15_21229 : exactInterval 15 21229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21229 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21229) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21229 : oddCount 21229 15 = 9 ∧ acceleratedOrbit 15 21229 = 12757 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21229 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21229) = 3 ^ 9 * m + 12757 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21229.1, data_15_21229.2]

/-- Complete interval computation for depth 15, residue 21230. -/
theorem bounds_15_21230 : exactInterval 15 21230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21230 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21230) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21230 : oddCount 21230 15 = 9 ∧ acceleratedOrbit 15 21230 = 12757 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21230 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21230) = 3 ^ 9 * m + 12757 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21230.1, data_15_21230.2]

/-- Complete interval computation for depth 15, residue 21231. -/
theorem bounds_15_21231 : exactInterval 15 21231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21231 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21231) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21231 : oddCount 21231 15 = 12 ∧ acceleratedOrbit 15 21231 = 344351 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21231 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21231) = 3 ^ 12 * m + 344351 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21231.1, data_15_21231.2]

/-- Complete interval computation for depth 15, residue 21232. -/
theorem bounds_15_21232 : exactInterval 15 21232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21232 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21232) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21232 : oddCount 21232 15 = 8 ∧ acceleratedOrbit 15 21232 = 4256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21232 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21232) = 3 ^ 8 * m + 4256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21232.1, data_15_21232.2]

end Collatz.Research.PassageAtlas.Batch0648
