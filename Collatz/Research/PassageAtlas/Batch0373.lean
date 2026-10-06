import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0373

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 12189. -/
theorem bounds_15_12189 : exactInterval 15 12189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12189 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12189) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12189 : oddCount 12189 15 = 7 ∧ acceleratedOrbit 15 12189 = 814 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12189 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12189) = 3 ^ 7 * m + 814 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12189.1, data_15_12189.2]

/-- Complete interval computation for depth 15, residue 12190. -/
theorem bounds_15_12190 : exactInterval 15 12190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12190 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12190) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12190 : oddCount 12190 15 = 7 ∧ acceleratedOrbit 15 12190 = 814 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12190 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12190) = 3 ^ 7 * m + 814 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12190.1, data_15_12190.2]

/-- Complete interval computation for depth 15, residue 12191. -/
theorem bounds_15_12191 : exactInterval 15 12191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12191 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12191) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12191 : oddCount 12191 15 = 10 ∧ acceleratedOrbit 15 12191 = 21971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12191 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12191) = 3 ^ 10 * m + 21971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12191.1, data_15_12191.2]

/-- Complete interval computation for depth 15, residue 12192. -/
theorem bounds_15_12192 : exactInterval 15 12192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12192 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12192) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12192 : oddCount 12192 15 = 5 ∧ acceleratedOrbit 15 12192 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12192 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12192) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12192.1, data_15_12192.2]

/-- Complete interval computation for depth 15, residue 12193. -/
theorem bounds_15_12193 : exactInterval 15 12193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12193 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12193) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12193 : oddCount 12193 15 = 8 ∧ acceleratedOrbit 15 12193 = 2443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12193 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12193) = 3 ^ 8 * m + 2443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12193.1, data_15_12193.2]

/-- Complete interval computation for depth 15, residue 12194. -/
theorem bounds_15_12194 : exactInterval 15 12194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12194 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12194) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12194 : oddCount 12194 15 = 6 ∧ acceleratedOrbit 15 12194 = 272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12194 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12194) = 3 ^ 6 * m + 272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12194.1, data_15_12194.2]

/-- Complete interval computation for depth 15, residue 12195. -/
theorem bounds_15_12195 : exactInterval 15 12195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12195 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12195) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12195 : oddCount 12195 15 = 6 ∧ acceleratedOrbit 15 12195 = 272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12195 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12195) = 3 ^ 6 * m + 272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12195.1, data_15_12195.2]

/-- Complete interval computation for depth 15, residue 12196. -/
theorem bounds_15_12196 : exactInterval 15 12196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12196 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12196) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12196 : oddCount 12196 15 = 10 ∧ acceleratedOrbit 15 12196 = 21991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12196 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12196) = 3 ^ 10 * m + 21991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12196.1, data_15_12196.2]

/-- Complete interval computation for depth 15, residue 12197. -/
theorem bounds_15_12197 : exactInterval 15 12197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12197 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12197) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12197 : oddCount 12197 15 = 10 ∧ acceleratedOrbit 15 12197 = 21991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12197 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12197) = 3 ^ 10 * m + 21991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12197.1, data_15_12197.2]

/-- Complete interval computation for depth 15, residue 12198. -/
theorem bounds_15_12198 : exactInterval 15 12198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12198 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12198) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12198 : oddCount 12198 15 = 10 ∧ acceleratedOrbit 15 12198 = 21991 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12198 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12198) = 3 ^ 10 * m + 21991 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12198.1, data_15_12198.2]

/-- Complete interval computation for depth 15, residue 12199. -/
theorem bounds_15_12199 : exactInterval 15 12199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12199 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12199) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12199 : oddCount 12199 15 = 11 ∧ acceleratedOrbit 15 12199 = 65960 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12199 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12199) = 3 ^ 11 * m + 65960 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12199.1, data_15_12199.2]

/-- Complete interval computation for depth 15, residue 12200. -/
theorem bounds_15_12200 : exactInterval 15 12200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12200 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12200) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12200 : oddCount 12200 15 = 5 ∧ acceleratedOrbit 15 12200 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12200 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12200) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12200.1, data_15_12200.2]

/-- Complete interval computation for depth 15, residue 12201. -/
theorem bounds_15_12201 : exactInterval 15 12201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12201 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12201) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12201 : oddCount 12201 15 = 12 ∧ acceleratedOrbit 15 12201 = 197909 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12201 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12201) = 3 ^ 12 * m + 197909 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12201.1, data_15_12201.2]

/-- Complete interval computation for depth 15, residue 12202. -/
theorem bounds_15_12202 : exactInterval 15 12202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12202 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12202) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12202 : oddCount 12202 15 = 5 ∧ acceleratedOrbit 15 12202 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12202 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12202) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12202.1, data_15_12202.2]

/-- Complete interval computation for depth 15, residue 12203. -/
theorem bounds_15_12203 : exactInterval 15 12203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12203 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12203) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12203 : oddCount 12203 15 = 8 ∧ acceleratedOrbit 15 12203 = 2444 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12203 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12203) = 3 ^ 8 * m + 2444 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12203.1, data_15_12203.2]

/-- Complete interval computation for depth 15, residue 12204. -/
theorem bounds_15_12204 : exactInterval 15 12204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12204 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12204) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12204 : oddCount 12204 15 = 7 ∧ acceleratedOrbit 15 12204 = 815 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12204 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12204) = 3 ^ 7 * m + 815 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12204.1, data_15_12204.2]

/-- Complete interval computation for depth 15, residue 12205. -/
theorem bounds_15_12205 : exactInterval 15 12205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12205 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12205) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12205 : oddCount 12205 15 = 7 ∧ acceleratedOrbit 15 12205 = 815 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12205 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12205) = 3 ^ 7 * m + 815 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12205.1, data_15_12205.2]

/-- Complete interval computation for depth 15, residue 12206. -/
theorem bounds_15_12206 : exactInterval 15 12206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12206 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12206) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12206 : oddCount 12206 15 = 7 ∧ acceleratedOrbit 15 12206 = 815 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12206 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12206) = 3 ^ 7 * m + 815 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12206.1, data_15_12206.2]

/-- Complete interval computation for depth 15, residue 12207. -/
theorem bounds_15_12207 : exactInterval 15 12207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12207 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12207) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12207 : oddCount 12207 15 = 7 ∧ acceleratedOrbit 15 12207 = 815 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12207 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12207) = 3 ^ 7 * m + 815 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12207.1, data_15_12207.2]

/-- Complete interval computation for depth 15, residue 12208. -/
theorem bounds_15_12208 : exactInterval 15 12208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12208 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12208) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12208 : oddCount 12208 15 = 8 ∧ acceleratedOrbit 15 12208 = 2450 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12208 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12208) = 3 ^ 8 * m + 2450 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12208.1, data_15_12208.2]

/-- Complete interval computation for depth 15, residue 12209. -/
theorem bounds_15_12209 : exactInterval 15 12209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12209 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12209) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12209 : oddCount 12209 15 = 5 ∧ acceleratedOrbit 15 12209 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12209 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12209) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12209.1, data_15_12209.2]

/-- Complete interval computation for depth 15, residue 12210. -/
theorem bounds_15_12210 : exactInterval 15 12210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12210 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12210) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12210 : oddCount 12210 15 = 5 ∧ acceleratedOrbit 15 12210 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12210 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12210) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12210.1, data_15_12210.2]

/-- Complete interval computation for depth 15, residue 12211. -/
theorem bounds_15_12211 : exactInterval 15 12211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12211 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12211) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12211 : oddCount 12211 15 = 5 ∧ acceleratedOrbit 15 12211 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12211 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12211) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12211.1, data_15_12211.2]

/-- Complete interval computation for depth 15, residue 12212. -/
theorem bounds_15_12212 : exactInterval 15 12212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12212 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12212) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12212 : oddCount 12212 15 = 8 ∧ acceleratedOrbit 15 12212 = 2450 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12212 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12212) = 3 ^ 8 * m + 2450 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12212.1, data_15_12212.2]

/-- Complete interval computation for depth 15, residue 12213. -/
theorem bounds_15_12213 : exactInterval 15 12213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12213 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12213) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12213 : oddCount 12213 15 = 8 ∧ acceleratedOrbit 15 12213 = 2450 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12213 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12213) = 3 ^ 8 * m + 2450 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12213.1, data_15_12213.2]

/-- Complete interval computation for depth 15, residue 12214. -/
theorem bounds_15_12214 : exactInterval 15 12214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12214 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12214) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12214 : oddCount 12214 15 = 8 ∧ acceleratedOrbit 15 12214 = 2447 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12214 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12214) = 3 ^ 8 * m + 2447 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12214.1, data_15_12214.2]

/-- Complete interval computation for depth 15, residue 12215. -/
theorem bounds_15_12215 : exactInterval 15 12215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12215 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12215) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12215 : oddCount 12215 15 = 8 ∧ acceleratedOrbit 15 12215 = 2447 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12215 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12215) = 3 ^ 8 * m + 2447 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12215.1, data_15_12215.2]

/-- Complete interval computation for depth 15, residue 12216. -/
theorem bounds_15_12216 : exactInterval 15 12216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12216 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12216) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12216 : oddCount 12216 15 = 8 ∧ acceleratedOrbit 15 12216 = 2450 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12216 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12216) = 3 ^ 8 * m + 2450 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12216.1, data_15_12216.2]

/-- Complete interval computation for depth 15, residue 12217. -/
theorem bounds_15_12217 : exactInterval 15 12217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12217 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12217) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12217 : oddCount 12217 15 = 6 ∧ acceleratedOrbit 15 12217 = 272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12217 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12217) = 3 ^ 6 * m + 272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12217.1, data_15_12217.2]

/-- Complete interval computation for depth 15, residue 12218. -/
theorem bounds_15_12218 : exactInterval 15 12218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12218 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12218) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12218 : oddCount 12218 15 = 8 ∧ acceleratedOrbit 15 12218 = 2450 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12218 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12218) = 3 ^ 8 * m + 2450 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12218.1, data_15_12218.2]

/-- Complete interval computation for depth 15, residue 12219. -/
theorem bounds_15_12219 : exactInterval 15 12219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12219 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12219) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12219 : oddCount 12219 15 = 6 ∧ acceleratedOrbit 15 12219 = 272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12219 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12219) = 3 ^ 6 * m + 272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12219.1, data_15_12219.2]

/-- Complete interval computation for depth 15, residue 12220. -/
theorem bounds_15_12220 : exactInterval 15 12220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12220 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12220) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12220 : oddCount 12220 15 = 10 ∧ acceleratedOrbit 15 12220 = 22031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12220 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12220) = 3 ^ 10 * m + 22031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12220.1, data_15_12220.2]

/-- Complete interval computation for depth 15, residue 12221. -/
theorem bounds_15_12221 : exactInterval 15 12221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12221 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12221) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12221 : oddCount 12221 15 = 10 ∧ acceleratedOrbit 15 12221 = 22031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12221 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12221) = 3 ^ 10 * m + 22031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12221.1, data_15_12221.2]

end Collatz.Research.PassageAtlas.Batch0373
