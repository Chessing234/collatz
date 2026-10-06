import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0831

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 27197. -/
theorem bounds_15_27197 : exactInterval 15 27197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27197 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27197) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27197 : oddCount 27197 15 = 8 ∧ acceleratedOrbit 15 27197 = 5447 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27197 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27197) = 3 ^ 8 * m + 5447 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27197.1, data_15_27197.2]

/-- Complete interval computation for depth 15, residue 27198. -/
theorem bounds_15_27198 : exactInterval 15 27198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27198 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27198) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27198 : oddCount 27198 15 = 8 ∧ acceleratedOrbit 15 27198 = 5447 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27198 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27198) = 3 ^ 8 * m + 5447 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27198.1, data_15_27198.2]

/-- Complete interval computation for depth 15, residue 27199. -/
theorem bounds_15_27199 : exactInterval 15 27199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27199 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27199) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27199 : oddCount 27199 15 = 8 ∧ acceleratedOrbit 15 27199 = 5447 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27199 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27199) = 3 ^ 8 * m + 5447 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27199.1, data_15_27199.2]

/-- Complete interval computation for depth 15, residue 27200. -/
theorem bounds_15_27200 : exactInterval 15 27200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27200 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27200) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27200 : oddCount 27200 15 = 7 ∧ acceleratedOrbit 15 27200 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27200 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27200) = 3 ^ 7 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27200.1, data_15_27200.2]

/-- Complete interval computation for depth 15, residue 27201. -/
theorem bounds_15_27201 : exactInterval 15 27201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27201 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27201) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27201 : oddCount 27201 15 = 5 ∧ acceleratedOrbit 15 27201 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27201 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27201) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27201.1, data_15_27201.2]

/-- Complete interval computation for depth 15, residue 27202. -/
theorem bounds_15_27202 : exactInterval 15 27202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27202 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27202) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27202 : oddCount 27202 15 = 5 ∧ acceleratedOrbit 15 27202 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27202 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27202) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27202.1, data_15_27202.2]

/-- Complete interval computation for depth 15, residue 27203. -/
theorem bounds_15_27203 : exactInterval 15 27203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27203 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27203) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27203 : oddCount 27203 15 = 5 ∧ acceleratedOrbit 15 27203 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27203 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27203) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27203.1, data_15_27203.2]

/-- Complete interval computation for depth 15, residue 27204. -/
theorem bounds_15_27204 : exactInterval 15 27204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27204 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27204) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27204 : oddCount 27204 15 = 8 ∧ acceleratedOrbit 15 27204 = 5453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27204 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27204) = 3 ^ 8 * m + 5453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27204.1, data_15_27204.2]

/-- Complete interval computation for depth 15, residue 27205. -/
theorem bounds_15_27205 : exactInterval 15 27205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27205 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27205) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27205 : oddCount 27205 15 = 8 ∧ acceleratedOrbit 15 27205 = 5453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27205 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27205) = 3 ^ 8 * m + 5453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27205.1, data_15_27205.2]

/-- Complete interval computation for depth 15, residue 27206. -/
theorem bounds_15_27206 : exactInterval 15 27206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27206 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27206) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27206 : oddCount 27206 15 = 8 ∧ acceleratedOrbit 15 27206 = 5453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27206 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27206) = 3 ^ 8 * m + 5453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27206.1, data_15_27206.2]

/-- Complete interval computation for depth 15, residue 27207. -/
theorem bounds_15_27207 : exactInterval 15 27207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27207 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27207) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27207 : oddCount 27207 15 = 7 ∧ acceleratedOrbit 15 27207 = 1816 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27207 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27207) = 3 ^ 7 * m + 1816 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27207.1, data_15_27207.2]

/-- Complete interval computation for depth 15, residue 27208. -/
theorem bounds_15_27208 : exactInterval 15 27208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27208 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27208) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27208 : oddCount 27208 15 = 8 ∧ acceleratedOrbit 15 27208 = 5453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27208 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27208) = 3 ^ 8 * m + 5453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27208.1, data_15_27208.2]

/-- Complete interval computation for depth 15, residue 27209. -/
theorem bounds_15_27209 : exactInterval 15 27209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27209 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27209) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27209 : oddCount 27209 15 = 8 ∧ acceleratedOrbit 15 27209 = 5449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27209 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27209) = 3 ^ 8 * m + 5449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27209.1, data_15_27209.2]

/-- Complete interval computation for depth 15, residue 27210. -/
theorem bounds_15_27210 : exactInterval 15 27210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27210 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27210) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27210 : oddCount 27210 15 = 8 ∧ acceleratedOrbit 15 27210 = 5453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27210 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27210) = 3 ^ 8 * m + 5453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27210.1, data_15_27210.2]

/-- Complete interval computation for depth 15, residue 27211. -/
theorem bounds_15_27211 : exactInterval 15 27211 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27211 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27211) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27211 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27211 : oddCount 27211 15 = 8 ∧ acceleratedOrbit 15 27211 = 5453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27211 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27211) = 3 ^ 8 * m + 5453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27211.1, data_15_27211.2]

/-- Complete interval computation for depth 15, residue 27212. -/
theorem bounds_15_27212 : exactInterval 15 27212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27212 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27212) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27212 : oddCount 27212 15 = 8 ∧ acceleratedOrbit 15 27212 = 5453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27212 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27212) = 3 ^ 8 * m + 5453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27212.1, data_15_27212.2]

/-- Complete interval computation for depth 15, residue 27213. -/
theorem bounds_15_27213 : exactInterval 15 27213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27213 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27213) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27213 : oddCount 27213 15 = 8 ∧ acceleratedOrbit 15 27213 = 5453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27213 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27213) = 3 ^ 8 * m + 5453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27213.1, data_15_27213.2]

/-- Complete interval computation for depth 15, residue 27214. -/
theorem bounds_15_27214 : exactInterval 15 27214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27214 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27214) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27214 : oddCount 27214 15 = 7 ∧ acceleratedOrbit 15 27214 = 1817 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27214 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27214) = 3 ^ 7 * m + 1817 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27214.1, data_15_27214.2]

/-- Complete interval computation for depth 15, residue 27215. -/
theorem bounds_15_27215 : exactInterval 15 27215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27215 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27215) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27215 : oddCount 27215 15 = 7 ∧ acceleratedOrbit 15 27215 = 1817 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27215 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27215) = 3 ^ 7 * m + 1817 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27215.1, data_15_27215.2]

/-- Complete interval computation for depth 15, residue 27216. -/
theorem bounds_15_27216 : exactInterval 15 27216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27216 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27216) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27216 : oddCount 27216 15 = 7 ∧ acceleratedOrbit 15 27216 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27216 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27216) = 3 ^ 7 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27216.1, data_15_27216.2]

/-- Complete interval computation for depth 15, residue 27217. -/
theorem bounds_15_27217 : exactInterval 15 27217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27217 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27217) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27217 : oddCount 27217 15 = 9 ∧ acceleratedOrbit 15 27217 = 16352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27217 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27217) = 3 ^ 9 * m + 16352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27217.1, data_15_27217.2]

/-- Complete interval computation for depth 15, residue 27218. -/
theorem bounds_15_27218 : exactInterval 15 27218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27218 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27218) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27218 : oddCount 27218 15 = 9 ∧ acceleratedOrbit 15 27218 = 16352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27218 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27218) = 3 ^ 9 * m + 16352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27218.1, data_15_27218.2]

/-- Complete interval computation for depth 15, residue 27219. -/
theorem bounds_15_27219 : exactInterval 15 27219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27219 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27219) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27219 : oddCount 27219 15 = 9 ∧ acceleratedOrbit 15 27219 = 16352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27219 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27219) = 3 ^ 9 * m + 16352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27219.1, data_15_27219.2]

/-- Complete interval computation for depth 15, residue 27220. -/
theorem bounds_15_27220 : exactInterval 15 27220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27220 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27220) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27220 : oddCount 27220 15 = 7 ∧ acceleratedOrbit 15 27220 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27220 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27220) = 3 ^ 7 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27220.1, data_15_27220.2]

/-- Complete interval computation for depth 15, residue 27221. -/
theorem bounds_15_27221 : exactInterval 15 27221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27221 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27221) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27221 : oddCount 27221 15 = 7 ∧ acceleratedOrbit 15 27221 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27221 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27221) = 3 ^ 7 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27221.1, data_15_27221.2]

/-- Complete interval computation for depth 15, residue 27222. -/
theorem bounds_15_27222 : exactInterval 15 27222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27222 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27222) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27222 : oddCount 27222 15 = 8 ∧ acceleratedOrbit 15 27222 = 5453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27222 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27222) = 3 ^ 8 * m + 5453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27222.1, data_15_27222.2]

/-- Complete interval computation for depth 15, residue 27223. -/
theorem bounds_15_27223 : exactInterval 15 27223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27223 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27223) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27223 : oddCount 27223 15 = 8 ∧ acceleratedOrbit 15 27223 = 5453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27223 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27223) = 3 ^ 8 * m + 5453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27223.1, data_15_27223.2]

/-- Complete interval computation for depth 15, residue 27224. -/
theorem bounds_15_27224 : exactInterval 15 27224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27224 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27224) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27224 : oddCount 27224 15 = 6 ∧ acceleratedOrbit 15 27224 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27224 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27224) = 3 ^ 6 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27224.1, data_15_27224.2]

/-- Complete interval computation for depth 15, residue 27225. -/
theorem bounds_15_27225 : exactInterval 15 27225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27225 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27225) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27225 : oddCount 27225 15 = 9 ∧ acceleratedOrbit 15 27225 = 16357 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27225 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27225) = 3 ^ 9 * m + 16357 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27225.1, data_15_27225.2]

/-- Complete interval computation for depth 15, residue 27226. -/
theorem bounds_15_27226 : exactInterval 15 27226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27226 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27226) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27226 : oddCount 27226 15 = 6 ∧ acceleratedOrbit 15 27226 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27226 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27226) = 3 ^ 6 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27226.1, data_15_27226.2]

/-- Complete interval computation for depth 15, residue 27227. -/
theorem bounds_15_27227 : exactInterval 15 27227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27227 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27227) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27227 : oddCount 27227 15 = 11 ∧ acceleratedOrbit 15 27227 = 147203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27227 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27227) = 3 ^ 11 * m + 147203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27227.1, data_15_27227.2]

/-- Complete interval computation for depth 15, residue 27228. -/
theorem bounds_15_27228 : exactInterval 15 27228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27228 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27228) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27228 : oddCount 27228 15 = 6 ∧ acceleratedOrbit 15 27228 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27228 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27228) = 3 ^ 6 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27228.1, data_15_27228.2]

/-- Complete interval computation for depth 15, residue 27229. -/
theorem bounds_15_27229 : exactInterval 15 27229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27229 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27229) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27229 : oddCount 27229 15 = 6 ∧ acceleratedOrbit 15 27229 = 607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27229 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27229) = 3 ^ 6 * m + 607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27229.1, data_15_27229.2]

end Collatz.Research.PassageAtlas.Batch0831
