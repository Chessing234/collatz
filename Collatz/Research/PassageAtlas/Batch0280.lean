import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0280

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 9142. -/
theorem bounds_15_9142 : exactInterval 15 9142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9142 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9142) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9142 : oddCount 9142 15 = 7 ∧ acceleratedOrbit 15 9142 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9142 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9142) = 3 ^ 7 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9142.1, data_15_9142.2]

/-- Complete interval computation for depth 15, residue 9143. -/
theorem bounds_15_9143 : exactInterval 15 9143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9143 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9143) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9143 : oddCount 9143 15 = 7 ∧ acceleratedOrbit 15 9143 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9143 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9143) = 3 ^ 7 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9143.1, data_15_9143.2]

/-- Complete interval computation for depth 15, residue 9144. -/
theorem bounds_15_9144 : exactInterval 15 9144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9144 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9144) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9144 : oddCount 9144 15 = 5 ∧ acceleratedOrbit 15 9144 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9144 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9144) = 3 ^ 5 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9144.1, data_15_9144.2]

/-- Complete interval computation for depth 15, residue 9145. -/
theorem bounds_15_9145 : exactInterval 15 9145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9145 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9145) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9145 : oddCount 9145 15 = 9 ∧ acceleratedOrbit 15 9145 = 5498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9145 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9145) = 3 ^ 9 * m + 5498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9145.1, data_15_9145.2]

/-- Complete interval computation for depth 15, residue 9146. -/
theorem bounds_15_9146 : exactInterval 15 9146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9146 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9146) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9146 : oddCount 9146 15 = 5 ∧ acceleratedOrbit 15 9146 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9146 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9146) = 3 ^ 5 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9146.1, data_15_9146.2]

/-- Complete interval computation for depth 15, residue 9147. -/
theorem bounds_15_9147 : exactInterval 15 9147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9147 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9147) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9147 : oddCount 9147 15 = 9 ∧ acceleratedOrbit 15 9147 = 5498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9147 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9147) = 3 ^ 9 * m + 5498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9147.1, data_15_9147.2]

/-- Complete interval computation for depth 15, residue 9148. -/
theorem bounds_15_9148 : exactInterval 15 9148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9148 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9148) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9148 : oddCount 9148 15 = 11 ∧ acceleratedOrbit 15 9148 = 49481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9148 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9148) = 3 ^ 11 * m + 49481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9148.1, data_15_9148.2]

/-- Complete interval computation for depth 15, residue 9149. -/
theorem bounds_15_9149 : exactInterval 15 9149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9149 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9149) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9149 : oddCount 9149 15 = 11 ∧ acceleratedOrbit 15 9149 = 49481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9149 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9149) = 3 ^ 11 * m + 49481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9149.1, data_15_9149.2]

/-- Complete interval computation for depth 15, residue 9150. -/
theorem bounds_15_9150 : exactInterval 15 9150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9150 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9150) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9150 : oddCount 9150 15 = 11 ∧ acceleratedOrbit 15 9150 = 49481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9150 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9150) = 3 ^ 11 * m + 49481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9150.1, data_15_9150.2]

/-- Complete interval computation for depth 15, residue 9151. -/
theorem bounds_15_9151 : exactInterval 15 9151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9151 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9151) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9151 : oddCount 9151 15 = 12 ∧ acceleratedOrbit 15 9151 = 148432 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9151 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9151) = 3 ^ 12 * m + 148432 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9151.1, data_15_9151.2]

/-- Complete interval computation for depth 15, residue 9152. -/
theorem bounds_15_9152 : exactInterval 15 9152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9152 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9152) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9152 : oddCount 9152 15 = 6 ∧ acceleratedOrbit 15 9152 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9152 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9152) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9152.1, data_15_9152.2]

/-- Complete interval computation for depth 15, residue 9153. -/
theorem bounds_15_9153 : exactInterval 15 9153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9153 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9153) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9153 : oddCount 9153 15 = 8 ∧ acceleratedOrbit 15 9153 = 1835 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9153 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9153) = 3 ^ 8 * m + 1835 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9153.1, data_15_9153.2]

/-- Complete interval computation for depth 15, residue 9154. -/
theorem bounds_15_9154 : exactInterval 15 9154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9154 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9154) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9154 : oddCount 9154 15 = 8 ∧ acceleratedOrbit 15 9154 = 1835 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9154 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9154) = 3 ^ 8 * m + 1835 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9154.1, data_15_9154.2]

/-- Complete interval computation for depth 15, residue 9155. -/
theorem bounds_15_9155 : exactInterval 15 9155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9155 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9155) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9155 : oddCount 9155 15 = 8 ∧ acceleratedOrbit 15 9155 = 1835 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9155 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9155) = 3 ^ 8 * m + 1835 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9155.1, data_15_9155.2]

/-- Complete interval computation for depth 15, residue 9156. -/
theorem bounds_15_9156 : exactInterval 15 9156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9156 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9156) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9156 : oddCount 9156 15 = 6 ∧ acceleratedOrbit 15 9156 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9156 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9156) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9156.1, data_15_9156.2]

/-- Complete interval computation for depth 15, residue 9157. -/
theorem bounds_15_9157 : exactInterval 15 9157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9157 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9157) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9157 : oddCount 9157 15 = 6 ∧ acceleratedOrbit 15 9157 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9157 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9157) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9157.1, data_15_9157.2]

/-- Complete interval computation for depth 15, residue 9158. -/
theorem bounds_15_9158 : exactInterval 15 9158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9158 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9158) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9158 : oddCount 9158 15 = 6 ∧ acceleratedOrbit 15 9158 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9158 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9158) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9158.1, data_15_9158.2]

/-- Complete interval computation for depth 15, residue 9159. -/
theorem bounds_15_9159 : exactInterval 15 9159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9159 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9159) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9159 : oddCount 9159 15 = 9 ∧ acceleratedOrbit 15 9159 = 5503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9159 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9159) = 3 ^ 9 * m + 5503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9159.1, data_15_9159.2]

/-- Complete interval computation for depth 15, residue 9160. -/
theorem bounds_15_9160 : exactInterval 15 9160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9160 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9160) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9160 : oddCount 9160 15 = 8 ∧ acceleratedOrbit 15 9160 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9160 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9160) = 3 ^ 8 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9160.1, data_15_9160.2]

/-- Complete interval computation for depth 15, residue 9161. -/
theorem bounds_15_9161 : exactInterval 15 9161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9161 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9161) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9161 : oddCount 9161 15 = 9 ∧ acceleratedOrbit 15 9161 = 5507 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9161 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9161) = 3 ^ 9 * m + 5507 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9161.1, data_15_9161.2]

/-- Complete interval computation for depth 15, residue 9162. -/
theorem bounds_15_9162 : exactInterval 15 9162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9162 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9162) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9162 : oddCount 9162 15 = 8 ∧ acceleratedOrbit 15 9162 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9162 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9162) = 3 ^ 8 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9162.1, data_15_9162.2]

/-- Complete interval computation for depth 15, residue 9163. -/
theorem bounds_15_9163 : exactInterval 15 9163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9163 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9163) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9163 : oddCount 9163 15 = 5 ∧ acceleratedOrbit 15 9163 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9163 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9163) = 3 ^ 5 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9163.1, data_15_9163.2]

/-- Complete interval computation for depth 15, residue 9164. -/
theorem bounds_15_9164 : exactInterval 15 9164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9164 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9164) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9164 : oddCount 9164 15 = 8 ∧ acceleratedOrbit 15 9164 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9164 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9164) = 3 ^ 8 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9164.1, data_15_9164.2]

/-- Complete interval computation for depth 15, residue 9165. -/
theorem bounds_15_9165 : exactInterval 15 9165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9165 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9165) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9165 : oddCount 9165 15 = 8 ∧ acceleratedOrbit 15 9165 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9165 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9165) = 3 ^ 8 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9165.1, data_15_9165.2]

/-- Complete interval computation for depth 15, residue 9166. -/
theorem bounds_15_9166 : exactInterval 15 9166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9166 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9166) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9166 : oddCount 9166 15 = 11 ∧ acceleratedOrbit 15 9166 = 49571 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9166 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9166) = 3 ^ 11 * m + 49571 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9166.1, data_15_9166.2]

/-- Complete interval computation for depth 15, residue 9167. -/
theorem bounds_15_9167 : exactInterval 15 9167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9167 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9167) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9167 : oddCount 9167 15 = 11 ∧ acceleratedOrbit 15 9167 = 49571 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9167 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9167) = 3 ^ 11 * m + 49571 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9167.1, data_15_9167.2]

/-- Complete interval computation for depth 15, residue 9168. -/
theorem bounds_15_9168 : exactInterval 15 9168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9168 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9168) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9168 : oddCount 9168 15 = 6 ∧ acceleratedOrbit 15 9168 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9168 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9168) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9168.1, data_15_9168.2]

/-- Complete interval computation for depth 15, residue 9169. -/
theorem bounds_15_9169 : exactInterval 15 9169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9169 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9169) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9169 : oddCount 9169 15 = 8 ∧ acceleratedOrbit 15 9169 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9169 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9169) = 3 ^ 8 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9169.1, data_15_9169.2]

/-- Complete interval computation for depth 15, residue 9170. -/
theorem bounds_15_9170 : exactInterval 15 9170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9170 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9170) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9170 : oddCount 9170 15 = 8 ∧ acceleratedOrbit 15 9170 = 1837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9170 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9170) = 3 ^ 8 * m + 1837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9170.1, data_15_9170.2]

/-- Complete interval computation for depth 15, residue 9171. -/
theorem bounds_15_9171 : exactInterval 15 9171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9171 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9171) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9171 : oddCount 9171 15 = 8 ∧ acceleratedOrbit 15 9171 = 1837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9171 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9171) = 3 ^ 8 * m + 1837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9171.1, data_15_9171.2]

/-- Complete interval computation for depth 15, residue 9172. -/
theorem bounds_15_9172 : exactInterval 15 9172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9172 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9172) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9172 : oddCount 9172 15 = 6 ∧ acceleratedOrbit 15 9172 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9172 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9172) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9172.1, data_15_9172.2]

/-- Complete interval computation for depth 15, residue 9173. -/
theorem bounds_15_9173 : exactInterval 15 9173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9173 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9173) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9173 : oddCount 9173 15 = 6 ∧ acceleratedOrbit 15 9173 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9173 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9173) = 3 ^ 6 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9173.1, data_15_9173.2]

/-- Complete interval computation for depth 15, residue 9174. -/
theorem bounds_15_9174 : exactInterval 15 9174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9174 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9174) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9174 : oddCount 9174 15 = 9 ∧ acceleratedOrbit 15 9174 = 5513 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9174 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9174) = 3 ^ 9 * m + 5513 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9174.1, data_15_9174.2]

end Collatz.Research.PassageAtlas.Batch0280
