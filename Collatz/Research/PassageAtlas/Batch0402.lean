import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0402

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 13139. -/
theorem bounds_15_13139 : exactInterval 15 13139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13139 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13139) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13139 : oddCount 13139 15 = 9 ∧ acceleratedOrbit 15 13139 = 7894 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13139 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13139) = 3 ^ 9 * m + 7894 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13139.1, data_15_13139.2]

/-- Complete interval computation for depth 15, residue 13140. -/
theorem bounds_15_13140 : exactInterval 15 13140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13140 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13140) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13140 : oddCount 13140 15 = 3 ∧ acceleratedOrbit 15 13140 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13140 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13140) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13140.1, data_15_13140.2]

/-- Complete interval computation for depth 15, residue 13141. -/
theorem bounds_15_13141 : exactInterval 15 13141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13141 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13141) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13141 : oddCount 13141 15 = 3 ∧ acceleratedOrbit 15 13141 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13141 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13141) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13141.1, data_15_13141.2]

/-- Complete interval computation for depth 15, residue 13142. -/
theorem bounds_15_13142 : exactInterval 15 13142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13142 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13142) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13142 : oddCount 13142 15 = 10 ∧ acceleratedOrbit 15 13142 = 23692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13142 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13142) = 3 ^ 10 * m + 23692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13142.1, data_15_13142.2]

/-- Complete interval computation for depth 15, residue 13143. -/
theorem bounds_15_13143 : exactInterval 15 13143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13143 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13143) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13143 : oddCount 13143 15 = 10 ∧ acceleratedOrbit 15 13143 = 23692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13143 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13143) = 3 ^ 10 * m + 23692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13143.1, data_15_13143.2]

/-- Complete interval computation for depth 15, residue 13144. -/
theorem bounds_15_13144 : exactInterval 15 13144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13144 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13144) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13144 : oddCount 13144 15 = 8 ∧ acceleratedOrbit 15 13144 = 2636 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13144 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13144) = 3 ^ 8 * m + 2636 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13144.1, data_15_13144.2]

/-- Complete interval computation for depth 15, residue 13145. -/
theorem bounds_15_13145 : exactInterval 15 13145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13145 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13145) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13145 : oddCount 13145 15 = 5 ∧ acceleratedOrbit 15 13145 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13145 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13145) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13145.1, data_15_13145.2]

/-- Complete interval computation for depth 15, residue 13146. -/
theorem bounds_15_13146 : exactInterval 15 13146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13146 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13146) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13146 : oddCount 13146 15 = 8 ∧ acceleratedOrbit 15 13146 = 2636 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13146 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13146) = 3 ^ 8 * m + 2636 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13146.1, data_15_13146.2]

/-- Complete interval computation for depth 15, residue 13147. -/
theorem bounds_15_13147 : exactInterval 15 13147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13147 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13147) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13147 : oddCount 13147 15 = 10 ∧ acceleratedOrbit 15 13147 = 23696 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13147 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13147) = 3 ^ 10 * m + 23696 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13147.1, data_15_13147.2]

/-- Complete interval computation for depth 15, residue 13148. -/
theorem bounds_15_13148 : exactInterval 15 13148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13148 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13148) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13148 : oddCount 13148 15 = 8 ∧ acceleratedOrbit 15 13148 = 2636 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13148 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13148) = 3 ^ 8 * m + 2636 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13148.1, data_15_13148.2]

/-- Complete interval computation for depth 15, residue 13149. -/
theorem bounds_15_13149 : exactInterval 15 13149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13149 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13149) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13149 : oddCount 13149 15 = 8 ∧ acceleratedOrbit 15 13149 = 2636 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13149 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13149) = 3 ^ 8 * m + 2636 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13149.1, data_15_13149.2]

/-- Complete interval computation for depth 15, residue 13150. -/
theorem bounds_15_13150 : exactInterval 15 13150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13150 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13150) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13150 : oddCount 13150 15 = 7 ∧ acceleratedOrbit 15 13150 = 878 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13150 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13150) = 3 ^ 7 * m + 878 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13150.1, data_15_13150.2]

/-- Complete interval computation for depth 15, residue 13151. -/
theorem bounds_15_13151 : exactInterval 15 13151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13151 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13151) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13151 : oddCount 13151 15 = 7 ∧ acceleratedOrbit 15 13151 = 878 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13151 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13151) = 3 ^ 7 * m + 878 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13151.1, data_15_13151.2]

/-- Complete interval computation for depth 15, residue 13152. -/
theorem bounds_15_13152 : exactInterval 15 13152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13152 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13152) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13152 : oddCount 13152 15 = 7 ∧ acceleratedOrbit 15 13152 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13152 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13152) = 3 ^ 7 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13152.1, data_15_13152.2]

/-- Complete interval computation for depth 15, residue 13153. -/
theorem bounds_15_13153 : exactInterval 15 13153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13153 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13153) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13153 : oddCount 13153 15 = 10 ∧ acceleratedOrbit 15 13153 = 23708 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13153 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13153) = 3 ^ 10 * m + 23708 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13153.1, data_15_13153.2]

/-- Complete interval computation for depth 15, residue 13154. -/
theorem bounds_15_13154 : exactInterval 15 13154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13154 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13154) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13154 : oddCount 13154 15 = 7 ∧ acceleratedOrbit 15 13154 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13154 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13154) = 3 ^ 7 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13154.1, data_15_13154.2]

/-- Complete interval computation for depth 15, residue 13155. -/
theorem bounds_15_13155 : exactInterval 15 13155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13155 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13155) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13155 : oddCount 13155 15 = 7 ∧ acceleratedOrbit 15 13155 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13155 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13155) = 3 ^ 7 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13155.1, data_15_13155.2]

/-- Complete interval computation for depth 15, residue 13156. -/
theorem bounds_15_13156 : exactInterval 15 13156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13156 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13156) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13156 : oddCount 13156 15 = 7 ∧ acceleratedOrbit 15 13156 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13156 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13156) = 3 ^ 7 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13156.1, data_15_13156.2]

/-- Complete interval computation for depth 15, residue 13157. -/
theorem bounds_15_13157 : exactInterval 15 13157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13157 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13157) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13157 : oddCount 13157 15 = 7 ∧ acceleratedOrbit 15 13157 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13157 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13157) = 3 ^ 7 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13157.1, data_15_13157.2]

/-- Complete interval computation for depth 15, residue 13158. -/
theorem bounds_15_13158 : exactInterval 15 13158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13158 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13158) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13158 : oddCount 13158 15 = 7 ∧ acceleratedOrbit 15 13158 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13158 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13158) = 3 ^ 7 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13158.1, data_15_13158.2]

/-- Complete interval computation for depth 15, residue 13159. -/
theorem bounds_15_13159 : exactInterval 15 13159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13159 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13159) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13159 : oddCount 13159 15 = 11 ∧ acceleratedOrbit 15 13159 = 71146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13159 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13159) = 3 ^ 11 * m + 71146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13159.1, data_15_13159.2]

/-- Complete interval computation for depth 15, residue 13160. -/
theorem bounds_15_13160 : exactInterval 15 13160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13160 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13160) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13160 : oddCount 13160 15 = 7 ∧ acceleratedOrbit 15 13160 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13160 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13160) = 3 ^ 7 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13160.1, data_15_13160.2]

/-- Complete interval computation for depth 15, residue 13161. -/
theorem bounds_15_13161 : exactInterval 15 13161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13161 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13161) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13161 : oddCount 13161 15 = 10 ∧ acceleratedOrbit 15 13161 = 23723 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13161 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13161) = 3 ^ 10 * m + 23723 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13161.1, data_15_13161.2]

/-- Complete interval computation for depth 15, residue 13162. -/
theorem bounds_15_13162 : exactInterval 15 13162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13162 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13162) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13162 : oddCount 13162 15 = 7 ∧ acceleratedOrbit 15 13162 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13162 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13162) = 3 ^ 7 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13162.1, data_15_13162.2]

/-- Complete interval computation for depth 15, residue 13163. -/
theorem bounds_15_13163 : exactInterval 15 13163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13163 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13163) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13163 : oddCount 13163 15 = 6 ∧ acceleratedOrbit 15 13163 = 293 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13163 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13163) = 3 ^ 6 * m + 293 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13163.1, data_15_13163.2]

/-- Complete interval computation for depth 15, residue 13164. -/
theorem bounds_15_13164 : exactInterval 15 13164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13164 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13164) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13164 : oddCount 13164 15 = 6 ∧ acceleratedOrbit 15 13164 = 293 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13164 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13164) = 3 ^ 6 * m + 293 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13164.1, data_15_13164.2]

/-- Complete interval computation for depth 15, residue 13165. -/
theorem bounds_15_13165 : exactInterval 15 13165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13165 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13165) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13165 : oddCount 13165 15 = 6 ∧ acceleratedOrbit 15 13165 = 293 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13165 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13165) = 3 ^ 6 * m + 293 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13165.1, data_15_13165.2]

/-- Complete interval computation for depth 15, residue 13166. -/
theorem bounds_15_13166 : exactInterval 15 13166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13166 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13166) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13166 : oddCount 13166 15 = 6 ∧ acceleratedOrbit 15 13166 = 293 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13166 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13166) = 3 ^ 6 * m + 293 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13166.1, data_15_13166.2]

/-- Complete interval computation for depth 15, residue 13167. -/
theorem bounds_15_13167 : exactInterval 15 13167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13167 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13167) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13167 : oddCount 13167 15 = 10 ∧ acceleratedOrbit 15 13167 = 23732 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13167 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13167) = 3 ^ 10 * m + 23732 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13167.1, data_15_13167.2]

/-- Complete interval computation for depth 15, residue 13168. -/
theorem bounds_15_13168 : exactInterval 15 13168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13168 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13168) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13168 : oddCount 13168 15 = 7 ∧ acceleratedOrbit 15 13168 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13168 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13168) = 3 ^ 7 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13168.1, data_15_13168.2]

/-- Complete interval computation for depth 15, residue 13169. -/
theorem bounds_15_13169 : exactInterval 15 13169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13169 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13169) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13169 : oddCount 13169 15 = 7 ∧ acceleratedOrbit 15 13169 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13169 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13169) = 3 ^ 7 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13169.1, data_15_13169.2]

/-- Complete interval computation for depth 15, residue 13170. -/
theorem bounds_15_13170 : exactInterval 15 13170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13170 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13170) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13170 : oddCount 13170 15 = 7 ∧ acceleratedOrbit 15 13170 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13170 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13170) = 3 ^ 7 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13170.1, data_15_13170.2]

/-- Complete interval computation for depth 15, residue 13171. -/
theorem bounds_15_13171 : exactInterval 15 13171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13171 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13171) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13171 : oddCount 13171 15 = 7 ∧ acceleratedOrbit 15 13171 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13171 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13171) = 3 ^ 7 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13171.1, data_15_13171.2]

end Collatz.Research.PassageAtlas.Batch0402
