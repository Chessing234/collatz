import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0921

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 30146. -/
theorem bounds_15_30146 : exactInterval 15 30146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30146 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30146) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30146 : oddCount 30146 15 = 8 ∧ acceleratedOrbit 15 30146 = 6037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30146 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30146) = 3 ^ 8 * m + 6037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30146.1, data_15_30146.2]

/-- Complete interval computation for depth 15, residue 30147. -/
theorem bounds_15_30147 : exactInterval 15 30147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30147 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30147) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30147 : oddCount 30147 15 = 8 ∧ acceleratedOrbit 15 30147 = 6037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30147 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30147) = 3 ^ 8 * m + 6037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30147.1, data_15_30147.2]

/-- Complete interval computation for depth 15, residue 30148. -/
theorem bounds_15_30148 : exactInterval 15 30148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30148 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30148) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30148 : oddCount 30148 15 = 6 ∧ acceleratedOrbit 15 30148 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30148 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30148) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30148.1, data_15_30148.2]

/-- Complete interval computation for depth 15, residue 30149. -/
theorem bounds_15_30149 : exactInterval 15 30149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30149 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30149) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30149 : oddCount 30149 15 = 6 ∧ acceleratedOrbit 15 30149 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30149 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30149) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30149.1, data_15_30149.2]

/-- Complete interval computation for depth 15, residue 30150. -/
theorem bounds_15_30150 : exactInterval 15 30150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30150 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30150) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30150 : oddCount 30150 15 = 6 ∧ acceleratedOrbit 15 30150 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30150 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30150) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30150.1, data_15_30150.2]

/-- Complete interval computation for depth 15, residue 30151. -/
theorem bounds_15_30151 : exactInterval 15 30151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30151 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30151) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30151 : oddCount 30151 15 = 8 ∧ acceleratedOrbit 15 30151 = 6038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30151 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30151) = 3 ^ 8 * m + 6038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30151.1, data_15_30151.2]

/-- Complete interval computation for depth 15, residue 30152. -/
theorem bounds_15_30152 : exactInterval 15 30152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30152 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30152) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30152 : oddCount 30152 15 = 7 ∧ acceleratedOrbit 15 30152 = 2015 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30152 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30152) = 3 ^ 7 * m + 2015 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30152.1, data_15_30152.2]

/-- Complete interval computation for depth 15, residue 30153. -/
theorem bounds_15_30153 : exactInterval 15 30153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30153 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30153) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30153 : oddCount 30153 15 = 6 ∧ acceleratedOrbit 15 30153 = 671 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30153 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30153) = 3 ^ 6 * m + 671 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30153.1, data_15_30153.2]

/-- Complete interval computation for depth 15, residue 30154. -/
theorem bounds_15_30154 : exactInterval 15 30154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30154 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30154) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30154 : oddCount 30154 15 = 7 ∧ acceleratedOrbit 15 30154 = 2015 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30154 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30154) = 3 ^ 7 * m + 2015 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30154.1, data_15_30154.2]

/-- Complete interval computation for depth 15, residue 30155. -/
theorem bounds_15_30155 : exactInterval 15 30155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30155 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30155) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30155 : oddCount 30155 15 = 6 ∧ acceleratedOrbit 15 30155 = 671 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30155 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30155) = 3 ^ 6 * m + 671 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30155.1, data_15_30155.2]

/-- Complete interval computation for depth 15, residue 30156. -/
theorem bounds_15_30156 : exactInterval 15 30156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30156 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30156) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30156 : oddCount 30156 15 = 7 ∧ acceleratedOrbit 15 30156 = 2015 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30156 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30156) = 3 ^ 7 * m + 2015 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30156.1, data_15_30156.2]

/-- Complete interval computation for depth 15, residue 30157. -/
theorem bounds_15_30157 : exactInterval 15 30157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30157 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30157) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30157 : oddCount 30157 15 = 7 ∧ acceleratedOrbit 15 30157 = 2015 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30157 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30157) = 3 ^ 7 * m + 2015 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30157.1, data_15_30157.2]

/-- Complete interval computation for depth 15, residue 30158. -/
theorem bounds_15_30158 : exactInterval 15 30158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30158 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30158) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30158 : oddCount 30158 15 = 12 ∧ acceleratedOrbit 15 30158 = 489158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30158 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30158) = 3 ^ 12 * m + 489158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30158.1, data_15_30158.2]

/-- Complete interval computation for depth 15, residue 30159. -/
theorem bounds_15_30159 : exactInterval 15 30159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30159 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30159) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30159 : oddCount 30159 15 = 12 ∧ acceleratedOrbit 15 30159 = 489158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30159 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30159) = 3 ^ 12 * m + 489158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30159.1, data_15_30159.2]

/-- Complete interval computation for depth 15, residue 30160. -/
theorem bounds_15_30160 : exactInterval 15 30160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30160 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30160) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30160 : oddCount 30160 15 = 6 ∧ acceleratedOrbit 15 30160 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30160 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30160) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30160.1, data_15_30160.2]

/-- Complete interval computation for depth 15, residue 30161. -/
theorem bounds_15_30161 : exactInterval 15 30161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30161 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30161) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30161 : oddCount 30161 15 = 7 ∧ acceleratedOrbit 15 30161 = 2015 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30161 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30161) = 3 ^ 7 * m + 2015 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30161.1, data_15_30161.2]

/-- Complete interval computation for depth 15, residue 30162. -/
theorem bounds_15_30162 : exactInterval 15 30162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30162 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30162) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30162 : oddCount 30162 15 = 8 ∧ acceleratedOrbit 15 30162 = 6040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30162 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30162) = 3 ^ 8 * m + 6040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30162.1, data_15_30162.2]

/-- Complete interval computation for depth 15, residue 30163. -/
theorem bounds_15_30163 : exactInterval 15 30163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30163 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30163) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30163 : oddCount 30163 15 = 8 ∧ acceleratedOrbit 15 30163 = 6040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30163 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30163) = 3 ^ 8 * m + 6040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30163.1, data_15_30163.2]

/-- Complete interval computation for depth 15, residue 30164. -/
theorem bounds_15_30164 : exactInterval 15 30164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30164 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30164) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30164 : oddCount 30164 15 = 6 ∧ acceleratedOrbit 15 30164 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30164 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30164) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30164.1, data_15_30164.2]

/-- Complete interval computation for depth 15, residue 30165. -/
theorem bounds_15_30165 : exactInterval 15 30165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30165 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30165) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30165 : oddCount 30165 15 = 6 ∧ acceleratedOrbit 15 30165 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30165 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30165) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30165.1, data_15_30165.2]

/-- Complete interval computation for depth 15, residue 30166. -/
theorem bounds_15_30166 : exactInterval 15 30166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30166 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30166) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30166 : oddCount 30166 15 = 8 ∧ acceleratedOrbit 15 30166 = 6041 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30166 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30166) = 3 ^ 8 * m + 6041 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30166.1, data_15_30166.2]

/-- Complete interval computation for depth 15, residue 30167. -/
theorem bounds_15_30167 : exactInterval 15 30167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30167 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30167) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30167 : oddCount 30167 15 = 8 ∧ acceleratedOrbit 15 30167 = 6041 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30167 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30167) = 3 ^ 8 * m + 6041 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30167.1, data_15_30167.2]

/-- Complete interval computation for depth 15, residue 30168. -/
theorem bounds_15_30168 : exactInterval 15 30168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30168 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30168) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30168 : oddCount 30168 15 = 7 ∧ acceleratedOrbit 15 30168 = 2015 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30168 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30168) = 3 ^ 7 * m + 2015 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30168.1, data_15_30168.2]

/-- Complete interval computation for depth 15, residue 30169. -/
theorem bounds_15_30169 : exactInterval 15 30169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30169 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30169) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30169 : oddCount 30169 15 = 7 ∧ acceleratedOrbit 15 30169 = 2015 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30169 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30169) = 3 ^ 7 * m + 2015 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30169.1, data_15_30169.2]

/-- Complete interval computation for depth 15, residue 30170. -/
theorem bounds_15_30170 : exactInterval 15 30170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30170 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30170) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30170 : oddCount 30170 15 = 7 ∧ acceleratedOrbit 15 30170 = 2015 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30170 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30170) = 3 ^ 7 * m + 2015 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30170.1, data_15_30170.2]

/-- Complete interval computation for depth 15, residue 30171. -/
theorem bounds_15_30171 : exactInterval 15 30171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30171 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30171) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30171 : oddCount 30171 15 = 7 ∧ acceleratedOrbit 15 30171 = 2015 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30171 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30171) = 3 ^ 7 * m + 2015 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30171.1, data_15_30171.2]

/-- Complete interval computation for depth 15, residue 30172. -/
theorem bounds_15_30172 : exactInterval 15 30172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30172 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30172) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30172 : oddCount 30172 15 = 7 ∧ acceleratedOrbit 15 30172 = 2015 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30172 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30172) = 3 ^ 7 * m + 2015 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30172.1, data_15_30172.2]

/-- Complete interval computation for depth 15, residue 30173. -/
theorem bounds_15_30173 : exactInterval 15 30173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30173 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30173) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30173 : oddCount 30173 15 = 7 ∧ acceleratedOrbit 15 30173 = 2015 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30173 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30173) = 3 ^ 7 * m + 2015 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30173.1, data_15_30173.2]

/-- Complete interval computation for depth 15, residue 30174. -/
theorem bounds_15_30174 : exactInterval 15 30174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30174 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30174) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30174 : oddCount 30174 15 = 10 ∧ acceleratedOrbit 15 30174 = 54379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30174 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30174) = 3 ^ 10 * m + 54379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30174.1, data_15_30174.2]

/-- Complete interval computation for depth 15, residue 30175. -/
theorem bounds_15_30175 : exactInterval 15 30175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30175 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30175) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30175 : oddCount 30175 15 = 10 ∧ acceleratedOrbit 15 30175 = 54379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30175 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30175) = 3 ^ 10 * m + 54379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30175.1, data_15_30175.2]

/-- Complete interval computation for depth 15, residue 30176. -/
theorem bounds_15_30176 : exactInterval 15 30176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30176 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30176) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30176 : oddCount 30176 15 = 5 ∧ acceleratedOrbit 15 30176 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30176 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30176) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30176.1, data_15_30176.2]

/-- Complete interval computation for depth 15, residue 30177. -/
theorem bounds_15_30177 : exactInterval 15 30177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30177 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30177) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30177 : oddCount 30177 15 = 8 ∧ acceleratedOrbit 15 30177 = 6043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30177 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30177) = 3 ^ 8 * m + 6043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30177.1, data_15_30177.2]

/-- Complete interval computation for depth 15, residue 30178. -/
theorem bounds_15_30178 : exactInterval 15 30178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30178 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30178) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30178 : oddCount 30178 15 = 6 ∧ acceleratedOrbit 15 30178 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30178 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30178) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30178.1, data_15_30178.2]

end Collatz.Research.PassageAtlas.Batch0921
