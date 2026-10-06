import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0860

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 28147. -/
theorem bounds_15_28147 : exactInterval 15 28147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28147 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28147) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28147 : oddCount 28147 15 = 7 ∧ acceleratedOrbit 15 28147 = 1880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28147 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28147) = 3 ^ 7 * m + 1880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28147.1, data_15_28147.2]

/-- Complete interval computation for depth 15, residue 28148. -/
theorem bounds_15_28148 : exactInterval 15 28148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28148 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28148) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28148 : oddCount 28148 15 = 7 ∧ acceleratedOrbit 15 28148 = 1880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28148 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28148) = 3 ^ 7 * m + 1880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28148.1, data_15_28148.2]

/-- Complete interval computation for depth 15, residue 28149. -/
theorem bounds_15_28149 : exactInterval 15 28149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28149 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28149) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28149 : oddCount 28149 15 = 7 ∧ acceleratedOrbit 15 28149 = 1880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28149 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28149) = 3 ^ 7 * m + 1880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28149.1, data_15_28149.2]

/-- Complete interval computation for depth 15, residue 28150. -/
theorem bounds_15_28150 : exactInterval 15 28150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28150 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28150) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28150 : oddCount 28150 15 = 7 ∧ acceleratedOrbit 15 28150 = 1879 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28150 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28150) = 3 ^ 7 * m + 1879 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28150.1, data_15_28150.2]

/-- Complete interval computation for depth 15, residue 28151. -/
theorem bounds_15_28151 : exactInterval 15 28151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28151 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28151) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28151 : oddCount 28151 15 = 7 ∧ acceleratedOrbit 15 28151 = 1879 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28151 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28151) = 3 ^ 7 * m + 1879 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28151.1, data_15_28151.2]

/-- Complete interval computation for depth 15, residue 28152. -/
theorem bounds_15_28152 : exactInterval 15 28152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28152 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28152) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28152 : oddCount 28152 15 = 10 ∧ acceleratedOrbit 15 28152 = 50746 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28152 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28152) = 3 ^ 10 * m + 50746 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28152.1, data_15_28152.2]

/-- Complete interval computation for depth 15, residue 28153. -/
theorem bounds_15_28153 : exactInterval 15 28153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28153 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28153) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28153 : oddCount 28153 15 = 8 ∧ acceleratedOrbit 15 28153 = 5638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28153 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28153) = 3 ^ 8 * m + 5638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28153.1, data_15_28153.2]

/-- Complete interval computation for depth 15, residue 28154. -/
theorem bounds_15_28154 : exactInterval 15 28154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28154 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28154) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28154 : oddCount 28154 15 = 10 ∧ acceleratedOrbit 15 28154 = 50746 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28154 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28154) = 3 ^ 10 * m + 50746 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28154.1, data_15_28154.2]

/-- Complete interval computation for depth 15, residue 28155. -/
theorem bounds_15_28155 : exactInterval 15 28155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28155 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28155) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28155 : oddCount 28155 15 = 8 ∧ acceleratedOrbit 15 28155 = 5638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28155 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28155) = 3 ^ 8 * m + 5638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28155.1, data_15_28155.2]

/-- Complete interval computation for depth 15, residue 28156. -/
theorem bounds_15_28156 : exactInterval 15 28156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28156 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28156) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28156 : oddCount 28156 15 = 10 ∧ acceleratedOrbit 15 28156 = 50746 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28156 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28156) = 3 ^ 10 * m + 50746 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28156.1, data_15_28156.2]

/-- Complete interval computation for depth 15, residue 28157. -/
theorem bounds_15_28157 : exactInterval 15 28157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28157 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28157) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28157 : oddCount 28157 15 = 10 ∧ acceleratedOrbit 15 28157 = 50746 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28157 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28157) = 3 ^ 10 * m + 50746 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28157.1, data_15_28157.2]

/-- Complete interval computation for depth 15, residue 28158. -/
theorem bounds_15_28158 : exactInterval 15 28158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28158 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28158) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28158 : oddCount 28158 15 = 11 ∧ acceleratedOrbit 15 28158 = 152236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28158 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28158) = 3 ^ 11 * m + 152236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28158.1, data_15_28158.2]

/-- Complete interval computation for depth 15, residue 28159. -/
theorem bounds_15_28159 : exactInterval 15 28159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28159 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28159) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28159 : oddCount 28159 15 = 11 ∧ acceleratedOrbit 15 28159 = 152236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28159 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28159) = 3 ^ 11 * m + 152236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28159.1, data_15_28159.2]

/-- Complete interval computation for depth 15, residue 28160. -/
theorem bounds_15_28160 : exactInterval 15 28160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28160 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28160) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28160 : oddCount 28160 15 = 4 ∧ acceleratedOrbit 15 28160 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28160 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28160) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28160.1, data_15_28160.2]

/-- Complete interval computation for depth 15, residue 28161. -/
theorem bounds_15_28161 : exactInterval 15 28161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28161 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28161) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28161 : oddCount 28161 15 = 9 ∧ acceleratedOrbit 15 28161 = 16919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28161 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28161) = 3 ^ 9 * m + 16919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28161.1, data_15_28161.2]

/-- Complete interval computation for depth 15, residue 28162. -/
theorem bounds_15_28162 : exactInterval 15 28162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28162 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28162) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28162 : oddCount 28162 15 = 5 ∧ acceleratedOrbit 15 28162 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28162 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28162) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28162.1, data_15_28162.2]

/-- Complete interval computation for depth 15, residue 28163. -/
theorem bounds_15_28163 : exactInterval 15 28163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28163 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28163) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28163 : oddCount 28163 15 = 5 ∧ acceleratedOrbit 15 28163 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28163 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28163) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28163.1, data_15_28163.2]

/-- Complete interval computation for depth 15, residue 28164. -/
theorem bounds_15_28164 : exactInterval 15 28164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28164 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28164) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28164 : oddCount 28164 15 = 9 ∧ acceleratedOrbit 15 28164 = 16928 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28164 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28164) = 3 ^ 9 * m + 16928 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28164.1, data_15_28164.2]

/-- Complete interval computation for depth 15, residue 28165. -/
theorem bounds_15_28165 : exactInterval 15 28165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28165 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28165) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28165 : oddCount 28165 15 = 9 ∧ acceleratedOrbit 15 28165 = 16928 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28165 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28165) = 3 ^ 9 * m + 16928 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28165.1, data_15_28165.2]

/-- Complete interval computation for depth 15, residue 28166. -/
theorem bounds_15_28166 : exactInterval 15 28166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28166 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28166) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28166 : oddCount 28166 15 = 9 ∧ acceleratedOrbit 15 28166 = 16928 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28166 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28166) = 3 ^ 9 * m + 16928 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28166.1, data_15_28166.2]

/-- Complete interval computation for depth 15, residue 28167. -/
theorem bounds_15_28167 : exactInterval 15 28167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28167 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28167) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28167 : oddCount 28167 15 = 9 ∧ acceleratedOrbit 15 28167 = 16922 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28167 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28167) = 3 ^ 9 * m + 16922 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28167.1, data_15_28167.2]

/-- Complete interval computation for depth 15, residue 28168. -/
theorem bounds_15_28168 : exactInterval 15 28168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28168 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28168) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28168 : oddCount 28168 15 = 7 ∧ acceleratedOrbit 15 28168 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28168 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28168) = 3 ^ 7 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28168.1, data_15_28168.2]

/-- Complete interval computation for depth 15, residue 28169. -/
theorem bounds_15_28169 : exactInterval 15 28169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28169 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28169) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28169 : oddCount 28169 15 = 8 ∧ acceleratedOrbit 15 28169 = 5642 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28169 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28169) = 3 ^ 8 * m + 5642 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28169.1, data_15_28169.2]

/-- Complete interval computation for depth 15, residue 28170. -/
theorem bounds_15_28170 : exactInterval 15 28170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28170 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28170) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28170 : oddCount 28170 15 = 7 ∧ acceleratedOrbit 15 28170 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28170 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28170) = 3 ^ 7 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28170.1, data_15_28170.2]

/-- Complete interval computation for depth 15, residue 28171. -/
theorem bounds_15_28171 : exactInterval 15 28171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28171 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28171) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28171 : oddCount 28171 15 = 9 ∧ acceleratedOrbit 15 28171 = 16928 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28171 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28171) = 3 ^ 9 * m + 16928 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28171.1, data_15_28171.2]

/-- Complete interval computation for depth 15, residue 28172. -/
theorem bounds_15_28172 : exactInterval 15 28172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28172 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28172) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28172 : oddCount 28172 15 = 7 ∧ acceleratedOrbit 15 28172 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28172 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28172) = 3 ^ 7 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28172.1, data_15_28172.2]

/-- Complete interval computation for depth 15, residue 28173. -/
theorem bounds_15_28173 : exactInterval 15 28173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28173 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28173) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28173 : oddCount 28173 15 = 7 ∧ acceleratedOrbit 15 28173 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28173 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28173) = 3 ^ 7 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28173.1, data_15_28173.2]

/-- Complete interval computation for depth 15, residue 28174. -/
theorem bounds_15_28174 : exactInterval 15 28174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28174 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28174) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28174 : oddCount 28174 15 = 9 ∧ acceleratedOrbit 15 28174 = 16928 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28174 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28174) = 3 ^ 9 * m + 16928 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28174.1, data_15_28174.2]

/-- Complete interval computation for depth 15, residue 28175. -/
theorem bounds_15_28175 : exactInterval 15 28175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28175 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28175) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28175 : oddCount 28175 15 = 9 ∧ acceleratedOrbit 15 28175 = 16928 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28175 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28175) = 3 ^ 9 * m + 16928 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28175.1, data_15_28175.2]

/-- Complete interval computation for depth 15, residue 28176. -/
theorem bounds_15_28176 : exactInterval 15 28176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28176 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28176) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28176 : oddCount 28176 15 = 7 ∧ acceleratedOrbit 15 28176 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28176 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28176) = 3 ^ 7 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28176.1, data_15_28176.2]

/-- Complete interval computation for depth 15, residue 28177. -/
theorem bounds_15_28177 : exactInterval 15 28177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28177 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28177) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28177 : oddCount 28177 15 = 7 ∧ acceleratedOrbit 15 28177 = 1883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28177 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28177) = 3 ^ 7 * m + 1883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28177.1, data_15_28177.2]

/-- Complete interval computation for depth 15, residue 28178. -/
theorem bounds_15_28178 : exactInterval 15 28178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28178 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28178) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28178 : oddCount 28178 15 = 11 ∧ acceleratedOrbit 15 28178 = 152360 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28178 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28178) = 3 ^ 11 * m + 152360 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28178.1, data_15_28178.2]

/-- Complete interval computation for depth 15, residue 28179. -/
theorem bounds_15_28179 : exactInterval 15 28179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28179 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28179) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28179 : oddCount 28179 15 = 11 ∧ acceleratedOrbit 15 28179 = 152360 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28179 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28179) = 3 ^ 11 * m + 152360 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28179.1, data_15_28179.2]

end Collatz.Research.PassageAtlas.Batch0860
