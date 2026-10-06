import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0738

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 24150. -/
theorem bounds_15_24150 : exactInterval 15 24150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24150 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24150) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24150 : oddCount 24150 15 = 7 ∧ acceleratedOrbit 15 24150 = 1613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24150 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24150) = 3 ^ 7 * m + 1613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24150.1, data_15_24150.2]

/-- Complete interval computation for depth 15, residue 24151. -/
theorem bounds_15_24151 : exactInterval 15 24151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24151 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24151) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24151 : oddCount 24151 15 = 7 ∧ acceleratedOrbit 15 24151 = 1613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24151 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24151) = 3 ^ 7 * m + 1613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24151.1, data_15_24151.2]

/-- Complete interval computation for depth 15, residue 24152. -/
theorem bounds_15_24152 : exactInterval 15 24152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24152 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24152) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24152 : oddCount 24152 15 = 6 ∧ acceleratedOrbit 15 24152 = 539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24152 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24152) = 3 ^ 6 * m + 539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24152.1, data_15_24152.2]

/-- Complete interval computation for depth 15, residue 24153. -/
theorem bounds_15_24153 : exactInterval 15 24153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24153 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24153) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24153 : oddCount 24153 15 = 9 ∧ acceleratedOrbit 15 24153 = 14512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24153 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24153) = 3 ^ 9 * m + 14512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24153.1, data_15_24153.2]

/-- Complete interval computation for depth 15, residue 24154. -/
theorem bounds_15_24154 : exactInterval 15 24154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24154 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24154) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24154 : oddCount 24154 15 = 6 ∧ acceleratedOrbit 15 24154 = 539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24154 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24154) = 3 ^ 6 * m + 539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24154.1, data_15_24154.2]

/-- Complete interval computation for depth 15, residue 24155. -/
theorem bounds_15_24155 : exactInterval 15 24155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24155 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24155) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24155 : oddCount 24155 15 = 8 ∧ acceleratedOrbit 15 24155 = 4837 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24155 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24155) = 3 ^ 8 * m + 4837 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24155.1, data_15_24155.2]

/-- Complete interval computation for depth 15, residue 24156. -/
theorem bounds_15_24156 : exactInterval 15 24156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24156 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24156) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24156 : oddCount 24156 15 = 6 ∧ acceleratedOrbit 15 24156 = 539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24156 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24156) = 3 ^ 6 * m + 539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24156.1, data_15_24156.2]

/-- Complete interval computation for depth 15, residue 24157. -/
theorem bounds_15_24157 : exactInterval 15 24157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24157 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24157) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24157 : oddCount 24157 15 = 6 ∧ acceleratedOrbit 15 24157 = 539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24157 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24157) = 3 ^ 6 * m + 539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24157.1, data_15_24157.2]

/-- Complete interval computation for depth 15, residue 24158. -/
theorem bounds_15_24158 : exactInterval 15 24158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24158 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24158) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24158 : oddCount 24158 15 = 7 ∧ acceleratedOrbit 15 24158 = 1613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24158 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24158) = 3 ^ 7 * m + 1613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24158.1, data_15_24158.2]

/-- Complete interval computation for depth 15, residue 24159. -/
theorem bounds_15_24159 : exactInterval 15 24159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24159 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24159) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24159 : oddCount 24159 15 = 7 ∧ acceleratedOrbit 15 24159 = 1613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24159 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24159) = 3 ^ 7 * m + 1613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24159.1, data_15_24159.2]

/-- Complete interval computation for depth 15, residue 24160. -/
theorem bounds_15_24160 : exactInterval 15 24160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24160 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24160) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24160 : oddCount 24160 15 = 7 ∧ acceleratedOrbit 15 24160 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24160 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24160) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24160.1, data_15_24160.2]

/-- Complete interval computation for depth 15, residue 24161. -/
theorem bounds_15_24161 : exactInterval 15 24161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24161 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24161) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24161 : oddCount 24161 15 = 7 ∧ acceleratedOrbit 15 24161 = 1613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24161 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24161) = 3 ^ 7 * m + 1613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24161.1, data_15_24161.2]

/-- Complete interval computation for depth 15, residue 24162. -/
theorem bounds_15_24162 : exactInterval 15 24162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24162 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24162) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24162 : oddCount 24162 15 = 6 ∧ acceleratedOrbit 15 24162 = 539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24162 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24162) = 3 ^ 6 * m + 539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24162.1, data_15_24162.2]

/-- Complete interval computation for depth 15, residue 24163. -/
theorem bounds_15_24163 : exactInterval 15 24163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24163 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24163) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24163 : oddCount 24163 15 = 6 ∧ acceleratedOrbit 15 24163 = 539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24163 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24163) = 3 ^ 6 * m + 539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24163.1, data_15_24163.2]

/-- Complete interval computation for depth 15, residue 24164. -/
theorem bounds_15_24164 : exactInterval 15 24164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24164 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24164) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24164 : oddCount 24164 15 = 6 ∧ acceleratedOrbit 15 24164 = 539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24164 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24164) = 3 ^ 6 * m + 539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24164.1, data_15_24164.2]

/-- Complete interval computation for depth 15, residue 24165. -/
theorem bounds_15_24165 : exactInterval 15 24165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24165 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24165) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24165 : oddCount 24165 15 = 6 ∧ acceleratedOrbit 15 24165 = 539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24165 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24165) = 3 ^ 6 * m + 539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24165.1, data_15_24165.2]

/-- Complete interval computation for depth 15, residue 24166. -/
theorem bounds_15_24166 : exactInterval 15 24166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24166 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24166) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24166 : oddCount 24166 15 = 6 ∧ acceleratedOrbit 15 24166 = 539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24166 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24166) = 3 ^ 6 * m + 539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24166.1, data_15_24166.2]

/-- Complete interval computation for depth 15, residue 24167. -/
theorem bounds_15_24167 : exactInterval 15 24167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24167 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24167) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24167 : oddCount 24167 15 = 10 ∧ acceleratedOrbit 15 24167 = 43553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24167 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24167) = 3 ^ 10 * m + 43553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24167.1, data_15_24167.2]

/-- Complete interval computation for depth 15, residue 24168. -/
theorem bounds_15_24168 : exactInterval 15 24168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24168 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24168) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24168 : oddCount 24168 15 = 7 ∧ acceleratedOrbit 15 24168 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24168 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24168) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24168.1, data_15_24168.2]

/-- Complete interval computation for depth 15, residue 24169. -/
theorem bounds_15_24169 : exactInterval 15 24169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24169 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24169) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24169 : oddCount 24169 15 = 11 ∧ acceleratedOrbit 15 24169 = 130673 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24169 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24169) = 3 ^ 11 * m + 130673 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24169.1, data_15_24169.2]

/-- Complete interval computation for depth 15, residue 24170. -/
theorem bounds_15_24170 : exactInterval 15 24170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24170 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24170) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24170 : oddCount 24170 15 = 7 ∧ acceleratedOrbit 15 24170 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24170 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24170) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24170.1, data_15_24170.2]

/-- Complete interval computation for depth 15, residue 24171. -/
theorem bounds_15_24171 : exactInterval 15 24171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24171 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24171) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24171 : oddCount 24171 15 = 9 ∧ acceleratedOrbit 15 24171 = 14521 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24171 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24171) = 3 ^ 9 * m + 14521 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24171.1, data_15_24171.2]

/-- Complete interval computation for depth 15, residue 24172. -/
theorem bounds_15_24172 : exactInterval 15 24172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24172 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24172) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24172 : oddCount 24172 15 = 9 ∧ acceleratedOrbit 15 24172 = 14525 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24172 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24172) = 3 ^ 9 * m + 14525 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24172.1, data_15_24172.2]

/-- Complete interval computation for depth 15, residue 24173. -/
theorem bounds_15_24173 : exactInterval 15 24173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24173 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24173) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24173 : oddCount 24173 15 = 9 ∧ acceleratedOrbit 15 24173 = 14525 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24173 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24173) = 3 ^ 9 * m + 14525 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24173.1, data_15_24173.2]

/-- Complete interval computation for depth 15, residue 24174. -/
theorem bounds_15_24174 : exactInterval 15 24174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24174 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24174) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24174 : oddCount 24174 15 = 9 ∧ acceleratedOrbit 15 24174 = 14525 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24174 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24174) = 3 ^ 9 * m + 14525 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24174.1, data_15_24174.2]

/-- Complete interval computation for depth 15, residue 24175. -/
theorem bounds_15_24175 : exactInterval 15 24175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24175 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24175) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24175 : oddCount 24175 15 = 10 ∧ acceleratedOrbit 15 24175 = 43568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24175 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24175) = 3 ^ 10 * m + 43568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24175.1, data_15_24175.2]

/-- Complete interval computation for depth 15, residue 24176. -/
theorem bounds_15_24176 : exactInterval 15 24176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24176 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24176) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24176 : oddCount 24176 15 = 7 ∧ acceleratedOrbit 15 24176 = 1615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24176 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24176) = 3 ^ 7 * m + 1615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24176.1, data_15_24176.2]

/-- Complete interval computation for depth 15, residue 24177. -/
theorem bounds_15_24177 : exactInterval 15 24177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24177 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24177) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24177 : oddCount 24177 15 = 7 ∧ acceleratedOrbit 15 24177 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24177 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24177) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24177.1, data_15_24177.2]

/-- Complete interval computation for depth 15, residue 24178. -/
theorem bounds_15_24178 : exactInterval 15 24178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24178 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24178) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24178 : oddCount 24178 15 = 6 ∧ acceleratedOrbit 15 24178 = 538 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24178 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24178) = 3 ^ 6 * m + 538 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24178.1, data_15_24178.2]

/-- Complete interval computation for depth 15, residue 24179. -/
theorem bounds_15_24179 : exactInterval 15 24179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24179 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24179) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24179 : oddCount 24179 15 = 6 ∧ acceleratedOrbit 15 24179 = 538 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24179 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24179) = 3 ^ 6 * m + 538 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24179.1, data_15_24179.2]

/-- Complete interval computation for depth 15, residue 24180. -/
theorem bounds_15_24180 : exactInterval 15 24180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24180 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24180) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24180 : oddCount 24180 15 = 7 ∧ acceleratedOrbit 15 24180 = 1615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24180 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24180) = 3 ^ 7 * m + 1615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24180.1, data_15_24180.2]

/-- Complete interval computation for depth 15, residue 24181. -/
theorem bounds_15_24181 : exactInterval 15 24181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24181 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24181) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24181 : oddCount 24181 15 = 7 ∧ acceleratedOrbit 15 24181 = 1615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24181 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24181) = 3 ^ 7 * m + 1615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24181.1, data_15_24181.2]

end Collatz.Research.PassageAtlas.Batch0738
