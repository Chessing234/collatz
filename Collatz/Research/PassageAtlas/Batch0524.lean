import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0524

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 17137. -/
theorem bounds_15_17137 : exactInterval 15 17137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17137 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17137) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17137 : oddCount 17137 15 = 5 ∧ acceleratedOrbit 15 17137 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17137 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17137) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17137.1, data_15_17137.2]

/-- Complete interval computation for depth 15, residue 17138. -/
theorem bounds_15_17138 : exactInterval 15 17138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17138 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17138) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17138 : oddCount 17138 15 = 9 ∧ acceleratedOrbit 15 17138 = 10297 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17138 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17138) = 3 ^ 9 * m + 10297 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17138.1, data_15_17138.2]

/-- Complete interval computation for depth 15, residue 17139. -/
theorem bounds_15_17139 : exactInterval 15 17139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17139 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17139) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17139 : oddCount 17139 15 = 9 ∧ acceleratedOrbit 15 17139 = 10297 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17139 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17139) = 3 ^ 9 * m + 10297 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17139.1, data_15_17139.2]

/-- Complete interval computation for depth 15, residue 17140. -/
theorem bounds_15_17140 : exactInterval 15 17140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17140 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17140) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17140 : oddCount 17140 15 = 7 ∧ acceleratedOrbit 15 17140 = 1145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17140 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17140) = 3 ^ 7 * m + 1145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17140.1, data_15_17140.2]

/-- Complete interval computation for depth 15, residue 17141. -/
theorem bounds_15_17141 : exactInterval 15 17141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17141 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17141) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17141 : oddCount 17141 15 = 7 ∧ acceleratedOrbit 15 17141 = 1145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17141 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17141) = 3 ^ 7 * m + 1145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17141.1, data_15_17141.2]

/-- Complete interval computation for depth 15, residue 17142. -/
theorem bounds_15_17142 : exactInterval 15 17142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17142 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17142) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17142 : oddCount 17142 15 = 9 ∧ acceleratedOrbit 15 17142 = 10300 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17142 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17142) = 3 ^ 9 * m + 10300 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17142.1, data_15_17142.2]

/-- Complete interval computation for depth 15, residue 17143. -/
theorem bounds_15_17143 : exactInterval 15 17143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17143 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17143) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17143 : oddCount 17143 15 = 9 ∧ acceleratedOrbit 15 17143 = 10300 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17143 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17143) = 3 ^ 9 * m + 10300 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17143.1, data_15_17143.2]

/-- Complete interval computation for depth 15, residue 17144. -/
theorem bounds_15_17144 : exactInterval 15 17144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17144 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17144) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17144 : oddCount 17144 15 = 7 ∧ acceleratedOrbit 15 17144 = 1145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17144 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17144) = 3 ^ 7 * m + 1145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17144.1, data_15_17144.2]

/-- Complete interval computation for depth 15, residue 17145. -/
theorem bounds_15_17145 : exactInterval 15 17145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17145 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17145) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17145 : oddCount 17145 15 = 7 ∧ acceleratedOrbit 15 17145 = 1145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17145 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17145) = 3 ^ 7 * m + 1145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17145.1, data_15_17145.2]

/-- Complete interval computation for depth 15, residue 17146. -/
theorem bounds_15_17146 : exactInterval 15 17146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17146 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17146) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17146 : oddCount 17146 15 = 7 ∧ acceleratedOrbit 15 17146 = 1145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17146 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17146) = 3 ^ 7 * m + 1145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17146.1, data_15_17146.2]

/-- Complete interval computation for depth 15, residue 17147. -/
theorem bounds_15_17147 : exactInterval 15 17147 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17147 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17147) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17147 : oddCount 17147 15 = 9 ∧ acceleratedOrbit 15 17147 = 10301 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17147 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17147) = 3 ^ 9 * m + 10301 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17147.1, data_15_17147.2]

/-- Complete interval computation for depth 15, residue 17148. -/
theorem bounds_15_17148 : exactInterval 15 17148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17148 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17148) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17148 : oddCount 17148 15 = 9 ∧ acceleratedOrbit 15 17148 = 10304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17148 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17148) = 3 ^ 9 * m + 10304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17148.1, data_15_17148.2]

/-- Complete interval computation for depth 15, residue 17149. -/
theorem bounds_15_17149 : exactInterval 15 17149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17149 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17149) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17149 : oddCount 17149 15 = 9 ∧ acceleratedOrbit 15 17149 = 10304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17149 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17149) = 3 ^ 9 * m + 10304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17149.1, data_15_17149.2]

/-- Complete interval computation for depth 15, residue 17150. -/
theorem bounds_15_17150 : exactInterval 15 17150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17150 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17150) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17150 : oddCount 17150 15 = 9 ∧ acceleratedOrbit 15 17150 = 10304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17150 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17150) = 3 ^ 9 * m + 10304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17150.1, data_15_17150.2]

/-- Complete interval computation for depth 15, residue 17151. -/
theorem bounds_15_17151 : exactInterval 15 17151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17151 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17151) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17151 : oddCount 17151 15 = 11 ∧ acceleratedOrbit 15 17151 = 92726 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17151 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17151) = 3 ^ 11 * m + 92726 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17151.1, data_15_17151.2]

/-- Complete interval computation for depth 15, residue 17152. -/
theorem bounds_15_17152 : exactInterval 15 17152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17152 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17152) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17152 : oddCount 17152 15 = 4 ∧ acceleratedOrbit 15 17152 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17152 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17152) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17152.1, data_15_17152.2]

/-- Complete interval computation for depth 15, residue 17153. -/
theorem bounds_15_17153 : exactInterval 15 17153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17153 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17153) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17153 : oddCount 17153 15 = 6 ∧ acceleratedOrbit 15 17153 = 382 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17153 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17153) = 3 ^ 6 * m + 382 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17153.1, data_15_17153.2]

/-- Complete interval computation for depth 15, residue 17154. -/
theorem bounds_15_17154 : exactInterval 15 17154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17154 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17154) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17154 : oddCount 17154 15 = 6 ∧ acceleratedOrbit 15 17154 = 382 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17154 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17154) = 3 ^ 6 * m + 382 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17154.1, data_15_17154.2]

/-- Complete interval computation for depth 15, residue 17155. -/
theorem bounds_15_17155 : exactInterval 15 17155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17155 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17155) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17155 : oddCount 17155 15 = 6 ∧ acceleratedOrbit 15 17155 = 382 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17155 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17155) = 3 ^ 6 * m + 382 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17155.1, data_15_17155.2]

/-- Complete interval computation for depth 15, residue 17156. -/
theorem bounds_15_17156 : exactInterval 15 17156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17156 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17156) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17156 : oddCount 17156 15 = 7 ∧ acceleratedOrbit 15 17156 = 1147 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17156 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17156) = 3 ^ 7 * m + 1147 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17156.1, data_15_17156.2]

/-- Complete interval computation for depth 15, residue 17157. -/
theorem bounds_15_17157 : exactInterval 15 17157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17157 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17157) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17157 : oddCount 17157 15 = 7 ∧ acceleratedOrbit 15 17157 = 1147 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17157 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17157) = 3 ^ 7 * m + 1147 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17157.1, data_15_17157.2]

/-- Complete interval computation for depth 15, residue 17158. -/
theorem bounds_15_17158 : exactInterval 15 17158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17158 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17158) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17158 : oddCount 17158 15 = 7 ∧ acceleratedOrbit 15 17158 = 1147 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17158 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17158) = 3 ^ 7 * m + 1147 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17158.1, data_15_17158.2]

/-- Complete interval computation for depth 15, residue 17159. -/
theorem bounds_15_17159 : exactInterval 15 17159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17159 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17159) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17159 : oddCount 17159 15 = 9 ∧ acceleratedOrbit 15 17159 = 10309 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17159 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17159) = 3 ^ 9 * m + 10309 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17159.1, data_15_17159.2]

/-- Complete interval computation for depth 15, residue 17160. -/
theorem bounds_15_17160 : exactInterval 15 17160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17160 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17160) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17160 : oddCount 17160 15 = 7 ∧ acceleratedOrbit 15 17160 = 1147 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17160 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17160) = 3 ^ 7 * m + 1147 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17160.1, data_15_17160.2]

/-- Complete interval computation for depth 15, residue 17161. -/
theorem bounds_15_17161 : exactInterval 15 17161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17161 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17161) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17161 : oddCount 17161 15 = 8 ∧ acceleratedOrbit 15 17161 = 3437 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17161 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17161) = 3 ^ 8 * m + 3437 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17161.1, data_15_17161.2]

/-- Complete interval computation for depth 15, residue 17162. -/
theorem bounds_15_17162 : exactInterval 15 17162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17162 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17162) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17162 : oddCount 17162 15 = 7 ∧ acceleratedOrbit 15 17162 = 1147 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17162 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17162) = 3 ^ 7 * m + 1147 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17162.1, data_15_17162.2]

/-- Complete interval computation for depth 15, residue 17163. -/
theorem bounds_15_17163 : exactInterval 15 17163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17163 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17163) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17163 : oddCount 17163 15 = 9 ∧ acceleratedOrbit 15 17163 = 10313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17163 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17163) = 3 ^ 9 * m + 10313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17163.1, data_15_17163.2]

/-- Complete interval computation for depth 15, residue 17164. -/
theorem bounds_15_17164 : exactInterval 15 17164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17164 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17164) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17164 : oddCount 17164 15 = 7 ∧ acceleratedOrbit 15 17164 = 1147 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17164 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17164) = 3 ^ 7 * m + 1147 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17164.1, data_15_17164.2]

/-- Complete interval computation for depth 15, residue 17165. -/
theorem bounds_15_17165 : exactInterval 15 17165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17165 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17165) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17165 : oddCount 17165 15 = 7 ∧ acceleratedOrbit 15 17165 = 1147 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17165 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17165) = 3 ^ 7 * m + 1147 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17165.1, data_15_17165.2]

/-- Complete interval computation for depth 15, residue 17166. -/
theorem bounds_15_17166 : exactInterval 15 17166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17166 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17166) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17166 : oddCount 17166 15 = 7 ∧ acceleratedOrbit 15 17166 = 1147 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17166 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17166) = 3 ^ 7 * m + 1147 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17166.1, data_15_17166.2]

/-- Complete interval computation for depth 15, residue 17167. -/
theorem bounds_15_17167 : exactInterval 15 17167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17167 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17167) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17167 : oddCount 17167 15 = 7 ∧ acceleratedOrbit 15 17167 = 1147 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17167 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17167) = 3 ^ 7 * m + 1147 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17167.1, data_15_17167.2]

/-- Complete interval computation for depth 15, residue 17168. -/
theorem bounds_15_17168 : exactInterval 15 17168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17168 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17168) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17168 : oddCount 17168 15 = 5 ∧ acceleratedOrbit 15 17168 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17168 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17168) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17168.1, data_15_17168.2]

/-- Complete interval computation for depth 15, residue 17169. -/
theorem bounds_15_17169 : exactInterval 15 17169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17169 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17169) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17169 : oddCount 17169 15 = 7 ∧ acceleratedOrbit 15 17169 = 1147 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17169 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17169) = 3 ^ 7 * m + 1147 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17169.1, data_15_17169.2]

end Collatz.Research.PassageAtlas.Batch0524
