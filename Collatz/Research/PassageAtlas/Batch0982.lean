import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0982

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 32145. -/
theorem bounds_15_32145 : exactInterval 15 32145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32145 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32145) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32145 : oddCount 32145 15 = 8 ∧ acceleratedOrbit 15 32145 = 6439 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32145 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32145) = 3 ^ 8 * m + 6439 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32145.1, data_15_32145.2]

/-- Complete interval computation for depth 15, residue 32146. -/
theorem bounds_15_32146 : exactInterval 15 32146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32146 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32146) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32146 : oddCount 32146 15 = 8 ∧ acceleratedOrbit 15 32146 = 6439 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32146 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32146) = 3 ^ 8 * m + 6439 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32146.1, data_15_32146.2]

/-- Complete interval computation for depth 15, residue 32147. -/
theorem bounds_15_32147 : exactInterval 15 32147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32147 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32147) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32147 : oddCount 32147 15 = 8 ∧ acceleratedOrbit 15 32147 = 6439 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32147 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32147) = 3 ^ 8 * m + 6439 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32147.1, data_15_32147.2]

/-- Complete interval computation for depth 15, residue 32148. -/
theorem bounds_15_32148 : exactInterval 15 32148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32148 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32148) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32148 : oddCount 32148 15 = 4 ∧ acceleratedOrbit 15 32148 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32148 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32148) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32148.1, data_15_32148.2]

/-- Complete interval computation for depth 15, residue 32149. -/
theorem bounds_15_32149 : exactInterval 15 32149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32149 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32149) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32149 : oddCount 32149 15 = 4 ∧ acceleratedOrbit 15 32149 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32149 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32149) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32149.1, data_15_32149.2]

/-- Complete interval computation for depth 15, residue 32150. -/
theorem bounds_15_32150 : exactInterval 15 32150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32150 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32150) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32150 : oddCount 32150 15 = 9 ∧ acceleratedOrbit 15 32150 = 19318 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32150 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32150) = 3 ^ 9 * m + 19318 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32150.1, data_15_32150.2]

/-- Complete interval computation for depth 15, residue 32151. -/
theorem bounds_15_32151 : exactInterval 15 32151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32151 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32151) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32151 : oddCount 32151 15 = 9 ∧ acceleratedOrbit 15 32151 = 19318 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32151 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32151) = 3 ^ 9 * m + 19318 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32151.1, data_15_32151.2]

/-- Complete interval computation for depth 15, residue 32152. -/
theorem bounds_15_32152 : exactInterval 15 32152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32152 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32152) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32152 : oddCount 32152 15 = 4 ∧ acceleratedOrbit 15 32152 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32152 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32152) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32152.1, data_15_32152.2]

/-- Complete interval computation for depth 15, residue 32153. -/
theorem bounds_15_32153 : exactInterval 15 32153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32153 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32153) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32153 : oddCount 32153 15 = 9 ∧ acceleratedOrbit 15 32153 = 19318 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32153 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32153) = 3 ^ 9 * m + 19318 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32153.1, data_15_32153.2]

/-- Complete interval computation for depth 15, residue 32154. -/
theorem bounds_15_32154 : exactInterval 15 32154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32154 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32154) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32154 : oddCount 32154 15 = 4 ∧ acceleratedOrbit 15 32154 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32154 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32154) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32154.1, data_15_32154.2]

/-- Complete interval computation for depth 15, residue 32155. -/
theorem bounds_15_32155 : exactInterval 15 32155 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32155 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32155) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32155 : oddCount 32155 15 = 9 ∧ acceleratedOrbit 15 32155 = 19316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32155 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32155) = 3 ^ 9 * m + 19316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32155.1, data_15_32155.2]

/-- Complete interval computation for depth 15, residue 32156. -/
theorem bounds_15_32156 : exactInterval 15 32156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32156 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32156) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32156 : oddCount 32156 15 = 11 ∧ acceleratedOrbit 15 32156 = 173866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32156 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32156) = 3 ^ 11 * m + 173866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32156.1, data_15_32156.2]

/-- Complete interval computation for depth 15, residue 32157. -/
theorem bounds_15_32157 : exactInterval 15 32157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32157 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32157) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32157 : oddCount 32157 15 = 11 ∧ acceleratedOrbit 15 32157 = 173866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32157 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32157) = 3 ^ 11 * m + 173866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32157.1, data_15_32157.2]

/-- Complete interval computation for depth 15, residue 32158. -/
theorem bounds_15_32158 : exactInterval 15 32158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32158 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32158) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32158 : oddCount 32158 15 = 11 ∧ acceleratedOrbit 15 32158 = 173866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32158 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32158) = 3 ^ 11 * m + 173866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32158.1, data_15_32158.2]

/-- Complete interval computation for depth 15, residue 32159. -/
theorem bounds_15_32159 : exactInterval 15 32159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32159 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32159) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32159 : oddCount 32159 15 = 12 ∧ acceleratedOrbit 15 32159 = 521585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32159 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32159) = 3 ^ 12 * m + 521585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32159.1, data_15_32159.2]

/-- Complete interval computation for depth 15, residue 32160. -/
theorem bounds_15_32160 : exactInterval 15 32160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32160 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32160) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32160 : oddCount 32160 15 = 6 ∧ acceleratedOrbit 15 32160 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32160 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32160) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32160.1, data_15_32160.2]

/-- Complete interval computation for depth 15, residue 32161. -/
theorem bounds_15_32161 : exactInterval 15 32161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32161 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32161) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32161 : oddCount 32161 15 = 9 ∧ acceleratedOrbit 15 32161 = 19322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32161 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32161) = 3 ^ 9 * m + 19322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32161.1, data_15_32161.2]

/-- Complete interval computation for depth 15, residue 32162. -/
theorem bounds_15_32162 : exactInterval 15 32162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32162 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32162) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32162 : oddCount 32162 15 = 8 ∧ acceleratedOrbit 15 32162 = 6443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32162 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32162) = 3 ^ 8 * m + 6443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32162.1, data_15_32162.2]

/-- Complete interval computation for depth 15, residue 32163. -/
theorem bounds_15_32163 : exactInterval 15 32163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32163 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32163) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32163 : oddCount 32163 15 = 8 ∧ acceleratedOrbit 15 32163 = 6443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32163 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32163) = 3 ^ 8 * m + 6443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32163.1, data_15_32163.2]

/-- Complete interval computation for depth 15, residue 32164. -/
theorem bounds_15_32164 : exactInterval 15 32164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32164 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32164) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32164 : oddCount 32164 15 = 8 ∧ acceleratedOrbit 15 32164 = 6443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32164 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32164) = 3 ^ 8 * m + 6443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32164.1, data_15_32164.2]

/-- Complete interval computation for depth 15, residue 32165. -/
theorem bounds_15_32165 : exactInterval 15 32165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32165 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32165) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32165 : oddCount 32165 15 = 8 ∧ acceleratedOrbit 15 32165 = 6443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32165 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32165) = 3 ^ 8 * m + 6443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32165.1, data_15_32165.2]

/-- Complete interval computation for depth 15, residue 32166. -/
theorem bounds_15_32166 : exactInterval 15 32166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32166 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32166) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32166 : oddCount 32166 15 = 8 ∧ acceleratedOrbit 15 32166 = 6443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32166 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32166) = 3 ^ 8 * m + 6443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32166.1, data_15_32166.2]

/-- Complete interval computation for depth 15, residue 32167. -/
theorem bounds_15_32167 : exactInterval 15 32167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32167 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32167) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32167 : oddCount 32167 15 = 7 ∧ acceleratedOrbit 15 32167 = 2147 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32167 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32167) = 3 ^ 7 * m + 2147 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32167.1, data_15_32167.2]

/-- Complete interval computation for depth 15, residue 32168. -/
theorem bounds_15_32168 : exactInterval 15 32168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32168 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32168) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32168 : oddCount 32168 15 = 6 ∧ acceleratedOrbit 15 32168 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32168 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32168) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32168.1, data_15_32168.2]

/-- Complete interval computation for depth 15, residue 32169. -/
theorem bounds_15_32169 : exactInterval 15 32169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32169 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32169) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32169 : oddCount 32169 15 = 9 ∧ acceleratedOrbit 15 32169 = 19325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32169 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32169) = 3 ^ 9 * m + 19325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32169.1, data_15_32169.2]

/-- Complete interval computation for depth 15, residue 32170. -/
theorem bounds_15_32170 : exactInterval 15 32170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32170 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32170) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32170 : oddCount 32170 15 = 6 ∧ acceleratedOrbit 15 32170 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32170 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32170) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32170.1, data_15_32170.2]

/-- Complete interval computation for depth 15, residue 32171. -/
theorem bounds_15_32171 : exactInterval 15 32171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32171 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32171) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32171 : oddCount 32171 15 = 8 ∧ acceleratedOrbit 15 32171 = 6442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32171 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32171) = 3 ^ 8 * m + 6442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32171.1, data_15_32171.2]

/-- Complete interval computation for depth 15, residue 32172. -/
theorem bounds_15_32172 : exactInterval 15 32172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32172 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32172) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32172 : oddCount 32172 15 = 6 ∧ acceleratedOrbit 15 32172 = 716 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32172 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32172) = 3 ^ 6 * m + 716 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32172.1, data_15_32172.2]

/-- Complete interval computation for depth 15, residue 32173. -/
theorem bounds_15_32173 : exactInterval 15 32173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32173 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32173) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32173 : oddCount 32173 15 = 6 ∧ acceleratedOrbit 15 32173 = 716 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32173 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32173) = 3 ^ 6 * m + 716 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32173.1, data_15_32173.2]

/-- Complete interval computation for depth 15, residue 32174. -/
theorem bounds_15_32174 : exactInterval 15 32174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32174 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32174) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32174 : oddCount 32174 15 = 6 ∧ acceleratedOrbit 15 32174 = 716 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32174 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32174) = 3 ^ 6 * m + 716 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32174.1, data_15_32174.2]

/-- Complete interval computation for depth 15, residue 32175. -/
theorem bounds_15_32175 : exactInterval 15 32175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32175 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32175) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32175 : oddCount 32175 15 = 10 ∧ acceleratedOrbit 15 32175 = 57986 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32175 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32175) = 3 ^ 10 * m + 57986 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32175.1, data_15_32175.2]

/-- Complete interval computation for depth 15, residue 32176. -/
theorem bounds_15_32176 : exactInterval 15 32176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32176 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32176) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32176 : oddCount 32176 15 = 7 ∧ acceleratedOrbit 15 32176 = 2150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32176 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32176) = 3 ^ 7 * m + 2150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32176.1, data_15_32176.2]

/-- Complete interval computation for depth 15, residue 32177. -/
theorem bounds_15_32177 : exactInterval 15 32177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32177 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32177) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32177 : oddCount 32177 15 = 7 ∧ acceleratedOrbit 15 32177 = 2150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32177 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32177) = 3 ^ 7 * m + 2150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32177.1, data_15_32177.2]

end Collatz.Research.PassageAtlas.Batch0982
