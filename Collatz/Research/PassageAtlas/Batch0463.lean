import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0463

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 15138. -/
theorem bounds_15_15138 : exactInterval 15 15138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15138 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15138) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15138 : oddCount 15138 15 = 7 ∧ acceleratedOrbit 15 15138 = 1012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15138 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15138) = 3 ^ 7 * m + 1012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15138.1, data_15_15138.2]

/-- Complete interval computation for depth 15, residue 15139. -/
theorem bounds_15_15139 : exactInterval 15 15139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15139 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15139) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15139 : oddCount 15139 15 = 7 ∧ acceleratedOrbit 15 15139 = 1012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15139 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15139) = 3 ^ 7 * m + 1012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15139.1, data_15_15139.2]

/-- Complete interval computation for depth 15, residue 15140. -/
theorem bounds_15_15140 : exactInterval 15 15140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15140 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15140) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15140 : oddCount 15140 15 = 7 ∧ acceleratedOrbit 15 15140 = 1012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15140 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15140) = 3 ^ 7 * m + 1012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15140.1, data_15_15140.2]

/-- Complete interval computation for depth 15, residue 15141. -/
theorem bounds_15_15141 : exactInterval 15 15141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15141 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15141) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15141 : oddCount 15141 15 = 7 ∧ acceleratedOrbit 15 15141 = 1012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15141 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15141) = 3 ^ 7 * m + 1012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15141.1, data_15_15141.2]

/-- Complete interval computation for depth 15, residue 15142. -/
theorem bounds_15_15142 : exactInterval 15 15142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15142 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15142) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15142 : oddCount 15142 15 = 7 ∧ acceleratedOrbit 15 15142 = 1012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15142 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15142) = 3 ^ 7 * m + 1012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15142.1, data_15_15142.2]

/-- Complete interval computation for depth 15, residue 15143. -/
theorem bounds_15_15143 : exactInterval 15 15143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15143 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15143) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15143 : oddCount 15143 15 = 10 ∧ acceleratedOrbit 15 15143 = 27292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15143 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15143) = 3 ^ 10 * m + 27292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15143.1, data_15_15143.2]

/-- Complete interval computation for depth 15, residue 15144. -/
theorem bounds_15_15144 : exactInterval 15 15144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15144 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15144) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15144 : oddCount 15144 15 = 4 ∧ acceleratedOrbit 15 15144 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15144 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15144) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15144.1, data_15_15144.2]

/-- Complete interval computation for depth 15, residue 15145. -/
theorem bounds_15_15145 : exactInterval 15 15145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15145 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15145) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15145 : oddCount 15145 15 = 11 ∧ acceleratedOrbit 15 15145 = 81890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15145 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15145) = 3 ^ 11 * m + 81890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15145.1, data_15_15145.2]

/-- Complete interval computation for depth 15, residue 15146. -/
theorem bounds_15_15146 : exactInterval 15 15146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15146 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15146) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15146 : oddCount 15146 15 = 4 ∧ acceleratedOrbit 15 15146 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15146 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15146) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15146.1, data_15_15146.2]

/-- Complete interval computation for depth 15, residue 15147. -/
theorem bounds_15_15147 : exactInterval 15 15147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15147 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15147) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15147 : oddCount 15147 15 = 8 ∧ acceleratedOrbit 15 15147 = 3034 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15147 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15147) = 3 ^ 8 * m + 3034 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15147.1, data_15_15147.2]

/-- Complete interval computation for depth 15, residue 15148. -/
theorem bounds_15_15148 : exactInterval 15 15148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15148 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15148) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15148 : oddCount 15148 15 = 8 ∧ acceleratedOrbit 15 15148 = 3037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15148 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15148) = 3 ^ 8 * m + 3037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15148.1, data_15_15148.2]

/-- Complete interval computation for depth 15, residue 15149. -/
theorem bounds_15_15149 : exactInterval 15 15149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15149 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15149) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15149 : oddCount 15149 15 = 8 ∧ acceleratedOrbit 15 15149 = 3037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15149 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15149) = 3 ^ 8 * m + 3037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15149.1, data_15_15149.2]

/-- Complete interval computation for depth 15, residue 15150. -/
theorem bounds_15_15150 : exactInterval 15 15150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15150 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15150) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15150 : oddCount 15150 15 = 8 ∧ acceleratedOrbit 15 15150 = 3037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15150 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15150) = 3 ^ 8 * m + 3037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15150.1, data_15_15150.2]

/-- Complete interval computation for depth 15, residue 15151. -/
theorem bounds_15_15151 : exactInterval 15 15151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15151 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15151) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15151 : oddCount 15151 15 = 8 ∧ acceleratedOrbit 15 15151 = 3034 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15151 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15151) = 3 ^ 8 * m + 3034 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15151.1, data_15_15151.2]

/-- Complete interval computation for depth 15, residue 15152. -/
theorem bounds_15_15152 : exactInterval 15 15152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15152 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15152) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15152 : oddCount 15152 15 = 4 ∧ acceleratedOrbit 15 15152 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15152 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15152) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15152.1, data_15_15152.2]

/-- Complete interval computation for depth 15, residue 15153. -/
theorem bounds_15_15153 : exactInterval 15 15153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15153 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15153) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15153 : oddCount 15153 15 = 8 ∧ acceleratedOrbit 15 15153 = 3037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15153 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15153) = 3 ^ 8 * m + 3037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15153.1, data_15_15153.2]

/-- Complete interval computation for depth 15, residue 15154. -/
theorem bounds_15_15154 : exactInterval 15 15154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15154 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15154) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15154 : oddCount 15154 15 = 8 ∧ acceleratedOrbit 15 15154 = 3037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15154 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15154) = 3 ^ 8 * m + 3037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15154.1, data_15_15154.2]

/-- Complete interval computation for depth 15, residue 15155. -/
theorem bounds_15_15155 : exactInterval 15 15155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15155 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15155) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15155 : oddCount 15155 15 = 8 ∧ acceleratedOrbit 15 15155 = 3037 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15155 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15155) = 3 ^ 8 * m + 3037 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15155.1, data_15_15155.2]

/-- Complete interval computation for depth 15, residue 15156. -/
theorem bounds_15_15156 : exactInterval 15 15156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15156 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15156) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15156 : oddCount 15156 15 = 4 ∧ acceleratedOrbit 15 15156 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15156 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15156) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15156.1, data_15_15156.2]

/-- Complete interval computation for depth 15, residue 15157. -/
theorem bounds_15_15157 : exactInterval 15 15157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15157 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15157) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15157 : oddCount 15157 15 = 4 ∧ acceleratedOrbit 15 15157 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15157 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15157) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15157.1, data_15_15157.2]

/-- Complete interval computation for depth 15, residue 15158. -/
theorem bounds_15_15158 : exactInterval 15 15158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15158 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15158) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15158 : oddCount 15158 15 = 10 ∧ acceleratedOrbit 15 15158 = 27323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15158 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15158) = 3 ^ 10 * m + 27323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15158.1, data_15_15158.2]

/-- Complete interval computation for depth 15, residue 15159. -/
theorem bounds_15_15159 : exactInterval 15 15159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15159 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15159) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15159 : oddCount 15159 15 = 10 ∧ acceleratedOrbit 15 15159 = 27323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15159 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15159) = 3 ^ 10 * m + 27323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15159.1, data_15_15159.2]

/-- Complete interval computation for depth 15, residue 15160. -/
theorem bounds_15_15160 : exactInterval 15 15160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15160 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15160) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15160 : oddCount 15160 15 = 10 ∧ acceleratedOrbit 15 15160 = 27337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15160 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15160) = 3 ^ 10 * m + 27337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15160.1, data_15_15160.2]

/-- Complete interval computation for depth 15, residue 15161. -/
theorem bounds_15_15161 : exactInterval 15 15161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15161 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15161) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15161 : oddCount 15161 15 = 9 ∧ acceleratedOrbit 15 15161 = 9109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15161 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15161) = 3 ^ 9 * m + 9109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15161.1, data_15_15161.2]

/-- Complete interval computation for depth 15, residue 15162. -/
theorem bounds_15_15162 : exactInterval 15 15162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15162 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15162) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15162 : oddCount 15162 15 = 10 ∧ acceleratedOrbit 15 15162 = 27337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15162 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15162) = 3 ^ 10 * m + 27337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15162.1, data_15_15162.2]

/-- Complete interval computation for depth 15, residue 15163. -/
theorem bounds_15_15163 : exactInterval 15 15163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15163 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15163) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15163 : oddCount 15163 15 = 9 ∧ acceleratedOrbit 15 15163 = 9112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15163 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15163) = 3 ^ 9 * m + 9112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15163.1, data_15_15163.2]

/-- Complete interval computation for depth 15, residue 15164. -/
theorem bounds_15_15164 : exactInterval 15 15164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15164 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15164) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15164 : oddCount 15164 15 = 10 ∧ acceleratedOrbit 15 15164 = 27337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15164 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15164) = 3 ^ 10 * m + 27337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15164.1, data_15_15164.2]

/-- Complete interval computation for depth 15, residue 15165. -/
theorem bounds_15_15165 : exactInterval 15 15165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15165 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15165) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15165 : oddCount 15165 15 = 10 ∧ acceleratedOrbit 15 15165 = 27337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15165 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15165) = 3 ^ 10 * m + 27337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15165.1, data_15_15165.2]

/-- Complete interval computation for depth 15, residue 15166. -/
theorem bounds_15_15166 : exactInterval 15 15166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15166 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15166) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15166 : oddCount 15166 15 = 10 ∧ acceleratedOrbit 15 15166 = 27334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15166 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15166) = 3 ^ 10 * m + 27334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15166.1, data_15_15166.2]

/-- Complete interval computation for depth 15, residue 15167. -/
theorem bounds_15_15167 : exactInterval 15 15167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15167 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15167) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15167 : oddCount 15167 15 = 10 ∧ acceleratedOrbit 15 15167 = 27334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15167 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15167) = 3 ^ 10 * m + 27334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15167.1, data_15_15167.2]

/-- Complete interval computation for depth 15, residue 15168. -/
theorem bounds_15_15168 : exactInterval 15 15168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15168 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15168) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15168 : oddCount 15168 15 = 4 ∧ acceleratedOrbit 15 15168 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15168 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15168) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15168.1, data_15_15168.2]

/-- Complete interval computation for depth 15, residue 15169. -/
theorem bounds_15_15169 : exactInterval 15 15169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15169 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15169) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15169 : oddCount 15169 15 = 4 ∧ acceleratedOrbit 15 15169 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15169 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15169) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15169.1, data_15_15169.2]

/-- Complete interval computation for depth 15, residue 15170. -/
theorem bounds_15_15170 : exactInterval 15 15170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15170 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15170) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15170 : oddCount 15170 15 = 7 ∧ acceleratedOrbit 15 15170 = 1013 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15170 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15170) = 3 ^ 7 * m + 1013 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15170.1, data_15_15170.2]

end Collatz.Research.PassageAtlas.Batch0463
