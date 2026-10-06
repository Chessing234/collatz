import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0708

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 23166. -/
theorem bounds_15_23166 : exactInterval 15 23166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23166 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23166) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23166 : oddCount 23166 15 = 11 ∧ acceleratedOrbit 15 23166 = 125252 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23166 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23166) = 3 ^ 11 * m + 125252 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23166.1, data_15_23166.2]

/-- Complete interval computation for depth 15, residue 23167. -/
theorem bounds_15_23167 : exactInterval 15 23167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23167 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23167) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23167 : oddCount 23167 15 = 10 ∧ acceleratedOrbit 15 23167 = 41750 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23167 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23167) = 3 ^ 10 * m + 41750 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23167.1, data_15_23167.2]

/-- Complete interval computation for depth 15, residue 23168. -/
theorem bounds_15_23168 : exactInterval 15 23168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23168 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23168) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23168 : oddCount 23168 15 = 3 ∧ acceleratedOrbit 15 23168 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23168 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23168) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23168.1, data_15_23168.2]

/-- Complete interval computation for depth 15, residue 23169. -/
theorem bounds_15_23169 : exactInterval 15 23169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23169 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23169) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23169 : oddCount 23169 15 = 10 ∧ acceleratedOrbit 15 23169 = 41759 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23169 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23169) = 3 ^ 10 * m + 41759 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23169.1, data_15_23169.2]

/-- Complete interval computation for depth 15, residue 23170. -/
theorem bounds_15_23170 : exactInterval 15 23170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23170 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23170) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23170 : oddCount 23170 15 = 5 ∧ acceleratedOrbit 15 23170 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23170 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23170) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23170.1, data_15_23170.2]

/-- Complete interval computation for depth 15, residue 23171. -/
theorem bounds_15_23171 : exactInterval 15 23171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23171 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23171) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23171 : oddCount 23171 15 = 5 ∧ acceleratedOrbit 15 23171 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23171 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23171) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23171.1, data_15_23171.2]

/-- Complete interval computation for depth 15, residue 23172. -/
theorem bounds_15_23172 : exactInterval 15 23172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23172 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23172) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23172 : oddCount 23172 15 = 8 ∧ acceleratedOrbit 15 23172 = 4643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23172 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23172) = 3 ^ 8 * m + 4643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23172.1, data_15_23172.2]

/-- Complete interval computation for depth 15, residue 23173. -/
theorem bounds_15_23173 : exactInterval 15 23173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23173 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23173) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23173 : oddCount 23173 15 = 8 ∧ acceleratedOrbit 15 23173 = 4643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23173 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23173) = 3 ^ 8 * m + 4643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23173.1, data_15_23173.2]

/-- Complete interval computation for depth 15, residue 23174. -/
theorem bounds_15_23174 : exactInterval 15 23174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23174 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23174) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23174 : oddCount 23174 15 = 8 ∧ acceleratedOrbit 15 23174 = 4643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23174 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23174) = 3 ^ 8 * m + 4643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23174.1, data_15_23174.2]

/-- Complete interval computation for depth 15, residue 23175. -/
theorem bounds_15_23175 : exactInterval 15 23175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23175 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23175) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23175 : oddCount 23175 15 = 8 ∧ acceleratedOrbit 15 23175 = 4643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23175 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23175) = 3 ^ 8 * m + 4643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23175.1, data_15_23175.2]

/-- Complete interval computation for depth 15, residue 23176. -/
theorem bounds_15_23176 : exactInterval 15 23176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23176 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23176) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23176 : oddCount 23176 15 = 7 ∧ acceleratedOrbit 15 23176 = 1549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23176 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23176) = 3 ^ 7 * m + 1549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23176.1, data_15_23176.2]

/-- Complete interval computation for depth 15, residue 23177. -/
theorem bounds_15_23177 : exactInterval 15 23177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23177 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23177) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23177 : oddCount 23177 15 = 7 ∧ acceleratedOrbit 15 23177 = 1547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23177 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23177) = 3 ^ 7 * m + 1547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23177.1, data_15_23177.2]

/-- Complete interval computation for depth 15, residue 23178. -/
theorem bounds_15_23178 : exactInterval 15 23178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23178 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23178) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23178 : oddCount 23178 15 = 7 ∧ acceleratedOrbit 15 23178 = 1549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23178 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23178) = 3 ^ 7 * m + 1549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23178.1, data_15_23178.2]

/-- Complete interval computation for depth 15, residue 23179. -/
theorem bounds_15_23179 : exactInterval 15 23179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23179 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23179) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23179 : oddCount 23179 15 = 8 ∧ acceleratedOrbit 15 23179 = 4643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23179 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23179) = 3 ^ 8 * m + 4643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23179.1, data_15_23179.2]

/-- Complete interval computation for depth 15, residue 23180. -/
theorem bounds_15_23180 : exactInterval 15 23180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23180 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23180) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23180 : oddCount 23180 15 = 7 ∧ acceleratedOrbit 15 23180 = 1549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23180 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23180) = 3 ^ 7 * m + 1549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23180.1, data_15_23180.2]

/-- Complete interval computation for depth 15, residue 23181. -/
theorem bounds_15_23181 : exactInterval 15 23181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23181 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23181) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23181 : oddCount 23181 15 = 7 ∧ acceleratedOrbit 15 23181 = 1549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23181 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23181) = 3 ^ 7 * m + 1549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23181.1, data_15_23181.2]

/-- Complete interval computation for depth 15, residue 23182. -/
theorem bounds_15_23182 : exactInterval 15 23182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23182 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23182) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23182 : oddCount 23182 15 = 9 ∧ acceleratedOrbit 15 23182 = 13927 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23182 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23182) = 3 ^ 9 * m + 13927 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23182.1, data_15_23182.2]

/-- Complete interval computation for depth 15, residue 23183. -/
theorem bounds_15_23183 : exactInterval 15 23183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23183 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23183) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23183 : oddCount 23183 15 = 9 ∧ acceleratedOrbit 15 23183 = 13927 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23183 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23183) = 3 ^ 9 * m + 13927 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23183.1, data_15_23183.2]

/-- Complete interval computation for depth 15, residue 23184. -/
theorem bounds_15_23184 : exactInterval 15 23184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23184 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23184) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23184 : oddCount 23184 15 = 7 ∧ acceleratedOrbit 15 23184 = 1549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23184 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23184) = 3 ^ 7 * m + 1549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23184.1, data_15_23184.2]

/-- Complete interval computation for depth 15, residue 23185. -/
theorem bounds_15_23185 : exactInterval 15 23185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23185 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23185) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23185 : oddCount 23185 15 = 10 ∧ acceleratedOrbit 15 23185 = 41795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23185 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23185) = 3 ^ 10 * m + 41795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23185.1, data_15_23185.2]

/-- Complete interval computation for depth 15, residue 23186. -/
theorem bounds_15_23186 : exactInterval 15 23186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23186 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23186) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23186 : oddCount 23186 15 = 10 ∧ acceleratedOrbit 15 23186 = 41795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23186 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23186) = 3 ^ 10 * m + 41795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23186.1, data_15_23186.2]

/-- Complete interval computation for depth 15, residue 23187. -/
theorem bounds_15_23187 : exactInterval 15 23187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23187 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23187) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23187 : oddCount 23187 15 = 10 ∧ acceleratedOrbit 15 23187 = 41795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23187 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23187) = 3 ^ 10 * m + 41795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23187.1, data_15_23187.2]

/-- Complete interval computation for depth 15, residue 23188. -/
theorem bounds_15_23188 : exactInterval 15 23188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23188 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23188) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23188 : oddCount 23188 15 = 7 ∧ acceleratedOrbit 15 23188 = 1549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23188 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23188) = 3 ^ 7 * m + 1549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23188.1, data_15_23188.2]

/-- Complete interval computation for depth 15, residue 23189. -/
theorem bounds_15_23189 : exactInterval 15 23189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23189 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23189) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23189 : oddCount 23189 15 = 7 ∧ acceleratedOrbit 15 23189 = 1549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23189 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23189) = 3 ^ 7 * m + 1549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23189.1, data_15_23189.2]

/-- Complete interval computation for depth 15, residue 23190. -/
theorem bounds_15_23190 : exactInterval 15 23190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23190 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23190) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23190 : oddCount 23190 15 = 7 ∧ acceleratedOrbit 15 23190 = 1549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23190 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23190) = 3 ^ 7 * m + 1549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23190.1, data_15_23190.2]

/-- Complete interval computation for depth 15, residue 23191. -/
theorem bounds_15_23191 : exactInterval 15 23191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23191 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23191) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23191 : oddCount 23191 15 = 7 ∧ acceleratedOrbit 15 23191 = 1549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23191 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23191) = 3 ^ 7 * m + 1549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23191.1, data_15_23191.2]

/-- Complete interval computation for depth 15, residue 23192. -/
theorem bounds_15_23192 : exactInterval 15 23192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23192 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23192) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23192 : oddCount 23192 15 = 7 ∧ acceleratedOrbit 15 23192 = 1549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23192 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23192) = 3 ^ 7 * m + 1549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23192.1, data_15_23192.2]

/-- Complete interval computation for depth 15, residue 23193. -/
theorem bounds_15_23193 : exactInterval 15 23193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23193 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23193) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23193 : oddCount 23193 15 = 8 ∧ acceleratedOrbit 15 23193 = 4645 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23193 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23193) = 3 ^ 8 * m + 4645 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23193.1, data_15_23193.2]

/-- Complete interval computation for depth 15, residue 23194. -/
theorem bounds_15_23194 : exactInterval 15 23194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23194 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23194) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23194 : oddCount 23194 15 = 7 ∧ acceleratedOrbit 15 23194 = 1549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23194 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23194) = 3 ^ 7 * m + 1549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23194.1, data_15_23194.2]

/-- Complete interval computation for depth 15, residue 23195. -/
theorem bounds_15_23195 : exactInterval 15 23195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23195 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23195) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23195 : oddCount 23195 15 = 10 ∧ acceleratedOrbit 15 23195 = 41801 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23195 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23195) = 3 ^ 10 * m + 41801 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23195.1, data_15_23195.2]

/-- Complete interval computation for depth 15, residue 23196. -/
theorem bounds_15_23196 : exactInterval 15 23196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23196 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23196) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23196 : oddCount 23196 15 = 8 ∧ acceleratedOrbit 15 23196 = 4646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23196 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23196) = 3 ^ 8 * m + 4646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23196.1, data_15_23196.2]

/-- Complete interval computation for depth 15, residue 23197. -/
theorem bounds_15_23197 : exactInterval 15 23197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23197 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23197) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23197 : oddCount 23197 15 = 8 ∧ acceleratedOrbit 15 23197 = 4646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23197 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23197) = 3 ^ 8 * m + 4646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23197.1, data_15_23197.2]

/-- Complete interval computation for depth 15, residue 23198. -/
theorem bounds_15_23198 : exactInterval 15 23198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23198 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23198) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23198 : oddCount 23198 15 = 8 ∧ acceleratedOrbit 15 23198 = 4646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23198 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23198) = 3 ^ 8 * m + 4646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23198.1, data_15_23198.2]

end Collatz.Research.PassageAtlas.Batch0708
