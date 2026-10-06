import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0403

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 13172. -/
theorem bounds_15_13172 : exactInterval 15 13172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13172 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13172) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13172 : oddCount 13172 15 = 7 ∧ acceleratedOrbit 15 13172 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13172 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13172) = 3 ^ 7 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13172.1, data_15_13172.2]

/-- Complete interval computation for depth 15, residue 13173. -/
theorem bounds_15_13173 : exactInterval 15 13173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13173 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13173) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13173 : oddCount 13173 15 = 7 ∧ acceleratedOrbit 15 13173 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13173 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13173) = 3 ^ 7 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13173.1, data_15_13173.2]

/-- Complete interval computation for depth 15, residue 13174. -/
theorem bounds_15_13174 : exactInterval 15 13174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13174 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13174) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13174 : oddCount 13174 15 = 8 ∧ acceleratedOrbit 15 13174 = 2639 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13174 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13174) = 3 ^ 8 * m + 2639 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13174.1, data_15_13174.2]

/-- Complete interval computation for depth 15, residue 13175. -/
theorem bounds_15_13175 : exactInterval 15 13175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13175 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13175) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13175 : oddCount 13175 15 = 8 ∧ acceleratedOrbit 15 13175 = 2639 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13175 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13175) = 3 ^ 8 * m + 2639 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13175.1, data_15_13175.2]

/-- Complete interval computation for depth 15, residue 13176. -/
theorem bounds_15_13176 : exactInterval 15 13176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13176 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13176) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13176 : oddCount 13176 15 = 7 ∧ acceleratedOrbit 15 13176 = 880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13176 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13176) = 3 ^ 7 * m + 880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13176.1, data_15_13176.2]

/-- Complete interval computation for depth 15, residue 13177. -/
theorem bounds_15_13177 : exactInterval 15 13177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13177 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13177) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13177 : oddCount 13177 15 = 10 ∧ acceleratedOrbit 15 13177 = 23750 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13177 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13177) = 3 ^ 10 * m + 23750 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13177.1, data_15_13177.2]

/-- Complete interval computation for depth 15, residue 13178. -/
theorem bounds_15_13178 : exactInterval 15 13178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13178 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13178) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13178 : oddCount 13178 15 = 7 ∧ acceleratedOrbit 15 13178 = 880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13178 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13178) = 3 ^ 7 * m + 880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13178.1, data_15_13178.2]

/-- Complete interval computation for depth 15, residue 13179. -/
theorem bounds_15_13179 : exactInterval 15 13179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13179 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13179) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13179 : oddCount 13179 15 = 10 ∧ acceleratedOrbit 15 13179 = 23753 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13179 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13179) = 3 ^ 10 * m + 23753 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13179.1, data_15_13179.2]

/-- Complete interval computation for depth 15, residue 13180. -/
theorem bounds_15_13180 : exactInterval 15 13180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13180 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13180) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13180 : oddCount 13180 15 = 7 ∧ acceleratedOrbit 15 13180 = 880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13180 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13180) = 3 ^ 7 * m + 880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13180.1, data_15_13180.2]

/-- Complete interval computation for depth 15, residue 13181. -/
theorem bounds_15_13181 : exactInterval 15 13181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13181 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13181) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13181 : oddCount 13181 15 = 7 ∧ acceleratedOrbit 15 13181 = 880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13181 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13181) = 3 ^ 7 * m + 880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13181.1, data_15_13181.2]

/-- Complete interval computation for depth 15, residue 13182. -/
theorem bounds_15_13182 : exactInterval 15 13182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13182 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13182) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13182 : oddCount 13182 15 = 11 ∧ acceleratedOrbit 15 13182 = 71275 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13182 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13182) = 3 ^ 11 * m + 71275 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13182.1, data_15_13182.2]

/-- Complete interval computation for depth 15, residue 13183. -/
theorem bounds_15_13183 : exactInterval 15 13183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13183 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13183) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13183 : oddCount 13183 15 = 11 ∧ acceleratedOrbit 15 13183 = 71275 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13183 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13183) = 3 ^ 11 * m + 71275 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13183.1, data_15_13183.2]

/-- Complete interval computation for depth 15, residue 13184. -/
theorem bounds_15_13184 : exactInterval 15 13184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13184 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13184) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13184 : oddCount 13184 15 = 7 ∧ acceleratedOrbit 15 13184 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13184 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13184) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13184.1, data_15_13184.2]

/-- Complete interval computation for depth 15, residue 13185. -/
theorem bounds_15_13185 : exactInterval 15 13185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13185 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13185) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13185 : oddCount 13185 15 = 8 ∧ acceleratedOrbit 15 13185 = 2641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13185 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13185) = 3 ^ 8 * m + 2641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13185.1, data_15_13185.2]

/-- Complete interval computation for depth 15, residue 13186. -/
theorem bounds_15_13186 : exactInterval 15 13186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13186 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13186) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13186 : oddCount 13186 15 = 9 ∧ acceleratedOrbit 15 13186 = 7928 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13186 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13186) = 3 ^ 9 * m + 7928 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13186.1, data_15_13186.2]

/-- Complete interval computation for depth 15, residue 13187. -/
theorem bounds_15_13187 : exactInterval 15 13187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13187 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13187) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13187 : oddCount 13187 15 = 9 ∧ acceleratedOrbit 15 13187 = 7928 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13187 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13187) = 3 ^ 9 * m + 7928 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13187.1, data_15_13187.2]

/-- Complete interval computation for depth 15, residue 13188. -/
theorem bounds_15_13188 : exactInterval 15 13188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13188 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13188) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13188 : oddCount 13188 15 = 9 ∧ acceleratedOrbit 15 13188 = 7928 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13188 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13188) = 3 ^ 9 * m + 7928 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13188.1, data_15_13188.2]

/-- Complete interval computation for depth 15, residue 13189. -/
theorem bounds_15_13189 : exactInterval 15 13189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13189 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13189) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13189 : oddCount 13189 15 = 9 ∧ acceleratedOrbit 15 13189 = 7928 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13189 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13189) = 3 ^ 9 * m + 7928 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13189.1, data_15_13189.2]

/-- Complete interval computation for depth 15, residue 13190. -/
theorem bounds_15_13190 : exactInterval 15 13190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13190 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13190) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13190 : oddCount 13190 15 = 9 ∧ acceleratedOrbit 15 13190 = 7928 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13190 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13190) = 3 ^ 9 * m + 7928 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13190.1, data_15_13190.2]

/-- Complete interval computation for depth 15, residue 13191. -/
theorem bounds_15_13191 : exactInterval 15 13191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13191 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13191) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13191 : oddCount 13191 15 = 9 ∧ acceleratedOrbit 15 13191 = 7928 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13191 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13191) = 3 ^ 9 * m + 7928 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13191.1, data_15_13191.2]

/-- Complete interval computation for depth 15, residue 13192. -/
theorem bounds_15_13192 : exactInterval 15 13192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13192 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13192) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13192 : oddCount 13192 15 = 3 ∧ acceleratedOrbit 15 13192 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13192 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13192) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13192.1, data_15_13192.2]

/-- Complete interval computation for depth 15, residue 13193. -/
theorem bounds_15_13193 : exactInterval 15 13193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13193 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13193) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13193 : oddCount 13193 15 = 8 ∧ acceleratedOrbit 15 13193 = 2642 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13193 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13193) = 3 ^ 8 * m + 2642 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13193.1, data_15_13193.2]

/-- Complete interval computation for depth 15, residue 13194. -/
theorem bounds_15_13194 : exactInterval 15 13194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13194 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13194) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13194 : oddCount 13194 15 = 3 ∧ acceleratedOrbit 15 13194 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13194 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13194) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13194.1, data_15_13194.2]

/-- Complete interval computation for depth 15, residue 13195. -/
theorem bounds_15_13195 : exactInterval 15 13195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13195 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13195) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13195 : oddCount 13195 15 = 11 ∧ acceleratedOrbit 15 13195 = 71351 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13195 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13195) = 3 ^ 11 * m + 71351 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13195.1, data_15_13195.2]

/-- Complete interval computation for depth 15, residue 13196. -/
theorem bounds_15_13196 : exactInterval 15 13196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13196 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13196) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13196 : oddCount 13196 15 = 3 ∧ acceleratedOrbit 15 13196 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13196 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13196) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13196.1, data_15_13196.2]

/-- Complete interval computation for depth 15, residue 13197. -/
theorem bounds_15_13197 : exactInterval 15 13197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13197 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13197) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13197 : oddCount 13197 15 = 3 ∧ acceleratedOrbit 15 13197 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13197 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13197) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13197.1, data_15_13197.2]

/-- Complete interval computation for depth 15, residue 13198. -/
theorem bounds_15_13198 : exactInterval 15 13198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13198 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13198) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13198 : oddCount 13198 15 = 9 ∧ acceleratedOrbit 15 13198 = 7931 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13198 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13198) = 3 ^ 9 * m + 7931 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13198.1, data_15_13198.2]

/-- Complete interval computation for depth 15, residue 13199. -/
theorem bounds_15_13199 : exactInterval 15 13199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13199 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13199) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13199 : oddCount 13199 15 = 9 ∧ acceleratedOrbit 15 13199 = 7931 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13199 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13199) = 3 ^ 9 * m + 7931 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13199.1, data_15_13199.2]

/-- Complete interval computation for depth 15, residue 13200. -/
theorem bounds_15_13200 : exactInterval 15 13200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13200 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13200) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13200 : oddCount 13200 15 = 7 ∧ acceleratedOrbit 15 13200 = 884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13200 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13200) = 3 ^ 7 * m + 884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13200.1, data_15_13200.2]

/-- Complete interval computation for depth 15, residue 13201. -/
theorem bounds_15_13201 : exactInterval 15 13201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13201 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13201) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13201 : oddCount 13201 15 = 9 ∧ acceleratedOrbit 15 13201 = 7937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13201 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13201) = 3 ^ 9 * m + 7937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13201.1, data_15_13201.2]

/-- Complete interval computation for depth 15, residue 13202. -/
theorem bounds_15_13202 : exactInterval 15 13202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13202 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13202) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13202 : oddCount 13202 15 = 9 ∧ acceleratedOrbit 15 13202 = 7937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13202 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13202) = 3 ^ 9 * m + 7937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13202.1, data_15_13202.2]

/-- Complete interval computation for depth 15, residue 13203. -/
theorem bounds_15_13203 : exactInterval 15 13203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13203 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13203) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13203 : oddCount 13203 15 = 9 ∧ acceleratedOrbit 15 13203 = 7937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13203 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13203) = 3 ^ 9 * m + 7937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13203.1, data_15_13203.2]

/-- Complete interval computation for depth 15, residue 13204. -/
theorem bounds_15_13204 : exactInterval 15 13204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13204 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13204) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13204 : oddCount 13204 15 = 7 ∧ acceleratedOrbit 15 13204 = 884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13204 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13204) = 3 ^ 7 * m + 884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13204.1, data_15_13204.2]

end Collatz.Research.PassageAtlas.Batch0403
