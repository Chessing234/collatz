import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0145

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1187. -/
theorem bounds_11_1187 : exactInterval 11 1187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1187 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1187) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1187 : oddCount 1187 11 = 6 ∧ acceleratedOrbit 11 1187 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1187 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1187) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1187.1, data_11_1187.2]

/-- Complete interval computation for depth 11, residue 1188. -/
theorem bounds_11_1188 : exactInterval 11 1188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1188 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1188) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1188 : oddCount 1188 11 = 6 ∧ acceleratedOrbit 11 1188 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1188 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1188) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1188.1, data_11_1188.2]

/-- Complete interval computation for depth 11, residue 1189. -/
theorem bounds_11_1189 : exactInterval 11 1189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1189 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1189) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1189 : oddCount 1189 11 = 6 ∧ acceleratedOrbit 11 1189 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1189 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1189) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1189.1, data_11_1189.2]

/-- Complete interval computation for depth 11, residue 1190. -/
theorem bounds_11_1190 : exactInterval 11 1190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1190 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1190) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1190 : oddCount 1190 11 = 6 ∧ acceleratedOrbit 11 1190 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1190 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1190) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1190.1, data_11_1190.2]

/-- Complete interval computation for depth 11, residue 1191. -/
theorem bounds_11_1191 : exactInterval 11 1191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1191 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1191) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1191 : oddCount 1191 11 = 8 ∧ acceleratedOrbit 11 1191 = 3820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1191 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1191) = 3 ^ 8 * m + 3820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1191.1, data_11_1191.2]

/-- Complete interval computation for depth 11, residue 1192. -/
theorem bounds_11_1192 : exactInterval 11 1192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1192 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1192) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1192 : oddCount 1192 11 = 3 ∧ acceleratedOrbit 11 1192 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1192 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1192) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1192.1, data_11_1192.2]

/-- Complete interval computation for depth 11, residue 1193. -/
theorem bounds_11_1193 : exactInterval 11 1193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1193 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1193) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1193 : oddCount 1193 11 = 8 ∧ acceleratedOrbit 11 1193 = 3827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1193 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1193) = 3 ^ 8 * m + 3827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1193.1, data_11_1193.2]

/-- Complete interval computation for depth 11, residue 1194. -/
theorem bounds_11_1194 : exactInterval 11 1194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1194 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1194) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1194 : oddCount 1194 11 = 3 ∧ acceleratedOrbit 11 1194 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1194 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1194) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1194.1, data_11_1194.2]

/-- Complete interval computation for depth 11, residue 1195. -/
theorem bounds_11_1195 : exactInterval 11 1195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1195 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1195) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1195 : oddCount 1195 11 = 5 ∧ acceleratedOrbit 11 1195 = 142 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1195 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1195) = 3 ^ 5 * m + 142 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1195.1, data_11_1195.2]

/-- Complete interval computation for depth 11, residue 1196. -/
theorem bounds_11_1196 : exactInterval 11 1196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1196 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1196) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1196 : oddCount 1196 11 = 5 ∧ acceleratedOrbit 11 1196 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1196 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1196) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1196.1, data_11_1196.2]

/-- Complete interval computation for depth 11, residue 1197. -/
theorem bounds_11_1197 : exactInterval 11 1197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1197 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1197) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1197 : oddCount 1197 11 = 5 ∧ acceleratedOrbit 11 1197 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1197 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1197) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1197.1, data_11_1197.2]

/-- Complete interval computation for depth 11, residue 1198. -/
theorem bounds_11_1198 : exactInterval 11 1198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1198 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1198) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1198 : oddCount 1198 11 = 5 ∧ acceleratedOrbit 11 1198 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1198 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1198) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1198.1, data_11_1198.2]

/-- Complete interval computation for depth 11, residue 1199. -/
theorem bounds_11_1199 : exactInterval 11 1199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1199 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1199) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1199 : oddCount 1199 11 = 7 ∧ acceleratedOrbit 11 1199 = 1282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1199 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1199) = 3 ^ 7 * m + 1282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1199.1, data_11_1199.2]

/-- Complete interval computation for depth 11, residue 1200. -/
theorem bounds_11_1200 : exactInterval 11 1200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1200 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1200) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1200 : oddCount 1200 11 = 3 ∧ acceleratedOrbit 11 1200 = 16 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1200 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1200) = 3 ^ 3 * m + 16 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1200.1, data_11_1200.2]

/-- Complete interval computation for depth 11, residue 1201. -/
theorem bounds_11_1201 : exactInterval 11 1201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1201 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1201) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1201 : oddCount 1201 11 = 6 ∧ acceleratedOrbit 11 1201 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1201 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1201) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1201.1, data_11_1201.2]

/-- Complete interval computation for depth 11, residue 1202. -/
theorem bounds_11_1202 : exactInterval 11 1202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1202 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1202) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1202 : oddCount 1202 11 = 6 ∧ acceleratedOrbit 11 1202 = 431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1202 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1202) = 3 ^ 6 * m + 431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1202.1, data_11_1202.2]

end Collatz.Research.StoppingAtlas.Batch0145
