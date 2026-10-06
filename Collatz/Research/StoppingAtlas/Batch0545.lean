import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0545

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1187. -/
theorem bounds_13_1187 : exactInterval 13 1187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1187 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1187) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1187 : oddCount 1187 13 = 7 ∧ acceleratedOrbit 13 1187 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1187 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1187) = 3 ^ 7 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1187.1, data_13_1187.2]

/-- Complete interval computation for depth 13, residue 1188. -/
theorem bounds_13_1188 : exactInterval 13 1188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1188 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1188) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1188 : oddCount 1188 13 = 7 ∧ acceleratedOrbit 13 1188 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1188 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1188) = 3 ^ 7 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1188.1, data_13_1188.2]

/-- Complete interval computation for depth 13, residue 1189. -/
theorem bounds_13_1189 : exactInterval 13 1189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1189 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1189) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1189 : oddCount 1189 13 = 7 ∧ acceleratedOrbit 13 1189 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1189 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1189) = 3 ^ 7 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1189.1, data_13_1189.2]

/-- Complete interval computation for depth 13, residue 1190. -/
theorem bounds_13_1190 : exactInterval 13 1190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1190 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1190) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1190 : oddCount 1190 13 = 7 ∧ acceleratedOrbit 13 1190 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1190 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1190) = 3 ^ 7 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1190.1, data_13_1190.2]

/-- Complete interval computation for depth 13, residue 1191. -/
theorem bounds_13_1191 : exactInterval 13 1191 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1191 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1191) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1191 : oddCount 1191 13 = 8 ∧ acceleratedOrbit 13 1191 = 955 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1191 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1191) = 3 ^ 8 * m + 955 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1191.1, data_13_1191.2]

/-- Complete interval computation for depth 13, residue 1192. -/
theorem bounds_13_1192 : exactInterval 13 1192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1192 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1192) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1192 : oddCount 1192 13 = 4 ∧ acceleratedOrbit 13 1192 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1192 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1192) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1192.1, data_13_1192.2]

/-- Complete interval computation for depth 13, residue 1193. -/
theorem bounds_13_1193 : exactInterval 13 1193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1193 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1193) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1193 : oddCount 1193 13 = 10 ∧ acceleratedOrbit 13 1193 = 8612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1193 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1193) = 3 ^ 10 * m + 8612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1193.1, data_13_1193.2]

/-- Complete interval computation for depth 13, residue 1194. -/
theorem bounds_13_1194 : exactInterval 13 1194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1194 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1194) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1194 : oddCount 1194 13 = 4 ∧ acceleratedOrbit 13 1194 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1194 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1194) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1194.1, data_13_1194.2]

/-- Complete interval computation for depth 13, residue 1195. -/
theorem bounds_13_1195 : exactInterval 13 1195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1195 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1195) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1195 : oddCount 1195 13 = 6 ∧ acceleratedOrbit 13 1195 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1195 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1195) = 3 ^ 6 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1195.1, data_13_1195.2]

/-- Complete interval computation for depth 13, residue 1196. -/
theorem bounds_13_1196 : exactInterval 13 1196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1196 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1196) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1196 : oddCount 1196 13 = 7 ∧ acceleratedOrbit 13 1196 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1196 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1196) = 3 ^ 7 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1196.1, data_13_1196.2]

/-- Complete interval computation for depth 13, residue 1197. -/
theorem bounds_13_1197 : exactInterval 13 1197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1197 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1197) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1197 : oddCount 1197 13 = 7 ∧ acceleratedOrbit 13 1197 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1197 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1197) = 3 ^ 7 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1197.1, data_13_1197.2]

/-- Complete interval computation for depth 13, residue 1198. -/
theorem bounds_13_1198 : exactInterval 13 1198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1198 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1198) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1198 : oddCount 1198 13 = 7 ∧ acceleratedOrbit 13 1198 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1198 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1198) = 3 ^ 7 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1198.1, data_13_1198.2]

/-- Complete interval computation for depth 13, residue 1199. -/
theorem bounds_13_1199 : exactInterval 13 1199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1199 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1199) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1199 : oddCount 1199 13 = 8 ∧ acceleratedOrbit 13 1199 = 962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1199 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1199) = 3 ^ 8 * m + 962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1199.1, data_13_1199.2]

/-- Complete interval computation for depth 13, residue 1200. -/
theorem bounds_13_1200 : exactInterval 13 1200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1200 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1200) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1200 : oddCount 1200 13 = 3 ∧ acceleratedOrbit 13 1200 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1200 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1200) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1200.1, data_13_1200.2]

/-- Complete interval computation for depth 13, residue 1201. -/
theorem bounds_13_1201 : exactInterval 13 1201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1201 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1201) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1201 : oddCount 1201 13 = 8 ∧ acceleratedOrbit 13 1201 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1201 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1201) = 3 ^ 8 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1201.1, data_13_1201.2]

/-- Complete interval computation for depth 13, residue 1202. -/
theorem bounds_13_1202 : exactInterval 13 1202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1202 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1202) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1202 : oddCount 1202 13 = 8 ∧ acceleratedOrbit 13 1202 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1202 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1202) = 3 ^ 8 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1202.1, data_13_1202.2]

end Collatz.Research.StoppingAtlas.Batch0545
