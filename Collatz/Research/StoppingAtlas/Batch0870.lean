import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0870

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6179. -/
theorem bounds_13_6179 : exactInterval 13 6179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6179 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6179) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6179 : oddCount 6179 13 = 5 ∧ acceleratedOrbit 13 6179 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6179 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6179) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6179.1, data_13_6179.2]

/-- Complete interval computation for depth 13, residue 6180. -/
theorem bounds_13_6180 : exactInterval 13 6180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6180 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6180) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6180 : oddCount 6180 13 = 6 ∧ acceleratedOrbit 13 6180 = 551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6180 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6180) = 3 ^ 6 * m + 551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6180.1, data_13_6180.2]

/-- Complete interval computation for depth 13, residue 6181. -/
theorem bounds_13_6181 : exactInterval 13 6181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6181 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6181) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6181 : oddCount 6181 13 = 6 ∧ acceleratedOrbit 13 6181 = 551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6181 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6181) = 3 ^ 6 * m + 551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6181.1, data_13_6181.2]

/-- Complete interval computation for depth 13, residue 6182. -/
theorem bounds_13_6182 : exactInterval 13 6182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6182 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6182) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6182 : oddCount 6182 13 = 6 ∧ acceleratedOrbit 13 6182 = 551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6182 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6182) = 3 ^ 6 * m + 551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6182.1, data_13_6182.2]

/-- Complete interval computation for depth 13, residue 6183. -/
theorem bounds_13_6183 : exactInterval 13 6183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6183 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6183) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6183 : oddCount 6183 13 = 8 ∧ acceleratedOrbit 13 6183 = 4954 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6183 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6183) = 3 ^ 8 * m + 4954 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6183.1, data_13_6183.2]

/-- Complete interval computation for depth 13, residue 6184. -/
theorem bounds_13_6184 : exactInterval 13 6184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6184 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6184) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6184 : oddCount 6184 13 = 4 ∧ acceleratedOrbit 13 6184 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6184 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6184) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6184.1, data_13_6184.2]

/-- Complete interval computation for depth 13, residue 6185. -/
theorem bounds_13_6185 : exactInterval 13 6185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6185 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6185) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6185 : oddCount 6185 13 = 8 ∧ acceleratedOrbit 13 6185 = 4955 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6185 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6185) = 3 ^ 8 * m + 4955 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6185.1, data_13_6185.2]

/-- Complete interval computation for depth 13, residue 6186. -/
theorem bounds_13_6186 : exactInterval 13 6186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6186 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6186) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6186 : oddCount 6186 13 = 4 ∧ acceleratedOrbit 13 6186 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6186 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6186) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6186.1, data_13_6186.2]

/-- Complete interval computation for depth 13, residue 6187. -/
theorem bounds_13_6187 : exactInterval 13 6187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6187 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6187) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6187 : oddCount 6187 13 = 6 ∧ acceleratedOrbit 13 6187 = 551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6187 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6187) = 3 ^ 6 * m + 551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6187.1, data_13_6187.2]

/-- Complete interval computation for depth 13, residue 6188. -/
theorem bounds_13_6188 : exactInterval 13 6188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6188 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6188) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6188 : oddCount 6188 13 = 5 ∧ acceleratedOrbit 13 6188 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6188 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6188) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6188.1, data_13_6188.2]

/-- Complete interval computation for depth 13, residue 6189. -/
theorem bounds_13_6189 : exactInterval 13 6189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6189 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6189) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6189 : oddCount 6189 13 = 5 ∧ acceleratedOrbit 13 6189 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6189 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6189) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6189.1, data_13_6189.2]

/-- Complete interval computation for depth 13, residue 6190. -/
theorem bounds_13_6190 : exactInterval 13 6190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6190 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6190) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6190 : oddCount 6190 13 = 5 ∧ acceleratedOrbit 13 6190 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6190 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6190) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6190.1, data_13_6190.2]

/-- Complete interval computation for depth 13, residue 6191. -/
theorem bounds_13_6191 : exactInterval 13 6191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6191 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6191) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6191 : oddCount 6191 13 = 9 ∧ acceleratedOrbit 13 6191 = 14879 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6191 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6191) = 3 ^ 9 * m + 14879 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6191.1, data_13_6191.2]

/-- Complete interval computation for depth 13, residue 6192. -/
theorem bounds_13_6192 : exactInterval 13 6192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6192 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6192) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6192 : oddCount 6192 13 = 4 ∧ acceleratedOrbit 13 6192 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6192 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6192) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6192.1, data_13_6192.2]

/-- Complete interval computation for depth 13, residue 6193. -/
theorem bounds_13_6193 : exactInterval 13 6193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6193 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6193) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6193 : oddCount 6193 13 = 8 ∧ acceleratedOrbit 13 6193 = 4967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6193 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6193) = 3 ^ 8 * m + 4967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6193.1, data_13_6193.2]

/-- Complete interval computation for depth 13, residue 6194. -/
theorem bounds_13_6194 : exactInterval 13 6194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6194 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6194) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6194 : oddCount 6194 13 = 8 ∧ acceleratedOrbit 13 6194 = 4967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6194 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6194) = 3 ^ 8 * m + 4967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6194.1, data_13_6194.2]

end Collatz.Research.StoppingAtlas.Batch0870
