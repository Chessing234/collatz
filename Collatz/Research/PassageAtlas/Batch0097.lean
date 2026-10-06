import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0097

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 3145. -/
theorem bounds_15_3145 : exactInterval 15 3145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3145 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3145) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3145 : oddCount 3145 15 = 9 ∧ acceleratedOrbit 15 3145 = 1891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3145 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3145) = 3 ^ 9 * m + 1891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3145.1, data_15_3145.2]

/-- Complete interval computation for depth 15, residue 3146. -/
theorem bounds_15_3146 : exactInterval 15 3146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3146 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3146) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3146 : oddCount 3146 15 = 7 ∧ acceleratedOrbit 15 3146 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3146 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3146) = 3 ^ 7 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3146.1, data_15_3146.2]

/-- Complete interval computation for depth 15, residue 3147. -/
theorem bounds_15_3147 : exactInterval 15 3147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3147 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3147) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3147 : oddCount 3147 15 = 6 ∧ acceleratedOrbit 15 3147 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3147 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3147) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3147.1, data_15_3147.2]

/-- Complete interval computation for depth 15, residue 3148. -/
theorem bounds_15_3148 : exactInterval 15 3148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3148 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3148) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3148 : oddCount 3148 15 = 7 ∧ acceleratedOrbit 15 3148 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3148 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3148) = 3 ^ 7 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3148.1, data_15_3148.2]

/-- Complete interval computation for depth 15, residue 3149. -/
theorem bounds_15_3149 : exactInterval 15 3149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3149 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3149) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3149 : oddCount 3149 15 = 7 ∧ acceleratedOrbit 15 3149 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3149 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3149) = 3 ^ 7 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3149.1, data_15_3149.2]

/-- Complete interval computation for depth 15, residue 3150. -/
theorem bounds_15_3150 : exactInterval 15 3150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3150 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3150) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3150 : oddCount 3150 15 = 7 ∧ acceleratedOrbit 15 3150 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3150 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3150) = 3 ^ 7 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3150.1, data_15_3150.2]

/-- Complete interval computation for depth 15, residue 3151. -/
theorem bounds_15_3151 : exactInterval 15 3151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3151 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3151) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3151 : oddCount 3151 15 = 7 ∧ acceleratedOrbit 15 3151 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3151 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3151) = 3 ^ 7 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3151.1, data_15_3151.2]

/-- Complete interval computation for depth 15, residue 3152. -/
theorem bounds_15_3152 : exactInterval 15 3152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3152 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3152) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3152 : oddCount 3152 15 = 5 ∧ acceleratedOrbit 15 3152 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3152 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3152) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3152.1, data_15_3152.2]

/-- Complete interval computation for depth 15, residue 3153. -/
theorem bounds_15_3153 : exactInterval 15 3153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3153 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3153) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3153 : oddCount 3153 15 = 7 ∧ acceleratedOrbit 15 3153 = 211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3153 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3153) = 3 ^ 7 * m + 211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3153.1, data_15_3153.2]

/-- Complete interval computation for depth 15, residue 3154. -/
theorem bounds_15_3154 : exactInterval 15 3154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3154 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3154) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3154 : oddCount 3154 15 = 10 ∧ acceleratedOrbit 15 3154 = 5690 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3154 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3154) = 3 ^ 10 * m + 5690 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3154.1, data_15_3154.2]

/-- Complete interval computation for depth 15, residue 3155. -/
theorem bounds_15_3155 : exactInterval 15 3155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3155 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3155) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3155 : oddCount 3155 15 = 10 ∧ acceleratedOrbit 15 3155 = 5690 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3155 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3155) = 3 ^ 10 * m + 5690 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3155.1, data_15_3155.2]

/-- Complete interval computation for depth 15, residue 3156. -/
theorem bounds_15_3156 : exactInterval 15 3156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3156 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3156) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3156 : oddCount 3156 15 = 5 ∧ acceleratedOrbit 15 3156 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3156 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3156) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3156.1, data_15_3156.2]

/-- Complete interval computation for depth 15, residue 3157. -/
theorem bounds_15_3157 : exactInterval 15 3157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3157 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3157) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3157 : oddCount 3157 15 = 5 ∧ acceleratedOrbit 15 3157 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3157 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3157) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3157.1, data_15_3157.2]

/-- Complete interval computation for depth 15, residue 3158. -/
theorem bounds_15_3158 : exactInterval 15 3158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3158 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3158) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3158 : oddCount 3158 15 = 6 ∧ acceleratedOrbit 15 3158 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3158 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3158) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3158.1, data_15_3158.2]

/-- Complete interval computation for depth 15, residue 3159. -/
theorem bounds_15_3159 : exactInterval 15 3159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3159 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3159) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3159 : oddCount 3159 15 = 6 ∧ acceleratedOrbit 15 3159 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3159 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3159) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3159.1, data_15_3159.2]

/-- Complete interval computation for depth 15, residue 3160. -/
theorem bounds_15_3160 : exactInterval 15 3160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3160 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3160) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3160 : oddCount 3160 15 = 8 ∧ acceleratedOrbit 15 3160 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3160 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3160) = 3 ^ 8 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3160.1, data_15_3160.2]

/-- Complete interval computation for depth 15, residue 3161. -/
theorem bounds_15_3161 : exactInterval 15 3161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3161 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3161) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3161 : oddCount 3161 15 = 9 ∧ acceleratedOrbit 15 3161 = 1903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3161 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3161) = 3 ^ 9 * m + 1903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3161.1, data_15_3161.2]

/-- Complete interval computation for depth 15, residue 3162. -/
theorem bounds_15_3162 : exactInterval 15 3162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3162 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3162) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3162 : oddCount 3162 15 = 8 ∧ acceleratedOrbit 15 3162 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3162 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3162) = 3 ^ 8 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3162.1, data_15_3162.2]

/-- Complete interval computation for depth 15, residue 3163. -/
theorem bounds_15_3163 : exactInterval 15 3163 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3163 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3163) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3163 : oddCount 3163 15 = 9 ∧ acceleratedOrbit 15 3163 = 1901 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3163 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3163) = 3 ^ 9 * m + 1901 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3163.1, data_15_3163.2]

/-- Complete interval computation for depth 15, residue 3164. -/
theorem bounds_15_3164 : exactInterval 15 3164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3164 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3164) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3164 : oddCount 3164 15 = 8 ∧ acceleratedOrbit 15 3164 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3164 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3164) = 3 ^ 8 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3164.1, data_15_3164.2]

/-- Complete interval computation for depth 15, residue 3165. -/
theorem bounds_15_3165 : exactInterval 15 3165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3165 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3165) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3165 : oddCount 3165 15 = 8 ∧ acceleratedOrbit 15 3165 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3165 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3165) = 3 ^ 8 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3165.1, data_15_3165.2]

/-- Complete interval computation for depth 15, residue 3166. -/
theorem bounds_15_3166 : exactInterval 15 3166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3166 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3166) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3166 : oddCount 3166 15 = 11 ∧ acceleratedOrbit 15 3166 = 17131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3166 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3166) = 3 ^ 11 * m + 17131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3166.1, data_15_3166.2]

/-- Complete interval computation for depth 15, residue 3167. -/
theorem bounds_15_3167 : exactInterval 15 3167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3167 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3167) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3167 : oddCount 3167 15 = 11 ∧ acceleratedOrbit 15 3167 = 17131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3167 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3167) = 3 ^ 11 * m + 17131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3167.1, data_15_3167.2]

/-- Complete interval computation for depth 15, residue 3168. -/
theorem bounds_15_3168 : exactInterval 15 3168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3168 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3168) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3168 : oddCount 3168 15 = 5 ∧ acceleratedOrbit 15 3168 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3168 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3168) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3168.1, data_15_3168.2]

/-- Complete interval computation for depth 15, residue 3169. -/
theorem bounds_15_3169 : exactInterval 15 3169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3169 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3169) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3169 : oddCount 3169 15 = 9 ∧ acceleratedOrbit 15 3169 = 1907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3169 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3169) = 3 ^ 9 * m + 1907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3169.1, data_15_3169.2]

/-- Complete interval computation for depth 15, residue 3170. -/
theorem bounds_15_3170 : exactInterval 15 3170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3170 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3170) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3170 : oddCount 3170 15 = 8 ∧ acceleratedOrbit 15 3170 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3170 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3170) = 3 ^ 8 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3170.1, data_15_3170.2]

/-- Complete interval computation for depth 15, residue 3171. -/
theorem bounds_15_3171 : exactInterval 15 3171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3171 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3171) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3171 : oddCount 3171 15 = 8 ∧ acceleratedOrbit 15 3171 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3171 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3171) = 3 ^ 8 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3171.1, data_15_3171.2]

/-- Complete interval computation for depth 15, residue 3172. -/
theorem bounds_15_3172 : exactInterval 15 3172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3172 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3172) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3172 : oddCount 3172 15 = 8 ∧ acceleratedOrbit 15 3172 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3172 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3172) = 3 ^ 8 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3172.1, data_15_3172.2]

/-- Complete interval computation for depth 15, residue 3173. -/
theorem bounds_15_3173 : exactInterval 15 3173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3173 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3173) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3173 : oddCount 3173 15 = 8 ∧ acceleratedOrbit 15 3173 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3173 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3173) = 3 ^ 8 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3173.1, data_15_3173.2]

/-- Complete interval computation for depth 15, residue 3174. -/
theorem bounds_15_3174 : exactInterval 15 3174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3174 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3174) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3174 : oddCount 3174 15 = 8 ∧ acceleratedOrbit 15 3174 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3174 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3174) = 3 ^ 8 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3174.1, data_15_3174.2]

/-- Complete interval computation for depth 15, residue 3175. -/
theorem bounds_15_3175 : exactInterval 15 3175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3175 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3175) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3175 : oddCount 3175 15 = 13 ∧ acceleratedOrbit 15 3175 = 154547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3175 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3175) = 3 ^ 13 * m + 154547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3175.1, data_15_3175.2]

/-- Complete interval computation for depth 15, residue 3176. -/
theorem bounds_15_3176 : exactInterval 15 3176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3176 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3176) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3176 : oddCount 3176 15 = 5 ∧ acceleratedOrbit 15 3176 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3176 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3176) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3176.1, data_15_3176.2]

/-- Complete interval computation for depth 15, residue 3177. -/
theorem bounds_15_3177 : exactInterval 15 3177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3177 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3177) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3177 : oddCount 3177 15 = 9 ∧ acceleratedOrbit 15 3177 = 1910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3177 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3177) = 3 ^ 9 * m + 1910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3177.1, data_15_3177.2]

end Collatz.Research.PassageAtlas.Batch0097
