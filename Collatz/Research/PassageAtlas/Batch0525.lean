import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0525

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 17170. -/
theorem bounds_15_17170 : exactInterval 15 17170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17170 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17170) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17170 : oddCount 17170 15 = 8 ∧ acceleratedOrbit 15 17170 = 3439 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17170 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17170) = 3 ^ 8 * m + 3439 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17170.1, data_15_17170.2]

/-- Complete interval computation for depth 15, residue 17171. -/
theorem bounds_15_17171 : exactInterval 15 17171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17171 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17171) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17171 : oddCount 17171 15 = 8 ∧ acceleratedOrbit 15 17171 = 3439 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17171 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17171) = 3 ^ 8 * m + 3439 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17171.1, data_15_17171.2]

/-- Complete interval computation for depth 15, residue 17172. -/
theorem bounds_15_17172 : exactInterval 15 17172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17172 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17172) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17172 : oddCount 17172 15 = 5 ∧ acceleratedOrbit 15 17172 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17172 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17172) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17172.1, data_15_17172.2]

/-- Complete interval computation for depth 15, residue 17173. -/
theorem bounds_15_17173 : exactInterval 15 17173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17173 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17173) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17173 : oddCount 17173 15 = 5 ∧ acceleratedOrbit 15 17173 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17173 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17173) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17173.1, data_15_17173.2]

/-- Complete interval computation for depth 15, residue 17174. -/
theorem bounds_15_17174 : exactInterval 15 17174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17174 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17174) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17174 : oddCount 17174 15 = 8 ∧ acceleratedOrbit 15 17174 = 3440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17174 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17174) = 3 ^ 8 * m + 3440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17174.1, data_15_17174.2]

/-- Complete interval computation for depth 15, residue 17175. -/
theorem bounds_15_17175 : exactInterval 15 17175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17175 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17175) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17175 : oddCount 17175 15 = 8 ∧ acceleratedOrbit 15 17175 = 3440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17175 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17175) = 3 ^ 8 * m + 3440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17175.1, data_15_17175.2]

/-- Complete interval computation for depth 15, residue 17176. -/
theorem bounds_15_17176 : exactInterval 15 17176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17176 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17176) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17176 : oddCount 17176 15 = 5 ∧ acceleratedOrbit 15 17176 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17176 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17176) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17176.1, data_15_17176.2]

/-- Complete interval computation for depth 15, residue 17177. -/
theorem bounds_15_17177 : exactInterval 15 17177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17177 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17177) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17177 : oddCount 17177 15 = 8 ∧ acceleratedOrbit 15 17177 = 3440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17177 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17177) = 3 ^ 8 * m + 3440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17177.1, data_15_17177.2]

/-- Complete interval computation for depth 15, residue 17178. -/
theorem bounds_15_17178 : exactInterval 15 17178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17178 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17178) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17178 : oddCount 17178 15 = 5 ∧ acceleratedOrbit 15 17178 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17178 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17178) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17178.1, data_15_17178.2]

/-- Complete interval computation for depth 15, residue 17179. -/
theorem bounds_15_17179 : exactInterval 15 17179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17179 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17179) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17179 : oddCount 17179 15 = 12 ∧ acceleratedOrbit 15 17179 = 278639 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17179 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17179) = 3 ^ 12 * m + 278639 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17179.1, data_15_17179.2]

/-- Complete interval computation for depth 15, residue 17180. -/
theorem bounds_15_17180 : exactInterval 15 17180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17180 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17180) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17180 : oddCount 17180 15 = 8 ∧ acceleratedOrbit 15 17180 = 3442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17180 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17180) = 3 ^ 8 * m + 3442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17180.1, data_15_17180.2]

/-- Complete interval computation for depth 15, residue 17181. -/
theorem bounds_15_17181 : exactInterval 15 17181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17181 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17181) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17181 : oddCount 17181 15 = 8 ∧ acceleratedOrbit 15 17181 = 3442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17181 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17181) = 3 ^ 8 * m + 3442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17181.1, data_15_17181.2]

/-- Complete interval computation for depth 15, residue 17182. -/
theorem bounds_15_17182 : exactInterval 15 17182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17182 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17182) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17182 : oddCount 17182 15 = 8 ∧ acceleratedOrbit 15 17182 = 3442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17182 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17182) = 3 ^ 8 * m + 3442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17182.1, data_15_17182.2]

/-- Complete interval computation for depth 15, residue 17183. -/
theorem bounds_15_17183 : exactInterval 15 17183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17183 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17183) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17183 : oddCount 17183 15 = 10 ∧ acceleratedOrbit 15 17183 = 30968 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17183 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17183) = 3 ^ 10 * m + 30968 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17183.1, data_15_17183.2]

/-- Complete interval computation for depth 15, residue 17184. -/
theorem bounds_15_17184 : exactInterval 15 17184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17184 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17184) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17184 : oddCount 17184 15 = 5 ∧ acceleratedOrbit 15 17184 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17184 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17184) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17184.1, data_15_17184.2]

/-- Complete interval computation for depth 15, residue 17185. -/
theorem bounds_15_17185 : exactInterval 15 17185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17185 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17185) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17185 : oddCount 17185 15 = 9 ∧ acceleratedOrbit 15 17185 = 10327 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17185 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17185) = 3 ^ 9 * m + 10327 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17185.1, data_15_17185.2]

/-- Complete interval computation for depth 15, residue 17186. -/
theorem bounds_15_17186 : exactInterval 15 17186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17186 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17186) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17186 : oddCount 17186 15 = 5 ∧ acceleratedOrbit 15 17186 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17186 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17186) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17186.1, data_15_17186.2]

/-- Complete interval computation for depth 15, residue 17187. -/
theorem bounds_15_17187 : exactInterval 15 17187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17187 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17187) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17187 : oddCount 17187 15 = 5 ∧ acceleratedOrbit 15 17187 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17187 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17187) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17187.1, data_15_17187.2]

/-- Complete interval computation for depth 15, residue 17188. -/
theorem bounds_15_17188 : exactInterval 15 17188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17188 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17188) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17188 : oddCount 17188 15 = 5 ∧ acceleratedOrbit 15 17188 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17188 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17188) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17188.1, data_15_17188.2]

/-- Complete interval computation for depth 15, residue 17189. -/
theorem bounds_15_17189 : exactInterval 15 17189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17189 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17189) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17189 : oddCount 17189 15 = 5 ∧ acceleratedOrbit 15 17189 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17189 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17189) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17189.1, data_15_17189.2]

/-- Complete interval computation for depth 15, residue 17190. -/
theorem bounds_15_17190 : exactInterval 15 17190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17190 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17190) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17190 : oddCount 17190 15 = 5 ∧ acceleratedOrbit 15 17190 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17190 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17190) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17190.1, data_15_17190.2]

/-- Complete interval computation for depth 15, residue 17191. -/
theorem bounds_15_17191 : exactInterval 15 17191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17191 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17191) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17191 : oddCount 17191 15 = 11 ∧ acceleratedOrbit 15 17191 = 92947 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17191 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17191) = 3 ^ 11 * m + 92947 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17191.1, data_15_17191.2]

/-- Complete interval computation for depth 15, residue 17192. -/
theorem bounds_15_17192 : exactInterval 15 17192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17192 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17192) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17192 : oddCount 17192 15 = 5 ∧ acceleratedOrbit 15 17192 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17192 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17192) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17192.1, data_15_17192.2]

/-- Complete interval computation for depth 15, residue 17193. -/
theorem bounds_15_17193 : exactInterval 15 17193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17193 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17193) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17193 : oddCount 17193 15 = 8 ∧ acceleratedOrbit 15 17193 = 3443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17193 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17193) = 3 ^ 8 * m + 3443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17193.1, data_15_17193.2]

/-- Complete interval computation for depth 15, residue 17194. -/
theorem bounds_15_17194 : exactInterval 15 17194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17194 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17194) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17194 : oddCount 17194 15 = 5 ∧ acceleratedOrbit 15 17194 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17194 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17194) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17194.1, data_15_17194.2]

/-- Complete interval computation for depth 15, residue 17195. -/
theorem bounds_15_17195 : exactInterval 15 17195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17195 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17195) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17195 : oddCount 17195 15 = 7 ∧ acceleratedOrbit 15 17195 = 1148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17195 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17195) = 3 ^ 7 * m + 1148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17195.1, data_15_17195.2]

/-- Complete interval computation for depth 15, residue 17196. -/
theorem bounds_15_17196 : exactInterval 15 17196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17196 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17196) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17196 : oddCount 17196 15 = 6 ∧ acceleratedOrbit 15 17196 = 383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17196 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17196) = 3 ^ 6 * m + 383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17196.1, data_15_17196.2]

/-- Complete interval computation for depth 15, residue 17197. -/
theorem bounds_15_17197 : exactInterval 15 17197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17197 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17197) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17197 : oddCount 17197 15 = 6 ∧ acceleratedOrbit 15 17197 = 383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17197 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17197) = 3 ^ 6 * m + 383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17197.1, data_15_17197.2]

/-- Complete interval computation for depth 15, residue 17198. -/
theorem bounds_15_17198 : exactInterval 15 17198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17198 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17198) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17198 : oddCount 17198 15 = 6 ∧ acceleratedOrbit 15 17198 = 383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17198 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17198) = 3 ^ 6 * m + 383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17198.1, data_15_17198.2]

/-- Complete interval computation for depth 15, residue 17199. -/
theorem bounds_15_17199 : exactInterval 15 17199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17199 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17199) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17199 : oddCount 17199 15 = 7 ∧ acceleratedOrbit 15 17199 = 1148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17199 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17199) = 3 ^ 7 * m + 1148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17199.1, data_15_17199.2]

/-- Complete interval computation for depth 15, residue 17200. -/
theorem bounds_15_17200 : exactInterval 15 17200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17200 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17200) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17200 : oddCount 17200 15 = 5 ∧ acceleratedOrbit 15 17200 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17200 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17200) = 3 ^ 5 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17200.1, data_15_17200.2]

/-- Complete interval computation for depth 15, residue 17201. -/
theorem bounds_15_17201 : exactInterval 15 17201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17201 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17201) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17201 : oddCount 17201 15 = 6 ∧ acceleratedOrbit 15 17201 = 383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17201 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17201) = 3 ^ 6 * m + 383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17201.1, data_15_17201.2]

/-- Complete interval computation for depth 15, residue 17202. -/
theorem bounds_15_17202 : exactInterval 15 17202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17202 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17202) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17202 : oddCount 17202 15 = 6 ∧ acceleratedOrbit 15 17202 = 383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17202 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17202) = 3 ^ 6 * m + 383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17202.1, data_15_17202.2]

end Collatz.Research.PassageAtlas.Batch0525
