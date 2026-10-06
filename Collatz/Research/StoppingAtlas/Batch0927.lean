import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0927

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7055. -/
theorem bounds_13_7055 : exactInterval 13 7055 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7055 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7055) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7055 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7055 : oddCount 7055 13 = 6 ∧ acceleratedOrbit 13 7055 = 628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7055 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7055) = 3 ^ 6 * m + 628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7055.1, data_13_7055.2]

/-- Complete interval computation for depth 13, residue 7056. -/
theorem bounds_13_7056 : exactInterval 13 7056 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7056 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7056) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7056 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7056 : oddCount 7056 13 = 4 ∧ acceleratedOrbit 13 7056 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7056 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7056) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7056.1, data_13_7056.2]

/-- Complete interval computation for depth 13, residue 7057. -/
theorem bounds_13_7057 : exactInterval 13 7057 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7057 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7057) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7057 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7057 : oddCount 7057 13 = 6 ∧ acceleratedOrbit 13 7057 = 629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7057 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7057) = 3 ^ 6 * m + 629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7057.1, data_13_7057.2]

/-- Complete interval computation for depth 13, residue 7058. -/
theorem bounds_13_7058 : exactInterval 13 7058 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7058 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7058) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7058 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7058 : oddCount 7058 13 = 6 ∧ acceleratedOrbit 13 7058 = 629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7058 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7058) = 3 ^ 6 * m + 629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7058.1, data_13_7058.2]

/-- Complete interval computation for depth 13, residue 7059. -/
theorem bounds_13_7059 : exactInterval 13 7059 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7059 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7059) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7059 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7059 : oddCount 7059 13 = 6 ∧ acceleratedOrbit 13 7059 = 629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7059 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7059) = 3 ^ 6 * m + 629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7059.1, data_13_7059.2]

/-- Complete interval computation for depth 13, residue 7060. -/
theorem bounds_13_7060 : exactInterval 13 7060 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7060 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7060) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7060 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7060 : oddCount 7060 13 = 4 ∧ acceleratedOrbit 13 7060 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7060 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7060) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7060.1, data_13_7060.2]

/-- Complete interval computation for depth 13, residue 7061. -/
theorem bounds_13_7061 : exactInterval 13 7061 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7061 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7061) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7061 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7061 : oddCount 7061 13 = 4 ∧ acceleratedOrbit 13 7061 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7061 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7061) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7061.1, data_13_7061.2]

/-- Complete interval computation for depth 13, residue 7062. -/
theorem bounds_13_7062 : exactInterval 13 7062 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7062 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7062) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7062 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7062 : oddCount 7062 13 = 7 ∧ acceleratedOrbit 13 7062 = 1889 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7062 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7062) = 3 ^ 7 * m + 1889 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7062.1, data_13_7062.2]

/-- Complete interval computation for depth 13, residue 7063. -/
theorem bounds_13_7063 : exactInterval 13 7063 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7063 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7063) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7063 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7063 : oddCount 7063 13 = 7 ∧ acceleratedOrbit 13 7063 = 1889 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7063 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7063) = 3 ^ 7 * m + 1889 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7063.1, data_13_7063.2]

/-- Complete interval computation for depth 13, residue 7064. -/
theorem bounds_13_7064 : exactInterval 13 7064 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7064 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7064) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7064 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7064 : oddCount 7064 13 = 4 ∧ acceleratedOrbit 13 7064 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7064 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7064) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7064.1, data_13_7064.2]

/-- Complete interval computation for depth 13, residue 7065. -/
theorem bounds_13_7065 : exactInterval 13 7065 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7065 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7065) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7065 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7065 : oddCount 7065 13 = 7 ∧ acceleratedOrbit 13 7065 = 1889 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7065 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7065) = 3 ^ 7 * m + 1889 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7065.1, data_13_7065.2]

/-- Complete interval computation for depth 13, residue 7066. -/
theorem bounds_13_7066 : exactInterval 13 7066 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7066 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7066) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7066 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7066 : oddCount 7066 13 = 4 ∧ acceleratedOrbit 13 7066 = 70 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7066 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7066) = 3 ^ 4 * m + 70 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7066.1, data_13_7066.2]

/-- Complete interval computation for depth 13, residue 7067. -/
theorem bounds_13_7067 : exactInterval 13 7067 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7067 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7067) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7067 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7067 : oddCount 7067 13 = 6 ∧ acceleratedOrbit 13 7067 = 629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7067 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7067) = 3 ^ 6 * m + 629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7067.1, data_13_7067.2]

/-- Complete interval computation for depth 13, residue 7068. -/
theorem bounds_13_7068 : exactInterval 13 7068 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7068 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7068) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7068 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7068 : oddCount 7068 13 = 8 ∧ acceleratedOrbit 13 7068 = 5665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7068 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7068) = 3 ^ 8 * m + 5665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7068.1, data_13_7068.2]

/-- Complete interval computation for depth 13, residue 7069. -/
theorem bounds_13_7069 : exactInterval 13 7069 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7069 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7069) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7069 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7069 : oddCount 7069 13 = 8 ∧ acceleratedOrbit 13 7069 = 5665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7069 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7069) = 3 ^ 8 * m + 5665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7069.1, data_13_7069.2]

end Collatz.Research.StoppingAtlas.Batch0927
