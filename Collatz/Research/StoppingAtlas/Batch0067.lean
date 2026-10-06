import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0067

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 1013. -/
theorem bounds_10_1013 : exactInterval 10 1013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_1013 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 1013) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_1013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_1013 : oddCount 1013 10 = 6 ∧ acceleratedOrbit 10 1013 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_1013 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 1013) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_1013.1, data_10_1013.2]

/-- Complete interval computation for depth 10, residue 1014. -/
theorem bounds_10_1014 : exactInterval 10 1014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_1014 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 1014) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_1014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_1014 : oddCount 1014 10 = 6 ∧ acceleratedOrbit 10 1014 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_1014 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 1014) = 3 ^ 6 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_1014.1, data_10_1014.2]

/-- Complete interval computation for depth 10, residue 1015. -/
theorem bounds_10_1015 : exactInterval 10 1015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_1015 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 1015) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_1015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_1015 : oddCount 1015 10 = 6 ∧ acceleratedOrbit 10 1015 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_1015 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 1015) = 3 ^ 6 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_1015.1, data_10_1015.2]

/-- Complete interval computation for depth 10, residue 1016. -/
theorem bounds_10_1016 : exactInterval 10 1016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_1016 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 1016) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_1016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_1016 : oddCount 1016 10 = 7 ∧ acceleratedOrbit 10 1016 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_1016 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 1016) = 3 ^ 7 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_1016.1, data_10_1016.2]

/-- Complete interval computation for depth 10, residue 1017. -/
theorem bounds_10_1017 : exactInterval 10 1017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_1017 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 1017) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_1017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_1017 : oddCount 1017 10 = 7 ∧ acceleratedOrbit 10 1017 = 2177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_1017 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 1017) = 3 ^ 7 * m + 2177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_1017.1, data_10_1017.2]

/-- Complete interval computation for depth 10, residue 1018. -/
theorem bounds_10_1018 : exactInterval 10 1018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_1018 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 1018) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_1018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_1018 : oddCount 1018 10 = 7 ∧ acceleratedOrbit 10 1018 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_1018 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 1018) = 3 ^ 7 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_1018.1, data_10_1018.2]

/-- Complete interval computation for depth 10, residue 1019. -/
theorem bounds_10_1019 : exactInterval 10 1019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_1019 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 1019) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_1019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_1019 : oddCount 1019 10 = 7 ∧ acceleratedOrbit 10 1019 = 2180 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_1019 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 1019) = 3 ^ 7 * m + 2180 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_1019.1, data_10_1019.2]

/-- Complete interval computation for depth 10, residue 1020. -/
theorem bounds_10_1020 : exactInterval 10 1020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_1020 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 1020) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_1020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_1020 : oddCount 1020 10 = 8 ∧ acceleratedOrbit 10 1020 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_1020 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 1020) = 3 ^ 8 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_1020.1, data_10_1020.2]

/-- Complete interval computation for depth 10, residue 1021. -/
theorem bounds_10_1021 : exactInterval 10 1021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_1021 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 1021) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_1021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_1021 : oddCount 1021 10 = 8 ∧ acceleratedOrbit 10 1021 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_1021 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 1021) = 3 ^ 8 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_1021.1, data_10_1021.2]

/-- Complete interval computation for depth 10, residue 1022. -/
theorem bounds_10_1022 : exactInterval 10 1022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_1022 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 1022) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_1022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_1022 : oddCount 1022 10 = 9 ∧ acceleratedOrbit 10 1022 = 19682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_1022 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 1022) = 3 ^ 9 * m + 19682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_1022.1, data_10_1022.2]

/-- Complete interval computation for depth 10, residue 1023. -/
theorem bounds_10_1023 : exactInterval 10 1023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_1023 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 1023) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_1023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_1023 : oddCount 1023 10 = 10 ∧ acceleratedOrbit 10 1023 = 59048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_1023 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 1023) = 3 ^ 10 * m + 59048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_1023.1, data_10_1023.2]

/-- Complete interval computation for depth 11, residue 0. -/
theorem bounds_11_0 : exactInterval 11 0 = ⟨1, some 1⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_0 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 0) 11 ↔ 1 ≤ m ∧ m < 1 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_0 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_0 : oddCount 0 11 = 0 ∧ acceleratedOrbit 11 0 = 0 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_0 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 0) = 3 ^ 0 * m + 0 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_0.1, data_11_0.2]

/-- Complete interval computation for depth 11, residue 1. -/
theorem bounds_11_1 : exactInterval 11 1 = ⟨1, some 1⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1) 11 ↔ 1 ≤ m ∧ m < 1 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1 : oddCount 1 11 = 6 ∧ acceleratedOrbit 11 1 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1) = 3 ^ 6 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1.1, data_11_1.2]

/-- Complete interval computation for depth 11, residue 2. -/
theorem bounds_11_2 : exactInterval 11 2 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_2 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 2) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_2 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_2 : oddCount 2 11 = 5 ∧ acceleratedOrbit 11 2 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_2 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 2) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_2.1, data_11_2.2]

/-- Complete interval computation for depth 11, residue 3. -/
theorem bounds_11_3 : exactInterval 11 3 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_3 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 3) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_3 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_3 : oddCount 3 11 = 5 ∧ acceleratedOrbit 11 3 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_3 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 3) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_3.1, data_11_3.2]

/-- Complete interval computation for depth 11, residue 4. -/
theorem bounds_11_4 : exactInterval 11 4 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_4 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 4) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_4 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_4 : oddCount 4 11 = 5 ∧ acceleratedOrbit 11 4 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_4 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 4) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_4.1, data_11_4.2]

end Collatz.Research.StoppingAtlas.Batch0067
