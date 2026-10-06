import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0917

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 30015. -/
theorem bounds_15_30015 : exactInterval 15 30015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30015 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30015) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30015 : oddCount 30015 15 = 8 ∧ acceleratedOrbit 15 30015 = 6010 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30015 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30015) = 3 ^ 8 * m + 6010 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30015.1, data_15_30015.2]

/-- Complete interval computation for depth 15, residue 30016. -/
theorem bounds_15_30016 : exactInterval 15 30016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30016 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30016) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30016 : oddCount 30016 15 = 3 ∧ acceleratedOrbit 15 30016 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30016 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30016) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30016.1, data_15_30016.2]

/-- Complete interval computation for depth 15, residue 30017. -/
theorem bounds_15_30017 : exactInterval 15 30017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30017 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30017) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30017 : oddCount 30017 15 = 8 ∧ acceleratedOrbit 15 30017 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30017 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30017) = 3 ^ 8 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30017.1, data_15_30017.2]

/-- Complete interval computation for depth 15, residue 30018. -/
theorem bounds_15_30018 : exactInterval 15 30018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30018 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30018) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30018 : oddCount 30018 15 = 10 ∧ acceleratedOrbit 15 30018 = 54107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30018 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30018) = 3 ^ 10 * m + 54107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30018.1, data_15_30018.2]

/-- Complete interval computation for depth 15, residue 30019. -/
theorem bounds_15_30019 : exactInterval 15 30019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30019 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30019) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30019 : oddCount 30019 15 = 10 ∧ acceleratedOrbit 15 30019 = 54107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30019 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30019) = 3 ^ 10 * m + 54107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30019.1, data_15_30019.2]

/-- Complete interval computation for depth 15, residue 30020. -/
theorem bounds_15_30020 : exactInterval 15 30020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30020 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30020) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30020 : oddCount 30020 15 = 8 ∧ acceleratedOrbit 15 30020 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30020 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30020) = 3 ^ 8 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30020.1, data_15_30020.2]

/-- Complete interval computation for depth 15, residue 30021. -/
theorem bounds_15_30021 : exactInterval 15 30021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30021 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30021) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30021 : oddCount 30021 15 = 8 ∧ acceleratedOrbit 15 30021 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30021 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30021) = 3 ^ 8 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30021.1, data_15_30021.2]

/-- Complete interval computation for depth 15, residue 30022. -/
theorem bounds_15_30022 : exactInterval 15 30022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30022 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30022) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30022 : oddCount 30022 15 = 8 ∧ acceleratedOrbit 15 30022 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30022 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30022) = 3 ^ 8 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30022.1, data_15_30022.2]

/-- Complete interval computation for depth 15, residue 30023. -/
theorem bounds_15_30023 : exactInterval 15 30023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30023 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30023) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30023 : oddCount 30023 15 = 11 ∧ acceleratedOrbit 15 30023 = 162317 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30023 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30023) = 3 ^ 11 * m + 162317 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30023.1, data_15_30023.2]

/-- Complete interval computation for depth 15, residue 30024. -/
theorem bounds_15_30024 : exactInterval 15 30024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30024 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30024) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30024 : oddCount 30024 15 = 10 ∧ acceleratedOrbit 15 30024 = 54128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30024 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30024) = 3 ^ 10 * m + 54128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30024.1, data_15_30024.2]

/-- Complete interval computation for depth 15, residue 30025. -/
theorem bounds_15_30025 : exactInterval 15 30025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30025 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30025) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30025 : oddCount 30025 15 = 9 ∧ acceleratedOrbit 15 30025 = 18038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30025 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30025) = 3 ^ 9 * m + 18038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30025.1, data_15_30025.2]

/-- Complete interval computation for depth 15, residue 30026. -/
theorem bounds_15_30026 : exactInterval 15 30026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30026 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30026) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30026 : oddCount 30026 15 = 10 ∧ acceleratedOrbit 15 30026 = 54128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30026 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30026) = 3 ^ 10 * m + 54128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30026.1, data_15_30026.2]

/-- Complete interval computation for depth 15, residue 30027. -/
theorem bounds_15_30027 : exactInterval 15 30027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30027 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30027) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30027 : oddCount 30027 15 = 8 ∧ acceleratedOrbit 15 30027 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30027 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30027) = 3 ^ 8 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30027.1, data_15_30027.2]

/-- Complete interval computation for depth 15, residue 30028. -/
theorem bounds_15_30028 : exactInterval 15 30028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30028 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30028) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30028 : oddCount 30028 15 = 10 ∧ acceleratedOrbit 15 30028 = 54128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30028 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30028) = 3 ^ 10 * m + 54128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30028.1, data_15_30028.2]

/-- Complete interval computation for depth 15, residue 30029. -/
theorem bounds_15_30029 : exactInterval 15 30029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30029 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30029) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30029 : oddCount 30029 15 = 10 ∧ acceleratedOrbit 15 30029 = 54128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30029 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30029) = 3 ^ 10 * m + 54128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30029.1, data_15_30029.2]

/-- Complete interval computation for depth 15, residue 30030. -/
theorem bounds_15_30030 : exactInterval 15 30030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30030 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30030) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30030 : oddCount 30030 15 = 10 ∧ acceleratedOrbit 15 30030 = 54121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30030 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30030) = 3 ^ 10 * m + 54121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30030.1, data_15_30030.2]

/-- Complete interval computation for depth 15, residue 30031. -/
theorem bounds_15_30031 : exactInterval 15 30031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30031 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30031) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30031 : oddCount 30031 15 = 10 ∧ acceleratedOrbit 15 30031 = 54121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30031 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30031) = 3 ^ 10 * m + 54121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30031.1, data_15_30031.2]

/-- Complete interval computation for depth 15, residue 30032. -/
theorem bounds_15_30032 : exactInterval 15 30032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30032 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30032) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30032 : oddCount 30032 15 = 3 ∧ acceleratedOrbit 15 30032 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30032 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30032) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30032.1, data_15_30032.2]

/-- Complete interval computation for depth 15, residue 30033. -/
theorem bounds_15_30033 : exactInterval 15 30033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30033 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30033) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30033 : oddCount 30033 15 = 10 ∧ acceleratedOrbit 15 30033 = 54128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30033 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30033) = 3 ^ 10 * m + 54128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30033.1, data_15_30033.2]

/-- Complete interval computation for depth 15, residue 30034. -/
theorem bounds_15_30034 : exactInterval 15 30034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30034 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30034) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30034 : oddCount 30034 15 = 12 ∧ acceleratedOrbit 15 30034 = 487154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30034 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30034) = 3 ^ 12 * m + 487154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30034.1, data_15_30034.2]

/-- Complete interval computation for depth 15, residue 30035. -/
theorem bounds_15_30035 : exactInterval 15 30035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30035 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30035) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30035 : oddCount 30035 15 = 12 ∧ acceleratedOrbit 15 30035 = 487154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30035 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30035) = 3 ^ 12 * m + 487154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30035.1, data_15_30035.2]

/-- Complete interval computation for depth 15, residue 30036. -/
theorem bounds_15_30036 : exactInterval 15 30036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30036 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30036) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30036 : oddCount 30036 15 = 3 ∧ acceleratedOrbit 15 30036 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30036 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30036) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30036.1, data_15_30036.2]

/-- Complete interval computation for depth 15, residue 30037. -/
theorem bounds_15_30037 : exactInterval 15 30037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30037 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30037) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30037 : oddCount 30037 15 = 3 ∧ acceleratedOrbit 15 30037 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30037 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30037) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30037.1, data_15_30037.2]

/-- Complete interval computation for depth 15, residue 30038. -/
theorem bounds_15_30038 : exactInterval 15 30038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30038 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30038) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30038 : oddCount 30038 15 = 8 ∧ acceleratedOrbit 15 30038 = 6016 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30038 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30038) = 3 ^ 8 * m + 6016 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30038.1, data_15_30038.2]

/-- Complete interval computation for depth 15, residue 30039. -/
theorem bounds_15_30039 : exactInterval 15 30039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30039 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30039) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30039 : oddCount 30039 15 = 8 ∧ acceleratedOrbit 15 30039 = 6016 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30039 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30039) = 3 ^ 8 * m + 6016 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30039.1, data_15_30039.2]

/-- Complete interval computation for depth 15, residue 30040. -/
theorem bounds_15_30040 : exactInterval 15 30040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30040 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30040) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30040 : oddCount 30040 15 = 8 ∧ acceleratedOrbit 15 30040 = 6020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30040 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30040) = 3 ^ 8 * m + 6020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30040.1, data_15_30040.2]

/-- Complete interval computation for depth 15, residue 30041. -/
theorem bounds_15_30041 : exactInterval 15 30041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30041 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30041) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30041 : oddCount 30041 15 = 7 ∧ acceleratedOrbit 15 30041 = 2006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30041 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30041) = 3 ^ 7 * m + 2006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30041.1, data_15_30041.2]

/-- Complete interval computation for depth 15, residue 30042. -/
theorem bounds_15_30042 : exactInterval 15 30042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30042 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30042) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30042 : oddCount 30042 15 = 8 ∧ acceleratedOrbit 15 30042 = 6020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30042 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30042) = 3 ^ 8 * m + 6020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30042.1, data_15_30042.2]

/-- Complete interval computation for depth 15, residue 30043. -/
theorem bounds_15_30043 : exactInterval 15 30043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30043 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30043) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30043 : oddCount 30043 15 = 8 ∧ acceleratedOrbit 15 30043 = 6016 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30043 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30043) = 3 ^ 8 * m + 6016 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30043.1, data_15_30043.2]

/-- Complete interval computation for depth 15, residue 30044. -/
theorem bounds_15_30044 : exactInterval 15 30044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30044 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30044) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30044 : oddCount 30044 15 = 8 ∧ acceleratedOrbit 15 30044 = 6020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30044 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30044) = 3 ^ 8 * m + 6020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30044.1, data_15_30044.2]

/-- Complete interval computation for depth 15, residue 30045. -/
theorem bounds_15_30045 : exactInterval 15 30045 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30045 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30045) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30045 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30045 : oddCount 30045 15 = 8 ∧ acceleratedOrbit 15 30045 = 6020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30045 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30045) = 3 ^ 8 * m + 6020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30045.1, data_15_30045.2]

/-- Complete interval computation for depth 15, residue 30046. -/
theorem bounds_15_30046 : exactInterval 15 30046 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30046 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30046) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30046 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30046 : oddCount 30046 15 = 7 ∧ acceleratedOrbit 15 30046 = 2006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30046 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30046) = 3 ^ 7 * m + 2006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30046.1, data_15_30046.2]

/-- Complete interval computation for depth 15, residue 30047. -/
theorem bounds_15_30047 : exactInterval 15 30047 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30047 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30047) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30047 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30047 : oddCount 30047 15 = 7 ∧ acceleratedOrbit 15 30047 = 2006 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30047 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30047) = 3 ^ 7 * m + 2006 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30047.1, data_15_30047.2]

end Collatz.Research.PassageAtlas.Batch0917
