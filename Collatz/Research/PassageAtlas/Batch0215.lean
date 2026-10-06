import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0215

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 7012. -/
theorem bounds_15_7012 : exactInterval 15 7012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7012 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7012) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7012 : oddCount 7012 15 = 6 ∧ acceleratedOrbit 15 7012 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7012 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7012) = 3 ^ 6 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7012.1, data_15_7012.2]

/-- Complete interval computation for depth 15, residue 7013. -/
theorem bounds_15_7013 : exactInterval 15 7013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7013 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7013) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7013 : oddCount 7013 15 = 6 ∧ acceleratedOrbit 15 7013 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7013 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7013) = 3 ^ 6 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7013.1, data_15_7013.2]

/-- Complete interval computation for depth 15, residue 7014. -/
theorem bounds_15_7014 : exactInterval 15 7014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7014 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7014) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7014 : oddCount 7014 15 = 6 ∧ acceleratedOrbit 15 7014 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7014 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7014) = 3 ^ 6 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7014.1, data_15_7014.2]

/-- Complete interval computation for depth 15, residue 7015. -/
theorem bounds_15_7015 : exactInterval 15 7015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7015 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7015) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7015 : oddCount 7015 15 = 10 ∧ acceleratedOrbit 15 7015 = 12644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7015 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7015) = 3 ^ 10 * m + 12644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7015.1, data_15_7015.2]

/-- Complete interval computation for depth 15, residue 7016. -/
theorem bounds_15_7016 : exactInterval 15 7016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7016 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7016) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7016 : oddCount 7016 15 = 6 ∧ acceleratedOrbit 15 7016 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7016 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7016) = 3 ^ 6 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7016.1, data_15_7016.2]

/-- Complete interval computation for depth 15, residue 7017. -/
theorem bounds_15_7017 : exactInterval 15 7017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7017 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7017) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7017 : oddCount 7017 15 = 8 ∧ acceleratedOrbit 15 7017 = 1406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7017 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7017) = 3 ^ 8 * m + 1406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7017.1, data_15_7017.2]

/-- Complete interval computation for depth 15, residue 7018. -/
theorem bounds_15_7018 : exactInterval 15 7018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7018 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7018) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7018 : oddCount 7018 15 = 6 ∧ acceleratedOrbit 15 7018 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7018 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7018) = 3 ^ 6 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7018.1, data_15_7018.2]

/-- Complete interval computation for depth 15, residue 7019. -/
theorem bounds_15_7019 : exactInterval 15 7019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7019 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7019) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7019 : oddCount 7019 15 = 7 ∧ acceleratedOrbit 15 7019 = 469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7019 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7019) = 3 ^ 7 * m + 469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7019.1, data_15_7019.2]

/-- Complete interval computation for depth 15, residue 7020. -/
theorem bounds_15_7020 : exactInterval 15 7020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7020 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7020) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7020 : oddCount 7020 15 = 7 ∧ acceleratedOrbit 15 7020 = 469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7020 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7020) = 3 ^ 7 * m + 469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7020.1, data_15_7020.2]

/-- Complete interval computation for depth 15, residue 7021. -/
theorem bounds_15_7021 : exactInterval 15 7021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7021 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7021) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7021 : oddCount 7021 15 = 7 ∧ acceleratedOrbit 15 7021 = 469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7021 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7021) = 3 ^ 7 * m + 469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7021.1, data_15_7021.2]

/-- Complete interval computation for depth 15, residue 7022. -/
theorem bounds_15_7022 : exactInterval 15 7022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7022 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7022) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7022 : oddCount 7022 15 = 7 ∧ acceleratedOrbit 15 7022 = 469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7022 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7022) = 3 ^ 7 * m + 469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7022.1, data_15_7022.2]

/-- Complete interval computation for depth 15, residue 7023. -/
theorem bounds_15_7023 : exactInterval 15 7023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7023 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7023) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7023 : oddCount 7023 15 = 9 ∧ acceleratedOrbit 15 7023 = 4220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7023 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7023) = 3 ^ 9 * m + 4220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7023.1, data_15_7023.2]

/-- Complete interval computation for depth 15, residue 7024. -/
theorem bounds_15_7024 : exactInterval 15 7024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7024 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7024) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7024 : oddCount 7024 15 = 6 ∧ acceleratedOrbit 15 7024 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7024 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7024) = 3 ^ 6 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7024.1, data_15_7024.2]

/-- Complete interval computation for depth 15, residue 7025. -/
theorem bounds_15_7025 : exactInterval 15 7025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7025 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7025) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7025 : oddCount 7025 15 = 6 ∧ acceleratedOrbit 15 7025 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7025 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7025) = 3 ^ 6 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7025.1, data_15_7025.2]

/-- Complete interval computation for depth 15, residue 7026. -/
theorem bounds_15_7026 : exactInterval 15 7026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7026 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7026) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7026 : oddCount 7026 15 = 6 ∧ acceleratedOrbit 15 7026 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7026 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7026) = 3 ^ 6 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7026.1, data_15_7026.2]

/-- Complete interval computation for depth 15, residue 7027. -/
theorem bounds_15_7027 : exactInterval 15 7027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7027 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7027) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7027 : oddCount 7027 15 = 6 ∧ acceleratedOrbit 15 7027 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7027 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7027) = 3 ^ 6 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7027.1, data_15_7027.2]

/-- Complete interval computation for depth 15, residue 7028. -/
theorem bounds_15_7028 : exactInterval 15 7028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7028 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7028) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7028 : oddCount 7028 15 = 6 ∧ acceleratedOrbit 15 7028 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7028 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7028) = 3 ^ 6 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7028.1, data_15_7028.2]

/-- Complete interval computation for depth 15, residue 7029. -/
theorem bounds_15_7029 : exactInterval 15 7029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7029 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7029) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7029 : oddCount 7029 15 = 6 ∧ acceleratedOrbit 15 7029 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7029 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7029) = 3 ^ 6 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7029.1, data_15_7029.2]

/-- Complete interval computation for depth 15, residue 7030. -/
theorem bounds_15_7030 : exactInterval 15 7030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7030 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7030) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7030 : oddCount 7030 15 = 7 ∧ acceleratedOrbit 15 7030 = 470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7030 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7030) = 3 ^ 7 * m + 470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7030.1, data_15_7030.2]

/-- Complete interval computation for depth 15, residue 7031. -/
theorem bounds_15_7031 : exactInterval 15 7031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7031 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7031) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7031 : oddCount 7031 15 = 7 ∧ acceleratedOrbit 15 7031 = 470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7031 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7031) = 3 ^ 7 * m + 470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7031.1, data_15_7031.2]

/-- Complete interval computation for depth 15, residue 7032. -/
theorem bounds_15_7032 : exactInterval 15 7032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7032 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7032) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7032 : oddCount 7032 15 = 7 ∧ acceleratedOrbit 15 7032 = 470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7032 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7032) = 3 ^ 7 * m + 470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7032.1, data_15_7032.2]

/-- Complete interval computation for depth 15, residue 7033. -/
theorem bounds_15_7033 : exactInterval 15 7033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7033 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7033) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7033 : oddCount 7033 15 = 9 ∧ acceleratedOrbit 15 7033 = 4226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7033 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7033) = 3 ^ 9 * m + 4226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7033.1, data_15_7033.2]

/-- Complete interval computation for depth 15, residue 7034. -/
theorem bounds_15_7034 : exactInterval 15 7034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7034 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7034) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7034 : oddCount 7034 15 = 7 ∧ acceleratedOrbit 15 7034 = 470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7034 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7034) = 3 ^ 7 * m + 470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7034.1, data_15_7034.2]

/-- Complete interval computation for depth 15, residue 7035. -/
theorem bounds_15_7035 : exactInterval 15 7035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7035 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7035) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7035 : oddCount 7035 15 = 8 ∧ acceleratedOrbit 15 7035 = 1409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7035 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7035) = 3 ^ 8 * m + 1409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7035.1, data_15_7035.2]

/-- Complete interval computation for depth 15, residue 7036. -/
theorem bounds_15_7036 : exactInterval 15 7036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7036 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7036) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7036 : oddCount 7036 15 = 7 ∧ acceleratedOrbit 15 7036 = 470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7036 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7036) = 3 ^ 7 * m + 470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7036.1, data_15_7036.2]

/-- Complete interval computation for depth 15, residue 7037. -/
theorem bounds_15_7037 : exactInterval 15 7037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7037 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7037) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7037 : oddCount 7037 15 = 7 ∧ acceleratedOrbit 15 7037 = 470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7037 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7037) = 3 ^ 7 * m + 470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7037.1, data_15_7037.2]

/-- Complete interval computation for depth 15, residue 7038. -/
theorem bounds_15_7038 : exactInterval 15 7038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7038 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7038) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7038 : oddCount 7038 15 = 11 ∧ acceleratedOrbit 15 7038 = 38060 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7038 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7038) = 3 ^ 11 * m + 38060 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7038.1, data_15_7038.2]

/-- Complete interval computation for depth 15, residue 7039. -/
theorem bounds_15_7039 : exactInterval 15 7039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7039 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7039) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7039 : oddCount 7039 15 = 11 ∧ acceleratedOrbit 15 7039 = 38060 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7039 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7039) = 3 ^ 11 * m + 38060 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7039.1, data_15_7039.2]

/-- Complete interval computation for depth 15, residue 7040. -/
theorem bounds_15_7040 : exactInterval 15 7040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7040 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7040) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7040 : oddCount 7040 15 = 6 ∧ acceleratedOrbit 15 7040 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7040 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7040) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7040.1, data_15_7040.2]

/-- Complete interval computation for depth 15, residue 7041. -/
theorem bounds_15_7041 : exactInterval 15 7041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7041 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7041) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7041 : oddCount 7041 15 = 9 ∧ acceleratedOrbit 15 7041 = 4232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7041 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7041) = 3 ^ 9 * m + 4232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7041.1, data_15_7041.2]

/-- Complete interval computation for depth 15, residue 7042. -/
theorem bounds_15_7042 : exactInterval 15 7042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7042 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7042) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7042 : oddCount 7042 15 = 9 ∧ acceleratedOrbit 15 7042 = 4238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7042 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7042) = 3 ^ 9 * m + 4238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7042.1, data_15_7042.2]

/-- Complete interval computation for depth 15, residue 7043. -/
theorem bounds_15_7043 : exactInterval 15 7043 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7043 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7043) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7043 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7043 : oddCount 7043 15 = 9 ∧ acceleratedOrbit 15 7043 = 4238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7043 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7043) = 3 ^ 9 * m + 4238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7043.1, data_15_7043.2]

/-- Complete interval computation for depth 15, residue 7044. -/
theorem bounds_15_7044 : exactInterval 15 7044 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7044 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7044) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7044 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7044 : oddCount 7044 15 = 9 ∧ acceleratedOrbit 15 7044 = 4238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7044 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7044) = 3 ^ 9 * m + 4238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7044.1, data_15_7044.2]

end Collatz.Research.PassageAtlas.Batch0215
