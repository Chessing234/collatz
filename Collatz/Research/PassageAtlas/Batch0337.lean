import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0337

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 11010. -/
theorem bounds_15_11010 : exactInterval 15 11010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11010 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11010) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11010 : oddCount 11010 15 = 8 ∧ acceleratedOrbit 15 11010 = 2207 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11010 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11010) = 3 ^ 8 * m + 2207 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11010.1, data_15_11010.2]

/-- Complete interval computation for depth 15, residue 11011. -/
theorem bounds_15_11011 : exactInterval 15 11011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11011 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11011) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11011 : oddCount 11011 15 = 8 ∧ acceleratedOrbit 15 11011 = 2207 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11011 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11011) = 3 ^ 8 * m + 2207 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11011.1, data_15_11011.2]

/-- Complete interval computation for depth 15, residue 11012. -/
theorem bounds_15_11012 : exactInterval 15 11012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11012 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11012) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11012 : oddCount 11012 15 = 5 ∧ acceleratedOrbit 15 11012 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11012 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11012) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11012.1, data_15_11012.2]

/-- Complete interval computation for depth 15, residue 11013. -/
theorem bounds_15_11013 : exactInterval 15 11013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11013 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11013) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11013 : oddCount 11013 15 = 5 ∧ acceleratedOrbit 15 11013 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11013 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11013) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11013.1, data_15_11013.2]

/-- Complete interval computation for depth 15, residue 11014. -/
theorem bounds_15_11014 : exactInterval 15 11014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11014 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11014) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11014 : oddCount 11014 15 = 5 ∧ acceleratedOrbit 15 11014 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11014 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11014) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11014.1, data_15_11014.2]

/-- Complete interval computation for depth 15, residue 11015. -/
theorem bounds_15_11015 : exactInterval 15 11015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11015 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11015) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11015 : oddCount 11015 15 = 8 ∧ acceleratedOrbit 15 11015 = 2206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11015 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11015) = 3 ^ 8 * m + 2206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11015.1, data_15_11015.2]

/-- Complete interval computation for depth 15, residue 11016. -/
theorem bounds_15_11016 : exactInterval 15 11016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11016 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11016) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11016 : oddCount 11016 15 = 7 ∧ acceleratedOrbit 15 11016 = 737 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11016 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11016) = 3 ^ 7 * m + 737 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11016.1, data_15_11016.2]

/-- Complete interval computation for depth 15, residue 11017. -/
theorem bounds_15_11017 : exactInterval 15 11017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11017 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11017) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11017 : oddCount 11017 15 = 10 ∧ acceleratedOrbit 15 11017 = 19858 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11017 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11017) = 3 ^ 10 * m + 19858 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11017.1, data_15_11017.2]

/-- Complete interval computation for depth 15, residue 11018. -/
theorem bounds_15_11018 : exactInterval 15 11018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11018 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11018) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11018 : oddCount 11018 15 = 7 ∧ acceleratedOrbit 15 11018 = 737 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11018 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11018) = 3 ^ 7 * m + 737 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11018.1, data_15_11018.2]

/-- Complete interval computation for depth 15, residue 11019. -/
theorem bounds_15_11019 : exactInterval 15 11019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11019 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11019) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11019 : oddCount 11019 15 = 10 ∧ acceleratedOrbit 15 11019 = 19865 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11019 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11019) = 3 ^ 10 * m + 19865 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11019.1, data_15_11019.2]

/-- Complete interval computation for depth 15, residue 11020. -/
theorem bounds_15_11020 : exactInterval 15 11020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11020 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11020) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11020 : oddCount 11020 15 = 7 ∧ acceleratedOrbit 15 11020 = 737 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11020 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11020) = 3 ^ 7 * m + 737 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11020.1, data_15_11020.2]

/-- Complete interval computation for depth 15, residue 11021. -/
theorem bounds_15_11021 : exactInterval 15 11021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11021 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11021) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11021 : oddCount 11021 15 = 7 ∧ acceleratedOrbit 15 11021 = 737 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11021 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11021) = 3 ^ 7 * m + 737 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11021.1, data_15_11021.2]

/-- Complete interval computation for depth 15, residue 11022. -/
theorem bounds_15_11022 : exactInterval 15 11022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11022 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11022) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11022 : oddCount 11022 15 = 5 ∧ acceleratedOrbit 15 11022 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11022 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11022) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11022.1, data_15_11022.2]

/-- Complete interval computation for depth 15, residue 11023. -/
theorem bounds_15_11023 : exactInterval 15 11023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11023 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11023) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11023 : oddCount 11023 15 = 5 ∧ acceleratedOrbit 15 11023 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11023 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11023) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11023.1, data_15_11023.2]

/-- Complete interval computation for depth 15, residue 11024. -/
theorem bounds_15_11024 : exactInterval 15 11024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11024 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11024) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11024 : oddCount 11024 15 = 5 ∧ acceleratedOrbit 15 11024 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11024 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11024) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11024.1, data_15_11024.2]

/-- Complete interval computation for depth 15, residue 11025. -/
theorem bounds_15_11025 : exactInterval 15 11025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11025 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11025) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11025 : oddCount 11025 15 = 7 ∧ acceleratedOrbit 15 11025 = 737 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11025 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11025) = 3 ^ 7 * m + 737 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11025.1, data_15_11025.2]

/-- Complete interval computation for depth 15, residue 11026. -/
theorem bounds_15_11026 : exactInterval 15 11026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11026 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11026) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11026 : oddCount 11026 15 = 8 ∧ acceleratedOrbit 15 11026 = 2209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11026 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11026) = 3 ^ 8 * m + 2209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11026.1, data_15_11026.2]

/-- Complete interval computation for depth 15, residue 11027. -/
theorem bounds_15_11027 : exactInterval 15 11027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11027 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11027) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11027 : oddCount 11027 15 = 8 ∧ acceleratedOrbit 15 11027 = 2209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11027 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11027) = 3 ^ 8 * m + 2209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11027.1, data_15_11027.2]

/-- Complete interval computation for depth 15, residue 11028. -/
theorem bounds_15_11028 : exactInterval 15 11028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11028 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11028) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11028 : oddCount 11028 15 = 5 ∧ acceleratedOrbit 15 11028 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11028 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11028) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11028.1, data_15_11028.2]

/-- Complete interval computation for depth 15, residue 11029. -/
theorem bounds_15_11029 : exactInterval 15 11029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11029 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11029) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11029 : oddCount 11029 15 = 5 ∧ acceleratedOrbit 15 11029 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11029 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11029) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11029.1, data_15_11029.2]

/-- Complete interval computation for depth 15, residue 11030. -/
theorem bounds_15_11030 : exactInterval 15 11030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11030 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11030) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11030 : oddCount 11030 15 = 7 ∧ acceleratedOrbit 15 11030 = 737 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11030 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11030) = 3 ^ 7 * m + 737 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11030.1, data_15_11030.2]

/-- Complete interval computation for depth 15, residue 11031. -/
theorem bounds_15_11031 : exactInterval 15 11031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11031 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11031) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11031 : oddCount 11031 15 = 7 ∧ acceleratedOrbit 15 11031 = 737 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11031 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11031) = 3 ^ 7 * m + 737 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11031.1, data_15_11031.2]

/-- Complete interval computation for depth 15, residue 11032. -/
theorem bounds_15_11032 : exactInterval 15 11032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11032 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11032) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11032 : oddCount 11032 15 = 5 ∧ acceleratedOrbit 15 11032 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11032 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11032) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11032.1, data_15_11032.2]

/-- Complete interval computation for depth 15, residue 11033. -/
theorem bounds_15_11033 : exactInterval 15 11033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11033 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11033) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11033 : oddCount 11033 15 = 10 ∧ acceleratedOrbit 15 11033 = 19889 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11033 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11033) = 3 ^ 10 * m + 19889 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11033.1, data_15_11033.2]

/-- Complete interval computation for depth 15, residue 11034. -/
theorem bounds_15_11034 : exactInterval 15 11034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11034 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11034) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11034 : oddCount 11034 15 = 5 ∧ acceleratedOrbit 15 11034 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11034 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11034) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11034.1, data_15_11034.2]

/-- Complete interval computation for depth 15, residue 11035. -/
theorem bounds_15_11035 : exactInterval 15 11035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11035 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11035) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11035 : oddCount 11035 15 = 10 ∧ acceleratedOrbit 15 11035 = 19888 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11035 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11035) = 3 ^ 10 * m + 19888 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11035.1, data_15_11035.2]

/-- Complete interval computation for depth 15, residue 11036. -/
theorem bounds_15_11036 : exactInterval 15 11036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11036 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11036) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11036 : oddCount 11036 15 = 8 ∧ acceleratedOrbit 15 11036 = 2213 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11036 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11036) = 3 ^ 8 * m + 2213 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11036.1, data_15_11036.2]

/-- Complete interval computation for depth 15, residue 11037. -/
theorem bounds_15_11037 : exactInterval 15 11037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11037 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11037) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11037 : oddCount 11037 15 = 8 ∧ acceleratedOrbit 15 11037 = 2213 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11037 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11037) = 3 ^ 8 * m + 2213 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11037.1, data_15_11037.2]

/-- Complete interval computation for depth 15, residue 11038. -/
theorem bounds_15_11038 : exactInterval 15 11038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11038 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11038) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11038 : oddCount 11038 15 = 8 ∧ acceleratedOrbit 15 11038 = 2213 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11038 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11038) = 3 ^ 8 * m + 2213 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11038.1, data_15_11038.2]

/-- Complete interval computation for depth 15, residue 11039. -/
theorem bounds_15_11039 : exactInterval 15 11039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11039 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11039) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11039 : oddCount 11039 15 = 11 ∧ acceleratedOrbit 15 11039 = 59687 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11039 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11039) = 3 ^ 11 * m + 59687 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11039.1, data_15_11039.2]

/-- Complete interval computation for depth 15, residue 11040. -/
theorem bounds_15_11040 : exactInterval 15 11040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11040 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11040) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11040 : oddCount 11040 15 = 5 ∧ acceleratedOrbit 15 11040 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11040 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11040) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11040.1, data_15_11040.2]

/-- Complete interval computation for depth 15, residue 11041. -/
theorem bounds_15_11041 : exactInterval 15 11041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11041 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11041) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11041 : oddCount 11041 15 = 8 ∧ acceleratedOrbit 15 11041 = 2213 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11041 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11041) = 3 ^ 8 * m + 2213 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11041.1, data_15_11041.2]

end Collatz.Research.PassageAtlas.Batch0337
