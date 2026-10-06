import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0989

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 8007. -/
theorem bounds_13_8007 : exactInterval 13 8007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8007 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8007) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8007 : oddCount 8007 13 = 7 ∧ acceleratedOrbit 13 8007 = 2138 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8007 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8007) = 3 ^ 7 * m + 2138 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8007.1, data_13_8007.2]

/-- Complete interval computation for depth 13, residue 8008. -/
theorem bounds_13_8008 : exactInterval 13 8008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8008 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8008) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8008 : oddCount 8008 13 = 8 ∧ acceleratedOrbit 13 8008 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8008 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8008) = 3 ^ 8 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8008.1, data_13_8008.2]

/-- Complete interval computation for depth 13, residue 8009. -/
theorem bounds_13_8009 : exactInterval 13 8009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8009 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8009) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8009 : oddCount 8009 13 = 6 ∧ acceleratedOrbit 13 8009 = 713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8009 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8009) = 3 ^ 6 * m + 713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8009.1, data_13_8009.2]

/-- Complete interval computation for depth 13, residue 8010. -/
theorem bounds_13_8010 : exactInterval 13 8010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8010 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8010) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8010 : oddCount 8010 13 = 8 ∧ acceleratedOrbit 13 8010 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8010 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8010) = 3 ^ 8 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8010.1, data_13_8010.2]

/-- Complete interval computation for depth 13, residue 8011. -/
theorem bounds_13_8011 : exactInterval 13 8011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8011 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8011) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8011 : oddCount 8011 13 = 5 ∧ acceleratedOrbit 13 8011 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8011 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8011) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8011.1, data_13_8011.2]

/-- Complete interval computation for depth 13, residue 8012. -/
theorem bounds_13_8012 : exactInterval 13 8012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8012 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8012) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8012 : oddCount 8012 13 = 8 ∧ acceleratedOrbit 13 8012 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8012 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8012) = 3 ^ 8 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8012.1, data_13_8012.2]

/-- Complete interval computation for depth 13, residue 8013. -/
theorem bounds_13_8013 : exactInterval 13 8013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8013 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8013) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8013 : oddCount 8013 13 = 8 ∧ acceleratedOrbit 13 8013 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8013 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8013) = 3 ^ 8 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8013.1, data_13_8013.2]

/-- Complete interval computation for depth 13, residue 8014. -/
theorem bounds_13_8014 : exactInterval 13 8014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8014 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8014) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8014 : oddCount 8014 13 = 8 ∧ acceleratedOrbit 13 8014 = 6421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8014 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8014) = 3 ^ 8 * m + 6421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8014.1, data_13_8014.2]

/-- Complete interval computation for depth 13, residue 8015. -/
theorem bounds_13_8015 : exactInterval 13 8015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8015 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8015) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8015 : oddCount 8015 13 = 8 ∧ acceleratedOrbit 13 8015 = 6421 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8015 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8015) = 3 ^ 8 * m + 6421 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8015.1, data_13_8015.2]

/-- Complete interval computation for depth 13, residue 8016. -/
theorem bounds_13_8016 : exactInterval 13 8016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8016 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8016) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8016 : oddCount 8016 13 = 5 ∧ acceleratedOrbit 13 8016 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8016 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8016) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8016.1, data_13_8016.2]

/-- Complete interval computation for depth 13, residue 8017. -/
theorem bounds_13_8017 : exactInterval 13 8017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8017 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8017) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8017 : oddCount 8017 13 = 8 ∧ acceleratedOrbit 13 8017 = 6425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8017 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8017) = 3 ^ 8 * m + 6425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8017.1, data_13_8017.2]

/-- Complete interval computation for depth 13, residue 8018. -/
theorem bounds_13_8018 : exactInterval 13 8018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8018 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8018) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8018 : oddCount 8018 13 = 9 ∧ acceleratedOrbit 13 8018 = 19273 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8018 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8018) = 3 ^ 9 * m + 19273 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8018.1, data_13_8018.2]

/-- Complete interval computation for depth 13, residue 8019. -/
theorem bounds_13_8019 : exactInterval 13 8019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8019 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8019) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8019 : oddCount 8019 13 = 9 ∧ acceleratedOrbit 13 8019 = 19273 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8019 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8019) = 3 ^ 9 * m + 19273 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8019.1, data_13_8019.2]

/-- Complete interval computation for depth 13, residue 8020. -/
theorem bounds_13_8020 : exactInterval 13 8020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8020 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8020) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8020 : oddCount 8020 13 = 5 ∧ acceleratedOrbit 13 8020 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8020 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8020) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8020.1, data_13_8020.2]

/-- Complete interval computation for depth 13, residue 8021. -/
theorem bounds_13_8021 : exactInterval 13 8021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8021 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8021) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8021 : oddCount 8021 13 = 5 ∧ acceleratedOrbit 13 8021 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8021 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8021) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8021.1, data_13_8021.2]

/-- Complete interval computation for depth 13, residue 8022. -/
theorem bounds_13_8022 : exactInterval 13 8022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8022 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8022) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8022 : oddCount 8022 13 = 7 ∧ acceleratedOrbit 13 8022 = 2143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8022 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8022) = 3 ^ 7 * m + 2143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8022.1, data_13_8022.2]

end Collatz.Research.StoppingAtlas.Batch0989
