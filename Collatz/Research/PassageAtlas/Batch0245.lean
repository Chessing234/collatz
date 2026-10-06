import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0245

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 7995. -/
theorem bounds_15_7995 : exactInterval 15 7995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7995 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7995) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7995 : oddCount 7995 15 = 6 ∧ acceleratedOrbit 15 7995 = 178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7995 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7995) = 3 ^ 6 * m + 178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7995.1, data_15_7995.2]

/-- Complete interval computation for depth 15, residue 7996. -/
theorem bounds_15_7996 : exactInterval 15 7996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7996 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7996) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7996 : oddCount 7996 15 = 6 ∧ acceleratedOrbit 15 7996 = 178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7996 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7996) = 3 ^ 6 * m + 178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7996.1, data_15_7996.2]

/-- Complete interval computation for depth 15, residue 7997. -/
theorem bounds_15_7997 : exactInterval 15 7997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7997 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7997) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7997 : oddCount 7997 15 = 6 ∧ acceleratedOrbit 15 7997 = 178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7997 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7997) = 3 ^ 6 * m + 178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7997.1, data_15_7997.2]

/-- Complete interval computation for depth 15, residue 7998. -/
theorem bounds_15_7998 : exactInterval 15 7998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7998 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7998) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7998 : oddCount 7998 15 = 11 ∧ acceleratedOrbit 15 7998 = 43253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7998 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7998) = 3 ^ 11 * m + 43253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7998.1, data_15_7998.2]

/-- Complete interval computation for depth 15, residue 7999. -/
theorem bounds_15_7999 : exactInterval 15 7999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7999 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7999) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7999 : oddCount 7999 15 = 11 ∧ acceleratedOrbit 15 7999 = 43253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7999 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7999) = 3 ^ 11 * m + 43253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7999.1, data_15_7999.2]

/-- Complete interval computation for depth 15, residue 8000. -/
theorem bounds_15_8000 : exactInterval 15 8000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8000 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8000) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8000 : oddCount 8000 15 = 6 ∧ acceleratedOrbit 15 8000 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8000 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8000) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8000.1, data_15_8000.2]

/-- Complete interval computation for depth 15, residue 8001. -/
theorem bounds_15_8001 : exactInterval 15 8001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8001 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8001) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8001 : oddCount 8001 15 = 6 ∧ acceleratedOrbit 15 8001 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8001 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8001) = 3 ^ 6 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8001.1, data_15_8001.2]

/-- Complete interval computation for depth 15, residue 8002. -/
theorem bounds_15_8002 : exactInterval 15 8002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8002 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8002) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8002 : oddCount 8002 15 = 7 ∧ acceleratedOrbit 15 8002 = 535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8002 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8002) = 3 ^ 7 * m + 535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8002.1, data_15_8002.2]

/-- Complete interval computation for depth 15, residue 8003. -/
theorem bounds_15_8003 : exactInterval 15 8003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8003 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8003) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8003 : oddCount 8003 15 = 7 ∧ acceleratedOrbit 15 8003 = 535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8003 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8003) = 3 ^ 7 * m + 535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8003.1, data_15_8003.2]

/-- Complete interval computation for depth 15, residue 8004. -/
theorem bounds_15_8004 : exactInterval 15 8004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8004 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8004) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8004 : oddCount 8004 15 = 6 ∧ acceleratedOrbit 15 8004 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8004 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8004) = 3 ^ 6 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8004.1, data_15_8004.2]

/-- Complete interval computation for depth 15, residue 8005. -/
theorem bounds_15_8005 : exactInterval 15 8005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8005 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8005) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8005 : oddCount 8005 15 = 6 ∧ acceleratedOrbit 15 8005 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8005 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8005) = 3 ^ 6 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8005.1, data_15_8005.2]

/-- Complete interval computation for depth 15, residue 8006. -/
theorem bounds_15_8006 : exactInterval 15 8006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8006 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8006) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8006 : oddCount 8006 15 = 6 ∧ acceleratedOrbit 15 8006 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8006 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8006) = 3 ^ 6 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8006.1, data_15_8006.2]

/-- Complete interval computation for depth 15, residue 8007. -/
theorem bounds_15_8007 : exactInterval 15 8007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8007 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8007) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8007 : oddCount 8007 15 = 8 ∧ acceleratedOrbit 15 8007 = 1604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8007 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8007) = 3 ^ 8 * m + 1604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8007.1, data_15_8007.2]

/-- Complete interval computation for depth 15, residue 8008. -/
theorem bounds_15_8008 : exactInterval 15 8008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8008 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8008) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8008 : oddCount 8008 15 = 9 ∧ acceleratedOrbit 15 8008 = 4819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8008 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8008) = 3 ^ 9 * m + 4819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8008.1, data_15_8008.2]

/-- Complete interval computation for depth 15, residue 8009. -/
theorem bounds_15_8009 : exactInterval 15 8009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8009 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8009) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8009 : oddCount 8009 15 = 7 ∧ acceleratedOrbit 15 8009 = 535 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8009 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8009) = 3 ^ 7 * m + 535 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8009.1, data_15_8009.2]

/-- Complete interval computation for depth 15, residue 8010. -/
theorem bounds_15_8010 : exactInterval 15 8010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8010 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8010) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8010 : oddCount 8010 15 = 9 ∧ acceleratedOrbit 15 8010 = 4819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8010 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8010) = 3 ^ 9 * m + 4819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8010.1, data_15_8010.2]

/-- Complete interval computation for depth 15, residue 8011. -/
theorem bounds_15_8011 : exactInterval 15 8011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8011 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8011) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8011 : oddCount 8011 15 = 6 ∧ acceleratedOrbit 15 8011 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8011 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8011) = 3 ^ 6 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8011.1, data_15_8011.2]

/-- Complete interval computation for depth 15, residue 8012. -/
theorem bounds_15_8012 : exactInterval 15 8012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8012 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8012) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8012 : oddCount 8012 15 = 9 ∧ acceleratedOrbit 15 8012 = 4819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8012 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8012) = 3 ^ 9 * m + 4819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8012.1, data_15_8012.2]

/-- Complete interval computation for depth 15, residue 8013. -/
theorem bounds_15_8013 : exactInterval 15 8013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8013 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8013) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8013 : oddCount 8013 15 = 9 ∧ acceleratedOrbit 15 8013 = 4819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8013 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8013) = 3 ^ 9 * m + 4819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8013.1, data_15_8013.2]

/-- Complete interval computation for depth 15, residue 8014. -/
theorem bounds_15_8014 : exactInterval 15 8014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8014 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8014) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8014 : oddCount 8014 15 = 9 ∧ acceleratedOrbit 15 8014 = 4816 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8014 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8014) = 3 ^ 9 * m + 4816 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8014.1, data_15_8014.2]

/-- Complete interval computation for depth 15, residue 8015. -/
theorem bounds_15_8015 : exactInterval 15 8015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8015 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8015) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8015 : oddCount 8015 15 = 9 ∧ acceleratedOrbit 15 8015 = 4816 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8015 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8015) = 3 ^ 9 * m + 4816 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8015.1, data_15_8015.2]

/-- Complete interval computation for depth 15, residue 8016. -/
theorem bounds_15_8016 : exactInterval 15 8016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8016 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8016) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8016 : oddCount 8016 15 = 6 ∧ acceleratedOrbit 15 8016 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8016 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8016) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8016.1, data_15_8016.2]

/-- Complete interval computation for depth 15, residue 8017. -/
theorem bounds_15_8017 : exactInterval 15 8017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8017 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8017) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8017 : oddCount 8017 15 = 9 ∧ acceleratedOrbit 15 8017 = 4819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8017 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8017) = 3 ^ 9 * m + 4819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8017.1, data_15_8017.2]

/-- Complete interval computation for depth 15, residue 8018. -/
theorem bounds_15_8018 : exactInterval 15 8018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8018 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8018) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8018 : oddCount 8018 15 = 10 ∧ acceleratedOrbit 15 8018 = 14455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8018 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8018) = 3 ^ 10 * m + 14455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8018.1, data_15_8018.2]

/-- Complete interval computation for depth 15, residue 8019. -/
theorem bounds_15_8019 : exactInterval 15 8019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8019 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8019) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8019 : oddCount 8019 15 = 10 ∧ acceleratedOrbit 15 8019 = 14455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8019 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8019) = 3 ^ 10 * m + 14455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8019.1, data_15_8019.2]

/-- Complete interval computation for depth 15, residue 8020. -/
theorem bounds_15_8020 : exactInterval 15 8020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8020 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8020) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8020 : oddCount 8020 15 = 6 ∧ acceleratedOrbit 15 8020 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8020 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8020) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8020.1, data_15_8020.2]

/-- Complete interval computation for depth 15, residue 8021. -/
theorem bounds_15_8021 : exactInterval 15 8021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8021 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8021) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8021 : oddCount 8021 15 = 6 ∧ acceleratedOrbit 15 8021 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8021 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8021) = 3 ^ 6 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8021.1, data_15_8021.2]

/-- Complete interval computation for depth 15, residue 8022. -/
theorem bounds_15_8022 : exactInterval 15 8022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8022 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8022) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8022 : oddCount 8022 15 = 9 ∧ acceleratedOrbit 15 8022 = 4823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8022 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8022) = 3 ^ 9 * m + 4823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8022.1, data_15_8022.2]

/-- Complete interval computation for depth 15, residue 8023. -/
theorem bounds_15_8023 : exactInterval 15 8023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8023 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8023) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8023 : oddCount 8023 15 = 9 ∧ acceleratedOrbit 15 8023 = 4823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8023 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8023) = 3 ^ 9 * m + 4823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8023.1, data_15_8023.2]

/-- Complete interval computation for depth 15, residue 8024. -/
theorem bounds_15_8024 : exactInterval 15 8024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8024 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8024) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8024 : oddCount 8024 15 = 8 ∧ acceleratedOrbit 15 8024 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8024 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8024) = 3 ^ 8 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8024.1, data_15_8024.2]

/-- Complete interval computation for depth 15, residue 8025. -/
theorem bounds_15_8025 : exactInterval 15 8025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8025 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8025) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8025 : oddCount 8025 15 = 8 ∧ acceleratedOrbit 15 8025 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8025 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8025) = 3 ^ 8 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8025.1, data_15_8025.2]

/-- Complete interval computation for depth 15, residue 8026. -/
theorem bounds_15_8026 : exactInterval 15 8026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8026 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8026) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8026 : oddCount 8026 15 = 8 ∧ acceleratedOrbit 15 8026 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8026 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8026) = 3 ^ 8 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8026.1, data_15_8026.2]

/-- Complete interval computation for depth 15, residue 8027. -/
theorem bounds_15_8027 : exactInterval 15 8027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8027 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8027) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8027 : oddCount 8027 15 = 11 ∧ acceleratedOrbit 15 8027 = 43406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8027 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8027) = 3 ^ 11 * m + 43406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8027.1, data_15_8027.2]

end Collatz.Research.PassageAtlas.Batch0245
