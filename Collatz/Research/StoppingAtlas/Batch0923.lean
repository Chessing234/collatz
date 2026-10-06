import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0923

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6993. -/
theorem bounds_13_6993 : exactInterval 13 6993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6993 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6993) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6993 : oddCount 6993 13 = 7 ∧ acceleratedOrbit 13 6993 = 1868 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6993 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6993) = 3 ^ 7 * m + 1868 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6993.1, data_13_6993.2]

/-- Complete interval computation for depth 13, residue 6994. -/
theorem bounds_13_6994 : exactInterval 13 6994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6994 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6994) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6994 : oddCount 6994 13 = 7 ∧ acceleratedOrbit 13 6994 = 1868 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6994 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6994) = 3 ^ 7 * m + 1868 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6994.1, data_13_6994.2]

/-- Complete interval computation for depth 13, residue 6995. -/
theorem bounds_13_6995 : exactInterval 13 6995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6995 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6995) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6995 : oddCount 6995 13 = 7 ∧ acceleratedOrbit 13 6995 = 1868 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6995 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6995) = 3 ^ 7 * m + 1868 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6995.1, data_13_6995.2]

/-- Complete interval computation for depth 13, residue 6996. -/
theorem bounds_13_6996 : exactInterval 13 6996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6996 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6996) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6996 : oddCount 6996 13 = 4 ∧ acceleratedOrbit 13 6996 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6996 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6996) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6996.1, data_13_6996.2]

/-- Complete interval computation for depth 13, residue 6997. -/
theorem bounds_13_6997 : exactInterval 13 6997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6997 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6997) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6997 : oddCount 6997 13 = 4 ∧ acceleratedOrbit 13 6997 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6997 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6997) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6997.1, data_13_6997.2]

/-- Complete interval computation for depth 13, residue 6998. -/
theorem bounds_13_6998 : exactInterval 13 6998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6998 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6998) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6998 : oddCount 6998 13 = 8 ∧ acceleratedOrbit 13 6998 = 5609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6998 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6998) = 3 ^ 8 * m + 5609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6998.1, data_13_6998.2]

/-- Complete interval computation for depth 13, residue 6999. -/
theorem bounds_13_6999 : exactInterval 13 6999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6999 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6999) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6999 : oddCount 6999 13 = 8 ∧ acceleratedOrbit 13 6999 = 5609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6999 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6999) = 3 ^ 8 * m + 5609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6999.1, data_13_6999.2]

/-- Complete interval computation for depth 13, residue 7000. -/
theorem bounds_13_7000 : exactInterval 13 7000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7000 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7000) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7000 : oddCount 7000 13 = 5 ∧ acceleratedOrbit 13 7000 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7000 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7000) = 3 ^ 5 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7000.1, data_13_7000.2]

/-- Complete interval computation for depth 13, residue 7001. -/
theorem bounds_13_7001 : exactInterval 13 7001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7001 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7001) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7001 : oddCount 7001 13 = 5 ∧ acceleratedOrbit 13 7001 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7001 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7001) = 3 ^ 5 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7001.1, data_13_7001.2]

/-- Complete interval computation for depth 13, residue 7002. -/
theorem bounds_13_7002 : exactInterval 13 7002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7002 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7002) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7002 : oddCount 7002 13 = 5 ∧ acceleratedOrbit 13 7002 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7002 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7002) = 3 ^ 5 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7002.1, data_13_7002.2]

/-- Complete interval computation for depth 13, residue 7003. -/
theorem bounds_13_7003 : exactInterval 13 7003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7003 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7003) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7003 : oddCount 7003 13 = 7 ∧ acceleratedOrbit 13 7003 = 1870 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7003 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7003) = 3 ^ 7 * m + 1870 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7003.1, data_13_7003.2]

/-- Complete interval computation for depth 13, residue 7004. -/
theorem bounds_13_7004 : exactInterval 13 7004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7004 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7004) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7004 : oddCount 7004 13 = 5 ∧ acceleratedOrbit 13 7004 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7004 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7004) = 3 ^ 5 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7004.1, data_13_7004.2]

/-- Complete interval computation for depth 13, residue 7005. -/
theorem bounds_13_7005 : exactInterval 13 7005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7005 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7005) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7005 : oddCount 7005 13 = 5 ∧ acceleratedOrbit 13 7005 = 208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7005 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7005) = 3 ^ 5 * m + 208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7005.1, data_13_7005.2]

/-- Complete interval computation for depth 13, residue 7006. -/
theorem bounds_13_7006 : exactInterval 13 7006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7006 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7006) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7006 : oddCount 7006 13 = 8 ∧ acceleratedOrbit 13 7006 = 5615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7006 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7006) = 3 ^ 8 * m + 5615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7006.1, data_13_7006.2]

/-- Complete interval computation for depth 13, residue 7007. -/
theorem bounds_13_7007 : exactInterval 13 7007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7007 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7007) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7007 : oddCount 7007 13 = 8 ∧ acceleratedOrbit 13 7007 = 5615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7007 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7007) = 3 ^ 8 * m + 5615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7007.1, data_13_7007.2]

/-- Complete interval computation for depth 13, residue 7008. -/
theorem bounds_13_7008 : exactInterval 13 7008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7008 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7008) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7008 : oddCount 7008 13 = 5 ∧ acceleratedOrbit 13 7008 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7008 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7008) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7008.1, data_13_7008.2]

end Collatz.Research.StoppingAtlas.Batch0923
