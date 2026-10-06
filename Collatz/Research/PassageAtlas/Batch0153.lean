import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0153

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 4980. -/
theorem bounds_15_4980 : exactInterval 15 4980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4980 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4980) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4980 : oddCount 4980 15 = 7 ∧ acceleratedOrbit 15 4980 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4980 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4980) = 3 ^ 7 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4980.1, data_15_4980.2]

/-- Complete interval computation for depth 15, residue 4981. -/
theorem bounds_15_4981 : exactInterval 15 4981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4981 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4981) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4981 : oddCount 4981 15 = 7 ∧ acceleratedOrbit 15 4981 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4981 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4981) = 3 ^ 7 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4981.1, data_15_4981.2]

/-- Complete interval computation for depth 15, residue 4982. -/
theorem bounds_15_4982 : exactInterval 15 4982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4982 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4982) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4982 : oddCount 4982 15 = 10 ∧ acceleratedOrbit 15 4982 = 8990 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4982 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4982) = 3 ^ 10 * m + 8990 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4982.1, data_15_4982.2]

/-- Complete interval computation for depth 15, residue 4983. -/
theorem bounds_15_4983 : exactInterval 15 4983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4983 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4983) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4983 : oddCount 4983 15 = 10 ∧ acceleratedOrbit 15 4983 = 8990 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4983 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4983) = 3 ^ 10 * m + 8990 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4983.1, data_15_4983.2]

/-- Complete interval computation for depth 15, residue 4984. -/
theorem bounds_15_4984 : exactInterval 15 4984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4984 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4984) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4984 : oddCount 4984 15 = 8 ∧ acceleratedOrbit 15 4984 = 1000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4984 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4984) = 3 ^ 8 * m + 1000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4984.1, data_15_4984.2]

/-- Complete interval computation for depth 15, residue 4985. -/
theorem bounds_15_4985 : exactInterval 15 4985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4985 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4985) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4985 : oddCount 4985 15 = 11 ∧ acceleratedOrbit 15 4985 = 26963 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4985 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4985) = 3 ^ 11 * m + 26963 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4985.1, data_15_4985.2]

/-- Complete interval computation for depth 15, residue 4986. -/
theorem bounds_15_4986 : exactInterval 15 4986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4986 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4986) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4986 : oddCount 4986 15 = 8 ∧ acceleratedOrbit 15 4986 = 1000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4986 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4986) = 3 ^ 8 * m + 1000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4986.1, data_15_4986.2]

/-- Complete interval computation for depth 15, residue 4987. -/
theorem bounds_15_4987 : exactInterval 15 4987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4987 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4987) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4987 : oddCount 4987 15 = 12 ∧ acceleratedOrbit 15 4987 = 80918 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4987 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4987) = 3 ^ 12 * m + 80918 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4987.1, data_15_4987.2]

/-- Complete interval computation for depth 15, residue 4988. -/
theorem bounds_15_4988 : exactInterval 15 4988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4988 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4988) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4988 : oddCount 4988 15 = 8 ∧ acceleratedOrbit 15 4988 = 1000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4988 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4988) = 3 ^ 8 * m + 1000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4988.1, data_15_4988.2]

/-- Complete interval computation for depth 15, residue 4989. -/
theorem bounds_15_4989 : exactInterval 15 4989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4989 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4989) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4989 : oddCount 4989 15 = 8 ∧ acceleratedOrbit 15 4989 = 1000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4989 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4989) = 3 ^ 8 * m + 1000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4989.1, data_15_4989.2]

/-- Complete interval computation for depth 15, residue 4990. -/
theorem bounds_15_4990 : exactInterval 15 4990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4990 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4990) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4990 : oddCount 4990 15 = 10 ∧ acceleratedOrbit 15 4990 = 8996 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4990 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4990) = 3 ^ 10 * m + 8996 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4990.1, data_15_4990.2]

/-- Complete interval computation for depth 15, residue 4991. -/
theorem bounds_15_4991 : exactInterval 15 4991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4991 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4991) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4991 : oddCount 4991 15 = 10 ∧ acceleratedOrbit 15 4991 = 8996 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4991 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4991) = 3 ^ 10 * m + 8996 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4991.1, data_15_4991.2]

/-- Complete interval computation for depth 15, residue 4992. -/
theorem bounds_15_4992 : exactInterval 15 4992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4992 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4992) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4992 : oddCount 4992 15 = 5 ∧ acceleratedOrbit 15 4992 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4992 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4992) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4992.1, data_15_4992.2]

/-- Complete interval computation for depth 15, residue 4993. -/
theorem bounds_15_4993 : exactInterval 15 4993 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4993 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4993) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4993 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4993 : oddCount 4993 15 = 8 ∧ acceleratedOrbit 15 4993 = 1001 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4993 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4993) = 3 ^ 8 * m + 1001 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4993.1, data_15_4993.2]

/-- Complete interval computation for depth 15, residue 4994. -/
theorem bounds_15_4994 : exactInterval 15 4994 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4994 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4994) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4994 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4994 : oddCount 4994 15 = 7 ∧ acceleratedOrbit 15 4994 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4994 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4994) = 3 ^ 7 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4994.1, data_15_4994.2]

/-- Complete interval computation for depth 15, residue 4995. -/
theorem bounds_15_4995 : exactInterval 15 4995 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4995 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4995) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4995 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4995 : oddCount 4995 15 = 7 ∧ acceleratedOrbit 15 4995 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4995 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4995) = 3 ^ 7 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4995.1, data_15_4995.2]

/-- Complete interval computation for depth 15, residue 4996. -/
theorem bounds_15_4996 : exactInterval 15 4996 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4996 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4996) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4996 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4996 : oddCount 4996 15 = 9 ∧ acceleratedOrbit 15 4996 = 3007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4996 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4996) = 3 ^ 9 * m + 3007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4996.1, data_15_4996.2]

/-- Complete interval computation for depth 15, residue 4997. -/
theorem bounds_15_4997 : exactInterval 15 4997 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4997 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4997) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4997 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4997 : oddCount 4997 15 = 9 ∧ acceleratedOrbit 15 4997 = 3007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4997 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4997) = 3 ^ 9 * m + 3007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4997.1, data_15_4997.2]

/-- Complete interval computation for depth 15, residue 4998. -/
theorem bounds_15_4998 : exactInterval 15 4998 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4998 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4998) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4998 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4998 : oddCount 4998 15 = 9 ∧ acceleratedOrbit 15 4998 = 3007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4998 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4998) = 3 ^ 9 * m + 3007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4998.1, data_15_4998.2]

/-- Complete interval computation for depth 15, residue 4999. -/
theorem bounds_15_4999 : exactInterval 15 4999 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4999 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4999) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4999 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4999 : oddCount 4999 15 = 7 ∧ acceleratedOrbit 15 4999 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4999 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4999) = 3 ^ 7 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4999.1, data_15_4999.2]

/-- Complete interval computation for depth 15, residue 5000. -/
theorem bounds_15_5000 : exactInterval 15 5000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5000 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5000) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5000 : oddCount 5000 15 = 4 ∧ acceleratedOrbit 15 5000 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5000 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5000) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5000.1, data_15_5000.2]

/-- Complete interval computation for depth 15, residue 5001. -/
theorem bounds_15_5001 : exactInterval 15 5001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5001 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5001) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5001 : oddCount 5001 15 = 10 ∧ acceleratedOrbit 15 5001 = 9017 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5001 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5001) = 3 ^ 10 * m + 9017 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5001.1, data_15_5001.2]

/-- Complete interval computation for depth 15, residue 5002. -/
theorem bounds_15_5002 : exactInterval 15 5002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5002 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5002) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5002 : oddCount 5002 15 = 4 ∧ acceleratedOrbit 15 5002 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5002 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5002) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5002.1, data_15_5002.2]

/-- Complete interval computation for depth 15, residue 5003. -/
theorem bounds_15_5003 : exactInterval 15 5003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5003 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5003) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5003 : oddCount 5003 15 = 9 ∧ acceleratedOrbit 15 5003 = 3007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5003 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5003) = 3 ^ 9 * m + 3007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5003.1, data_15_5003.2]

/-- Complete interval computation for depth 15, residue 5004. -/
theorem bounds_15_5004 : exactInterval 15 5004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5004 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5004) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5004 : oddCount 5004 15 = 4 ∧ acceleratedOrbit 15 5004 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5004 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5004) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5004.1, data_15_5004.2]

/-- Complete interval computation for depth 15, residue 5005. -/
theorem bounds_15_5005 : exactInterval 15 5005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5005 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5005) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5005 : oddCount 5005 15 = 4 ∧ acceleratedOrbit 15 5005 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5005 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5005) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5005.1, data_15_5005.2]

/-- Complete interval computation for depth 15, residue 5006. -/
theorem bounds_15_5006 : exactInterval 15 5006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5006 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5006) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5006 : oddCount 5006 15 = 9 ∧ acceleratedOrbit 15 5006 = 3010 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5006 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5006) = 3 ^ 9 * m + 3010 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5006.1, data_15_5006.2]

/-- Complete interval computation for depth 15, residue 5007. -/
theorem bounds_15_5007 : exactInterval 15 5007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5007 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5007) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5007 : oddCount 5007 15 = 9 ∧ acceleratedOrbit 15 5007 = 3010 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5007 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5007) = 3 ^ 9 * m + 3010 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5007.1, data_15_5007.2]

/-- Complete interval computation for depth 15, residue 5008. -/
theorem bounds_15_5008 : exactInterval 15 5008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5008 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5008) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5008 : oddCount 5008 15 = 7 ∧ acceleratedOrbit 15 5008 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5008 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5008) = 3 ^ 7 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5008.1, data_15_5008.2]

/-- Complete interval computation for depth 15, residue 5009. -/
theorem bounds_15_5009 : exactInterval 15 5009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5009 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5009) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5009 : oddCount 5009 15 = 7 ∧ acceleratedOrbit 15 5009 = 335 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5009 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5009) = 3 ^ 7 * m + 335 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5009.1, data_15_5009.2]

/-- Complete interval computation for depth 15, residue 5010. -/
theorem bounds_15_5010 : exactInterval 15 5010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5010 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5010) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5010 : oddCount 5010 15 = 7 ∧ acceleratedOrbit 15 5010 = 335 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5010 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5010) = 3 ^ 7 * m + 335 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5010.1, data_15_5010.2]

/-- Complete interval computation for depth 15, residue 5011. -/
theorem bounds_15_5011 : exactInterval 15 5011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5011 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5011) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5011 : oddCount 5011 15 = 7 ∧ acceleratedOrbit 15 5011 = 335 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5011 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5011) = 3 ^ 7 * m + 335 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5011.1, data_15_5011.2]

/-- Complete interval computation for depth 15, residue 5012. -/
theorem bounds_15_5012 : exactInterval 15 5012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5012 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5012) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5012 : oddCount 5012 15 = 7 ∧ acceleratedOrbit 15 5012 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5012 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5012) = 3 ^ 7 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5012.1, data_15_5012.2]

end Collatz.Research.PassageAtlas.Batch0153
