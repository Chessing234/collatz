import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0924

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7009. -/
theorem bounds_13_7009 : exactInterval 13 7009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7009 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7009) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7009 : oddCount 7009 13 = 10 ∧ acceleratedOrbit 13 7009 = 50543 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7009 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7009) = 3 ^ 10 * m + 50543 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7009.1, data_13_7009.2]

/-- Complete interval computation for depth 13, residue 7010. -/
theorem bounds_13_7010 : exactInterval 13 7010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7010 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7010) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7010 : oddCount 7010 13 = 5 ∧ acceleratedOrbit 13 7010 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7010 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7010) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7010.1, data_13_7010.2]

/-- Complete interval computation for depth 13, residue 7011. -/
theorem bounds_13_7011 : exactInterval 13 7011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7011 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7011) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7011 : oddCount 7011 13 = 5 ∧ acceleratedOrbit 13 7011 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7011 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7011) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7011.1, data_13_7011.2]

/-- Complete interval computation for depth 13, residue 7012. -/
theorem bounds_13_7012 : exactInterval 13 7012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7012 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7012) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7012 : oddCount 7012 13 = 5 ∧ acceleratedOrbit 13 7012 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7012 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7012) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7012.1, data_13_7012.2]

/-- Complete interval computation for depth 13, residue 7013. -/
theorem bounds_13_7013 : exactInterval 13 7013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7013 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7013) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7013 : oddCount 7013 13 = 5 ∧ acceleratedOrbit 13 7013 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7013 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7013) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7013.1, data_13_7013.2]

/-- Complete interval computation for depth 13, residue 7014. -/
theorem bounds_13_7014 : exactInterval 13 7014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7014 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7014) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7014 : oddCount 7014 13 = 5 ∧ acceleratedOrbit 13 7014 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7014 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7014) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7014.1, data_13_7014.2]

/-- Complete interval computation for depth 13, residue 7015. -/
theorem bounds_13_7015 : exactInterval 13 7015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7015 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7015) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7015 : oddCount 7015 13 = 9 ∧ acceleratedOrbit 13 7015 = 16858 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7015 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7015) = 3 ^ 9 * m + 16858 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7015.1, data_13_7015.2]

/-- Complete interval computation for depth 13, residue 7016. -/
theorem bounds_13_7016 : exactInterval 13 7016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7016 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7016) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7016 : oddCount 7016 13 = 5 ∧ acceleratedOrbit 13 7016 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7016 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7016) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7016.1, data_13_7016.2]

/-- Complete interval computation for depth 13, residue 7017. -/
theorem bounds_13_7017 : exactInterval 13 7017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7017 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7017) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7017 : oddCount 7017 13 = 7 ∧ acceleratedOrbit 13 7017 = 1874 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7017 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7017) = 3 ^ 7 * m + 1874 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7017.1, data_13_7017.2]

/-- Complete interval computation for depth 13, residue 7018. -/
theorem bounds_13_7018 : exactInterval 13 7018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7018 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7018) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7018 : oddCount 7018 13 = 5 ∧ acceleratedOrbit 13 7018 = 209 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7018 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7018) = 3 ^ 5 * m + 209 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7018.1, data_13_7018.2]

/-- Complete interval computation for depth 13, residue 7019. -/
theorem bounds_13_7019 : exactInterval 13 7019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7019 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7019) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7019 : oddCount 7019 13 = 6 ∧ acceleratedOrbit 13 7019 = 625 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7019 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7019) = 3 ^ 6 * m + 625 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7019.1, data_13_7019.2]

/-- Complete interval computation for depth 13, residue 7020. -/
theorem bounds_13_7020 : exactInterval 13 7020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7020 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7020) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7020 : oddCount 7020 13 = 7 ∧ acceleratedOrbit 13 7020 = 1876 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7020 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7020) = 3 ^ 7 * m + 1876 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7020.1, data_13_7020.2]

/-- Complete interval computation for depth 13, residue 7021. -/
theorem bounds_13_7021 : exactInterval 13 7021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7021 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7021) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7021 : oddCount 7021 13 = 7 ∧ acceleratedOrbit 13 7021 = 1876 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7021 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7021) = 3 ^ 7 * m + 1876 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7021.1, data_13_7021.2]

/-- Complete interval computation for depth 13, residue 7022. -/
theorem bounds_13_7022 : exactInterval 13 7022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7022 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7022) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7022 : oddCount 7022 13 = 7 ∧ acceleratedOrbit 13 7022 = 1876 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7022 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7022) = 3 ^ 7 * m + 1876 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7022.1, data_13_7022.2]

/-- Complete interval computation for depth 13, residue 7023. -/
theorem bounds_13_7023 : exactInterval 13 7023 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7023 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7023) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7023 : oddCount 7023 13 = 8 ∧ acceleratedOrbit 13 7023 = 5626 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7023 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7023) = 3 ^ 8 * m + 5626 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7023.1, data_13_7023.2]

end Collatz.Research.StoppingAtlas.Batch0924
