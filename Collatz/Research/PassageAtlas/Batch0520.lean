import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0520

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 17006. -/
theorem bounds_15_17006 : exactInterval 15 17006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17006 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17006) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17006 : oddCount 17006 15 = 8 ∧ acceleratedOrbit 15 17006 = 3406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17006 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17006) = 3 ^ 8 * m + 3406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17006.1, data_15_17006.2]

/-- Complete interval computation for depth 15, residue 17007. -/
theorem bounds_15_17007 : exactInterval 15 17007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17007 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17007) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17007 : oddCount 17007 15 = 9 ∧ acceleratedOrbit 15 17007 = 10217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17007 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17007) = 3 ^ 9 * m + 10217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17007.1, data_15_17007.2]

/-- Complete interval computation for depth 15, residue 17008. -/
theorem bounds_15_17008 : exactInterval 15 17008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17008 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17008) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17008 : oddCount 17008 15 = 6 ∧ acceleratedOrbit 15 17008 = 379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17008 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17008) = 3 ^ 6 * m + 379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17008.1, data_15_17008.2]

/-- Complete interval computation for depth 15, residue 17009. -/
theorem bounds_15_17009 : exactInterval 15 17009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17009 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17009) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17009 : oddCount 17009 15 = 6 ∧ acceleratedOrbit 15 17009 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17009 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17009) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17009.1, data_15_17009.2]

/-- Complete interval computation for depth 15, residue 17010. -/
theorem bounds_15_17010 : exactInterval 15 17010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17010 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17010) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17010 : oddCount 17010 15 = 8 ∧ acceleratedOrbit 15 17010 = 3407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17010 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17010) = 3 ^ 8 * m + 3407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17010.1, data_15_17010.2]

/-- Complete interval computation for depth 15, residue 17011. -/
theorem bounds_15_17011 : exactInterval 15 17011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17011 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17011) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17011 : oddCount 17011 15 = 8 ∧ acceleratedOrbit 15 17011 = 3407 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17011 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17011) = 3 ^ 8 * m + 3407 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17011.1, data_15_17011.2]

/-- Complete interval computation for depth 15, residue 17012. -/
theorem bounds_15_17012 : exactInterval 15 17012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17012 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17012) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17012 : oddCount 17012 15 = 6 ∧ acceleratedOrbit 15 17012 = 379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17012 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17012) = 3 ^ 6 * m + 379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17012.1, data_15_17012.2]

/-- Complete interval computation for depth 15, residue 17013. -/
theorem bounds_15_17013 : exactInterval 15 17013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17013 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17013) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17013 : oddCount 17013 15 = 6 ∧ acceleratedOrbit 15 17013 = 379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17013 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17013) = 3 ^ 6 * m + 379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17013.1, data_15_17013.2]

/-- Complete interval computation for depth 15, residue 17014. -/
theorem bounds_15_17014 : exactInterval 15 17014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17014 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17014) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17014 : oddCount 17014 15 = 6 ∧ acceleratedOrbit 15 17014 = 379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17014 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17014) = 3 ^ 6 * m + 379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17014.1, data_15_17014.2]

/-- Complete interval computation for depth 15, residue 17015. -/
theorem bounds_15_17015 : exactInterval 15 17015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17015 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17015) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17015 : oddCount 17015 15 = 6 ∧ acceleratedOrbit 15 17015 = 379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17015 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17015) = 3 ^ 6 * m + 379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17015.1, data_15_17015.2]

/-- Complete interval computation for depth 15, residue 17016. -/
theorem bounds_15_17016 : exactInterval 15 17016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17016 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17016) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17016 : oddCount 17016 15 = 6 ∧ acceleratedOrbit 15 17016 = 379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17016 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17016) = 3 ^ 6 * m + 379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17016.1, data_15_17016.2]

/-- Complete interval computation for depth 15, residue 17017. -/
theorem bounds_15_17017 : exactInterval 15 17017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17017 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17017) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17017 : oddCount 17017 15 = 7 ∧ acceleratedOrbit 15 17017 = 1136 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17017 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17017) = 3 ^ 7 * m + 1136 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17017.1, data_15_17017.2]

/-- Complete interval computation for depth 15, residue 17018. -/
theorem bounds_15_17018 : exactInterval 15 17018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17018 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17018) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17018 : oddCount 17018 15 = 6 ∧ acceleratedOrbit 15 17018 = 379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17018 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17018) = 3 ^ 6 * m + 379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17018.1, data_15_17018.2]

/-- Complete interval computation for depth 15, residue 17019. -/
theorem bounds_15_17019 : exactInterval 15 17019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17019 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17019) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17019 : oddCount 17019 15 = 9 ∧ acceleratedOrbit 15 17019 = 10226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17019 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17019) = 3 ^ 9 * m + 10226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17019.1, data_15_17019.2]

/-- Complete interval computation for depth 15, residue 17020. -/
theorem bounds_15_17020 : exactInterval 15 17020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17020 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17020) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17020 : oddCount 17020 15 = 11 ∧ acceleratedOrbit 15 17020 = 92036 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17020 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17020) = 3 ^ 11 * m + 92036 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17020.1, data_15_17020.2]

/-- Complete interval computation for depth 15, residue 17021. -/
theorem bounds_15_17021 : exactInterval 15 17021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17021 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17021) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17021 : oddCount 17021 15 = 11 ∧ acceleratedOrbit 15 17021 = 92036 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17021 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17021) = 3 ^ 11 * m + 92036 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17021.1, data_15_17021.2]

/-- Complete interval computation for depth 15, residue 17022. -/
theorem bounds_15_17022 : exactInterval 15 17022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17022 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17022) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17022 : oddCount 17022 15 = 11 ∧ acceleratedOrbit 15 17022 = 92036 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17022 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17022) = 3 ^ 11 * m + 92036 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17022.1, data_15_17022.2]

/-- Complete interval computation for depth 15, residue 17023. -/
theorem bounds_15_17023 : exactInterval 15 17023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17023 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17023) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17023 : oddCount 17023 15 = 13 ∧ acceleratedOrbit 15 17023 = 828305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17023 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17023) = 3 ^ 13 * m + 828305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17023.1, data_15_17023.2]

/-- Complete interval computation for depth 15, residue 17024. -/
theorem bounds_15_17024 : exactInterval 15 17024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17024 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17024) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17024 : oddCount 17024 15 = 4 ∧ acceleratedOrbit 15 17024 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17024 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17024) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17024.1, data_15_17024.2]

/-- Complete interval computation for depth 15, residue 17025. -/
theorem bounds_15_17025 : exactInterval 15 17025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17025 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17025) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17025 : oddCount 17025 15 = 8 ∧ acceleratedOrbit 15 17025 = 3410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17025 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17025) = 3 ^ 8 * m + 3410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17025.1, data_15_17025.2]

/-- Complete interval computation for depth 15, residue 17026. -/
theorem bounds_15_17026 : exactInterval 15 17026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17026 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17026) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17026 : oddCount 17026 15 = 6 ∧ acceleratedOrbit 15 17026 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17026 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17026) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17026.1, data_15_17026.2]

/-- Complete interval computation for depth 15, residue 17027. -/
theorem bounds_15_17027 : exactInterval 15 17027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17027 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17027) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17027 : oddCount 17027 15 = 6 ∧ acceleratedOrbit 15 17027 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17027 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17027) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17027.1, data_15_17027.2]

/-- Complete interval computation for depth 15, residue 17028. -/
theorem bounds_15_17028 : exactInterval 15 17028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17028 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17028) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17028 : oddCount 17028 15 = 8 ∧ acceleratedOrbit 15 17028 = 3412 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17028 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17028) = 3 ^ 8 * m + 3412 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17028.1, data_15_17028.2]

/-- Complete interval computation for depth 15, residue 17029. -/
theorem bounds_15_17029 : exactInterval 15 17029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17029 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17029) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17029 : oddCount 17029 15 = 8 ∧ acceleratedOrbit 15 17029 = 3412 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17029 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17029) = 3 ^ 8 * m + 3412 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17029.1, data_15_17029.2]

/-- Complete interval computation for depth 15, residue 17030. -/
theorem bounds_15_17030 : exactInterval 15 17030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17030 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17030) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17030 : oddCount 17030 15 = 8 ∧ acceleratedOrbit 15 17030 = 3412 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17030 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17030) = 3 ^ 8 * m + 3412 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17030.1, data_15_17030.2]

/-- Complete interval computation for depth 15, residue 17031. -/
theorem bounds_15_17031 : exactInterval 15 17031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17031 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17031) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17031 : oddCount 17031 15 = 6 ∧ acceleratedOrbit 15 17031 = 379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17031 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17031) = 3 ^ 6 * m + 379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17031.1, data_15_17031.2]

/-- Complete interval computation for depth 15, residue 17032. -/
theorem bounds_15_17032 : exactInterval 15 17032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17032 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17032) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17032 : oddCount 17032 15 = 6 ∧ acceleratedOrbit 15 17032 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17032 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17032) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17032.1, data_15_17032.2]

/-- Complete interval computation for depth 15, residue 17033. -/
theorem bounds_15_17033 : exactInterval 15 17033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17033 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17033) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17033 : oddCount 17033 15 = 11 ∧ acceleratedOrbit 15 17033 = 92096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17033 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17033) = 3 ^ 11 * m + 92096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17033.1, data_15_17033.2]

/-- Complete interval computation for depth 15, residue 17034. -/
theorem bounds_15_17034 : exactInterval 15 17034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17034 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17034) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17034 : oddCount 17034 15 = 6 ∧ acceleratedOrbit 15 17034 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17034 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17034) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17034.1, data_15_17034.2]

/-- Complete interval computation for depth 15, residue 17035. -/
theorem bounds_15_17035 : exactInterval 15 17035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17035 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17035) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17035 : oddCount 17035 15 = 8 ∧ acceleratedOrbit 15 17035 = 3412 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17035 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17035) = 3 ^ 8 * m + 3412 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17035.1, data_15_17035.2]

/-- Complete interval computation for depth 15, residue 17036. -/
theorem bounds_15_17036 : exactInterval 15 17036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17036 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17036) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17036 : oddCount 17036 15 = 6 ∧ acceleratedOrbit 15 17036 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17036 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17036) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17036.1, data_15_17036.2]

/-- Complete interval computation for depth 15, residue 17037. -/
theorem bounds_15_17037 : exactInterval 15 17037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17037 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17037) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17037 : oddCount 17037 15 = 6 ∧ acceleratedOrbit 15 17037 = 380 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17037 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17037) = 3 ^ 6 * m + 380 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17037.1, data_15_17037.2]

/-- Complete interval computation for depth 15, residue 17038. -/
theorem bounds_15_17038 : exactInterval 15 17038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17038 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17038) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17038 : oddCount 17038 15 = 10 ∧ acceleratedOrbit 15 17038 = 30709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17038 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17038) = 3 ^ 10 * m + 30709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17038.1, data_15_17038.2]

end Collatz.Research.PassageAtlas.Batch0520
