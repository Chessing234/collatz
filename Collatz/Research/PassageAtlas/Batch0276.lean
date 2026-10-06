import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0276

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 9011. -/
theorem bounds_15_9011 : exactInterval 15 9011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9011 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9011) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9011 : oddCount 9011 15 = 8 ∧ acceleratedOrbit 15 9011 = 1808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9011 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9011) = 3 ^ 8 * m + 1808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9011.1, data_15_9011.2]

/-- Complete interval computation for depth 15, residue 9012. -/
theorem bounds_15_9012 : exactInterval 15 9012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9012 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9012) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9012 : oddCount 9012 15 = 6 ∧ acceleratedOrbit 15 9012 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9012 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9012) = 3 ^ 6 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9012.1, data_15_9012.2]

/-- Complete interval computation for depth 15, residue 9013. -/
theorem bounds_15_9013 : exactInterval 15 9013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9013 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9013) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9013 : oddCount 9013 15 = 6 ∧ acceleratedOrbit 15 9013 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9013 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9013) = 3 ^ 6 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9013.1, data_15_9013.2]

/-- Complete interval computation for depth 15, residue 9014. -/
theorem bounds_15_9014 : exactInterval 15 9014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9014 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9014) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9014 : oddCount 9014 15 = 9 ∧ acceleratedOrbit 15 9014 = 5417 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9014 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9014) = 3 ^ 9 * m + 5417 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9014.1, data_15_9014.2]

/-- Complete interval computation for depth 15, residue 9015. -/
theorem bounds_15_9015 : exactInterval 15 9015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9015 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9015) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9015 : oddCount 9015 15 = 9 ∧ acceleratedOrbit 15 9015 = 5417 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9015 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9015) = 3 ^ 9 * m + 5417 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9015.1, data_15_9015.2]

/-- Complete interval computation for depth 15, residue 9016. -/
theorem bounds_15_9016 : exactInterval 15 9016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9016 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9016) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9016 : oddCount 9016 15 = 9 ∧ acceleratedOrbit 15 9016 = 5422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9016 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9016) = 3 ^ 9 * m + 5422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9016.1, data_15_9016.2]

/-- Complete interval computation for depth 15, residue 9017. -/
theorem bounds_15_9017 : exactInterval 15 9017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9017 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9017) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9017 : oddCount 9017 15 = 7 ∧ acceleratedOrbit 15 9017 = 602 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9017 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9017) = 3 ^ 7 * m + 602 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9017.1, data_15_9017.2]

/-- Complete interval computation for depth 15, residue 9018. -/
theorem bounds_15_9018 : exactInterval 15 9018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9018 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9018) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9018 : oddCount 9018 15 = 9 ∧ acceleratedOrbit 15 9018 = 5422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9018 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9018) = 3 ^ 9 * m + 5422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9018.1, data_15_9018.2]

/-- Complete interval computation for depth 15, residue 9019. -/
theorem bounds_15_9019 : exactInterval 15 9019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9019 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9019) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9019 : oddCount 9019 15 = 8 ∧ acceleratedOrbit 15 9019 = 1808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9019 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9019) = 3 ^ 8 * m + 1808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9019.1, data_15_9019.2]

/-- Complete interval computation for depth 15, residue 9020. -/
theorem bounds_15_9020 : exactInterval 15 9020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9020 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9020) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9020 : oddCount 9020 15 = 9 ∧ acceleratedOrbit 15 9020 = 5422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9020 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9020) = 3 ^ 9 * m + 5422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9020.1, data_15_9020.2]

/-- Complete interval computation for depth 15, residue 9021. -/
theorem bounds_15_9021 : exactInterval 15 9021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9021 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9021) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9021 : oddCount 9021 15 = 9 ∧ acceleratedOrbit 15 9021 = 5422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9021 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9021) = 3 ^ 9 * m + 5422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9021.1, data_15_9021.2]

/-- Complete interval computation for depth 15, residue 9022. -/
theorem bounds_15_9022 : exactInterval 15 9022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9022 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9022) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9022 : oddCount 9022 15 = 11 ∧ acceleratedOrbit 15 9022 = 48788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9022 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9022) = 3 ^ 11 * m + 48788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9022.1, data_15_9022.2]

/-- Complete interval computation for depth 15, residue 9023. -/
theorem bounds_15_9023 : exactInterval 15 9023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9023 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9023) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9023 : oddCount 9023 15 = 11 ∧ acceleratedOrbit 15 9023 = 48788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9023 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9023) = 3 ^ 11 * m + 48788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9023.1, data_15_9023.2]

/-- Complete interval computation for depth 15, residue 9024. -/
theorem bounds_15_9024 : exactInterval 15 9024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9024 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9024) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9024 : oddCount 9024 15 = 3 ∧ acceleratedOrbit 15 9024 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9024 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9024) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9024.1, data_15_9024.2]

/-- Complete interval computation for depth 15, residue 9025. -/
theorem bounds_15_9025 : exactInterval 15 9025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9025 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9025) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9025 : oddCount 9025 15 = 6 ∧ acceleratedOrbit 15 9025 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9025 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9025) = 3 ^ 6 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9025.1, data_15_9025.2]

/-- Complete interval computation for depth 15, residue 9026. -/
theorem bounds_15_9026 : exactInterval 15 9026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9026 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9026) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9026 : oddCount 9026 15 = 10 ∧ acceleratedOrbit 15 9026 = 16280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9026 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9026) = 3 ^ 10 * m + 16280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9026.1, data_15_9026.2]

/-- Complete interval computation for depth 15, residue 9027. -/
theorem bounds_15_9027 : exactInterval 15 9027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9027 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9027) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9027 : oddCount 9027 15 = 10 ∧ acceleratedOrbit 15 9027 = 16280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9027 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9027) = 3 ^ 10 * m + 16280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9027.1, data_15_9027.2]

/-- Complete interval computation for depth 15, residue 9028. -/
theorem bounds_15_9028 : exactInterval 15 9028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9028 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9028) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9028 : oddCount 9028 15 = 7 ∧ acceleratedOrbit 15 9028 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9028 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9028) = 3 ^ 7 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9028.1, data_15_9028.2]

/-- Complete interval computation for depth 15, residue 9029. -/
theorem bounds_15_9029 : exactInterval 15 9029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9029 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9029) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9029 : oddCount 9029 15 = 7 ∧ acceleratedOrbit 15 9029 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9029 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9029) = 3 ^ 7 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9029.1, data_15_9029.2]

/-- Complete interval computation for depth 15, residue 9030. -/
theorem bounds_15_9030 : exactInterval 15 9030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9030 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9030) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9030 : oddCount 9030 15 = 7 ∧ acceleratedOrbit 15 9030 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9030 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9030) = 3 ^ 7 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9030.1, data_15_9030.2]

/-- Complete interval computation for depth 15, residue 9031. -/
theorem bounds_15_9031 : exactInterval 15 9031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9031 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9031) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9031 : oddCount 9031 15 = 11 ∧ acceleratedOrbit 15 9031 = 48833 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9031 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9031) = 3 ^ 11 * m + 48833 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9031.1, data_15_9031.2]

/-- Complete interval computation for depth 15, residue 9032. -/
theorem bounds_15_9032 : exactInterval 15 9032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9032 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9032) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9032 : oddCount 9032 15 = 7 ∧ acceleratedOrbit 15 9032 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9032 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9032) = 3 ^ 7 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9032.1, data_15_9032.2]

/-- Complete interval computation for depth 15, residue 9033. -/
theorem bounds_15_9033 : exactInterval 15 9033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9033 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9033) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9033 : oddCount 9033 15 = 5 ∧ acceleratedOrbit 15 9033 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9033 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9033) = 3 ^ 5 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9033.1, data_15_9033.2]

/-- Complete interval computation for depth 15, residue 9034. -/
theorem bounds_15_9034 : exactInterval 15 9034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9034 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9034) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9034 : oddCount 9034 15 = 7 ∧ acceleratedOrbit 15 9034 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9034 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9034) = 3 ^ 7 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9034.1, data_15_9034.2]

/-- Complete interval computation for depth 15, residue 9035. -/
theorem bounds_15_9035 : exactInterval 15 9035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9035 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9035) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9035 : oddCount 9035 15 = 7 ∧ acceleratedOrbit 15 9035 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9035 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9035) = 3 ^ 7 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9035.1, data_15_9035.2]

/-- Complete interval computation for depth 15, residue 9036. -/
theorem bounds_15_9036 : exactInterval 15 9036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9036 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9036) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9036 : oddCount 9036 15 = 7 ∧ acceleratedOrbit 15 9036 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9036 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9036) = 3 ^ 7 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9036.1, data_15_9036.2]

/-- Complete interval computation for depth 15, residue 9037. -/
theorem bounds_15_9037 : exactInterval 15 9037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9037 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9037) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9037 : oddCount 9037 15 = 7 ∧ acceleratedOrbit 15 9037 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9037 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9037) = 3 ^ 7 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9037.1, data_15_9037.2]

/-- Complete interval computation for depth 15, residue 9038. -/
theorem bounds_15_9038 : exactInterval 15 9038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9038 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9038) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9038 : oddCount 9038 15 = 8 ∧ acceleratedOrbit 15 9038 = 1811 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9038 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9038) = 3 ^ 8 * m + 1811 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9038.1, data_15_9038.2]

/-- Complete interval computation for depth 15, residue 9039. -/
theorem bounds_15_9039 : exactInterval 15 9039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9039 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9039) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9039 : oddCount 9039 15 = 8 ∧ acceleratedOrbit 15 9039 = 1811 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9039 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9039) = 3 ^ 8 * m + 1811 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9039.1, data_15_9039.2]

/-- Complete interval computation for depth 15, residue 9040. -/
theorem bounds_15_9040 : exactInterval 15 9040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9040 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9040) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9040 : oddCount 9040 15 = 3 ∧ acceleratedOrbit 15 9040 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9040 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9040) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9040.1, data_15_9040.2]

/-- Complete interval computation for depth 15, residue 9041. -/
theorem bounds_15_9041 : exactInterval 15 9041 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9041 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9041) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9041 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9041 : oddCount 9041 15 = 10 ∧ acceleratedOrbit 15 9041 = 16301 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9041 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9041) = 3 ^ 10 * m + 16301 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9041.1, data_15_9041.2]

/-- Complete interval computation for depth 15, residue 9042. -/
theorem bounds_15_9042 : exactInterval 15 9042 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9042 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9042) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9042 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9042 : oddCount 9042 15 = 10 ∧ acceleratedOrbit 15 9042 = 16301 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9042 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9042) = 3 ^ 10 * m + 16301 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9042.1, data_15_9042.2]

end Collatz.Research.PassageAtlas.Batch0276
