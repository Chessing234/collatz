import Collatz.Exploration.CoefficientBand

/-! Affine-error control from lower survival, without a heavy-coefficient
hypothesis. All floor assumptions refer to an explicitly finite prefix. -/
namespace Collatz.Exploration.FloorAffineError
open CoefficientBand

/-- The least odd natural number at least b. Only odd states inject affine error. -/
def oddCeil (b : Nat) : Nat := if b%2=0 then b+1 else b

def weight (b : Nat) : Nat := 3*oddCeil b+1

theorem oddCeil_ge (b : Nat) : b ≤ oddCeil b := by unfold oddCeil; split <;> omega

theorem oddCeil_odd (b : Nat) : oddCeil b%2=1 := by unfold oddCeil; split <;> omega

theorem oddCeil_le_of_odd {b x : Nat} (hx : x%2=1) (hb : b ≤ x) : oddCeil b ≤ x := by
  unfold oddCeil
  split <;> omega

/-- The odd affine update preserves an error budget paid by the orbit floor. -/
theorem odd_error_update {b j B D T : Nat} (hB : (3*b+1)*B ≤ j*T) (hD : b*D ≤ T) :
    (3*b+1)*(3*B+D) ≤ (j+1)*(3*T+D) := by
  have h3 := Nat.mul_le_mul_left 3 hB
  have hd3 := Nat.mul_le_mul_left 3 hD
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] at h3 hd3 ⊢
  omega

/-- Lower survival controls the affine constant relative to the actual endpoint.
No coefficient is assumed heavy, and the endpoint itself need not survive. -/
theorem survival_affine_bound (n b j : Nat)
    (hfloor : ∀ i, i < j → b ≤ acceleratedOrbit i n) :
    ∃ B : Nat, 2^j*acceleratedOrbit j n = 3^oddCount n j*n+B ∧
      weight b*B ≤ oddCount n j*(3^oddCount n j*n+B) := by
  induction j with
  | zero => refine ⟨0,by simp,by simp⟩
  | succ j ih =>
    obtain ⟨B,heq,hB⟩ := ih (fun i hi => hfloor i (by omega))
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j n) with he | ho
    · refine ⟨B,?_,?_⟩
      · rw [acceleratedOrbit_succ_step, Density.oddCount_succ_last, he, Nat.add_zero, Nat.pow_succ]
        have hx : 2*acceleratedStep (acceleratedOrbit j n) = acceleratedOrbit j n := by
          simp only [acceleratedStep, he, ↓reduceIte]
          omega
        rw [Nat.mul_assoc, hx]
        exact heq
      · rw [Density.oddCount_succ_last, he, Nat.add_zero]
        exact hB
    · refine ⟨3*B+2^j,?_,?_⟩
      · rw [acceleratedOrbit_succ_step, Density.oddCount_succ_last, ho, Nat.pow_succ, Nat.pow_succ]
        have hx : 2*acceleratedStep (acceleratedOrbit j n) = 3*acceleratedOrbit j n+1 := by
          simp only [acceleratedStep, show acceleratedOrbit j n%2 ≠ 0 by omega, ↓reduceIte]
          omega
        rw [Nat.mul_assoc, hx, Nat.mul_add, Nat.mul_one]
        have hh : 2^j*(3*acceleratedOrbit j n) = 3*(2^j*acceleratedOrbit j n) := by ac_rfl
        rw [hh, heq, Nat.mul_add]
        ac_rfl
      · have hlo := Nat.mul_le_mul_left (2^j)
          (oddCeil_le_of_odd ho (hfloor j (by omega)))
        rw [heq] at hlo
        have hD : oddCeil b*2^j ≤ 3^oddCount n j*n+B := by simpa only [Nat.mul_comm] using hlo
        have hu := odd_error_update (b := oddCeil b) hB hD
        rw [Density.oddCount_succ_last, ho, Nat.pow_succ]
        have ht : (3^oddCount n j*3)*n+(3*B+2^j) = 3*(3^oddCount n j*n+B)+2^j := by
          rw [Nat.mul_add]
          ac_rfl
        rw [ht]
        exact hu

/-- The same floor budget holds for any exact affine constant at that time. -/
theorem survival_offset_budget {n b j B : Nat}
    (hfloor : ∀ i, i < j → b ≤ acceleratedOrbit i n)
    (heq : 2^j*acceleratedOrbit j n = 3^oddCount n j*n+B) :
    weight b*B ≤ oddCount n j*(3^oddCount n j*n+B) := by
  obtain ⟨B',heq',hb⟩ := survival_affine_bound n b j hfloor
  have : B = B' := by omega
  subst B'
  exact hb

/-- The paid offset bound is useful when the odd-step count is below the floor weight. -/
theorem survival_offset_paid {n b j B : Nat}
    (hfloor : ∀ i, i < j → b ≤ acceleratedOrbit i n)
    (heq : 2^j*acceleratedOrbit j n = 3^oddCount n j*n+B) :
    (weight b-oddCount n j)*B ≤ oddCount n j*3^oddCount n j*n := by
  have hb := survival_offset_budget hfloor heq
  rw [Nat.sub_mul]
  simp only [Nat.mul_add, Nat.mul_assoc] at hb ⊢
  omega

/-- No larger uniform floor weight is possible: the first odd step at oddCeil b is sharp. -/
theorem weight_optimal (b F : Nat)
    (h : ∀ n j B : Nat, (∀ i, i < j → b ≤ acceleratedOrbit i n) →
      2^j*acceleratedOrbit j n = 3^oddCount n j*n+B →
      F*B ≤ oddCount n j*(3^oddCount n j*n+B)) : F ≤ weight b := by
  let n := oddCeil b
  have ho : n%2=1 := oddCeil_odd b
  have hc : oddCount n 1 = 1 := by
    simpa using Congruence.oddCount_succ_of_odd ho 0
  have hf : ∀ i, i < 1 → b ≤ acceleratedOrbit i n := by
    intro i hi
    have : i=0 := by omega
    subst i
    exact oddCeil_ge b
  have he : 2^1*acceleratedOrbit 1 n = 3^oddCount n 1*n+1 := by
    rw [hc]
    change 2*acceleratedStep n = 3*n+1
    simp only [acceleratedStep, show n%2 ≠ 0 by omega, ↓reduceIte]
    omega
  have hh := h n 1 1 hf he
  rw [hc] at hh
  simpa only [Nat.pow_one, Nat.one_mul, Nat.mul_one, weight, n] using hh

/-- Exact classification of all valid uniform weights for this finite floor budget. -/
theorem uniform_weight_iff (b F : Nat) :
    (∀ n j B : Nat, (∀ i, i < j → b ≤ acceleratedOrbit i n) →
      2^j*acceleratedOrbit j n = 3^oddCount n j*n+B →
      F*B ≤ oddCount n j*(3^oddCount n j*n+B)) ↔ F ≤ weight b := by
  constructor
  · exact weight_optimal b F
  · intro hF n j B hf he
    have hm := Nat.mul_le_mul_right B hF
    exact Nat.le_trans hm (survival_offset_budget hf he)

end Collatz.Exploration.FloorAffineError
