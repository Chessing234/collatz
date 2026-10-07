import Collatz.Exploration.FloorAffineError
import Collatz.Structure.AffineBound

/-! Multiplicative floor control keeps the error budget nontrivial at all odd counts. -/
namespace Collatz.Exploration.FloorProductError
open FloorAffineError

def base (b : Nat) : Nat := 3*oddCeil b

/-- Each odd state contributes a factor bounded by the least admissible odd state. -/
theorem odd_factor {b x : Nat} (ho : x%2=1) (hf : b ≤ x) :
    base b*(3*x+1) ≤ 3*weight b*x := by
  have h := oddCeil_le_of_odd ho hf
  unfold base weight
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]
  have he : 3*oddCeil b*(3*x) = 3*(3*oddCeil b)*x := by ac_rfl
  rw [he]
  omega

/-- Product error control from a finite lower floor, with no restriction on odd count. -/
theorem survival_product (n b j : Nat)
    (hf : ∀ i, i < j → b ≤ acceleratedOrbit i n) :
    base b^oddCount n j*(2^j*acceleratedOrbit j n) ≤
      weight b^oddCount n j*(3^oddCount n j*n) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hp := ih (fun i hi => hf i (by omega))
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j n) with he | ho
    · rw [acceleratedOrbit_succ_step, Density.oddCount_succ_last, he, Nat.add_zero, Nat.pow_succ]
      have hx : 2*acceleratedStep (acceleratedOrbit j n) = acceleratedOrbit j n := by
        simp only [acceleratedStep,he,↓reduceIte]
        omega
      rw [Nat.mul_assoc (2^j),hx]
      exact hp
    · have hl := odd_factor ho (hf j (by omega))
      have hm := Nat.mul_le_mul_left (base b^oddCount n j*2^j) hl
      have hh := Nat.mul_le_mul_left (3*weight b) hp
      rw [acceleratedOrbit_succ_step, Density.oddCount_succ_last,ho,
        Nat.pow_succ,Nat.pow_succ,Nat.pow_succ,Nat.pow_succ]
      have hx : 2*acceleratedStep (acceleratedOrbit j n) = 3*acceleratedOrbit j n+1 := by
        simp only [acceleratedStep,show acceleratedOrbit j n%2 ≠ 0 by omega,↓reduceIte]
        omega
      rw [Nat.mul_assoc (2^j),hx]
      simp only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] at hm hh ⊢
      exact Nat.le_trans hm hh

/-- An exponential paid budget remains informative when the linear weight is exhausted. -/
theorem offset_product {n b j B : Nat}
    (hf : ∀ i, i < j → b ≤ acceleratedOrbit i n)
    (he : 2^j*acceleratedOrbit j n = 3^oddCount n j*n+B) :
    base b^oddCount n j*B ≤
      (weight b^oddCount n j-base b^oddCount n j)*(3^oddCount n j*n) := by
  have hp := survival_product n b j hf
  rw [he,Nat.mul_add] at hp
  rw [Nat.sub_mul]
  omega

/-- Source elimination with multiplicative error control; no initial upper bound is needed. -/
theorem product_band_budget {n b a c P Q : Nat}
    (hb : 0 < b)
    (hf : ∀ i, i < a → b ≤ acceleratedOrbit i n)
    (hl : b ≤ acceleratedOrbit a n)
    (hu : Q*acceleratedOrbit c n ≤ P*b) :
    Q*3^oddCount n c*2^a*base b^oddCount n a ≤
      P*2^c*3^oddCount n a*weight b^oddCount n a := by
  have hp := survival_product n b a hf
  obtain ⟨B,he,_⟩ := AffineBound.exists_affine_bounded n c
  have hh : 3^oddCount n c*n ≤ 2^c*acceleratedOrbit c n := by omega
  have h1 := Nat.mul_le_mul_left (base b^oddCount n a*2^a) hl
  have h2 := Nat.mul_le_mul_left (Q*3^oddCount n c) hp
  have h3 := Nat.mul_le_mul_left (Q*weight b^oddCount n a*3^oddCount n a) hh
  have h4 := Nat.mul_le_mul_left (weight b^oddCount n a*3^oddCount n a*2^c) hu
  have h5 := Nat.mul_le_mul_left (Q*3^oddCount n c) h1
  simp only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] at h2 h3 h4 h5
  have hz :
      (Q*3^oddCount n c*2^a*base b^oddCount n a)*b ≤
      (P*2^c*3^oddCount n a*weight b^oddCount n a)*b := by
    simp only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]
    omega
  exact Nat.le_of_mul_le_mul_right hz hb

end Collatz.Exploration.FloorProductError
