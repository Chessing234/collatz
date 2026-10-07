import Collatz.Exploration.FloorProductError

/-! Exact finite telescoping product of odd-state error factors.
This is a classical product identity formalized without division. -/
namespace Collatz.Exploration.ExactTraceProduct

def numerator (n : Nat) : Nat → Nat
  | 0 => 1
  | j+1 => numerator n j *
    (if acceleratedOrbit j n%2=0 then 1 else 3*acceleratedOrbit j n)

def denominator (n : Nat) : Nat → Nat
  | 0 => 1
  | j+1 => denominator n j *
    (if acceleratedOrbit j n%2=0 then 1 else 3*acceleratedOrbit j n+1)

/-- Every odd-state correction is retained exactly in this finite identity. -/
theorem exact_product (n j : Nat) :
    numerator n j*(2^j*acceleratedOrbit j n) =
      denominator n j*(3^oddCount n j*n) := by
  induction j with
  | zero => simp [numerator,denominator]
  | succ j ih =>
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j n) with he | ho
    · rw [numerator,denominator,he]
      simp only [↓reduceIte,Nat.mul_one]
      rw [acceleratedOrbit_succ_step,Density.oddCount_succ_last,he,Nat.add_zero,Nat.pow_succ]
      have hx : 2*acceleratedStep (acceleratedOrbit j n) = acceleratedOrbit j n := by
        simp only [acceleratedStep,he,↓reduceIte]
        omega
      rw [Nat.mul_assoc (2^j),hx]
      exact ih
    · rw [numerator,denominator]
      simp only [show acceleratedOrbit j n%2 ≠ 0 by omega,↓reduceIte]
      rw [acceleratedOrbit_succ_step,Density.oddCount_succ_last,ho,Nat.pow_succ,Nat.pow_succ]
      have hx : 2*acceleratedStep (acceleratedOrbit j n) = 3*acceleratedOrbit j n+1 := by
        simp only [acceleratedStep,show acceleratedOrbit j n%2 ≠ 0 by omega,↓reduceIte]
        omega
      rw [Nat.mul_assoc (2^j),hx]
      have hh := congrArg (fun z => z*(3*(3*acceleratedOrbit j n+1))) ih
      simp only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] at hh ⊢
      exact hh

theorem numerator_positive {n : Nat} (hn : 0 < n) (j : Nat) : 0 < numerator n j := by
  induction j with
  | zero => simp [numerator]
  | succ j ih =>
    rw [numerator]
    split
    · simpa using ih
    · exact Nat.mul_pos ih (Nat.mul_pos (by decide) (acceleratedOrbit_positive hn j))

/-- Exact finite descent test. It uses the actual trace, not an orbit-independent prediction. -/
theorem descent_iff {n : Nat} (hn : 0 < n) (j : Nat) :
    acceleratedOrbit j n < n ↔
      denominator n j*3^oddCount n j < numerator n j*2^j := by
  have ha := numerator_positive hn j
  have hd : 0 < 2^j := Nat.pow_pos (by decide)
  have hmul : 0 < numerator n j*2^j := Nat.mul_pos ha hd
  have hi := exact_product n j
  rw [← Nat.mul_assoc] at hi
  have h1 := Nat.mul_lt_mul_left hmul (b := acceleratedOrbit j n) (c := n)
  have h2 := Nat.mul_lt_mul_right hn
    (b := denominator n j*3^oddCount n j) (c := numerator n j*2^j)
  rw [hi] at h1
  rw [← Nat.mul_assoc (denominator n j)] at h1
  exact h1.symm.trans h2

end Collatz.Exploration.ExactTraceProduct
