import Collatz.Strategy.RealizableBound
import Collatz.Strategy.FirstLightConsequences

/-! Localize the inherited Beatty accumulator barrier to a finite orbit prefix.
These statements do not assume or establish a never-descending infinite orbit. -/
namespace Collatz.Exploration.FiniteBeattyBarrier
open RealizableBound AffineExact AccumulatorArith FirstLightDescent FirstLightConsequences

/-- The time-cap argument needs non-descent only at its current index. -/
theorem time_cap_at_nondrop {m c a j : Nat} (hc : c ≤ m)
    (hnd : m ≤ acceleratedOrbit j m)
    (hcert : Bcap a + 3 ^ a * c < 2 * 2 ^ fexp a * c)
    (ha : oddCount m j = a) (hB : affineC j m ≤ Bcap a) : j ≤ fexp a := by
  rcases Nat.lt_or_ge (fexp a) j with hcon | hok
  case inr => exact hok
  exfalso
  have harith : 2 ^ j * m ≤ 3 ^ oddCount m j * m + affineC j m := by
    have he := affine_exact m j
    have hmul := Nat.mul_le_mul_left (2 ^ j) hnd
    omega
  rw [ha] at harith
  -- `j > fexp a` gives `2 ^ (fexp a + 1) ≤ 2 ^ j`
  have hstep : 2 * 2 ^ fexp a ≤ 2 ^ j := by
    have h1 : fexp a + 1 ≤ j := by omega
    have h2 : (2:Nat) ^ (fexp a + 1) ≤ 2 ^ j := Arith.two_pow_le_two_pow h1
    rw [Arith.two_pow_succ] at h2
    exact h2
  have hkey : 2 * 2 ^ fexp a * m ≤ 3 ^ a * m + Bcap a := by
    have h1 : 2 * 2 ^ fexp a * m ≤ 2 ^ j * m := Nat.mul_le_mul_right _ hstep
    omega
  -- the gap `d = 2 ^ (fexp a + 1) − 3 ^ a` is positive
  have hgap : 3 ^ a < 2 * 2 ^ fexp a := by
    rcases Nat.lt_or_ge (3 ^ a) (2 * 2 ^ fexp a) with hg | hle
    · exact hg
    · exfalso
      have h1 : (2 * 2 ^ fexp a) * c ≤ (3 ^ a) * c := Nat.mul_le_mul_right _ hle
      omega
  obtain ⟨d, hd⟩ : ∃ d : Nat, 2 * 2 ^ fexp a = 3 ^ a + d := ⟨2 * 2 ^ fexp a - 3 ^ a, by omega⟩
  rw [hd] at hkey hcert
  rw [Nat.add_mul] at hkey hcert
  -- `d · m ≤ Bcap a` from the non-drop side, `Bcap a < d · c` from the certificate
  have hlow : d * m ≤ Bcap a := by omega
  have hhigh : Bcap a < d * c := by omega
  have hmono : d * c ≤ d * m := Nat.mul_le_mul_left _ hc
  omega

/-- The Beatty accumulator cap uses only non-descent through the given horizon. -/
theorem accumulator_cap {m c A H : Nat} (hc : c ≤ m)
    (hnd : ∀ i, i ≤ H → m ≤ acceleratedOrbit i m)
    (hcert : ∀ i, i < A → Bcap i + 3 ^ i * c < 2 * 2 ^ fexp i * c) :
    ∀ j, j ≤ H → oddCount m j ≤ A → affineC j m ≤ Bcap (oddCount m j) := by
  intro j
  induction j with
  | zero => intro _ _; simp
  | succ j ih =>
    intro hj hA
    have hlast := Density.oddCount_succ_last m j
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j m) with he | ho
    · have hcount : oddCount m (j+1) = oddCount m j := by omega
      rw [hcount, affineC_even he]
      exact ih (by omega) (by omega)
    · have hcount : oddCount m (j+1) = oddCount m j+1 := by omega
      have hlt : oddCount m j < A := by omega
      have hIH := ih (by omega) (by omega)
      have htime : j ≤ fexp (oddCount m j) :=
        time_cap_at_nondrop hc (hnd j (by omega)) (hcert _ hlt) rfl hIH
      have hpow := Arith.two_pow_le_two_pow htime
      rw [hcount, affineC_odd ho, Bcap_succ]
      omega

/-- A first light crossing inside the certified odd-count reach must descend. -/
theorem first_light_descent {m c A j : Nat} (hc : c ≤ m)
    (hcert : ∀ i, i < A → Bcap i + 3 ^ i * c < 2 * 2 ^ fexp i * c)
    (hf : FirstLight m j) (hA : oddCount m j < A) : acceleratedOrbit j m < m := by
  by_cases hd : acceleratedOrbit j m < m
  · exact hd
  · have hnd : ∀ i, i ≤ j → m ≤ acceleratedOrbit i m := by
      intro i hi
      by_cases he : i=j
      · subst i; omega
      · exact no_descent_before_first_light hf i (by omega)
    have hB := accumulator_cap hc hnd hcert j (Nat.le_refl j) (by omega)
    have ht := time_cap_at_nondrop hc (hnd j (Nat.le_refl j))
      (hcert _ hA) rfl hB
    have hp := Arith.two_pow_le_two_pow ht
    have hb := fexp_le (oddCount m j)
    have hl := hf.1
    omega

/-- A power bracket converts the odd-count reach into a finite crossing horizon. -/
theorem first_light_descent_through {m c A H j : Nat} (hc : c ≤ m)
    (hcert : ∀ i, i < A → Bcap i + 3 ^ i * c < 2 * 2 ^ fexp i * c)
    (hgap : 2 ^ H < 3 ^ A) (hj : j ≤ H) (hf : FirstLight m j) :
    acceleratedOrbit j m < m := by
  apply first_light_descent hc hcert hf
  by_cases ha : oddCount m j < A
  · exact ha
  · have hmono : (3:Nat) ^ A ≤ 3 ^ oddCount m j := Nat.pow_le_pow_right (by decide) (by omega)
    have ht := Arith.two_pow_le_two_pow hj
    have hl := hf.1
    omega

end Collatz.Exploration.FiniteBeattyBarrier
