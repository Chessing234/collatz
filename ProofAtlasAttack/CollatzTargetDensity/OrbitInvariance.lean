import CollatzTargetDensity.RawBridge

/-! Elementary orbit facts for interpreting the predecessor density result. -/
namespace CollatzTargetDensity
open Erdos1135

theorem reaches_one_forward {n a : ℕ} (hna : Reaches n a) (hn : Reaches n 1) :
    Reaches a 1 := by
  obtain ⟨d, hd⟩ := hna
  obtain ⟨t, ht⟩ := hn
  have hcycle : (collatzStep^[3]) 1 = 1 := by decide
  have hperiod : (collatzStep^[3 * d]) 1 = 1 := by
    simpa only [Nat.mul_comm] using periodic_multiples hcycle d
  refine ⟨t + 2 * d, ?_⟩
  rw [← hd, ← Function.iterate_add_apply,
    show t + 2 * d + d = 3 * d + t by omega,
    Function.iterate_add_apply, ht]
  exact hperiod

theorem reaches_three_unit (n : ℕ) (hn : 0 < n) :
    ∃ a : ℕ, a % 3 ≠ 0 ∧ Reaches n a := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hthree : n % 3 ≠ 0
    · exact ⟨n, hthree, reaches_refl n⟩
    · by_cases he : Even n
      · have hmod := Nat.even_iff.mp he
        have hpos : 0 < n / 2 := by omega
        have hlt : n / 2 < n := Nat.div_lt_self hn (by decide)
        obtain ⟨a, ha, hreach⟩ := ih (n / 2) hlt hpos
        refine ⟨a, ha, reaches_of_reaches_step ?_⟩
        simpa only [collatzStep_eq_div_two_of_even he] using hreach
      · exact ⟨3 * n + 1, by omega,
          reaches_of_step_eq (collatzStep_eq_three_mul_add_one_of_not_even he)⟩

def rawBad : Set ℕ := {n | 0 < n ∧ ¬Reaches n 1}

theorem rawReaches_subset_bad {a : ℕ} (ha : ¬Reaches a 1) :
    rawReaches a ⊆ rawBad := by
  intro n hn
  exact ⟨hn.1, fun h => ha (reaches_one_forward hn.2 h)⟩

theorem bad_three_unit_of_bad {n : ℕ} (hn : n ∈ rawBad) :
    ∃ a : ℕ, a % 3 ≠ 0 ∧ ¬Reaches a 1 := by
  obtain ⟨a, ha, hreach⟩ := reaches_three_unit n hn.1
  exact ⟨a, ha, fun h => hn.2 (hreach.trans h)⟩

end CollatzTargetDensity
