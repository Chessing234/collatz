import Collatz.Strategy.ExcursionClock

/-!
# The plus-five valuation, a complete invariant of the first excursion

Literature on Collatz (Terras–Everett stopping times, the 3-vs-7 mixing
reductions, the crown coordinates on `n+1`) keeps splitting odd starts
into residue classes.  Those classes are one 2-adic fact about a
*different* translate:

  `n + 5  =  (n + 1)  +  4`.

`Val2 (n + 1) = v` is the odd-run length.  `Val2 4 = 2`.  The ultrametric
law on that sum is a trichotomy on every odd `n`, with no covering list:

* `v = 1`  ⇒  `v₂(n + 5) = 1`  ⇒  `n ≡ 1 (mod 4)`  ⇒  first excursion drops;
* `v ≥ 3`  ⇒  `v₂(n + 5) = 2`  ⇒  `n ≡ 7 (mod 8)`, the leftover odd-`v` family;
* `v = 2`  ⇒  collision, `v₂(n + 5) = 2 + v₂(u + 1) ≥ 3`.
  Then `v₂(n + 5) = 3` is `W ≥ 2` (`3 (mod 16)`, drops) and
  `v₂(n + 5) ≥ 4` is `(v, W) = (2, 1)` (the light clock).

So Lemma X's remaining set is exactly `{ n odd : v₂(n + 5) = 2 or ≥ 4 }`.
The first of those is born leftover; the second is the `(2, 1)` block,
which the clock burns down until it exits in `{1, 2, 3}`.  Exit `2`
joins the first family at a larger integer.  That is the obstruction,
not another modulus.

`expStep` has no extra halvings and does not preserve this reading of `W`.
-/

namespace Collatz
namespace ExcursionPlusFive

open Collatz.Arith Collatz.LiftExponent Collatz.ExcursionMap
open Collatz.ExcursionClock


/-! ## 1.  The split `n + 5 = (n + 1) + 4` -/

/-- `4` has valuation exactly `2`. -/
theorem val2_four : Val2 4 2 :=
  Val2.two_iff.mpr rfl

/-- **Peak identity for the translate.** -/
theorem plus_five_split {n : Nat} : n + 5 = (n + 1) + 4 := by
  omega


/-! ## 2.  The three cases for `v` -/

/-- `v = 1` forces `v₂(n + 5) = 1`. -/
theorem val2_of_v_one {n v u W e : Nat}
    (h : IsExcursion n v u W e) (hv : v = 1) : Val2 (n + 5) 1 := by
  subst hv
  have hsum := Val2.add_of_lt (val2_succ_of h) val2_four (by omega : (1 : Nat) < 2)
  exact plus_five_split ▸ hsum

/-- `v ≥ 3` forces `v₂(n + 5) = 2`. -/
theorem val2_of_v_ge_three {n v u W e : Nat}
    (h : IsExcursion n v u W e) (hv : 3 ≤ v) : Val2 (n + 5) 2 := by
  have hsum := Val2.add_of_lt val2_four (val2_succ_of h) (by omega : 2 < v)
  have hcomm : n + 5 = 4 + (n + 1) := by omega
  exact hcomm ▸ hsum

/-- Odd `u` makes `u + 1` even. -/
theorem val2_u_succ_pos {u t : Nat} (hu : u % 2 = 1) (ht : Val2 (u + 1) t) :
    1 ≤ t := by
  rcases Nat.eq_zero_or_pos t with rfl | hp
  · have : (u + 1) % 2 = 1 := Val2.odd_of_zero ht
    omega
  · exact Nat.succ_le_of_lt hp

/-- `v = 2` is the collision: `n + 5 = 4(u + 1)`, so
`v₂(n + 5) = 2 + v₂(u + 1) ≥ 3`. -/
theorem val2_of_v_two {n v u W e t : Nat}
    (h : IsExcursion n v u W e) (hv : v = 2) (ht : Val2 (u + 1) t) :
    Val2 (n + 5) (t + 2) := by
  subst hv
  have hnu : n + 1 = 4 * u := by
    have := h.2.2.2.2.2.1
    rw [show (2 : Nat) ^ 2 = 4 by decide] at this
    exact this
  have hsplit : n + 5 = 4 * (u + 1) := by omega
  have h4 : (4 : Nat) = 2 ^ 2 := by decide
  have hmul : Val2 (2 ^ 2 * (u + 1)) (2 + t) := Val2.two_pow_mul ht 2
  have hmul' : Val2 (4 * (u + 1)) (t + 2) := by
    rw [h4]
    simpa [Nat.add_comm] using hmul
  exact hsplit ▸ hmul'


/-! ## 3.  Dictionary with the first-excursion type -/

/-- `v₂(n + 5) = 1` iff the first run has length `1`. -/
theorem val2_eq_one_iff {n v u W e : Nat} (h : IsExcursion n v u W e) :
    Val2 (n + 5) 1 ↔ v = 1 := by
  constructor
  · intro hr
    have : (n + 5) % 4 = 2 := Val2.one_iff.mp hr
    have hmod : n % 4 = 1 := by omega
    exact (v_eq_one_iff h).mpr hmod
  · exact val2_of_v_one h

/-- `v₂(n + 5) = 2` iff the first run has length at least `3`. -/
theorem val2_eq_two_iff {n v u W e : Nat} (h : IsExcursion n v u W e) :
    Val2 (n + 5) 2 ↔ 3 ≤ v := by
  constructor
  · intro hr
    have : (n + 5) % 8 = 4 := Val2.two_iff.mp hr
    have h8 : n % 8 = 7 := by omega
    have hv : ¬ v = 1 := by
      intro hv
      have : n % 4 = 1 := (v_eq_one_iff h).mp hv
      omega
    have hv2 : ¬ v = 2 := by
      intro hv
      have : n % 8 = 3 := (v_eq_two_iff h).mp hv
      omega
    have hvpos : 0 < v := h.2.2.2.1
    omega
  · exact val2_of_v_ge_three h

/-- `v₂(n + 5) = 3` iff `v = 2` and `W ≥ 2`, i.e. `n ≡ 3 (mod 16)`. -/
theorem val2_eq_three_iff {n v u W e : Nat} (h : IsExcursion n v u W e) :
    Val2 (n + 5) 3 ↔ v = 2 ∧ 2 ≤ W := by
  constructor
  · intro hr
    have hpow : (2 : Nat) ^ (3 + 1) = 16 := by decide
    have : (n + 5) % 16 = 8 := by
      have := Val2.mod hr
      rwa [hpow] at this
    have hmod : n % 16 = 3 := by omega
    exact (v_two_W_ge_two_iff h).mpr hmod
  · intro ⟨hv, hW⟩
    have hmod : n % 16 = 3 := (v_two_W_ge_two_iff h).mp ⟨hv, hW⟩
    have : (n + 5) % 16 = 8 := by omega
    have hpow : (2 : Nat) ^ (3 + 1) = 16 := by decide
    rw [← hpow] at this
    exact Val2.of_mod this

/-- `v₂(n + 5) ≥ 4` iff the first excursion is the light block `(2, 1)`. -/
theorem val2_ge_four_iff {n v u W e : Nat} (h : IsExcursion n v u W e) :
    (∃ r : Nat, 4 ≤ r ∧ Val2 (n + 5) r) ↔ v = 2 ∧ W = 1 := by
  constructor
  · intro ⟨r, h4, hr⟩
    have hdvd : 16 ∣ n + 5 := by
      have hpow : (2 : Nat) ^ 4 = 16 := by decide
      have : 2 ^ 4 ∣ n + 5 := (Val2.dvd_iff_le hr).mpr h4
      rwa [hpow] at this
    exact (light_iff_dvd h).mpr hdvd
  · intro hvW
    have hdvd : 16 ∣ n + 5 := (light_iff_dvd h).mp hvW
    obtain ⟨r, hr⟩ := Val2.exists_of_pos (by omega : 0 < n + 5)
    have hpow : (2 : Nat) ^ 4 = 16 := by decide
    have h4 : 4 ≤ r := (Val2.dvd_iff_le hr).mp (hpow ▸ hdvd)
    exact ⟨r, h4, hr⟩


/-! ## 4.  Drops on `v₂ = 1` and `v₂ = 3`; the rest is Lemma X -/

/-- `v₂(n + 5) = 1` drops in one excursion. -/
theorem lemmaX_of_val2_one {n : Nat} (hn : 1 < n) (hodd : n % 2 = 1)
    (hr : Val2 (n + 5) 1) : ∃ e : Nat, ExChain n e ∧ e < n := by
  obtain ⟨v, u, W, e, h⟩ := exists_excursion hodd
  have hv : v = 1 := (val2_eq_one_iff h).mp hr
  have hmod : n % 4 = 1 := (v_eq_one_iff h).mp hv
  exact lemmaX_of_one_mod_four hn hmod

/-- `v₂(n + 5) = 3` drops in one excursion. -/
theorem lemmaX_of_val2_three {n : Nat} (hn : 1 < n) (hodd : n % 2 = 1)
    (hr : Val2 (n + 5) 3) : ∃ e : Nat, ExChain n e ∧ e < n := by
  obtain ⟨v, u, W, e, h⟩ := exists_excursion hodd
  have ⟨hv, hW⟩ := (val2_eq_three_iff h).mp hr
  have hmod : n % 16 = 3 := (v_two_W_ge_two_iff h).mp ⟨hv, hW⟩
  exact lemmaX_of_three_mod_sixteen hn hmod

/-- **What remains, as a 2-adic class.**  Collatz follows from Lemma X on
odd starts with `v₂(n + 5) = 2` or `v₂(n + 5) ≥ 4`.  Those are the odd-`v`
leftover and the `(2, 1)` light clock, not a new pair of moduli. -/
theorem collatz_of_lemmaX_plus_five
    (hX : ∀ n r : Nat, 1 < n → n % 2 = 1 → Val2 (n + 5) r →
      (r = 2 ∨ 4 ≤ r) → ∃ e : Nat, ExChain n e ∧ e < n) :
    CollatzConjecture :=
  collatz_of_lemmaX fun n hodd hn => by
    obtain ⟨r, hr⟩ := Val2.exists_of_pos (by omega : 0 < n + 5)
    rcases Nat.lt_trichotomy r 2 with hlt | heq | hgt
    · have hr1 : r = 1 := by
        have : 0 < r := by
          rcases Nat.eq_zero_or_pos r with rfl | hp
          · have : (n + 5) % 2 = 1 := Val2.odd_of_zero hr
            omega
          · exact hp
        omega
      exact lemmaX_of_val2_one hn hodd (hr1 ▸ hr)
    · exact hX n r hn hodd hr (Or.inl heq)
    · rcases Nat.eq_or_lt_of_le (show 3 ≤ r by omega) with h3 | h4
      · exact lemmaX_of_val2_three hn hodd (h3 ▸ hr)
      · exact hX n r hn hodd hr (Or.inr (by omega))


/-! ## 5.  Witnesses -/

/-- `v₂ = 1`: `5 + 5 = 10`, valuation `1`, drops. -/
theorem five_val2 : Val2 (5 + 5) 1 ∧ IsExcursion 5 1 3 3 1 :=
  ⟨⟨5, rfl, rfl⟩, ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩⟩

/-- `v₂ = 2`: `7 + 5 = 12`, valuation `2`, first landing `13 > 7`. -/
theorem seven_val2 : Val2 (7 + 5) 2 ∧ IsExcursion 7 3 1 1 13 ∧ 7 ≤ 13 :=
  ⟨⟨3, rfl, rfl⟩, ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega⟩

/-- `v₂ = 3`: `3 + 5 = 8`, valuation `3`, the `3 (mod 16)` drop. -/
theorem three_val2 : Val2 (3 + 5) 3 ∧ IsExcursion 3 2 1 3 1 :=
  ⟨⟨1, rfl, rfl⟩, ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩⟩

/-- `v₂ ≥ 4`: `11 + 5 = 16`, valuation `4`, the light clock. -/
theorem eleven_val2 : Val2 (11 + 5) 4 ∧ IsExcursion 11 2 3 1 13 :=
  ⟨⟨1, rfl, rfl⟩, ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩⟩

end ExcursionPlusFive
end Collatz

section AxiomAudit
open Collatz.ExcursionPlusFive
#print axioms val2_of_v_one
#print axioms val2_of_v_ge_three
#print axioms val2_of_v_two
#print axioms val2_eq_one_iff
#print axioms val2_eq_two_iff
#print axioms val2_eq_three_iff
#print axioms val2_ge_four_iff
#print axioms lemmaX_of_val2_one
#print axioms lemmaX_of_val2_three
#print axioms collatz_of_lemmaX_plus_five
end AxiomAudit
