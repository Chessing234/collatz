import Collatz.Strategy.LiftExponent
import Collatz.Structure.RunDescent
import Collatz.Strategy.NeverDrops

/-!
# Round XVI — the excursion map, and the only remaining lemma

Round XV proved that **every finite valuation word is realized by some integer**
(`ValuationTransition.word_realizable`).  That kills every automaton on the
free shift.  It does *not* say that a *single* integer orbit can follow an
arbitrary infinite word: the start `n` determines every subsequent letter.

This file names that determined dynamics.  For odd `n` write

  `n + 1 = 2 ^ v * u`  with `u` odd,

which is `Val2 (n + 1) v`.  The maximal odd run has length `v` and ends at
`3 ^ v * u − 1`.  The extra halvings that follow are exactly

  `W = v₂(3 ^ v * u − 1) ≥ 1`,

and the next odd state is the odd cofactor

  `e = (3 ^ v * u − 1) / 2 ^ W`.

The pair `(v, u)` is a complete state; `W` and `e` are functions of it.  This
is the local 2-adic constraint `v₂(3n+1) ≥ k ↔ n ≡ −3⁻¹ (mod 2^k)` pushed
along a whole orbit.

Three things are proved, and one thing is not.

1. **Even contraction is used.**  Every genuine excursion has `W ≥ 1`: after
   the odd run the state is even, and the accelerated map divides by two.
   `expStep` replaces that step by `3x/2` and so has no `W`.  The one-step
   drop criterion below is false of `expStep` at every odd start.

2. **The drop criterion is exact and size-free.**  The landing is below the
   start if and only if `3^v u + 2^W ≤ 2^{v+W} u`.  No lower bound on `n`
   is required.  (`RunDescent.drops_of_excursion` needed `2^{v+W} ≤ n`, which
   already fails at `n = 5`.)

3. **Every `n ≡ 1 (mod 4)` greater than one drops in one excursion.**  That
   is `v = 1`.  Combined with the even branch `n ↦ n/2`, Collatz reduces to
   odd starts `≡ 3 (mod 4)`.

Target A as written in the brief — `∀ n > 1, ∃ k, T^k(n) < n` — is already
the full conjecture (`NeverDrops.collatz_iff_neverDrops`): a cycle minimum
never drops, so return-below-start kills cycles as well as divergent orbits.
After the theorems of this file the conjecture is exactly:

  **Lemma X.**  For every odd `n > 1` there is an excursion iterate `e < n`.

Everything else in the chain is kernel-checked.  Lemma X is not.
-/

namespace Collatz
namespace ExcursionMap

open Collatz.Arith Collatz.LiftExponent Collatz.OddRuns Collatz.RunValue Collatz.RunDescent
open Collatz.NeverDrops


/-! ## 1.  The excursion datum -/

/-- One complete excursion from an odd start: maximal odd run of length `v`,
then exactly `W` halvings, landing on the odd state `e`.

The last equation is `3^v u = 2^W e + 1`, i.e. `v₂(3^v u − 1) = W` with odd
cofactor `e`, written without truncated subtraction. -/
def IsExcursion (n v u W e : Nat) : Prop :=
  n % 2 = 1 ∧ u % 2 = 1 ∧ e % 2 = 1 ∧
  0 < v ∧ 0 < W ∧
  n + 1 = 2 ^ v * u ∧
  3 ^ v * u = 2 ^ W * e + 1

/-- Extra halvings actually occur: this is the even branch. -/
theorem IsExcursion.one_le_W {n v u W e : Nat} (h : IsExcursion n v u W e) : 1 ≤ W :=
  h.2.2.2.2.1

/-- `n + 1` has valuation exactly `v`. -/
theorem val2_succ_of {n v u W e : Nat} (h : IsExcursion n v u W e) : Val2 (n + 1) v :=
  ⟨u, h.2.1, h.2.2.2.2.2.1⟩

/-- `3^v * u` is at least two. -/
private theorem three_pow_u_ge_two {v u : Nat} (hv : 0 < v) (hu : u % 2 = 1) :
    2 ≤ 3 ^ v * u := by
  have h3 : 3 ≤ 3 ^ v := three_le_three_pow hv
  have hu' : 1 ≤ u := by omega
  have : 3 * 1 ≤ 3 ^ v * u := Nat.mul_le_mul h3 hu'
  omega

/-- `3^v u − 1` has valuation exactly `W`. -/
theorem val2_peak_of {n v u W e : Nat} (h : IsExcursion n v u W e) :
    Val2 (3 ^ v * u - 1) W := by
  obtain ⟨_, hu, he, hv, _, _, hpeak⟩ := h
  have hge := three_pow_u_ge_two hv hu
  have hsub : 3 ^ v * u - 1 = 2 ^ W * e := by
    rw [hpeak, Nat.add_sub_cancel]
  exact ⟨e, he, hsub⟩

/-- Powers of three are odd. -/
private theorem three_pow_odd (k : Nat) : (3 : Nat) ^ k % 2 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih]

/-- Odd times odd is odd. -/
private theorem mul_odd {a b : Nat} (ha : a % 2 = 1) (hb : b % 2 = 1) :
    (a * b) % 2 = 1 := by
  rw [Nat.mul_mod, ha, hb]


/-! ## 2.  Existence and uniqueness -/

/-- **Every odd start has an excursion.**  `v` is `v₂(n+1)`, `W` is
`v₂(3^v u − 1)`, and both are at least one because `n+1` and `3^v u − 1` are
even. -/
theorem exists_excursion {n : Nat} (hn : n % 2 = 1) :
    ∃ v u W e : Nat, IsExcursion n v u W e := by
  have hnp : 0 < n + 1 := by omega
  obtain ⟨v, hv⟩ := Val2.exists_of_pos hnp
  obtain ⟨u, hu, hnu⟩ := hv
  have hvpos : 0 < v := by
    rcases Nat.eq_zero_or_pos v with rfl | hp
    · rw [Nat.pow_zero, Nat.one_mul] at hnu
      omega
    · exact hp
  have hpeak : 0 < 3 ^ v * u - 1 := by
    have := three_pow_u_ge_two hvpos hu
    omega
  obtain ⟨W, hW⟩ := Val2.exists_of_pos hpeak
  obtain ⟨e, he, hpeakEq⟩ := hW
  have hWpos : 0 < W := by
    rcases Nat.eq_zero_or_pos W with rfl | hp
    · rw [Nat.pow_zero, Nat.one_mul] at hpeakEq
      have hodd : (3 ^ v * u) % 2 = 1 := mul_odd (three_pow_odd v) hu
      omega
    · exact hp
  have hpeak' : 3 ^ v * u = 2 ^ W * e + 1 := by
    have := three_pow_u_ge_two hvpos hu
    omega
  exact ⟨v, u, W, e, hn, hu, he, hvpos, hWpos, hnu, hpeak'⟩

/-- The run length is uniquely determined. -/
theorem excursion_v_unique {n v u W e v' u' W' e' : Nat}
    (h : IsExcursion n v u W e) (h' : IsExcursion n v' u' W' e') : v = v' :=
  Val2.unique (val2_succ_of h) (val2_succ_of h')

/-- The odd cofactor of `n+1` is unique. -/
theorem excursion_u_unique {n v u W e u' W' e' : Nat}
    (h : IsExcursion n v u W e) (h' : IsExcursion n v u' W' e') : u = u' := by
  have heq : 2 ^ v * u = 2 ^ v * u' :=
    (h.2.2.2.2.2.1).symm.trans h'.2.2.2.2.2.1
  exact Nat.eq_of_mul_eq_mul_left (two_pow_pos v) heq

/-- The landing is unique. -/
theorem excursion_e_unique {n v u W e W' e' : Nat}
    (h : IsExcursion n v u W e) (h' : IsExcursion n v u W' e') : e = e' := by
  have hvW : W = W' := Val2.unique (val2_peak_of h) (val2_peak_of h')
  subst hvW
  have heq : 2 ^ W * e + 1 = 2 ^ W * e' + 1 :=
    h.2.2.2.2.2.2.symm.trans h'.2.2.2.2.2.2
  have : 2 ^ W * e = 2 ^ W * e' := by omega
  exact Nat.eq_of_mul_eq_mul_left (two_pow_pos W) this

/-- The next odd state is a well-defined function of the start. -/
theorem next_odd_unique {n v u W e v' u' W' e' : Nat}
    (h : IsExcursion n v u W e) (h' : IsExcursion n v' u' W' e') : e = e' := by
  have hv := excursion_v_unique h h'
  subst hv
  have hu := excursion_u_unique h h'
  subst hu
  exact excursion_e_unique h h'


/-! ## 3.  Identification with the accelerated orbit -/

/-- From a power of two times an odd cofactor, the first `r` accelerated steps
are even. -/
theorem even_orbit_of_val2 {m r y : Nat} (_hm : m % 2 = 1) (hy : y = 2 ^ r * m) :
    ∀ i : Nat, i < r → acceleratedOrbit i y % 2 = 0 := by
  induction r generalizing y with
  | zero =>
    intro i hi
    omega
  | succ r ih =>
    intro i hi
    have hsplit : (2 : Nat) ^ (r + 1) = 2 * 2 ^ r := two_pow_succ r
    have hyeven : y % 2 = 0 := by
      rw [hy, hsplit, Nat.mul_assoc]
      omega
    cases i with
    | zero =>
      rw [acceleratedOrbit]
      exact hyeven
    | succ i =>
      have hi' : i < r := by omega
      have hy2 : y / 2 = 2 ^ r * m := by
        rw [hy, hsplit, Nat.mul_assoc]
        exact Nat.mul_div_cancel_left (2 ^ r * m) (by omega)
      have horb : acceleratedOrbit (i + 1) y = acceleratedOrbit i (y / 2) := by
        rw [acceleratedOrbit, acceleratedStep, if_pos hyeven]
      rw [horb]
      exact ih hy2 i hi'

/-- The peak of the odd run is `3^v u − 1`. -/
theorem peak_eq {n v u W e : Nat} (h : IsExcursion n v u W e) :
    acceleratedOrbit v n = 3 ^ v * u - 1 := by
  have hrun : OddRun n v := (oddRun_iff v n).mpr ⟨u, h.2.2.2.2.2.1⟩
  have hquot := oddRun_value_quot hrun h.2.2.2.2.2.1
  have hge := three_pow_u_ge_two h.2.2.2.1 h.2.1
  omega

/-- **The landing is an accelerated iterate.**  After `v + W` accelerated
steps the state is exactly the next odd number of the excursion. -/
theorem landing_eq {n v u W e : Nat} (h : IsExcursion n v u W e) :
    acceleratedOrbit (v + W) n = e := by
  have hpeak := peak_eq h
  have hy : acceleratedOrbit v n = 2 ^ W * e := by
    rw [hpeak, h.2.2.2.2.2.2, Nat.add_sub_cancel]
  have heven := even_orbit_of_val2 h.2.2.1 hy
  have hchain := halving_chain W (acceleratedOrbit v n) heven
  have hshift : acceleratedOrbit W (acceleratedOrbit v n) = acceleratedOrbit (v + W) n := by
    rw [acceleratedOrbit_add, Nat.add_comm]
  rw [hshift] at hchain
  have : 2 ^ W * acceleratedOrbit (v + W) n = 2 ^ W * e := by
    rw [hchain, hy]
  exact Nat.eq_of_mul_eq_mul_left (two_pow_pos W) this

/-- A one-step excursion. -/
def NextOdd (n e : Nat) : Prop := ∃ v u W : Nat, IsExcursion n v u W e

/-- Finite chains of excursions. -/
inductive ExChain : Nat → Nat → Prop where
  | one {n e : Nat} : NextOdd n e → ExChain n e
  | cons {n e e' : Nat} : NextOdd n e → ExChain e e' → ExChain n e'

/-- Every landing is an accelerated iterate. -/
theorem chain_is_orbit {n e : Nat} (h : ExChain n e) :
    ∃ t : Nat, acceleratedOrbit t n = e := by
  induction h with
  | one hnext =>
    obtain ⟨v, u, W, hex⟩ := hnext
    exact ⟨v + W, landing_eq hex⟩
  | cons hnext _ ih =>
    obtain ⟨v, u, W, hex⟩ := hnext
    obtain ⟨t, ht⟩ := ih
    refine ⟨v + W + t, ?_⟩
    have hland := landing_eq hex
    have hcomm : v + W + t = t + (v + W) := Nat.add_comm _ _
    rw [hcomm]
    rw [← acceleratedOrbit_add, hland, ht]


/-! ## 4.  The exact drop criterion

This is the even contraction consumed as an inequality: `W` extra factors of
`1/2` after the odd run, with no size hypothesis on `n`. -/

/-- **Exact one-step drop.**  The landing is strictly below the start if and
only if `3^v u + 2^W ≤ 2^{v+W} u`. -/
theorem drop_iff {n v u W e : Nat} (h : IsExcursion n v u W e) :
    e < n ↔ 3 ^ v * u + 2 ^ W ≤ 2 ^ (v + W) * u := by
  have hWpos : 0 < 2 ^ W := two_pow_pos W
  have hn' : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
  have hpeak : 2 ^ W * e + 1 = 3 ^ v * u := h.2.2.2.2.2.2.symm
  have hpow : (2 : Nat) ^ (v + W) * u = 2 ^ W * (n + 1) := by
    rw [Nat.pow_add, hn']
    simp [Nat.mul_assoc, Nat.mul_comm]
  constructor
  · intro hlt
    have hmul : 2 ^ W * e < 2 ^ W * n := Nat.mul_lt_mul_of_pos_left hlt hWpos
    have h1 : 2 ^ W * e + 1 ≤ 2 ^ W * n := Nat.succ_le_of_lt hmul
    have h2 : 3 ^ v * u ≤ 2 ^ W * n := by rw [← hpeak]; exact h1
    have h3 : 3 ^ v * u + 2 ^ W ≤ 2 ^ W * n + 2 ^ W := Nat.add_le_add_right h2 _
    have h4 : 2 ^ W * n + 2 ^ W = 2 ^ W * (n + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
    rw [h4, ← hpow] at h3
    exact h3
  · intro hle
    have h3 : 3 ^ v * u + 2 ^ W ≤ 2 ^ W * (n + 1) := by rw [← hpow]; exact hle
    have h4 : 2 ^ W * (n + 1) = 2 ^ W * n + 2 ^ W := by
      rw [Nat.mul_add, Nat.mul_one]
    rw [h4] at h3
    have h2 : 3 ^ v * u ≤ 2 ^ W * n := Nat.le_of_add_le_add_right h3
    have h1 : 2 ^ W * e + 1 ≤ 2 ^ W * n := by rw [hpeak]; exact h2
    have hmul : 2 ^ W * e < 2 ^ W * n := Nat.lt_of_succ_le h1
    exact Nat.lt_of_mul_lt_mul_left hmul

/-- **Necessity of surplus halvings.**  A one-step drop forces `3^v < 2^{v+W}`.
This is why `expStep` (which has no extra halvings) never drops. -/
theorem drop_needs_surplus {n v u W e : Nat} (h : IsExcursion n v u W e) (hlt : e < n) :
    3 ^ v < 2 ^ (v + W) := by
  have hiff := (drop_iff h).mp hlt
  have hleft : 3 ^ v * u < 3 ^ v * u + 2 ^ W := by
    have := two_pow_pos W
    omega
  have : 3 ^ v * u < 2 ^ (v + W) * u := Nat.lt_of_lt_of_le hleft hiff
  exact Nat.lt_of_mul_lt_mul_right this

/-- **The complementary bound.**  If the extra halvings do not beat
`log₂ 3 − 1`, the excursion cannot drop. -/
theorem no_drop_of_light {n v u W e : Nat} (h : IsExcursion n v u W e)
    (hlight : 2 ^ (v + W) ≤ 3 ^ v) : n ≤ e := by
  rcases Nat.lt_or_ge e n with hlt | hge
  · exact absurd (drop_needs_surplus h hlt) (by omega)
  · exact hge


/-! ## 5.  The even branch, and the class `v = 1` -/

/-- **Exact even contraction.**  For even `n > 1` the accelerated map is
`n/2`, which is strictly smaller.  `expStep` does `3n/2` here and grows. -/
theorem even_branch_contracts {n : Nat} (hn : 1 < n) (he : n % 2 = 0) :
    acceleratedStep n < n := by
  rw [acceleratedStep, if_pos he]
  omega

/-- `v = 1` is the residue `1 mod 4`. -/
theorem v_eq_one_iff {n v u W e : Nat} (h : IsExcursion n v u W e) :
    v = 1 ↔ n % 4 = 1 := by
  constructor
  · intro hv
    have hu : u % 2 = 1 := h.2.1
    have hnu : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
    rw [hv, Nat.pow_one] at hnu
    omega
  · intro h4
    have hval : Val2 (n + 1) 1 := by
      refine Val2.of_mod ?_
      have hmod : (2 : Nat) ^ (1 + 1) = 4 := by decide
      rw [hmod]
      have hadd : (n + 1) % 4 = (n % 4 + 1) % 4 := Nat.add_mod n 1 4
      rw [hadd, h4]
    exact Val2.unique (val2_succ_of h) hval

/-- Auxiliary: `3u + 2^W ≤ 2^{W+1} u` for odd `u ≥ 3` and `W ≥ 1`. -/
private theorem v_one_ineq {u W : Nat} (hu : 3 ≤ u) (hW : 1 ≤ W) :
    3 * u + 2 ^ W ≤ 2 * 2 ^ W * u := by
  match W with
  | 0 => omega
  | 1 =>
    have : (2 : Nat) * 2 ^ 1 * u = 4 * u := by simp
    omega
  | k + 2 =>
    have h4 : 4 ≤ 2 ^ (k + 2) := by
      have : (2 : Nat) ^ 2 ≤ 2 ^ (k + 2) := two_pow_le_two_pow (by omega)
      simpa using this
    have hsum : 3 + 2 ^ (k + 2) ≤ 2 * 2 ^ (k + 2) := by omega
    have hstep : 3 * u + 2 ^ (k + 2) ≤ (3 + 2 ^ (k + 2)) * u := by
      have hmul : 2 ^ (k + 2) ≤ 2 ^ (k + 2) * u :=
        Nat.le_mul_of_pos_right _ (by omega)
      have : 3 * u + 2 ^ (k + 2) ≤ 3 * u + 2 ^ (k + 2) * u :=
        Nat.add_le_add_left hmul _
      have hdist : 3 * u + 2 ^ (k + 2) * u = (3 + 2 ^ (k + 2)) * u := by
        rw [Nat.add_mul]
      omega
    have hmul : (3 + 2 ^ (k + 2)) * u ≤ (2 * 2 ^ (k + 2)) * u :=
      Nat.mul_le_mul_right u hsum
    have : (2 * 2 ^ (k + 2)) * u = 2 * 2 ^ (k + 2) * u := by
      simp [Nat.mul_assoc]
    omega

/-- **Every odd `n > 1` with `v = 1` drops in one excursion.**  These are
exactly the numbers `≡ 1 (mod 4)`.  The proof uses `W ≥ 1` — the even
branch — and is false of any map that does not divide by two on evens. -/
theorem drop_of_v_one {n v u W e : Nat} (h : IsExcursion n v u W e)
    (hv : v = 1) (hn : 1 < n) : e < n := by
  subst hv
  have hnu : n + 1 = 2 * u := by
    have := h.2.2.2.2.2.1
    rw [Nat.pow_one] at this
    exact this
  have hu3 : 3 ≤ u := by
    have : u % 2 = 1 := h.2.1
    omega
  have hW : 1 ≤ W := IsExcursion.one_le_W h
  refine (drop_iff h).mpr ?_
  have hpow : (2 : Nat) ^ (1 + W) = 2 * 2 ^ W := by
    rw [Nat.pow_add, Nat.pow_one]
  rw [Nat.pow_one, hpow]
  exact v_one_ineq hu3 hW

/-- Auxiliary: `9u + 2^W ≤ 2^{W+2} u` for `W ≥ 2` and `u ≥ 1`. -/
private theorem v_two_ineq {u W : Nat} (hu : 1 ≤ u) (hW : 2 ≤ W) :
    9 * u + 2 ^ W ≤ 2 ^ (W + 2) * u := by
  have hpow : (2 : Nat) ^ (W + 2) = 4 * 2 ^ W := by
    rw [Nat.pow_add, show (2 : Nat) ^ 2 = 4 by decide, Nat.mul_comm]
  rw [hpow]
  have hp : 4 ≤ 2 ^ W := by
    have : (2 : Nat) ^ 2 ≤ 2 ^ W := two_pow_le_two_pow hW
    simpa using this
  have hsum : 9 + 2 ^ W ≤ 4 * 2 ^ W := by omega
  have hstep : 9 * u + 2 ^ W ≤ (9 + 2 ^ W) * u := by
    have hmul : 2 ^ W ≤ 2 ^ W * u := Nat.le_mul_of_pos_right _ (by omega)
    have : 9 * u + 2 ^ W ≤ 9 * u + 2 ^ W * u := Nat.add_le_add_left hmul _
    have hdist : 9 * u + 2 ^ W * u = (9 + 2 ^ W) * u := by rw [Nat.add_mul]
    omega
  have hmul : (9 + 2 ^ W) * u ≤ (4 * 2 ^ W) * u := Nat.mul_le_mul_right u hsum
  have : (4 * 2 ^ W) * u = 4 * 2 ^ W * u := by simp [Nat.mul_assoc]
  omega

/-- **Every odd `n > 1` with `v = 2` and `W ≥ 2` drops in one excursion.** -/
theorem drop_of_v_two {n v u W e : Nat} (h : IsExcursion n v u W e)
    (hv : v = 2) (hW : 2 ≤ W) (hn : 1 < n) : e < n := by
  subst hv
  have hnu : n + 1 = 4 * u := by
    have := h.2.2.2.2.2.1
    rw [show (2 : Nat) ^ 2 = 4 by decide] at this
    exact this
  have hu : 1 ≤ u := by omega
  refine (drop_iff h).mpr ?_
  have hpow : (2 : Nat) ^ (2 + W) = 2 ^ (W + 2) := by rw [Nat.add_comm]
  rw [show (3 : Nat) ^ 2 = 9 by decide, hpow]
  exact v_two_ineq hu hW

/-- `v = 2` is the residue `3 mod 8`. -/
theorem v_eq_two_iff {n v u W e : Nat} (h : IsExcursion n v u W e) :
    v = 2 ↔ n % 8 = 3 := by
  constructor
  · intro hv
    have hu : u % 2 = 1 := h.2.1
    have hnu : n + 1 = 2 ^ v * u := h.2.2.2.2.2.1
    rw [hv, show (2 : Nat) ^ 2 = 4 by decide] at hnu
    omega
  · intro h8
    have hval : Val2 (n + 1) 2 := Val2.two_iff.mpr (by rw [Nat.add_mod, h8])
    exact Val2.unique (val2_succ_of h) hval

/-- With `v = 2`, extra halvings `W ≥ 2` iff `4 ∣ 9u − 1` iff `u ≡ 1 (mod 4)`. -/
theorem W_ge_two_iff_u {n v u W e : Nat} (h : IsExcursion n v u W e) (hv : v = 2) :
    2 ≤ W ↔ u % 4 = 1 := by
  subst hv
  have hpeak : 9 * u = 2 ^ W * e + 1 := by
    have := h.2.2.2.2.2.2
    rw [show (3 : Nat) ^ 2 = 9 by decide] at this
    exact this
  have he : e % 2 = 1 := h.2.2.1
  have nine_mod : (9 * u) % 4 = u % 4 := by
    rw [Nat.mul_mod, show (9 : Nat) % 4 = 1 by decide, Nat.one_mul, Nat.mod_mod]
  constructor
  · intro hW
    have hpe : (2 ^ W * e + 1) % 4 = 1 := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hW
      subst hk
      rw [Nat.pow_add, show (2 : Nat) ^ 2 = 4 by decide, Nat.mul_assoc,
          Nat.mul_add_mod_self_left]
    rw [← nine_mod, hpeak]
    exact hpe
  · intro hu
    rcases Nat.lt_or_ge W 2 with hlt | hge
    · have hWpos : 0 < W := h.2.2.2.2.1
      have hW1 : W = 1 := by omega
      subst hW1
      have he4 : e % 4 = 1 ∨ e % 4 = 3 := by omega
      have hpe : (2 * e + 1) % 4 = 3 := by
        rcases he4 with he1 | he3
        · rw [Nat.add_mod, Nat.mul_mod, he1]
        · rw [Nat.add_mod, Nat.mul_mod, he3]
      have hu1 : (9 * u) % 4 = 1 := by rw [nine_mod, hu]
      rw [hpeak] at hu1
      omega
    · exact hge

/-- `v = 2` and `W ≥ 2` is the residue `3 mod 16`. -/
theorem v_two_W_ge_two_iff {n v u W e : Nat} (h : IsExcursion n v u W e) :
    v = 2 ∧ 2 ≤ W ↔ n % 16 = 3 := by
  constructor
  · intro ⟨hv, hW⟩
    have hu : u % 4 = 1 := (W_ge_two_iff_u h hv).mp hW
    have hnu : n + 1 = 4 * u := by
      have := h.2.2.2.2.2.1
      rw [hv, show (2 : Nat) ^ 2 = 4 by decide] at this
      exact this
    omega
  · intro h16
    have hv : v = 2 := (v_eq_two_iff h).mpr (by omega)
    refine ⟨hv, ?_⟩
    have hnu : n + 1 = 4 * u := by
      have := h.2.2.2.2.2.1
      rw [hv, show (2 : Nat) ^ 2 = 4 by decide] at this
      exact this
    have hu : u % 4 = 1 := by omega
    exact (W_ge_two_iff_u h hv).mpr hu

/-- **Every odd `n > 1` congruent to `3 mod 16` drops in one excursion.** -/
theorem drop_of_three_mod_sixteen {n v u W e : Nat} (h : IsExcursion n v u W e)
    (hmod : n % 16 = 3) (hn : 1 < n) : e < n := by
  obtain ⟨hv, hW⟩ := (v_two_W_ge_two_iff h).mpr hmod
  exact drop_of_v_two h hv hW hn

/-- `5 ≡ 1 (mod 4)`: one excursion lands at `1`. -/
theorem five_drops : IsExcursion 5 1 3 3 1 ∧ 1 < 5 := by
  refine ⟨⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩, by omega⟩

/-- `7 ≡ 3 (mod 4)`: the first excursion lands at `13 > 7`.  So Lemma X is not
the first-excursion statement, and `v = 1` is sharp as a one-step class. -/
theorem seven_first_excursion : IsExcursion 7 3 1 1 13 :=
  ⟨rfl, rfl, rfl, by omega, by omega, rfl, rfl⟩

/-- The first excursion of `7` cannot drop: `2^{v+W} = 16 ≤ 27 = 3^v`. -/
theorem seven_no_first_drop {e : Nat} (h : IsExcursion 7 3 1 1 e) : 7 ≤ e :=
  no_drop_of_light h (by decide)


/-! ## 6.  Return-below-start is the full conjecture -/

/-- **Target A as written is Collatz, not the divergence half.**  A nontrivial
cycle's minimum never drops, so `∀ n > 1, ∃ k, T^k(n) < n` kills both halves. -/
theorem collatz_iff_return :
    CollatzConjecture ↔ ∀ n : Nat, 1 < n → ∃ k : Nat, acceleratedOrbit k n < n := by
  rw [collatz_iff_neverDrops]
  constructor
  · intro h n hn
    have hnd : ¬ NeverDrops n := fun hnd => by
      have := h n hnd
      omega
    unfold NeverDrops at hnd
    obtain ⟨k, hk⟩ := Classical.not_forall.mp hnd
    exact ⟨k, by omega⟩
  · intro h x hnd
    rcases Nat.lt_or_ge x 2 with hlt | hge
    · omega
    · obtain ⟨k, hk⟩ := h x hge
      have := hnd k
      omega

/-- An excursion landing below the start is a return. -/
theorem return_of_drop {n v u W e : Nat} (h : IsExcursion n v u W e) (hlt : e < n) :
    ∃ k : Nat, acceleratedOrbit k n < n :=
  ⟨v + W, landing_eq h ▸ hlt⟩

/-- **The `v = 1` class of Target A, closed.**  Every odd `n > 1` congruent to
`1 mod 4` returns below its start, in one excursion. -/
theorem return_of_one_mod_four {n : Nat} (hn : 1 < n) (hmod : n % 4 = 1) :
    ∃ k : Nat, acceleratedOrbit k n < n := by
  have hodd : n % 2 = 1 := by omega
  obtain ⟨v, u, W, e, h⟩ := exists_excursion hodd
  have hv : v = 1 := (v_eq_one_iff h).mpr hmod
  exact return_of_drop h (drop_of_v_one h hv hn)

/-- **What remains after consuming the even branch and the class `v = 1`.** -/
theorem collatz_of_three_mod_four
    (h : ∀ n : Nat, 1 < n → n % 4 = 3 → ∃ k : Nat, acceleratedOrbit k n < n) :
    CollatzConjecture := by
  refine collatz_iff_return.mpr ?_
  intro n hn
  rcases Arith.mod_two_eq_zero_or_one n with he | ho
  · exact ⟨1, even_branch_contracts hn he⟩
  · have h4 : n % 4 = 1 ∨ n % 4 = 3 := by omega
    rcases h4 with h1 | h3
    · exact return_of_one_mod_four hn h1
    · exact h n hn h3

/-- The `v = 2`, `W ≥ 2` class of Target A, closed.  Every odd `n > 1`
congruent to `3 mod 16` returns below its start, in one excursion. -/
theorem return_of_three_mod_sixteen {n : Nat} (hn : 1 < n) (hmod : n % 16 = 3) :
    ∃ k : Nat, acceleratedOrbit k n < n := by
  have hodd : n % 2 = 1 := by omega
  obtain ⟨v, u, W, e, h⟩ := exists_excursion hodd
  exact return_of_drop h (drop_of_three_mod_sixteen h hmod hn)

/-- **What remains after consuming the even branch, `v = 1`, and `v = 2` with
`W ≥ 2`.**  Collatz follows from return on `{7, 11, 15}` mod 16. -/
theorem collatz_of_seven_eleven_fifteen_mod_sixteen
    (h : ∀ n : Nat, 1 < n → (n % 16 = 7 ∨ n % 16 = 11 ∨ n % 16 = 15) →
      ∃ k : Nat, acceleratedOrbit k n < n) :
    CollatzConjecture := by
  refine collatz_of_three_mod_four ?_
  intro n hn h3
  have h16 : n % 16 = 3 ∨ n % 16 = 7 ∨ n % 16 = 11 ∨ n % 16 = 15 := by omega
  rcases h16 with h3' | hrest
  · exact return_of_three_mod_sixteen hn h3'
  · exact h n hn hrest


/-! ## 7.  Lemma X -/

/-- **Lemma X.**  Every odd `n > 1` has an excursion iterate strictly below
`n`.  Equivalently: the exact criterion `3^v u + 2^W ≤ 2^{v+W} u` fires at
some generation of the `(v, u)` map.

This is the return-below-start theorem restricted to odd starts.  Combined
with `even_branch_contracts` and `return_of_one_mod_four` it is the full
conjecture.  It is *not* a finite verification, *not* a density statement,
and *not* a restatement of a word-only obstruction: the criterion consumes
the extra halvings `W = v₂(3^v u − 1)`, which `expStep` does not have. -/
def LemmaX : Prop :=
  ∀ n : Nat, n % 2 = 1 → 1 < n → ∃ e : Nat, ExChain n e ∧ e < n

/-- Lemma X implies Collatz.  The even branch and the class `v = 1` are
already closed; Lemma X is used only on `n ≡ 3 (mod 4)`. -/
theorem collatz_of_lemmaX (hX : LemmaX) : CollatzConjecture := by
  refine collatz_of_three_mod_four ?_
  intro n hn h3
  have hodd : n % 2 = 1 := by omega
  obtain ⟨e, hchain, hlt⟩ := hX n hodd hn
  obtain ⟨t, ht⟩ := chain_is_orbit hchain
  exact ⟨t, ht ▸ hlt⟩

/-- Lemma X holds on the class `v = 1`. -/
theorem lemmaX_of_one_mod_four {n : Nat} (hn : 1 < n) (hmod : n % 4 = 1) :
    ∃ e : Nat, ExChain n e ∧ e < n := by
  have hodd : n % 2 = 1 := by omega
  obtain ⟨v, u, W, e, h⟩ := exists_excursion hodd
  have hv : v = 1 := (v_eq_one_iff h).mpr hmod
  exact ⟨e, ExChain.one ⟨v, u, W, h⟩, drop_of_v_one h hv hn⟩

/-- Lemma X holds on the class `v = 2` with `W ≥ 2`. -/
theorem lemmaX_of_three_mod_sixteen {n : Nat} (hn : 1 < n) (hmod : n % 16 = 3) :
    ∃ e : Nat, ExChain n e ∧ e < n := by
  have hodd : n % 2 = 1 := by omega
  obtain ⟨v, u, W, e, h⟩ := exists_excursion hodd
  exact ⟨e, ExChain.one ⟨v, u, W, h⟩, drop_of_three_mod_sixteen h hmod hn⟩

/-- **The remaining input, after everything this file proves.**  Collatz
follows from Lemma X on the single residue class `3 mod 4`. -/
theorem collatz_of_lemmaX_three_mod_four
    (h : ∀ n : Nat, 1 < n → n % 4 = 3 → ∃ e : Nat, ExChain n e ∧ e < n) :
    CollatzConjecture :=
  collatz_of_lemmaX fun n hodd hn =>
    have h4 : n % 4 = 1 ∨ n % 4 = 3 := by omega
    h4.elim (fun h1 => lemmaX_of_one_mod_four hn h1) (fun h3 => h n hn h3)

/-- **The remaining input after closing `3 mod 16`.**  Collatz follows from
Lemma X on `{7, 11, 15}` mod 16. -/
theorem collatz_of_lemmaX_seven_eleven_fifteen_mod_sixteen
    (h : ∀ n : Nat, 1 < n → (n % 16 = 7 ∨ n % 16 = 11 ∨ n % 16 = 15) →
      ∃ e : Nat, ExChain n e ∧ e < n) :
    CollatzConjecture :=
  collatz_of_lemmaX_three_mod_four fun n hn h3 =>
    have h16 : n % 16 = 3 ∨ n % 16 = 7 ∨ n % 16 = 11 ∨ n % 16 = 15 := by omega
    h16.elim (fun h3' => lemmaX_of_three_mod_sixteen hn h3') (fun hrest => h n hn hrest)


/-! ## 8.  Two excursions on `n ≡ 11 (mod 32)`

The complementary `v = 2` class is `W = 1`, i.e. `n ≡ 11 (mod 16)`.  The first
landing sits above the start (`2^{v+W} = 8 ≤ 9 = 3^v`).  On the subclass
`n ≡ 11 (mod 32)` that landing is `≡ 1 (mod 4)`, so the second excursion is a
`v = 1` drop, and the extra factor of `1/2` is already enough to pass back
below the original start. -/

/-- `v = 2` and `W = 1` is the residue `11 mod 16`. -/
theorem v_two_W_one_iff {n v u W e : Nat} (h : IsExcursion n v u W e) :
    v = 2 ∧ W = 1 ↔ n % 16 = 11 := by
  constructor
  · intro ⟨hv, hW⟩
    have h8 : n % 8 = 3 := (v_eq_two_iff h).mp hv
    have hne : n % 16 ≠ 3 := by
      intro h3
      have := ((v_two_W_ge_two_iff h).mpr h3).2
      omega
    omega
  · intro h16
    have hv : v = 2 := (v_eq_two_iff h).mpr (by omega)
    have hne : ¬ 2 ≤ W := by
      intro hW
      have : n % 16 = 3 := (v_two_W_ge_two_iff h).mp ⟨hv, hW⟩
      omega
    have hW1 : 1 ≤ W := IsExcursion.one_le_W h
    exact ⟨hv, by omega⟩

/-- The first excursion of `n ≡ 11 (mod 16)` cannot drop. -/
theorem no_drop_of_eleven_mod_sixteen {n v u W e : Nat}
    (h : IsExcursion n v u W e) (hmod : n % 16 = 11) : n ≤ e := by
  obtain ⟨hv, hW⟩ := (v_two_W_one_iff h).mpr hmod
  subst hv
  subst hW
  exact no_drop_of_light h (by decide)

/-- On `n ≡ 11 (mod 32)` the first landing is `≡ 1 (mod 4)`. -/
theorem landing_one_mod_four_of_eleven_mod_thirtytwo {n v u W e : Nat}
    (h : IsExcursion n v u W e) (hmod : n % 32 = 11) : e % 4 = 1 := by
  obtain ⟨hv, hW⟩ := (v_two_W_one_iff h).mpr (by omega)
  have hnu : n + 1 = 4 * u := by
    have := h.2.2.2.2.2.1
    rw [hv, show (2 : Nat) ^ 2 = 4 by decide] at this
    exact this
  have hpeak : 9 * u = 2 * e + 1 := by
    have := h.2.2.2.2.2.2
    rw [hv, hW, show (3 : Nat) ^ 2 = 9 by decide, Nat.pow_one] at this
    exact this
  have he : e % 2 = 1 := h.2.2.1
  omega

/-- From `4 u' = 9 u + 1` and the crude bound `2 e' ≤ 3 u' − 1`, the second
landing is already below the original start `4u − 1` when `u ≥ 3`. -/
private theorem eleven_second_lt {u u' e' : Nat}
    (hu : 3 ≤ u) (hrel : 4 * u' = 9 * u + 1)
    (h2e : 2 * e' ≤ 3 * u' - 1) : e' < 4 * u - 1 := by
  have hu' : 1 ≤ u' := by
    have : 28 ≤ 4 * u' := by omega
    omega
  have hlt : 3 * u' - 1 < 8 * u - 2 := by
    have hlhs : 4 * (3 * u' - 1) = 27 * u - 1 := by
      have : 4 * (3 * u' - 1) = 3 * (4 * u') - 4 := by omega
      rw [this, hrel]
      omega
    have : 4 * (3 * u' - 1) < 4 * (8 * u - 2) := by omega
    exact Nat.lt_of_mul_lt_mul_left this
  have : 2 * e' < 2 * (4 * u - 1) := by
    have : 8 * u - 2 = 2 * (4 * u - 1) := by omega
    omega
  exact Nat.lt_of_mul_lt_mul_left this

/-- **The class `11 mod 32` drops in two excursions.** -/
theorem lemmaX_of_eleven_mod_thirtytwo {n : Nat} (_hn : 1 < n) (hmod : n % 32 = 11) :
    ∃ e : Nat, ExChain n e ∧ e < n := by
  have hodd : n % 2 = 1 := by omega
  obtain ⟨v, u, W, e, h⟩ := exists_excursion hodd
  have hvW := (v_two_W_one_iff h).mpr (show n % 16 = 11 by omega)
  have hv := hvW.1
  have hW := hvW.2
  have hnu : n + 1 = 4 * u := by
    have := h.2.2.2.2.2.1
    rw [hv, show (2 : Nat) ^ 2 = 4 by decide] at this
    exact this
  have hu : 3 ≤ u := by omega
  have hpeak : 9 * u = 2 * e + 1 := by
    have := h.2.2.2.2.2.2
    rw [hv, hW, show (3 : Nat) ^ 2 = 9 by decide, Nat.pow_one] at this
    exact this
  have heodd : e % 2 = 1 := h.2.2.1
  have he4 : e % 4 = 1 := landing_one_mod_four_of_eleven_mod_thirtytwo h hmod
  obtain ⟨v', u', W', e', h'⟩ := exists_excursion heodd
  have hv' : v' = 1 := (v_eq_one_iff h').mpr he4
  have hnu' : e + 1 = 2 * u' := by
    have := h'.2.2.2.2.2.1
    rw [hv', Nat.pow_one] at this
    exact this
  have hrel : 4 * u' = 9 * u + 1 := by omega
  have hpeak' : 3 * u' = 2 ^ W' * e' + 1 := by
    have := h'.2.2.2.2.2.2
    rw [hv', Nat.pow_one] at this
    exact this
  have h2e : 2 * e' ≤ 3 * u' - 1 := by
    have hW' : 1 ≤ W' := IsExcursion.one_le_W h'
    have hge : 2 ≤ 2 ^ W' := two_le_two_pow (by omega)
    have hmul : 2 * e' ≤ 2 ^ W' * e' := Nat.mul_le_mul_right e' hge
    have : 2 ^ W' * e' = 3 * u' - 1 := by omega
    omega
  have hlt : e' < n := by
    have : e' < 4 * u - 1 := eleven_second_lt hu hrel h2e
    omega
  exact ⟨e', ExChain.cons ⟨v, u, W, h⟩ (ExChain.one ⟨v', u', W', h'⟩), hlt⟩

/-- The `11 mod 32` class of Target A, closed. -/
theorem return_of_eleven_mod_thirtytwo {n : Nat} (hn : 1 < n) (hmod : n % 32 = 11) :
    ∃ k : Nat, acceleratedOrbit k n < n := by
  obtain ⟨e, hchain, hlt⟩ := lemmaX_of_eleven_mod_thirtytwo hn hmod
  obtain ⟨t, ht⟩ := chain_is_orbit hchain
  exact ⟨t, ht ▸ hlt⟩

/-- **What remains after closing `11 mod 32`.**  Collatz follows from Lemma X
on `{7, 15}` mod 16 and `27 mod 32`. -/
theorem collatz_of_lemmaX_remaining
    (h : ∀ n : Nat, 1 < n →
      (n % 16 = 7 ∨ n % 16 = 15 ∨ n % 32 = 27) →
      ∃ e : Nat, ExChain n e ∧ e < n) :
    CollatzConjecture :=
  collatz_of_lemmaX_seven_eleven_fifteen_mod_sixteen fun n hn hrest => by
    rcases hrest with h7 | h11 | h15
    · exact h n hn (Or.inl h7)
    · have h32 : n % 32 = 11 ∨ n % 32 = 27 := by omega
      rcases h32 with h11' | h27
      · exact lemmaX_of_eleven_mod_thirtytwo hn h11'
      · exact h n hn (Or.inr (Or.inr h27))
    · exact h n hn (Or.inr (Or.inl h15))

/-- Orbit form of the same reduction. -/
theorem collatz_of_remaining
    (h : ∀ n : Nat, 1 < n →
      (n % 16 = 7 ∨ n % 16 = 15 ∨ n % 32 = 27) →
      ∃ k : Nat, acceleratedOrbit k n < n) :
    CollatzConjecture :=
  collatz_of_seven_eleven_fifteen_mod_sixteen fun n hn hrest => by
    rcases hrest with h7 | h11 | h15
    · exact h n hn (Or.inl h7)
    · have h32 : n % 32 = 11 ∨ n % 32 = 27 := by omega
      rcases h32 with h11' | h27
      · exact return_of_eleven_mod_thirtytwo hn h11'
      · exact h n hn (Or.inr (Or.inr h27))
    · exact h n hn (Or.inr (Or.inl h15))

end ExcursionMap
end Collatz

section AxiomAudit
open Collatz.ExcursionMap
#print axioms exists_excursion
#print axioms drop_iff
#print axioms drop_of_v_one
#print axioms drop_of_v_two
#print axioms v_eq_two_iff
#print axioms v_two_W_ge_two_iff
#print axioms drop_of_three_mod_sixteen
#print axioms v_two_W_one_iff
#print axioms lemmaX_of_eleven_mod_thirtytwo
#print axioms collatz_of_lemmaX
#print axioms collatz_of_lemmaX_three_mod_four
#print axioms collatz_of_seven_eleven_fifteen_mod_sixteen
#print axioms collatz_of_lemmaX_seven_eleven_fifteen_mod_sixteen
#print axioms collatz_of_lemmaX_remaining
#print axioms collatz_of_remaining
end AxiomAudit
