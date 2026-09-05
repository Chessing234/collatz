import Collatz.Strategy.NewModels
import Collatz.Strategy.CycleAccumulator
import Collatz.Core.Pigeonhole

/-!
# Local blindness at `2` and `3`: what a cycle proof must use about `d = 1`

**Novelty tag: NEW as a stated theorem; corollary of known results.**  The
ingredients are Lagarias's rational-cycle theorem (*The set of rational cycles
for the 3x+1 problem*, Acta Arith. 56, 1990 — every periodic parity word is the
word of an integer cycle of some `3x + d`, here `NewModels.word_is_cycle_word`)
and the Chinese remainder theorem.  The barrier it expresses — that `3x − 1`,
`3x + 5`, … have cycles, so no argument blind to `d` can exclude them — is
folklore and is `CLOSURE.md`'s Class 4.  What is new is the *quantitative*
form: blindness holds modulo **every** power of `6`, and only at the primes
`2` and `3`.

## The theorem

Let `w` be any parity word of length `L ≥ 1` with at least one odd step and a
contracting multiplier `3 ^ a ≤ 2 ^ L` (a *light* word; every cycle word is
light).  Then for **every** `k` there is an odd `d` with

    d ≡ 1  (mod 6 ^ k)

and a positive integer `x` which is a period-`L` cycle point of
`x ↦ (3x + d)/2, x/2` carrying exactly the word `w` — same odd count, same
accumulator (`local_blindness`).  In particular `d ≡ 1 (mod 2 ^ k)` and
`d ≡ 1 (mod 3 ^ k)` simultaneously (`local_blindness_two_three`).

## What it says

The parity-word combinatorics of `3x + d` (Terras's residue classes, the affine
law `2 ^ L x_L = 3 ^ a x + d · C`, heaviness, the order of `2` modulo the gap,
every `2`-adic and `3`-adic statement to finite precision) sees `d` only
through its residues modulo powers of `2` and `3`.  This theorem says those
residues carry **no information about which words are cycle words**: every
light word is realised by a `d` that is `1` to any prescribed `2`-adic and
`3`-adic precision.  So a proof that `3x + 1` has no nontrivial cycle must use
`d = 1` as an *integer* — through its size, i.e. through the archimedean
place — and not through any congruence.  The cycle-side assets that survive
this test are exactly the ones `CLOSURE.md` lists as `d = 1`-specific: the
verified range (`x ≥ 3 998 720`) and `|d| < 2`.

## Why only `2` and `3`

The realising constants of a word `w` are the multiples of its denominator
`δ(w) = G / gcd(C, G)`, and `δ(w)` divides `G = 2 ^ L − 3 ^ a`, which is prime
to `6`.  That is all the proof uses.  At other primes the statement is false:
the two `3x + 5` cycle words of length `27` have `δ = 5`
(`DeltaSpectrum.w187_delta`), so no `d ≡ 1 (mod 5)` realises them.  The
dynamics is blind to `d` exactly at the primes it is built from.

## The one new tool

Core Lean has no Bézout identity.  The modular inverse needed for
`d ≡ 1 (mod 6 ^ k)` is obtained instead from the repository's pigeonhole
principle on the powers of `δ` (`exists_pow_one_mod`): two of
`δ ^ 0, …, δ ^ M` agree modulo `M`, and Euclid's lemma cancels the common
factor.  So `d` is itself a power of `δ`.
-/

namespace Collatz
namespace LocalBlindness

open Reach AffineExact Denominator DenominatorScalar NewModels

/-! ## 1. A modular inverse from the pigeonhole -/

/-- Some positive power of `δ` is `1` modulo `M` when `δ` is prime to `M`. -/
theorem exists_pow_one_mod {δ M : Nat} (hM : 0 < M) (hδ : 0 < δ) (hcop : Nat.Coprime δ M) :
    ∃ e, 0 < e ∧ δ ^ e % M = 1 % M := by
  obtain ⟨i, j, hij, hf⟩ := Pigeonhole.exists_repeat_of_le (f := fun i => δ ^ i % M)
    (B := M - 1) (fun i => by have := Nat.mod_lt (δ ^ i) hM; omega)
  obtain ⟨e, rfl⟩ : ∃ e, j = i + (e + 1) := ⟨j - i - 1, by omega⟩
  have hdvd : M ∣ δ ^ (i + (e + 1)) - δ ^ i :=
    Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hf.symm)
  rw [Nat.pow_add, ← Nat.mul_sub_one] at hdvd
  have hcop' : Nat.Coprime M (δ ^ i) := Nat.Coprime.pow_right i hcop.symm
  have h1 : M ∣ δ ^ (e + 1) - 1 := Nat.Coprime.dvd_of_dvd_mul_left hcop' hdvd
  refine ⟨e + 1, by omega, ?_⟩
  have hpos : 1 ≤ δ ^ (e + 1) := Nat.pow_pos hδ
  have hsplit : δ ^ (e + 1) = (δ ^ (e + 1) - 1) + 1 := by omega
  rw [hsplit, Nat.add_mod, Nat.mod_eq_zero_of_dvd h1, Nat.zero_add, Nat.mod_mod]

/-- Powers of an odd number are odd. -/
theorem odd_pow {n : Nat} (h : n % 2 = 1) : ∀ e, n ^ e % 2 = 1 := by
  intro e
  induction e with
  | zero => rfl
  | succ e ih => rw [Nat.pow_succ, Nat.mul_mod, ih, h]

/-! ## 2. The gap is prime to `6`, hence so is the denominator -/

theorem two_pow_mod_three : ∀ L : Nat, 2 ^ L % 3 = 1 ∨ 2 ^ L % 3 = 2 := by
  intro L
  induction L with
  | zero => left; rfl
  | succ L ih => rw [Nat.pow_succ]; omega

/-- With at least one odd step the gap is not divisible by `3`. -/
theorem gap_not_three_dvd {r L : Nat} (ha : 0 < oddCount r L)
    (hgap : 3 ^ oddCount r L ≤ 2 ^ L) : (2 ^ L - 3 ^ oddCount r L) % 3 ≠ 0 := by
  obtain ⟨a, ha'⟩ : ∃ a, oddCount r L = a + 1 := ⟨oddCount r L - 1, by omega⟩
  rw [ha'] at hgap ⊢
  rw [Nat.pow_succ] at hgap ⊢
  have := two_pow_mod_three L
  omega

theorem coprime_two_of_odd {n : Nat} (h : n % 2 = 1) : Nat.Coprime n 2 := by
  show Nat.gcd n 2 = 1
  have hd : Nat.gcd n 2 ∣ 2 := Nat.gcd_dvd_right n 2
  have hn : Nat.gcd n 2 ∣ n := Nat.gcd_dvd_left n 2
  have hle : Nat.gcd n 2 ≤ 2 := Nat.le_of_dvd (by decide) hd
  have hpos : 0 < Nat.gcd n 2 := Nat.gcd_pos_of_pos_left 2 (by omega)
  rcases (show Nat.gcd n 2 = 1 ∨ Nat.gcd n 2 = 2 by omega) with h1 | h2
  · exact h1
  · rw [h2] at hn
    obtain ⟨c, hc⟩ := hn
    omega

theorem coprime_three_of_not_dvd {n : Nat} (h : n % 3 ≠ 0) : Nat.Coprime n 3 := by
  show Nat.gcd n 3 = 1
  have hd : Nat.gcd n 3 ∣ 3 := Nat.gcd_dvd_right n 3
  have hn : Nat.gcd n 3 ∣ n := Nat.gcd_dvd_left n 3
  have hle : Nat.gcd n 3 ≤ 3 := Nat.le_of_dvd (by decide) hd
  have hpos : 0 < Nat.gcd n 3 := Nat.gcd_pos_of_pos_left 3 (by omega)
  rcases (show Nat.gcd n 3 = 1 ∨ Nat.gcd n 3 = 2 ∨ Nat.gcd n 3 = 3 by omega) with h1 | h2 | h3
  · exact h1
  · rw [h2] at hd
    obtain ⟨c, hc⟩ := hd
    omega
  · rw [h3] at hn
    obtain ⟨c, hc⟩ := hn
    omega

/-- Odd and prime to `3` means prime to every power of `6`. -/
theorem coprime_six_pow {n : Nat} (h2 : n % 2 = 1) (h3 : n % 3 ≠ 0) (k : Nat) :
    Nat.Coprime n (6 ^ k) := by
  have h6 : Nat.Coprime n (2 * 3) :=
    Nat.Coprime.mul_right (coprime_two_of_odd h2) (coprime_three_of_not_dvd h3)
  exact Nat.Coprime.pow_right k h6

theorem four_comm (g δ p c : Nat) : g * δ * (p * c) = p * δ * (g * c) := by
  rw [Nat.mul_assoc, Nat.mul_left_comm δ p c, Nat.mul_left_comm g p,
    Nat.mul_left_comm g δ c, ← Nat.mul_assoc]

/-! ## 3. The theorem -/

/-- **Local blindness.**  Every light word with an odd step is the cycle word of
`3x + d` for some odd `d ≡ 1 (mod 6 ^ k)`, for every `k`. -/
theorem local_blindness {r L : Nat} (hL : 0 < L) (ha : 0 < oddCount r L)
    (hgap : 3 ^ oddCount r L ≤ 2 ^ L) (k : Nat) :
    ∃ d x : Nat, d % 2 = 1 ∧ d % 6 ^ k = 1 % 6 ^ k ∧ 0 < x ∧
      genOrbit d L x = x ∧ genOddCount d L x = oddCount r L ∧ genU d L x = affineC L r := by
  -- the gap, the accumulator, their gcd, the denominator
  have hGodd : (2 ^ L - 3 ^ oddCount r L) % 2 = 1 := gap_odd hL hgap
  have hG3 : (2 ^ L - 3 ^ oddCount r L) % 3 ≠ 0 := gap_not_three_dvd ha hgap
  have hGpos : 0 < 2 ^ L - 3 ^ oddCount r L := by omega
  have hCpos : 0 < affineC L r := CycleAccumulator.affineC_pos ha
  have hgpos : 0 < Nat.gcd (affineC L r) (2 ^ L - 3 ^ oddCount r L) :=
    Nat.gcd_pos_of_pos_left _ hCpos
  have hgG : Nat.gcd (affineC L r) (2 ^ L - 3 ^ oddCount r L)
      * ((2 ^ L - 3 ^ oddCount r L) / Nat.gcd (affineC L r) (2 ^ L - 3 ^ oddCount r L))
      = 2 ^ L - 3 ^ oddCount r L :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  have hgC : Nat.gcd (affineC L r) (2 ^ L - 3 ^ oddCount r L)
      * (affineC L r / Nat.gcd (affineC L r) (2 ^ L - 3 ^ oddCount r L)) = affineC L r :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  -- name them
  generalize hg : Nat.gcd (affineC L r) (2 ^ L - 3 ^ oddCount r L) = g at hgpos hgG hgC
  generalize hδ : (2 ^ L - 3 ^ oddCount r L) / g = δ at hgG
  generalize hc : affineC L r / g = c at hgC
  have hδodd : δ % 2 = 1 := odd_quotient hgG.symm hGodd
  have hδ3 : δ % 3 ≠ 0 := by
    intro h3
    have : (2 ^ L - 3 ^ oddCount r L) % 3 = 0 := by
      rw [← hgG, Nat.mul_mod, h3, Nat.mul_zero]
    exact hG3 this
  have hδpos : 0 < δ := by omega
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [h0, Nat.mul_zero] at hgC; omega
    · exact h0
  -- the inverse power
  obtain ⟨e, he, hmod⟩ := exists_pow_one_mod (Nat.pow_pos (by decide)) hδpos
    (coprime_six_pow hδodd hδ3 k)
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  have hdodd : δ ^ (e' + 1) % 2 = 1 := odd_pow hδodd _
  -- the cycle point
  refine ⟨δ ^ (e' + 1), δ ^ e' * c, hdodd, hmod, Nat.mul_pos (Nat.pow_pos hδpos) hcpos, ?_⟩
  have hscale := gen_scale_data hdodd L r
  have hx : (2 ^ L - 3 ^ genOddCount (δ ^ (e' + 1)) L (δ ^ (e' + 1) * r)) * (δ ^ e' * c)
      = δ ^ (e' + 1) * genU (δ ^ (e' + 1)) L (δ ^ (e' + 1) * r) := by
    rw [hscale.1, hscale.2, ← hgG, ← hgC, Nat.pow_succ]
    exact four_comm g δ (δ ^ e') c
  have hgap' : 3 ^ genOddCount (δ ^ (e' + 1)) L (δ ^ (e' + 1) * r) ≤ 2 ^ L := by
    rw [hscale.1]; exact hgap
  obtain ⟨hcyc, hres⟩ := gen_cycle_of_gap_dvd hdodd hgap' hx
  obtain ⟨hcount, hU⟩ := gen_congr_of_mod hdodd hres
  refine ⟨hcyc, ?_, ?_⟩
  · rw [hcount, hscale.1]
  · rw [hU, hscale.2]

/-- The `2`-adic and `3`-adic readings: the realising constant is `1` to
precision `k` at both primes at once. -/
theorem local_blindness_two_three {r L : Nat} (hL : 0 < L) (ha : 0 < oddCount r L)
    (hgap : 3 ^ oddCount r L ≤ 2 ^ L) (k : Nat) :
    ∃ d x : Nat, d % 2 ^ k = 1 % 2 ^ k ∧ d % 3 ^ k = 1 % 3 ^ k ∧ 0 < x ∧
      genOrbit d L x = x ∧ genOddCount d L x = oddCount r L := by
  obtain ⟨d, x, _, hd6, hx, hcyc, hcount, _⟩ := local_blindness hL ha hgap k
  have h6 : (6:Nat) ^ k = 2 ^ k * 3 ^ k := by rw [← Nat.mul_pow]
  refine ⟨d, x, ?_, ?_, hx, hcyc, hcount⟩
  · have h2 : 2 ^ k ∣ 6 ^ k := ⟨3 ^ k, h6⟩
    rw [← Nat.mod_mod_of_dvd d h2, hd6, Nat.mod_mod_of_dvd 1 h2]
  · have h3 : 3 ^ k ∣ 6 ^ k := ⟨2 ^ k, by rw [h6, Nat.mul_comm]⟩
    rw [← Nat.mod_mod_of_dvd d h3, hd6, Nat.mod_mod_of_dvd 1 h3]

end LocalBlindness
end Collatz
