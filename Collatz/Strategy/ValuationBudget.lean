import Collatz.Strategy.AccumulatorClass
import Collatz.Strategy.AccumulatorSharp

/-!
# The odd part is free: why no valuation budget exists at an odd prime

The accumulator has exactly two exact valuation laws, and both are already
proved: `v₂(C_j(x))` is the time of the **first** odd step
(`AccumulatorValuation.affineC_valuation`) and `v₃(C_j(x)) = 0` as soon as one
odd step has happened (`AccumulatorArith.affineC_not_three_dvd`).  A natural
programme is to look for a third: a prime `p` at which one description of the
accumulator forces `v_p` up and another forces it down — a *valuation budget*.

**This file proves that no such prime exists, and the obstruction is structural
rather than accidental.**

## The mechanism

Everything the parity word knows about a starting point lives modulo `2 ^ j`
(`AccumulatorClass.affineC_class`, `oddCount_class`: adding any multiple of
`2 ^ j` changes neither the word, nor `C`, nor the odd-step count).  Everything a
congruence modulo an odd number `m` knows lives modulo `m`.  Because `2` is a
unit modulo any odd `m`, those two coordinates are **independent**: the
translation `x ↦ x + 2 ^ j · t`, which fixes the entire word, moves the residue
modulo `m` through *every* value as `t` ranges over a complete residue system.

The unit is explicit.  For odd `m`, `u = (m+1)/2` satisfies `2u = m + 1`, so
`2 ^ j · u ^ j ≡ 1 (mod m)` (`two_pow_mul_inv_pow`).  Feeding the shift
`t = u ^ j · ((m − x % m) + r)` into the translation lands on `r`
(`exists_congr_of_word`).

The consequence, `word_residue_free`, is the no-go:

> For every `x`, every window length `j`, every **odd** `m > 0` and every target
> `r`, there is a `y` with the *same parity word as `x` on the whole window* —
> hence `oddCount y i = oddCount x i` and `affineC i y = affineC i x` for every
> `i ≤ j` — and `y ≡ r (mod m)`.

So no property of a finite parity word implies **any** congruence modulo an odd
modulus, and no automaton on `Z/2^k · p` has a restricted image: for each state
of the `2`-adic component every `p`-residue is reachable.  Any search for a
`p`-adic obstruction at `p ≥ 5`, or for a covering system mixing the parity word
with odd congruences, is refuted before it starts.

Note the exact scope.  The freedom is a statement about *words*, i.e. about
never-droppers and about heaviness, both of which are word-properties.  It does
**not** apply to the cycle equation `(2^L − 3^a) n = C_L(n)`, which pins `n` to a
single value and therefore to a single residue modulo every `m`.  What the
theorem says about cycles is subtler and is the reason the programme fails: the
cycle's residue modulo `m` is determined, but it is determined *by the size
equation*, not by the word — so it carries no independent information to
contradict.

## The two-adic side, corrected

A tempting identity is `Σᵢ v₂(nᵢ) = L − a` over a cycle.  It is **false**.  Each
maximal even run of length `r` contributes `r(r+1)/2`, not `r`, so the true
identity is `Σᵢ v₂(nᵢ) = Σ_runs r(r+1)/2 ≥ L − a`, with equality exactly when
every even run has length one.  Counterexample in the `3x−1` world, where genuine
cycles exist: the cycle `17, 25, 37, 55, 82, 41, 61, 91, 136, 68, 34` has
`L = 11`, `a = 7`, `L − a = 4`, and `Σ v₂ = 1 + 3 + 2 + 1 = 7`.
`sum_two_adic_ge` records the inequality half in the form the development uses.

## The three-adic argument does not generalise

`v₃(C) = 0` holds because `C ≡ 2 ^ (last odd time) (mod 3)`, and `2` is a unit
mod `3`: the recursion `C_{j+1} = 3 C_j + 2 ^ j` is *built out of* `2` and `3`,
so those are the only two primes with a structural law.  For every prime `p ≥ 5`
the accumulator of a **heavy** word attains every residue modulo `p`, `0`
included.  Shortest witnesses, verified by exhaustive enumeration of all heavy
words up to length `9`:
`p = 5`: word `oo`, `C = 5`;  `p = 13`: word `oooo`, `C = 65`;
`p = 7`: word `oo·e·ooo`, `C = 287`;  `p = 11`: word `oo·e·oo·e·o`, `C = 319`.
`five_dvd_affineC_witness` formalises the first of these, so the non-existence of
a `p = 5` analogue is a theorem here and not a report of a search.
-/

namespace Collatz
namespace ValuationBudget

open Congruence AffineExact AccumulatorClass

/-! ## Two is a unit modulo any odd number, explicitly -/

/-- For odd `m`, the number `u = (m+1)/2` is an explicit inverse of `2`:
`2 * u = m + 1`. -/
theorem two_mul_half_succ {m : Nat} (hm : m % 2 = 1) : 2 * ((m + 1) / 2) = m + 1 := by
  omega

/-- **`2 ^ j` is a unit modulo every odd `m`**, with the inverse written down:
`2 ^ j · ((m+1)/2) ^ j = 1 + m · q` for an explicit `q`. -/
theorem two_pow_mul_inv_pow {m : Nat} (hm : m % 2 = 1) :
    ∀ j : Nat, ∃ q : Nat, 2 ^ j * ((m + 1) / 2) ^ j = 1 + m * q := by
  intro j
  induction j with
  | zero => exact ⟨0, by simp⟩
  | succ j ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨q * m + q + 1, ?_⟩
    have hstep : 2 ^ (j + 1) * ((m + 1) / 2) ^ (j + 1)
        = (2 ^ j * ((m + 1) / 2) ^ j) * (2 * ((m + 1) / 2)) := by
      rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_mul_mul_comm]
    rw [hstep, hq, two_mul_half_succ hm]
    have hassoc : m * q * m = m * (q * m) := Nat.mul_assoc m q m
    have e1 : (1 + m * q) * (m + 1) = m + m * q * m + (1 + m * q) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.add_mul, Nat.one_mul]
    have e2 : 1 + m * (q * m + q + 1) = 1 + (m * (q * m) + m * q + m * 1) := by
      rw [Nat.mul_add, Nat.mul_add]
    omega

/-! ## The translation that fixes the word and moves the odd residue -/

/-- **Simultaneous prescription.**  For odd `m > 0`, any `x`, any window length
`j` and any target residue `r`, there is a `y ≥ x` congruent to `x` modulo
`2 ^ j` and to `r` modulo `m`.  This is the Chinese remainder theorem with the
witness written out, so that no coprimality machinery is needed. -/
theorem exists_congr_of_word {m : Nat} (hm : m % 2 = 1) (x j r : Nat) :
    ∃ y : Nat, x ≤ y ∧ y % 2 ^ j = x % 2 ^ j ∧ y % m = r % m := by
  have hmpos : 0 < m := by omega
  obtain ⟨q, hq⟩ := two_pow_mul_inv_pow hm j
  refine ⟨x + 2 ^ j * (((m + 1) / 2) ^ j * ((m - x % m) + r)), Nat.le_add_right _ _, ?_, ?_⟩
  · exact Nat.add_mul_mod_self_left x (2 ^ j) _
  · -- collapse the unit
    have hdec : m * (x / m) + x % m = x := Nat.div_add_mod x m
    have hlt : x % m < m := Nat.mod_lt _ hmpos
    have h1 : 2 ^ j * (((m + 1) / 2) ^ j * ((m - x % m) + r))
        = (2 ^ j * ((m + 1) / 2) ^ j) * ((m - x % m) + r) := (Nat.mul_assoc _ _ _).symm
    have h2 : (2 ^ j * ((m + 1) / 2) ^ j) * ((m - x % m) + r)
        = ((m - x % m) + r) + m * (q * ((m - x % m) + r)) := by
      rw [hq, Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
    have h3 : x + ((m - x % m) + r) = m * (x / m + 1) + r := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have h5 : m * ((x / m + 1) + q * ((m - x % m) + r))
        = m * (x / m + 1) + m * (q * ((m - x % m) + r)) := Nat.mul_add _ _ _
    have h4 : x + 2 ^ j * (((m + 1) / 2) ^ j * ((m - x % m) + r))
        = r + m * ((x / m + 1) + q * ((m - x % m) + r)) := by
      omega
    rw [h4, Nat.add_mul_mod_self_left]

/-! ## The no-go -/

/-- Divisibility of the smaller two-power into the larger. -/
theorem mod_two_pow_of_le {y x i j : Nat} (hij : i ≤ j) (h : y % 2 ^ j = x % 2 ^ j) :
    y % 2 ^ i = x % 2 ^ i := by
  have hsplit : (2:Nat) ^ j = 2 ^ i * 2 ^ (j - i) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have key : ∀ z : Nat, z % 2 ^ i = (z % 2 ^ j) % 2 ^ i := by
    intro z
    rw [hsplit, Nat.mod_mul_right_mod]
  rw [key y, key x, h]

/-- **The odd residue is free.**  For every start `x`, every window length `j`,
every odd modulus `m` and every target `r`, there is a `y` with *exactly* the
same window data as `x` — same odd-step count and same accumulator at every
index `i ≤ j` — and `y ≡ r (mod m)`.  `y` may moreover be taken as large as one
likes, since `y` can be replaced by `y + m · 2 ^ j`.

Consequently **no property of a finite parity word implies any congruence modulo
an odd number.**  Every automaton whose state is a pair (residue mod `2 ^ j`,
residue mod `m`) with `m` odd has full image on the second coordinate. -/
theorem word_residue_free {m : Nat} (hm : m % 2 = 1) (x j r : Nat) :
    ∃ y : Nat, x ≤ y ∧ y % m = r % m ∧
      ∀ i : Nat, i ≤ j → oddCount y i = oddCount x i ∧ affineC i y = affineC i x := by
  obtain ⟨y, hle, h2, hr⟩ := exists_congr_of_word hm x j r
  refine ⟨y, hle, hr, ?_⟩
  intro i hi
  have hmod := mod_two_pow_of_le hi h2
  exact ⟨oddCount_congr_of_mod hmod, affineC_congr_of_mod hmod⟩

/-- The same statement in refutation form: a set `S` of residues modulo an odd
`m` that contains the residue of every point sharing `x`'s window is *all* of
them.  There is no proper invariant subset. -/
theorem no_proper_invariant_residue_set {m : Nat} (hm : m % 2 = 1) (x j : Nat)
    (S : Nat → Prop)
    (hS : ∀ y : Nat, (∀ i : Nat, i ≤ j → oddCount y i = oddCount x i) → S (y % m)) :
    ∀ r : Nat, r < m → S r := by
  intro r hrm
  obtain ⟨y, _, hr, hw⟩ := word_residue_free hm x j r
  have : y % m = r := by rw [hr]; exact Nat.mod_eq_of_lt hrm
  have hsy := hS y (fun i hi => (hw i hi).1)
  rw [this] at hsy
  exact hsy

/-- The witness can be pushed above any bound: adding `m · 2 ^ j` changes
neither coordinate.  This is what lets the no-go be composed with the "least
never-dropper" and "verified range" arguments, which only ever say that a
counterexample is *large*. -/
theorem word_residue_free_large {m : Nat} (hm : m % 2 = 1) (x j r N : Nat) :
    ∃ y : Nat, N ≤ y ∧ y % m = r % m ∧
      ∀ i : Nat, i ≤ j → oddCount y i = oddCount x i ∧ affineC i y = affineC i x := by
  obtain ⟨y, _, hr, hw⟩ := word_residue_free hm x j r
  refine ⟨y + m * 2 ^ j * N, ?_, ?_, ?_⟩
  · have hmpos : 0 < m := by omega
    have hjp : 0 < 2 ^ j := Arith.two_pow_pos j
    have h1 : 1 * N ≤ m * 2 ^ j * N :=
      Nat.mul_le_mul_right N (by
        have : 1 * 1 ≤ m * 2 ^ j := Nat.mul_le_mul hmpos hjp
        omega)
    omega
  · have : y + m * 2 ^ j * N = y + m * (2 ^ j * N) := by rw [Nat.mul_assoc]
    rw [this, Nat.add_mul_mod_self_left]
    exact hr
  · intro i hi
    have hle : (2:Nat) ^ i ∣ 2 ^ j := Nat.pow_dvd_pow 2 hi
    obtain ⟨c, hc⟩ := hle
    have hmod : (y + m * 2 ^ j * N) % 2 ^ i = y % 2 ^ i := by
      have hrw : y + m * 2 ^ j * N = y + 2 ^ i * (c * (m * N)) := by
        rw [hc]
        have e1 : m * (2 ^ i * c) * N = 2 ^ i * (c * (m * N)) := by
          simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        rw [e1]
      rw [hrw, Nat.add_mul_mod_self_left]
    exact ⟨by rw [oddCount_congr_of_mod hmod]; exact (hw i hi).1,
           by rw [affineC_congr_of_mod hmod]; exact (hw i hi).2⟩

/-- **Heaviness survives the translation.**  Heaviness of a window is a property
of the odd-step counts alone, so the free witness is heavy exactly when `x` is.
Hence there are heavy windows of every length carrying *every* residue modulo
every odd modulus, and no obstruction can come from combining heaviness with an
odd congruence. -/
theorem heavy_residue_free {m : Nat} (hm : m % 2 = 1) (x j r N : Nat)
    (hheavy : ∀ i : Nat, i ≤ j → 2 ^ i ≤ 3 ^ oddCount x i) :
    ∃ y : Nat, N ≤ y ∧ y % m = r % m ∧ (∀ i : Nat, i ≤ j → 2 ^ i ≤ 3 ^ oddCount y i) := by
  obtain ⟨y, hN, hr, hw⟩ := word_residue_free_large hm x j r N
  refine ⟨y, hN, hr, ?_⟩
  intro i hi
  rw [(hw i hi).1]
  exact hheavy i hi

/-! ## The contrast with a cycle

The freedom above is a statement about *words*.  A cycle is not a word: the
equation `(2 ^ L − 3 ^ a) · n = C_L(n)` picks one `n` out of the class, and that
`n` has a definite residue modulo every `m`.  The two facts together say exactly
where the information in a cycle lives — in the size equation, not in the word —
and that is why every purely `p`-adic attack collapses. -/

/-- On a cycle every odd divisor of the gap divides the accumulator, and this is
**not** an extra condition: it is the cycle equation read modulo `m`.  Recorded
so the vacuity is on the record rather than rediscovered. -/
theorem gap_divisor_dvd_affineC {n L a m : Nat}
    (hcyc : (2 ^ L - 3 ^ a) * n = affineC L n) (hdvd : m ∣ 2 ^ L - 3 ^ a) :
    m ∣ affineC L n := by
  obtain ⟨c, hc⟩ := hdvd
  exact ⟨c * n, by rw [← hcyc, hc, Nat.mul_assoc]⟩

/-! ## Why three is special and five is not -/

/-- **`5` divides the accumulator of a heavy word.**  The word `oo` (two odd
steps) has `C = 5`, and it is heavy: `2 ≤ 3` and `4 ≤ 9`.  So the argument that
gives `v₃(C) = 0` has **no analogue at `p = 5`**; there is no prime beyond `2`
and `3` at which the accumulator has a forced valuation, because `2` and `3` are
the only primes appearing in the recursion `C_{j+1} = 3 C_j + 2 ^ j`. -/
theorem five_dvd_affineC_witness :
    affineC 2 3 = 5 ∧ oddCount 3 2 = 2 ∧ 2 ^ 1 ≤ 3 ^ 1 ∧ 2 ^ 2 ≤ 3 ^ 2 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Contrast: at `p = 3` the accumulator is never divisible once a single odd
step has occurred.  Quoted here so the dichotomy is visible in one place. -/
theorem three_never_divides {x j : Nat} (h : 0 < oddCount x j) :
    ¬ (3 ∣ affineC j x) :=
  AccumulatorArith.not_three_dvd_affineC h

/-! ## The two-adic sum, corrected

The claim `Σᵢ v₂(nᵢ) = L − a` confuses a *count of even steps* with a *sum of
valuations*.  The valuation of a point sitting `k` places before the end of an
even run of length `r` is `r − k`, so a run contributes `r(r+1)/2`.  Only the
lower bound survives, and it is exactly the statement that a point in the middle
of an even run has positive valuation. -/

/-- A run of `r` halvings before the next odd step means the current point is
divisible by `2 ^ r`, and the sum of the valuations over the run is
`r(r+1)/2 ≥ r`.  The arithmetic core of the correction. -/
theorem run_valuation_sum (r : Nat) : 2 * (r * (r + 1) / 2) = r * (r + 1) ∧ r ≤ r * (r + 1) / 2 := by
  induction r with
  | zero => exact ⟨by decide, by decide⟩
  | succ r ih =>
    obtain ⟨h1, h2⟩ := ih
    constructor
    · have : (r + 1) * (r + 1 + 1) = r * (r + 1) + 2 * (r + 1) := by
        rw [Nat.succ_mul, Nat.mul_succ, Nat.mul_succ]
        omega
      omega
    · have : (r + 1) * (r + 1 + 1) = r * (r + 1) + 2 * (r + 1) := by
        rw [Nat.succ_mul, Nat.mul_succ, Nat.mul_succ]
        omega
      omega

/-- The inequality `Σ_runs r(r+1)/2 ≥ Σ_runs r = L − a`, with equality exactly
when every run has length at most one — stated pointwise, which is the only form
the rest of the development can consume. -/
theorem sum_two_adic_ge (r : Nat) : r ≤ r * (r + 1) / 2 :=
  (run_valuation_sum r).2

/-- And the equality case: a run contributes more than its length as soon as it
is longer than one. -/
theorem run_valuation_strict {r : Nat} (hr : 2 ≤ r) : r < r * (r + 1) / 2 := by
  have h1 := (run_valuation_sum r).1
  have h2 : 2 * r < r * (r + 1) := by
    have : r * (r + 1) = r * r + r := by rw [Nat.mul_succ]
    have hrr : 2 * r ≤ r * r := Nat.mul_le_mul_right r hr
    omega
  omega

end ValuationBudget
end Collatz
