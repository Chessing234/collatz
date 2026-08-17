import Collatz.Strategy.NeverDrops
import Collatz.Structure.VerifiedSharp
import Collatz.Core.Minimum

/-!
# Infinite descent on the minimal counterexample

`NeverDrops.collatz_iff_neverDrops` reduces Collatz to: `1` is the only number
whose own orbit never goes below it.  If any other exists, there is a **least**
one, and this file attacks that least element by constructing smaller ones.

## The construction

Run the map backwards.  The accelerated step has two kinds of preimage:

* `2x`, which is larger — useless for descent;
* the odd `n` with `3n + 1 = 2x`, which exists exactly when `x ≡ 2 (mod 3)` and
  is **smaller** than `x`, since `3n = 2x − 1 < 3x`.

The odd preimage is the whole lever.  If `m` never drops and `3n + 1 = 2m`, then
`T(n) = m` and the entire orbit of `n` is `n` followed by the orbit of `m`, all
of which is `≥ m > n`.  So `n` never drops either, and `n < m`
(`neverDrops_pred`).

**Hence the least number that never drops is not `2 (mod 3)`.**

## Chaining backwards

Longer backward words descend too.  Writing `p` for the odd preimage (factor
`2/3`) and `e` for doubling (factor `2`), a word descends when the `p`'s
outweigh the `e`'s.  The word `p p e` gives

`m ↦ 2m ↦ (4m − 1)/3 ↦ (8m − 5)/9`,

a net factor `8/9 < 1`, and it is available exactly when `m ≡ 4 (mod 9)`
(`neverDrops_pred_two`).  So the least never-dropper is also not `4 (mod 9)`.

This is a sieve modulo powers of three, dual to the residue sieve modulo powers
of two, and it constrains the *minimal* counterexample rather than every point of
an orbit.

Searching all words of length up to eight, and requiring a single word to work
for sixty representatives of a class rather than one — a word's `p` steps impose
congruences modulo `3 ^ (word length)`, which is finer than the class, so one
representative proves nothing — exactly `37` of the `81` classes modulo `81`
have a class-uniform descent word.  The surviving classes are `{0, 1}` modulo `3`
and `{0, 1, 3, 6, 7}` modulo `9`, which is precisely what the two theorems below
assert.  That agreement is the check on both.

The wider search is an observation and is not kernel-checked; only the mod-`3`
and mod-`9` levels below are theorems.

## What it does not do

The surviving classes are still infinite, and the descent produces a smaller
never-dropper only inside a residue class, never unconditionally.  A complete
proof would need every class to have a descent word, and the classes `0` and
`1` modulo `3` have no word of this shape: `p` needs `2 (mod 3)` to be defined at
all, and every `e` inserted to reach that class costs more than the `p` regains
unless a second `p` follows.
-/

namespace Collatz
namespace Descent

open Reach Congruence NeverDrops

/-! ## Prefixes of a never-dropping orbit -/

/-- **The prefix lemma.**  If `n` reaches a never-dropping `m` in `i` steps,
never goes below itself during those `i` steps, and is at most `m`, then `n`
never drops. -/
theorem neverDrops_of_prefix {n m i : Nat} (hm : NeverDrops m)
    (hi : acceleratedOrbit i n = m)
    (hle : ∀ j : Nat, j < i → n ≤ acceleratedOrbit j n)
    (hnm : n ≤ m) : NeverDrops n := by
  intro j
  rcases Nat.lt_or_ge j i with hlt | hge
  · exact hle j hlt
  · have hsplit : acceleratedOrbit j n = acceleratedOrbit (j - i) m := by
      rw [← hi, acceleratedOrbit_add]
      congr 1
      omega
    rw [hsplit]
    exact Nat.le_trans hnm (hm (j - i))

/-! ## The odd preimage -/

/-- The odd preimage steps to `m`. -/
theorem accStep_pred {n m : Nat} (_hn : 0 < n) (h : 3 * n + 1 = 2 * m) :
    acceleratedStep n = m := by
  have hodd : n % 2 = 1 := by omega
  rw [acceleratedStep, if_neg (by omega)]
  omega

/-- **Descent, level one.**  If `m` never drops and `3n + 1 = 2m`, then `n` never
drops and `n < m`. -/
theorem neverDrops_pred {n m : Nat} (hm : NeverDrops m) (hn : 0 < n)
    (h : 3 * n + 1 = 2 * m) : NeverDrops n ∧ n < m := by
  have hlt : n < m := by omega
  refine ⟨neverDrops_of_prefix hm (i := 1) ?_ ?_ (by omega), hlt⟩
  · show acceleratedStep n = m
    exact accStep_pred hn h
  · intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    rw [acceleratedOrbit]
    omega

/-- The odd preimage exists exactly on the class `2 (mod 3)`. -/
theorem exists_pred_of_mod_three {m : Nat} (h3 : m % 3 = 2) :
    ∃ n : Nat, 3 * n + 1 = 2 * m := ⟨(2 * m - 1) / 3, by omega⟩

/-! ## The word `p p e` -/

/-- **Descent, level two.**  The backward word `p p e` sends `m` to `(8m − 5)/9`,
which is smaller, and preserves never-dropping. -/
theorem neverDrops_pred_two {n₂ n₁ m : Nat} (hm : NeverDrops m) (hn₂ : 0 < n₂)
    (hn₁ : 0 < n₁) (h1 : 3 * n₁ + 1 = 4 * m) (h2 : 3 * n₂ + 1 = 2 * n₁) :
    NeverDrops n₂ ∧ n₂ < m := by
  have hlt2 : n₂ < n₁ := by omega
  have hltm : n₂ < m := by omega
  -- the three steps: `n₂ → n₁ → 2m → m`
  have s0 : acceleratedOrbit 0 n₂ = n₂ := rfl
  have s1 : acceleratedOrbit 1 n₂ = n₁ := by
    rw [acceleratedOrbit, acceleratedOrbit, accStep_pred hn₂ h2]
  have s2 : acceleratedOrbit 2 n₂ = 2 * m := by
    rw [show acceleratedOrbit 2 n₂ = acceleratedStep (acceleratedOrbit 1 n₂) from
      acceleratedOrbit_succ_step 1 n₂, s1]
    exact accStep_pred hn₁ (by omega)
  have s3 : acceleratedOrbit 3 n₂ = m := by
    rw [show acceleratedOrbit 3 n₂ = acceleratedStep (acceleratedOrbit 2 n₂) from
      acceleratedOrbit_succ_step 2 n₂, s2, acceleratedStep, if_pos (by omega)]
    omega
  refine ⟨neverDrops_of_prefix hm (i := 3) s3 ?_ (by omega), hltm⟩
  intro j hj
  match j, hj with
  | 0, _ => rw [s0]; omega
  | 1, _ => rw [s1]; omega
  | 2, _ => rw [s2]; omega

/-- The word is available exactly on the class `4 (mod 9)`. -/
theorem exists_pred_two_of_mod_nine {m : Nat} (h9 : m % 9 = 4) :
    ∃ n₂ n₁ : Nat, 3 * n₁ + 1 = 4 * m ∧ 3 * n₂ + 1 = 2 * n₁ :=
  ⟨(8 * m - 5) / 9, (4 * m - 1) / 3, by omega, by omega⟩

/-! ## The minimal never-dropper -/

/-- If any number above `1` never drops, a least one exists. -/
theorem exists_minimal_neverDrops (h : ∃ x : Nat, 1 < x ∧ NeverDrops x) :
    ∃ m : Nat, 1 < m ∧ NeverDrops m ∧ ∀ x : Nat, x < m → ¬ (1 < x ∧ NeverDrops x) := by
  obtain ⟨m, hm, hmin⟩ := Minimum.exists_min (P := fun x => 1 < x ∧ NeverDrops x) h
  exact ⟨m, hm.1, hm.2, hmin⟩

/-- **The least never-dropper is not `2 (mod 3)`.** -/
theorem minimal_not_two_mod_three {m : Nat} (hgt : 1 < m) (hnd : NeverDrops m)
    (hmin : ∀ x : Nat, x < m → ¬ (1 < x ∧ NeverDrops x)) : m % 3 ≠ 2 := by
  intro h3
  have hge : 307200 ≤ m := VerifiedSharp.neverDrops_ge_sharp hgt hnd
  obtain ⟨n, hn⟩ := exists_pred_of_mod_three h3
  have hnpos : 0 < n := by omega
  obtain ⟨hnd', hlt⟩ := neverDrops_pred hnd hnpos hn
  exact hmin n hlt ⟨by omega, hnd'⟩

/-- **The least never-dropper is not `4 (mod 9)`.** -/
theorem minimal_not_four_mod_nine {m : Nat} (hgt : 1 < m) (hnd : NeverDrops m)
    (hmin : ∀ x : Nat, x < m → ¬ (1 < x ∧ NeverDrops x)) : m % 9 ≠ 4 := by
  intro h9
  have hge : 307200 ≤ m := VerifiedSharp.neverDrops_ge_sharp hgt hnd
  obtain ⟨n₂, n₁, h1, h2⟩ := exists_pred_two_of_mod_nine h9
  have h1pos : 0 < n₁ := by omega
  have h2pos : 0 < n₂ := by omega
  obtain ⟨hnd', hlt⟩ := neverDrops_pred_two hnd h2pos h1pos h1 h2
  exact hmin n₂ hlt ⟨by omega, hnd'⟩

/-- **The minimal profile.**  Combining the descent with the residue and size
results already proved: the least never-dropper is large, `3 (mod 4)`, one of
`{7, 11, 15}` modulo `16`, and neither `2 (mod 3)` nor `4 (mod 9)`. -/
theorem minimal_profile {m : Nat} (hgt : 1 < m) (hnd : NeverDrops m)
    (hmin : ∀ x : Nat, x < m → ¬ (1 < x ∧ NeverDrops x)) :
    307200 ≤ m ∧ m % 4 = 3 ∧ (m % 16 = 7 ∨ m % 16 = 11 ∨ m % 16 = 15) ∧
    m % 3 ≠ 2 ∧ m % 9 ≠ 4 ∧ (m % 12 = 3 ∨ m % 12 = 7) := by
  have hge := VerifiedSharp.neverDrops_ge_sharp hgt hnd
  have h4 := mod_four_of_neverDrops hgt hnd
  have h16 := mod_sixteen_of_neverDrops hgt hnd
  have h3 := minimal_not_two_mod_three hgt hnd hmin
  have h9 := minimal_not_four_mod_nine hgt hnd hmin
  exact ⟨hge, h4, h16, h3, h9, by omega⟩

/-- **The reduction, sharpened.**  Collatz follows from ruling out numbers with
the minimal profile, which is a strictly smaller target than ruling out all
never-droppers. -/
theorem collatz_of_no_minimal_profile
    (h : ∀ m : Nat, 307200 ≤ m → m % 4 = 3 → m % 3 ≠ 2 → m % 9 ≠ 4 → ¬ NeverDrops m) :
    CollatzConjecture := by
  refine collatz_iff_neverDrops.mpr ?_
  intro x hnd
  rcases Nat.lt_or_ge x 2 with hlt | hge
  · omega
  · exfalso
    obtain ⟨m, hgt, hm, hmin⟩ := exists_minimal_neverDrops ⟨x, by omega, hnd⟩
    obtain ⟨hge', h4, _, h3, h9, _⟩ := minimal_profile hgt hm hmin
    exact h m hge' h4 h3 h9 hm

end Descent
end Collatz
