import Collatz.Strategy.CycleAccumulator
import Collatz.Strategy.AccumulatorClass

/-!
# The accumulator's image modulo the gap, and cycle lengths it excludes outright

Every thread of this development has collapsed onto one object, the Lagarias /
Halbeisen–Hungerbühler accumulator `φ = affineC`: the affine cycle equation is
`(2^L − 3^a)·x₀ = φ(s)`, the `3n+c` family is the same with `c` a bare multiplier
(`GenBlock`), and `hhMin` and `Bcap` are both built from it (`PosBridge`).  So the
whole cycle question is:

**for which words `s` of length `L` with `a` ones does `2^L − 3^a` divide `φ(s)`?**

By Terras realization each of the `2^L` residues mod `2^L` gives exactly one word, so
at fixed `L` this is a *finite, decidable* question — with no verified range anywhere.

## What the image looks like

Computed exhaustively over all `2^L` words for `L ≤ 21`:

| `L` | shapes `a` with a solution |
|---|---|
| even | exactly `a = L/2` |
| odd | **none at all** |

and every solution found is the `L/2`-fold repetition of `10` or `01` — the trivial
cycle `1 → 2 → 1` re-encoded at a multiple of its period, with quotient `x = 1` or
`2`.  So over this range:

**every solution of `(2^L − 3^a) ∣ φ(s)` has `L = 2a`.**

Note `L = 2a` is ratio `L/a = 2`, nowhere near the critical ratio `log₂ 3 = 1.585…`
that an actual cycle needs.  The divisibility solutions all sit far away from where
cycles could hide.

**This pattern is an exhaustive computation to `L = 21`, not a theorem.**  Proving
`(2^L − 3^a) ∣ φ(s) ⟹ L = 2a` in general *is* the cycle half of Collatz, and nothing
here proves it.

## What is proved

* **`no_cycle_of_shape`** — the reusable bridge, and the point of this file.  If no
  residue `r < 2^L` with `oddCount r L = a` has `(2^L − 3^a) ∣ affineC L r`, then no
  accelerated cycle of length `L` has `a` odd steps, **for every starting point** —
  via `CycleAccumulator.cycle_gap_dvd` and the class-invariance lemmas.  It turns a
  cycle-exclusion into a `decide`.
* `no_cycle_length_3`, `no_cycle_length_5`, `no_cycle_length_7` — instances.

## Scope, stated plainly

These lengths are **already covered** by `RealizableFrontier6809.length_ge_6809`, so
this adds no new excluded length and does not improve any bound.  What is different
is the route: `length_ge_6809` needs the verified range `ge_verified_1086464` and a
`¬ ReachesOne n` hypothesis, whereas these need **neither** — they are pure
divisibility over finitely many words, and they exclude the lengths for *every*
starting point, trivial cycle included (the trivial cycle has period `2`, so it is
not a cycle of odd length).  The bridge is what is worth keeping; the instances show
it works.

The obstruction to going further is plain: `no_cycle_of_shape` costs a `decide` over
`2^L` residues, so it is exponential and dies well before `L` reaches interesting
territory.  It is a structural tool, not a route to a bound.
-/

namespace Collatz
namespace ImageExclusion

open AccCycle AffineExact AccumulatorClass CycleAccumulator

/-- Reduce the accumulator/multiplier of an arbitrary cycle point to its
residue mod `2 ^ L`: the "word" of any cycle of length `L` is one of the
`2 ^ L` residues, and its accumulator/oddCount agree with the residue's. -/
theorem affineC_eq_mod (n L : Nat) :
    affineC L n = affineC L (n % 2 ^ L) := by
  have hdec : 2 ^ L * (n / 2 ^ L) + n % 2 ^ L = n := by
    have := Nat.div_add_mod n (2 ^ L); omega
  have h := affineC_class L (n / 2 ^ L) (n % 2 ^ L)
  rw [hdec] at h
  exact h

theorem oddCount_eq_mod (n L : Nat) :
    oddCount n L = oddCount (n % 2 ^ L) L := by
  have hdec : 2 ^ L * (n / 2 ^ L) + n % 2 ^ L = n := by
    have := Nat.div_add_mod n (2 ^ L); omega
  have h := oddCount_class L (n / 2 ^ L) (n % 2 ^ L)
  rw [hdec] at h
  exact h

/-- **The general exclusion principle.**  If no residue `r < 2 ^ L` with
exactly `a` odd steps has its accumulator divisible by the gap `2 ^ L − 3 ^ a`,
then no accelerated cycle of length `L` has exactly `a` odd steps — for
*every* starting point `n`, not just verified ones. -/
theorem no_cycle_of_shape {L a : Nat}
    (hno : ∀ r : Nat, r < 2 ^ L → oddCount r L = a → ¬ (2 ^ L - 3 ^ a) ∣ affineC L r)
    (n : Nat) (hn : 0 < n) (h : AccIsCycleOf n L) (ha : oddCount n L = a) : False := by
  have hmodlt : n % 2 ^ L < 2 ^ L := Nat.mod_lt n (Arith.two_pow_pos L)
  have hcount : oddCount (n % 2 ^ L) L = a := by
    rw [← oddCount_eq_mod n L]; exact ha
  have hdvd : (2 ^ L - 3 ^ a) ∣ affineC L n := by
    rw [← ha]; exact CycleAccumulator.cycle_gap_dvd hn h
  have hdvd' : (2 ^ L - 3 ^ a) ∣ affineC L (n % 2 ^ L) := by
    rw [← affineC_eq_mod n L]; exact hdvd
  exact hno (n % 2 ^ L) hmodlt hcount hdvd'

/-! ## Kill test: the trivial cycle at `(L,a) = (2,1)` MUST show up in the image -/

example : (2 ^ 2 - 3 ^ 1) ∣ affineC 2 1 := by decide
example : oddCount 1 2 = 1 := by decide
-- indexing sanity check passes: g = 1 divides everything, and n = 1 does carry
-- exactly one odd step in a length-2 accelerated window, as expected.

/-! ## `L = 3`: the only valid shape is `a = 1`, and it is excluded -/

theorem no_witness_L3_a1 :
    ∀ r : Nat, r < 2 ^ 3 → oddCount r 3 = 1 → ¬ (2 ^ 3 - 3 ^ 1) ∣ affineC 3 r := by
  decide

/-- **No accelerated cycle has length 3.**  Every hypothetical cycle of
length 3 has `1 ≤ a < 3` with `3 ^ a < 8`, which forces `a = 1`
(`accCycle_bounds`), and that shape's image excludes `0`. -/
theorem no_cycle_length_3 (n : Nat) (hn : 0 < n) (h : AccIsCycleOf n 3) : False := by
  have hb := accCycle_bounds hn h
  have h1 := hb.1
  have h2 := hb.2.1
  have h3 := hb.2.2
  have hcases : oddCount n 3 = 1 ∨ oddCount n 3 = 2 := by omega
  rcases hcases with ha | ha
  · exact no_cycle_of_shape no_witness_L3_a1 n hn h ha
  · rw [ha] at h3
    exact absurd h3 (by decide)

/-! ## `L = 5`: valid shapes are `a ∈ {1,2,3}`, and all three are excluded -/

theorem no_witness_L5_a1 :
    ∀ r : Nat, r < 2 ^ 5 → oddCount r 5 = 1 → ¬ (2 ^ 5 - 3 ^ 1) ∣ affineC 5 r := by
  decide

theorem no_witness_L5_a2 :
    ∀ r : Nat, r < 2 ^ 5 → oddCount r 5 = 2 → ¬ (2 ^ 5 - 3 ^ 2) ∣ affineC 5 r := by
  decide

theorem no_witness_L5_a3 :
    ∀ r : Nat, r < 2 ^ 5 → oddCount r 5 = 3 → ¬ (2 ^ 5 - 3 ^ 3) ∣ affineC 5 r := by
  decide

theorem no_cycle_length_5 (n : Nat) (hn : 0 < n) (h : AccIsCycleOf n 5) : False := by
  have hb := accCycle_bounds hn h
  have h1 := hb.1
  have h2 := hb.2.1
  have h3 := hb.2.2
  have hcases : oddCount n 5 = 1 ∨ oddCount n 5 = 2 ∨ oddCount n 5 = 3 ∨ oddCount n 5 = 4 := by
    omega
  rcases hcases with ha | ha | ha | ha
  · exact no_cycle_of_shape no_witness_L5_a1 n hn h ha
  · exact no_cycle_of_shape no_witness_L5_a2 n hn h ha
  · exact no_cycle_of_shape no_witness_L5_a3 n hn h ha
  · rw [ha] at h3
    exact absurd h3 (by decide)

/-! ## `L = 7`: valid shapes are `a ∈ {1,2,3,4}`, all excluded -/

theorem no_witness_L7_a1 :
    ∀ r : Nat, r < 2 ^ 7 → oddCount r 7 = 1 → ¬ (2 ^ 7 - 3 ^ 1) ∣ affineC 7 r := by
  decide

theorem no_witness_L7_a2 :
    ∀ r : Nat, r < 2 ^ 7 → oddCount r 7 = 2 → ¬ (2 ^ 7 - 3 ^ 2) ∣ affineC 7 r := by
  decide

theorem no_witness_L7_a3 :
    ∀ r : Nat, r < 2 ^ 7 → oddCount r 7 = 3 → ¬ (2 ^ 7 - 3 ^ 3) ∣ affineC 7 r := by
  decide

theorem no_witness_L7_a4 :
    ∀ r : Nat, r < 2 ^ 7 → oddCount r 7 = 4 → ¬ (2 ^ 7 - 3 ^ 4) ∣ affineC 7 r := by
  decide

theorem no_cycle_length_7 (n : Nat) (hn : 0 < n) (h : AccIsCycleOf n 7) : False := by
  have hb := accCycle_bounds hn h
  have h1 := hb.1
  have h2 := hb.2.1
  have h3 := hb.2.2
  have hcases : oddCount n 7 = 1 ∨ oddCount n 7 = 2 ∨ oddCount n 7 = 3 ∨
      oddCount n 7 = 4 ∨ oddCount n 7 = 5 ∨ oddCount n 7 = 6 := by omega
  rcases hcases with ha | ha | ha | ha | ha | ha
  · exact no_cycle_of_shape no_witness_L7_a1 n hn h ha
  · exact no_cycle_of_shape no_witness_L7_a2 n hn h ha
  · exact no_cycle_of_shape no_witness_L7_a3 n hn h ha
  · exact no_cycle_of_shape no_witness_L7_a4 n hn h ha
  · rw [ha] at h3; exact absurd h3 (by decide)
  · rw [ha] at h3; exact absurd h3 (by decide)

end ImageExclusion
end Collatz
