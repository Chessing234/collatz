import Collatz.Accelerated
import Collatz.Core.Reach

/-!
# No finite window of the parity word can obstruct anything

`Accelerated.parityVector_surjective_mod_pow_two` proves that every `0-1` word of
length `k` occurs as a parity vector.  This file draws the consequence that a wave
of symbolic-dynamics attacks kept running into, and states it once so it need not
be rediscovered.

## The statement

**`no_finite_window_obstruction`: if a property `P` of `0-1` words holds on the
length-`k` parity word of every positive integer, then it holds on *every* `0-1`
word of length `k`.**

So a test that inspects a bounded prefix of the parity word and is satisfied by all
positive integers is satisfied by everything — it separates nothing.

## Consequence: no subshift of finite type

A subshift of finite type is given by a finite set `F` of forbidden words, and a
word is admissible when it avoids all of them.  Let `L` be the longest word in `F`.
Any `f ∈ F` with `|f| ≤ L` is, by `parity_prefix_surjective`, the parity prefix of
an actual positive integer, so forbidding it excludes that integer's parity word.
Hence `F` must be empty, the subshift is the full shift, and it contains the
never-dropping words too.

**There is no subshift of finite type containing every positive integer's parity
word and excluding the never-dropping ones.**  `no_forbidden_prefix` is that
argument's load-bearing step, in the form Lean can carry: no `0-1` word can be
forbidden without excluding a positive integer.

This closes the *combinatorial* branch of symbolic dynamics outright.  It does not
touch weighted or quantitative automata, where the obstruction is different: the
affine accumulator `affineC` depends on the positions of all earlier odd steps, so
no finite-state device computes it, and a bounded-window surrogate has error that
is bounded but does not vanish.

## Positivity

The repository's surjectivity theorem produces a witness `a < 2 ^ k`, which may be
`0`.  `parityVector_mod_pow_two` upgrades it to a positive one: `a + 2 ^ k` has the
same parity vector and is positive.
-/

namespace Collatz
namespace NoWindowObstruction

open Reach

/-- **Every `0-1` word is the parity prefix of a positive integer.**  The
repository's `parityVector_surjective_mod_pow_two` with the witness made
positive. -/
theorem parity_prefix_surjective (p : List Nat) (hp : ∀ x ∈ p, x = 0 ∨ x = 1) :
    ∃ a : Nat, 0 < a ∧ parityVector a p.length = p := by
  obtain ⟨a, halt, ha⟩ := parityVector_surjective_mod_pow_two p.length p rfl hp
  refine ⟨a + 2 ^ p.length, ?_, ?_⟩
  · have := Arith.two_pow_pos p.length
    omega
  · have hmod : (a + 2 ^ p.length) % 2 ^ p.length = a := by
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt halt]
    rw [parityVector_mod_pow_two, hmod, ha]

/-- **No finite window can obstruct.**  A property of `0-1` words satisfied by the
length-`k` parity word of every positive integer is satisfied by every `0-1` word
of length `k`. -/
theorem no_finite_window_obstruction {k : Nat} (P : List Nat → Prop)
    (hall : ∀ n : Nat, 0 < n → P (parityVector n k))
    (p : List Nat) (hlen : p.length = k) (hp : ∀ x ∈ p, x = 0 ∨ x = 1) : P p := by
  obtain ⟨a, hapos, ha⟩ := parity_prefix_surjective p hp
  rw [hlen] at ha
  have := hall a hapos
  rw [ha] at this
  exact this

/-- **No word can be forbidden.**  For every `0-1` word there is a positive integer
whose parity vector begins with it, so declaring it forbidden excludes a genuine
integer.  This is the step that kills every subshift of finite type. -/
theorem no_forbidden_prefix (f : List Nat) (hf : ∀ x ∈ f, x = 0 ∨ x = 1) :
    ∃ a : Nat, 0 < a ∧ parityVector a f.length = f :=
  parity_prefix_surjective f hf

/-- The contrapositive, in the shape an obstruction proof would want to use and
therefore cannot: no predicate on bounded parity prefixes distinguishes a
particular word from the integers. -/
theorem no_separating_window {k : Nat} (P : List Nat → Prop)
    (p : List Nat) (hlen : p.length = k) (hp : ∀ x ∈ p, x = 0 ∨ x = 1)
    (hnot : ¬ P p) : ∃ n : Nat, 0 < n ∧ ¬ P (parityVector n k) := by
  obtain ⟨a, hapos, ha⟩ := parity_prefix_surjective p hp
  rw [hlen] at ha
  exact ⟨a, hapos, by rw [ha]; exact hnot⟩

end NoWindowObstruction
end Collatz
