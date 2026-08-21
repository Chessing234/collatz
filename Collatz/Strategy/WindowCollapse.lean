import Collatz.Strategy.SieveGrowth
import Collatz.Strategy.CycleLanguage

/-!
# Consecutive windows of an orbit carry no information beyond a single word

Round VI proposed attacking the cycle problem with *state-dependent* quantities,
chiefly by chaining overlapping windows of the same orbit: the hope was that a
window sequence is more constrained than an arbitrary word, so that
`C mod G` information from adjacent windows would compose into an obstruction.

**It collapses, and this file is the proof.**

## The collapse

Two facts already in the development, never before put together:

* `SieveGrowth.parityVector_add` — the parity vector of a window of length `j + k`
  is the concatenation of the length-`j` window and the length-`k` window starting
  at `T^j(x)`.  So a *sequence of consecutive windows is literally a single longer
  word*.
* `parityVector_surjective_mod_pow_two` (`Accelerated.lean:909`) — every binary
  word of length `k` is realised, by some `a < 2^k`.

Together: **every sequence of consecutive windows is realised by an actual orbit**
(`window_sequence_realized`).  The language of orbit-consistent window sequences
equals the language of arbitrary binary words.  There is no compatibility condition
between adjacent windows to exploit.

Measured independently before this was proved: for every `N ≤ 14`, all `2^N` words
occur, each by *exactly one* residue class mod `2^N`.  So the "shrinking
intersection of possible states" shrinks by exactly one bit per letter — the maximum
conceivable — and is never empty; every prefix extends to every continuation.  The
growth rate of compatible window sequences equals the word entropy exactly.

## What this closes

Multi-window composition, window-pair obstructions, cross-scale compatibility,
orbit-state counting and compatible-sequence entropy are all the single-word attack
at larger `L`.  Combined with `SinkStructure.wC_inj` (the triple
`(length, ones, wC)` is a complete invariant) and `NewModels.word_is_cycle_word`,
the word-level picture is closed: the word determines the affine data, and every
word occurs.

## What survives

For a window of length `L` the word determines `x mod 2^L` exactly, so the residual
information is the *high part*: `x = r + 2^L · m` with `r` fixed by the word.  That
— magnitude — is the only orbit information a finite word does not carry, and it is
asset (a), capped for the size sandwich by `ArchimedeanCeiling.sandwich_vacuous`.

One correction recorded here.  Round IV's descent agent and Round V's sink agent
both listed Terras surjectivity as a *missing bridge* and carried it as an explicit
hypothesis (`hr : parityVector r L = w`).  It is **not** missing: it is
`parityVector_surjective_mod_pow_two`, proved in `Accelerated.lean` with axioms
`[propext, Classical.choice, Quot.sound]`.  Their theorems can be discharged.
-/

namespace Collatz
namespace WindowCollapse

open Reach SieveGrowth

/-- **Every binary word is realised as a window of an actual orbit.**  A restatement
of `parityVector_surjective_mod_pow_two` in the form the window discussion needs. -/
theorem word_is_a_window (w : List Nat) (hw : ∀ b ∈ w, b = 0 ∨ b = 1) :
    ∃ x : Nat, parityVector x w.length = w :=
  let ⟨a, _, ha⟩ := parityVector_surjective_mod_pow_two w.length w rfl hw
  ⟨a, ha⟩

/-- **A sequence of consecutive windows is a single word.**  The length-`(j+k)`
window splits as the length-`j` window followed by the length-`k` window read from
`T^j(x)` — so "two consecutive windows" is not a richer object than one word. -/
theorem consecutive_windows (x j k : Nat) :
    parityVector x (j + k)
      = parityVector x j ++ parityVector (acceleratedOrbit j x) k :=
  parityVector_add x j k

/-- **The collapse.**  Given any two words `u` and `v`, there is an actual orbit
whose first window is `u` and whose next window is `v`.  So no compatibility
constraint between consecutive windows exists to be exploited. -/
theorem window_sequence_realized (u v : List Nat)
    (hu : ∀ b ∈ u, b = 0 ∨ b = 1) (hv : ∀ b ∈ v, b = 0 ∨ b = 1) :
    ∃ x : Nat, parityVector x u.length = u ∧
      parityVector (acceleratedOrbit u.length x) v.length = v := by
  have hcat : ∀ b ∈ u ++ v, b = 0 ∨ b = 1 := by
    intro b hb
    rcases List.mem_append.mp hb with h | h
    · exact hu b h
    · exact hv b h
  obtain ⟨x, hx⟩ := word_is_a_window (u ++ v) hcat
  refine ⟨x, ?_, ?_⟩
  · have hsplit := consecutive_windows x u.length v.length
    rw [List.length_append] at hx
    rw [hsplit] at hx
    exact (List.append_inj hx (by simp)).1
  · have hsplit := consecutive_windows x u.length v.length
    rw [List.length_append] at hx
    rw [hsplit] at hx
    exact (List.append_inj hx (by simp)).2

end WindowCollapse
end Collatz
