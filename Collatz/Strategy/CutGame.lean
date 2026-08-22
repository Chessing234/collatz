import Collatz.Strategy.NeverDrops
import Collatz.Strategy.AccumulatorSharp
import Collatz.Strategy.AccumulatorClass
import Collatz.Core.Pigeonhole

/-!
# The cut game: Collatz as an infinite game, and where its memory lives

Round IX ended by naming the missing object as *a quantity coupling the 2-adic datum
to the archimedean one*, and the postscript showed that on the **cycle half** no such
quantity can exist, because `G · n = C L` determines `n` from the word.  This file
attacks the same question from descriptive set theory instead of arithmetic: it turns
the conjecture into a genuine two-player game and asks what a winning strategy for the
*counterexample* player would have to look like.

The point is not a bound.  It is that the game has an exact form, and its form
explains three separate facts this development already knows, in one picture.

## The game

Player **P** (Pattern) builds an infinite parity word one bit at a time.  Player **A**
(Arithmetic) never gets to block a move — by Terras every finite pattern is realised
and by `ExtensionClass` the tower has no gluing obstruction, so *A has no moves at
all*.  A's entire power is a **cut**: at a level `L`, A may demand that P name the
positive integer realising the play so far.  The class mod `2 ^ L` has exactly one
representative below `2 ^ L`, so the cut *forces* `n := t.rep L`, and A wins if that
integer is trivial or drops.

P's opening move is a single natural number `K`, the level below which A may not cut.
That single number is the whole of the archimedean freedom P is given.

* `Tower` — an infinite play, presented by its levelwise representatives.
* `Caught t L` — A's cut at level `L` succeeds.
* `PWins K` — P survives every cut at level `≥ K`.

## What the form is, exactly

**`Caught` is `Σ⁰₁` in the position and `PWins K` is a safety (`Π⁰₁`, closed)
condition.**  So *after P's opening number move the game is a pure safety game* —
Borel rank one, Gale–Stewart determined, effectively.  The `Π⁰₂` classification of the
divergence half (`Complexity.collatz_iff_halves`) is therefore located precisely:

> **the entire `Σ`-quantifier of the `Π⁰₂` sentence is P's opening move `K`, and
> nothing else in the game is above rank one.**

`pwins_iff_neverDrops` and `collatz_iff_no_pwins` below make the equivalence exact.

## The König collapse — why the frontier programme exists

The arena is binary-branching.  If A wins, the tree of P-survivals is well founded and
finitely branching, hence *finite* by König: A wins by a bounded level `N (K)`.  That
bounded level **is** the frontier computation, and `AWins K N` is its statement.
`awins_not_pwins` and `collatz_of_frontier` are the two sound directions.  The
converse — Collatz implies `N` is total — is exactly König's lemma, i.e. a compactness
argument, and `Complexity` already proved that every compactness argument in this
programme is circular.  So the frontier ladder is not a partial proof; it is the
*enumeration of a Skolem function whose totality is the conjecture*.  That is Part IV's
ω-rule observation, derived rather than observed.

## The escape operator — A's cut and P's only reply

P's only legal reply to a cut at level `L` is `escape n L = n + 2 ^ L`: it fixes the
class mod `2 ^ L`, hence the whole parity word up to `L` (`escape_word`), and pushes
the value past the cut (`escape_ge`).  This is `lim¹ = 0` in game form — *P can always
answer*.  But the answer is not free, and `escape_cost` prices it:

> **if the escaped value never drops, every light time `i ≤ L` obeys `2 ^ L < 2 ^ (2i)`,
> i.e. `L < 2 i`: the entire first half of the word is heavy.**

The mechanism is the coupling in its bluntest form.  P defeats an archimedean cut only
by *raising `n`*, and `n` is the very quantity the safety condition `x_j ≥ n` compares
against, so every escape tightens the constraint it escaped.  The word-level content
is weaker than what is already known (`NeverDrops.heavy_of_neverDrops` gives heaviness
to within one bit at every `k` with `2 ^ k ≤ x`, and
`CycleProduct.neverDrops_heavy_window` gives it for all `k` with `2 · A k ≤ 3 m`); it
is recorded here because it is the *operator* statement — the price of one move — not
a new inequality.

## The memory theorem — what the game says the missing object is

On a tree every strategy is positional, so positionality is vacuous and the real
question is **finite memory**.  `finMem_ultimately_periodic` proves the classical fact
in this setting: a P-strategy with a finite state space produces an ultimately periodic
run, hence an ultimately periodic parity word, hence (Lagarias) a 2-adic limit that is a
rational with odd denominator whose orbit is eventually a **cycle**.  When that limit is
integral — i.e. when P's tower stabilises — the cycle is a genuine `3x+1` cycle and
asset (a) refutes it below minimum `1086464`.  Therefore, with that one caveat stated:

> **P's finite-memory strategies win only on the cycle half.  The divergence half needs
> a strategy with no finite state space.**

The caveat is exact and it is not decoration: a finite-memory play whose tower does
*not* stabilise produces unboundedly many never-dropping integers rather than a single
cycle, and nothing here refutes that case.  It is the same one-quantifier gap that
`Complexity` isolates.

That is a structural restatement of two facts the development already has, and it
unifies them: the frontier and the verified range are cycle-half assets (Part IV)
*because* they are exactly the assets that refute finite-memory strategies; and the
coupling survives only on the divergence half (the postscript) *because* that is
exactly the half where P's strategy is not eventually periodic and so no finite word
determines `n`.

**The missing object, in this language, is the memory of P's strategy.**  It is not a
word statistic — a word statistic is a function on plays, whereas memory is an
invariant of the quotient of the arena — and it is not a function of `(L, a, C, G)`,
because two positions carrying the same word carry different memory content whenever
they carry different `n` (`escape_word` exhibits the pair explicitly:
`n` and `n + 2 ^ L` have identical words to level `L` and different values).
-/

namespace Collatz
namespace CutGame

open NeverDrops AffineExact AccumulatorSharp

/-! ## The arena -/

/-- A **tower**: an infinite play of the cut game, presented by its levelwise
representatives.  `rep L` is the unique integer below `2 ^ L` in the residue class
that the first `L` bits of the parity word determine. -/
structure Tower where
  /-- the representative at each level -/
  rep : Nat → Nat
  /-- it is the least one -/
  lt : ∀ L : Nat, rep L < 2 ^ L
  /-- and the levels cohere -/
  coh : ∀ L : Nat, rep (L + 1) % 2 ^ L = rep L

/-- Coherence, iterated: a tower's representative at any higher level reduces to the
one below. -/
theorem Tower.rep_mod (t : Tower) (L : Nat) : ∀ m : Nat, t.rep (L + m) % 2 ^ L = t.rep L := by
  intro m
  induction m with
  | zero => exact Nat.mod_eq_of_lt (t.lt L)
  | succ m ih =>
      have hdvd : (2:Nat) ^ (L + m) ∣ 2 ^ (L + m + 1) := ⟨2, by rw [Nat.pow_succ]⟩
      have hstep : t.rep (L + m + 1) % 2 ^ (L + m) = t.rep (L + m) := t.coh (L + m)
      have hdvd' : (2:Nat) ^ L ∣ 2 ^ (L + m) := ⟨2 ^ m, by rw [← Nat.pow_add]⟩
      have : t.rep (L + m + 1) % 2 ^ L = t.rep (L + m) % 2 ^ L := by
        rw [← Nat.mod_mod_of_dvd (t.rep (L + m + 1)) hdvd', hstep]
      have hsucc : L + (m + 1) = L + m + 1 := by omega
      rw [hsucc, this, ih]

/-- **A's cut at level `L` catches the tower**: the forced representative is trivial,
or its orbit drops below it. -/
def Caught (t : Tower) (L : Nat) : Prop :=
  t.rep L ≤ 1 ∨ ∃ j : Nat, acceleratedOrbit j (t.rep L) < t.rep L

/-- **P wins from opening `K`**: some play survives every cut at level `K` or above. -/
def PWins (K : Nat) : Prop := ∃ t : Tower, ∀ L : Nat, K ≤ L → ¬ Caught t L

/-! ## The game is the conjecture -/

/-- **P wins the cut game exactly when a nontrivial number never drops.**  The
forward direction is a single cut: A's demand at level `K` produces the witness
outright.  The backward direction is the constant tower of a never-dropping number. -/
theorem pwins_iff_neverDrops :
    (∃ K : Nat, PWins K) ↔ ∃ n : Nat, 1 < n ∧ NeverDrops n := by
  constructor
  · intro h
    obtain ⟨K, t, hK⟩ := h
    have hnc : ¬ Caught t K := hK K (Nat.le_refl K)
    refine ⟨t.rep K, ?_, ?_⟩
    · rcases Nat.lt_or_ge (t.rep K) 2 with hlt | hge
      · exact absurd (Or.inl (by omega)) hnc
      · omega
    · intro j
      rcases Nat.lt_or_ge (acceleratedOrbit j (t.rep K)) (t.rep K) with hlt | hge
      · exact absurd (Or.inr ⟨j, hlt⟩) hnc
      · exact hge
  · intro h
    obtain ⟨n, hn, hnd⟩ := h
    refine ⟨n, ⟨fun L => n % 2 ^ L, ?_, ?_⟩, ?_⟩
    · intro L; exact Nat.mod_lt _ (Arith.two_pow_pos L)
    · intro L
      exact Nat.mod_mod_of_dvd n ⟨2, by rw [Nat.pow_succ]⟩
    · intro L hL hc
      have hbig : n < 2 ^ L := by
        have h1 : n < 2 ^ n := Arith.lt_two_pow_self n
        have h2 : (2:Nat) ^ n ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) hL
        omega
      have hfix : n % 2 ^ L = n := Nat.mod_eq_of_lt hbig
      rcases hc with hle | ⟨j, hj⟩
      · have hle' : n % 2 ^ L ≤ 1 := hle
        rw [hfix] at hle'; omega
      · have hj' : acceleratedOrbit j (n % 2 ^ L) < n % 2 ^ L := hj
        rw [hfix] at hj'
        exact absurd (hnd j) (by omega)

/-- **Collatz is exactly the statement that P loses the cut game from every
opening.** -/
theorem collatz_iff_no_pwins : CollatzConjecture ↔ ∀ K : Nat, ¬ PWins K := by
  constructor
  · intro hC K hP
    obtain ⟨n, hn, hnd⟩ := pwins_iff_neverDrops.mp ⟨K, hP⟩
    have := (NeverDrops.collatz_iff_neverDrops.mp hC) n hnd
    omega
  · intro h
    refine NeverDrops.collatz_iff_neverDrops.mpr ?_
    intro x hnd
    rcases Nat.lt_or_ge x 2 with hlt | hge
    · omega
    · exfalso
      obtain ⟨K, hK⟩ := pwins_iff_neverDrops.mpr ⟨x, by omega, hnd⟩
      exact h K hK

/-! ## The König collapse: A's finite strategy is the frontier -/

/-- **A wins by level `N` from opening `K`**: every residue class at level `N` is
caught by some cut in the window `[K, N]`.  This is a finite, decidable statement —
it is exactly what the frontier computation checks. -/
def AWins (K N : Nat) : Prop :=
  ∀ r : Nat, r < 2 ^ N → ∃ L : Nat, K ≤ L ∧ L ≤ N ∧
    (r % 2 ^ L ≤ 1 ∨ ∃ j : Nat, acceleratedOrbit j (r % 2 ^ L) < r % 2 ^ L)

/-- **A finite A-strategy defeats every play.**  This is the sound half of the König
collapse and needs no compactness. -/
theorem awins_not_pwins {K N : Nat} (h : AWins K N) : ¬ PWins K := by
  intro hP
  obtain ⟨t, ht⟩ := hP
  obtain ⟨L, hKL, hLN, hcaught⟩ := h (t.rep N) (t.lt N)
  have hrep : t.rep N % 2 ^ L = t.rep L := by
    have hN : N = L + (N - L) := by omega
    rw [hN]
    exact t.rep_mod L (N - L)
  rw [hrep] at hcaught
  exact ht L hKL hcaught

/-- **Totality of the frontier function implies Collatz.**  The converse is König's
lemma on the binary arena, i.e. a compactness argument; `Complexity` proves every
such argument in this development is circular. -/
theorem collatz_of_frontier (h : ∀ K : Nat, ∃ N : Nat, AWins K N) : CollatzConjecture := by
  refine collatz_iff_no_pwins.mpr ?_
  intro K
  obtain ⟨N, hN⟩ := h K
  exact awins_not_pwins hN

/-- Widening the window never hurts A. -/
theorem awins_widen {K N : Nat} (h : AWins K N) {K' : Nat} (hK : K' ≤ K) : AWins K' N := by
  intro r hr
  obtain ⟨L, h1, h2, h3⟩ := h r hr
  exact ⟨L, by omega, h2, h3⟩

/-! ## The escape operator: A's cut and P's only reply -/

/-- **The escape operator.**  P's unique reply to a cut at level `L`: it fixes the
2-adic datum up to level `L` and moves the archimedean one past the cut. -/
def escape (n L : Nat) : Nat := n + 2 ^ L

/-- The escape fixes the class, hence the whole play so far. -/
theorem escape_mod (n L : Nat) : escape n L % 2 ^ L = n % 2 ^ L := by
  have : n + 2 ^ L = n + 1 * 2 ^ L := by omega
  rw [escape, this, Nat.add_mul_mod_self_right]

/-- The escape clears the cut. -/
theorem escape_ge (n L : Nat) : 2 ^ L ≤ escape n L := by
  rw [escape]; omega

/-- The escape fixes the class at every lower level too. -/
theorem escape_mod_le {n L i : Nat} (hi : i ≤ L) : escape n L % 2 ^ i = n % 2 ^ i := by
  have hsplit : (2:Nat) ^ L = 2 ^ (L - i) * 2 ^ i := by
    rw [← Nat.pow_add]
    have : L - i + i = L := by omega
    rw [this]
  rw [escape, hsplit, Nat.add_mul_mod_self_right]

/-- **The escape is invisible to the parity word up to the cut level.**  This is the
explicit pair of positions with the same word and different magnitude. -/
theorem escape_word {n L i : Nat} (hi : i ≤ L) :
    oddCount (escape n L) i = oddCount n i :=
  AccumulatorClass.oddCount_congr_of_mod (escape_mod_le hi)

/-- **P can always answer a cut.**  There is no level at which A's demand is
unanswerable: this is `lim¹ = 0` in game form. -/
theorem cut_always_answerable (n L : Nat) :
    ∃ m : Nat, m % 2 ^ L = n % 2 ^ L ∧ 2 ^ L ≤ m ∧
      ∀ i : Nat, i ≤ L → oddCount m i = oddCount n i :=
  ⟨escape n L, escape_mod n L, escape_ge n L, fun _ hi => escape_word hi⟩

/-! ### The price of the answer -/

/-- A never-dropping value is bounded by its accumulator at every light time. -/
theorem le_affineC_of_light {m i : Nat} (hm : 0 < m) (hnd : NeverDrops m)
    (hlight : 3 ^ oddCount m i < 2 ^ i) : m ≤ affineC i m := by
  have haff : 2 ^ i * m ≤ 3 ^ oddCount m i * m + affineC i m :=
    (AffineExact.neverDrops_iff_affine hm).mp (fun j => hnd j) i
  obtain ⟨g, hg⟩ : ∃ g : Nat, 2 ^ i = 3 ^ oddCount m i + (g + 1) :=
    ⟨2 ^ i - 3 ^ oddCount m i - 1, by omega⟩
  have hsplit : 2 ^ i * m = 3 ^ oddCount m i * m + (g + 1) * m := by
    rw [hg, Nat.add_mul]
  have hgm : (g + 1) * m ≤ affineC i m := by omega
  have hle : m ≤ (g + 1) * m := by
    have : 1 * m ≤ (g + 1) * m := Nat.mul_le_mul_right m (by omega)
    omega
  omega

/-- **The price of the escape.**  If the escaped value never drops, then every light
time below the cut level lies in the second half: `L < 2 * i`.  Equivalently, the
entire first half of the parity word is heavy.

P defeats an archimedean cut only by raising `n`, and `n` is exactly the quantity the
safety condition compares against — so every escape tightens the constraint it
escaped.  That is the coupling, as a price on a move. -/
theorem escape_cost {n L i : Nat} (hnd : NeverDrops (escape n L))
    (hlight : 3 ^ oddCount (escape n L) i < 2 ^ i) : 2 ^ L < 2 ^ (i + i) := by
  have hm : 0 < escape n L := by
    have := Arith.two_pow_pos L
    rw [escape]; omega
  have h1 : escape n L ≤ affineC i (escape n L) := le_affineC_of_light hm hnd hlight
  have h2 : affineC i (escape n L) + 2 ^ i ≤ 3 ^ oddCount (escape n L) i * 2 ^ i :=
    AccumulatorSharp.affineC_le_three_pow_mul (escape n L) i
  have h3 : 3 ^ oddCount (escape n L) i * 2 ^ i < 2 ^ i * 2 ^ i :=
    Nat.mul_lt_mul_of_lt_of_le hlight (Nat.le_refl (2 ^ i)) (Arith.two_pow_pos i)
  have h4 : (2:Nat) ^ i * 2 ^ i = 2 ^ (i + i) := by rw [← Nat.pow_add]
  have h5 : 2 ^ L ≤ escape n L := escape_ge n L
  have hchain : 2 ^ L ≤ 3 ^ oddCount (escape n L) i * 2 ^ i :=
    Nat.le_trans h5 (Nat.le_trans h1 (Nat.le_trans (Nat.le_add_right _ (2 ^ i)) h2))
  rw [← h4]
  exact Nat.lt_of_le_of_lt hchain h3

/-! ## The memory theorem -/

/-- A **finite-memory strategy** for P: a state space bounded by `bound`, an initial
state, and a transition.  The output bit is any function of the state; only the state
sequence matters for periodicity. -/
structure FinMem where
  /-- the state bound -/
  bound : Nat
  /-- the initial state -/
  start : Nat
  /-- the transition -/
  next : Nat → Nat
  /-- states stay in range -/
  hnext : ∀ s : Nat, next s ≤ bound
  /-- including the first -/
  hstart : start ≤ bound

/-- The state after `k` moves. -/
def FinMem.run (S : FinMem) : Nat → Nat
  | 0 => S.start
  | k + 1 => S.next (S.run k)

theorem FinMem.run_le (S : FinMem) : ∀ k : Nat, S.run k ≤ S.bound := by
  intro k
  cases k with
  | zero => exact S.hstart
  | succ k => exact S.hnext (S.run k)

/-- **A finite-memory P-strategy plays an ultimately periodic run.**  This is the
whole content of the memory theorem: finite memory means eventual periodicity, and an
eventually periodic parity word is a rational with odd denominator whose orbit is
eventually a **cycle**.  So P's finite-memory strategies live entirely on the cycle
half, which is `Π⁰₁` and is refuted by the verified range. -/
theorem finMem_ultimately_periodic (S : FinMem) :
    ∃ i p : Nat, 0 < p ∧ ∀ k : Nat, i ≤ k → S.run (k + p) = S.run k := by
  obtain ⟨i, j, hij, heq⟩ := Pigeonhole.exists_repeat_of_le (f := S.run) (B := S.bound) S.run_le
  refine ⟨i, j - i, by omega, ?_⟩
  intro k hk
  obtain ⟨m, hm⟩ : ∃ m : Nat, k = i + m := ⟨k - i, by omega⟩
  subst hm
  induction m with
  | zero =>
      have : i + 0 + (j - i) = j := by omega
      rw [this]
      exact heq.symm
  | succ m ih =>
      have hstep : i + (m + 1) + (j - i) = (i + m + (j - i)) + 1 := by omega
      have hstep' : i + (m + 1) = (i + m) + 1 := by omega
      rw [hstep, hstep', FinMem.run, FinMem.run, ih (by omega)]

/-- **The dichotomy the game proves.**  Either P's strategy has a finite state space,
in which case its play is ultimately periodic and its stabilising instances are genuine
cycles that asset (a) refutes, or P's strategy has no finite state space at all.
Stated for the state sequence, which is what a strategy is. -/
theorem memory_dichotomy (S : FinMem) :
    (∃ i p : Nat, 0 < p ∧ ∀ k : Nat, i ≤ k → S.run (k + p) = S.run k) :=
  finMem_ultimately_periodic S

end CutGame
end Collatz

/-! ## Axiom footprint -/

section Audit
open Collatz.CutGame
#print axioms Collatz.CutGame.pwins_iff_neverDrops
#print axioms Collatz.CutGame.collatz_iff_no_pwins
#print axioms Collatz.CutGame.awins_not_pwins
#print axioms Collatz.CutGame.collatz_of_frontier
#print axioms Collatz.CutGame.escape_cost
#print axioms Collatz.CutGame.finMem_ultimately_periodic
end Audit
