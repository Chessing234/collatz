import Collatz.Strategy.CycleAccumulator

/-!
# Powers of two and powers of three at distance one

A hypothetical cycle of the accelerated map is governed by a single integer, the
*gap* `2 ^ L − 3 ^ a`, where `L` is the length and `a` the number of `3n+1`
steps.  `CycleAccumulator.cycle_gap_mul` turns the cycle into the equation

`(2 ^ L − 3 ^ a) · n = C_L(n)`,

so the smaller the gap, the larger the cycle point must be relative to its own
accumulator, and the gap `1` is the extreme case: the cycle point *is* its
accumulator.  This file asks which gaps of size one are even arithmetically
available, and answers completely.

## The two classifications

Both are the Catalan/Levi ben Gerson special case — the only powers of `2` and
`3` that differ by one are `(1,2)`, `(2,3)`, `(3,4)`, `(8,9)` — and both have
elementary congruence proofs that need nothing beyond periodicity of `2 ^ j` and
`3 ^ a` in small moduli.

*`2 ^ j = 3 ^ a + 1`.*  If `j ≥ 3` then the left side is `0` mod `8`, so
`3 ^ a ≡ 7 (mod 8)`.  But `3 ^ a` alternates between `1` and `3` mod `8`, for
the trivial reason that `3 · 1 ≡ 3` and `3 · 3 ≡ 1`.  So `j ≤ 2`, and the two
survivors are `2 = 1 + 1` and `4 = 3 + 1`.

*`3 ^ a = 2 ^ j + 1`.*  This is the harder direction, and the usual route
factors `3 ^ (2b) − 1 = (3 ^ b − 1)(3 ^ b + 1)` and observes that two powers of
two differing by `2` must be `2` and `4`.  Factorisation is awkward without a
divisibility library, so we take a purely congruential detour through *two*
moduli at once.  Suppose `j ≥ 4`.  Then `3 ^ a ≡ 1 (mod 16)`.  The powers of
three mod `16` cycle with period four — `1, 3, 9, 11` — so `3 ^ a ≡ 1 (mod 16)`
happens exactly when `4 ∣ a`.  And `3 ^ 4 = 81 ≡ 1 (mod 5)`, so `4 ∣ a` forces
`3 ^ a ≡ 1 (mod 5)`, hence `2 ^ j = 3 ^ a − 1 ≡ 0 (mod 5)`, which is absurd:
`2 ^ j` runs through `1, 2, 4, 3` mod `5` and never hits `0`.  Rather than prove
"`4 ∣ a`" as a statement about `a`, we carry the two residues together in one
induction (`three_pow_mod_sixteen_five`): the pair `(3 ^ a % 16, 3 ^ a % 5)`
takes only the four values `(1,1), (3,3), (9,4), (11,2)`, and the first
coordinate being `1` pins the second to `1`.  That is the whole argument, and it
is entirely finite.

## What this buys the cycle problem

`AccCycle.accCycle_bounds` already gives `3 ^ a < 2 ^ L` for every positive
accelerated cycle, so the gap is a genuine positive natural number and
`2 ^ L − 3 ^ a = 1` is the same as `2 ^ L = 3 ^ a + 1`.  The classification then
leaves only `(L, a) = (2, 1)`, and a positive cycle of length two is the trivial
one (`AccCycle.accIsCycleOf_two_length`).  So:

**a positive accelerated cycle whose gap is one is the trivial cycle** — the
point is `1` or `2`, the two elements of `1 → 2 → 1`.  This is
`gap_one_forces_trivial`, and it is sharp: `n = 2` really does occur, so `n = 1`
is *not* provable without additionally assuming `n` odd, which is
`gap_one_odd_forces_one`.

Two further gaps die cheaply from the same congruence style, and each one
excludes an infinite family of hypothetical cycles:

* the gap is always odd (`CycleAccumulator.cycle_gap_odd`), so **no even gap** —
  in particular `2 ^ L − 3 ^ a = 2` is impossible (`gap_ne_two`);
* `2 ^ L − 3 ^ a = 3` would give `3 ∣ 2 ^ L`, since a cycle has `a ≥ 1`
  (`gap_ne_three`).

Together: a positive accelerated cycle through any `n ≥ 3` has gap at least `5`
(`gap_ge_five_of_nontrivial`).  This is a statement about the *arithmetic* of a
hypothetical cycle only; it does not by itself bound `L`, because gaps of size
`5` and above are plentiful.  What it does is remove the regime in which the
cycle equation is tightest, and it removes it unconditionally rather than by
computation.

## What is not proved here

Nothing here excludes a cycle with a large gap, which is the actual difficulty;
the gap of a hypothetical cycle is expected to be enormous.  The classification
theorems are also stated for the exponents only — they say which pairs `(j, a)`
solve the equation, not anything about the shape of a would-be counterexample
orbit.  And `gap_one_forces_trivial` concludes `n = 1 ∨ n = 2` rather than
`n = 1`, because both are true.
-/

namespace Collatz
namespace GapOne

open Congruence AffineExact AccCycle CycleAccumulator

/-! ## Small powers, exactly -/

/-- The powers of three, split into the three small ones and a tail bounded
below by `27`. -/
theorem three_pow_cases (a : Nat) :
    (a = 0 ∧ 3 ^ a = 1) ∨ (a = 1 ∧ 3 ^ a = 3) ∨ (a = 2 ∧ 3 ^ a = 9) ∨
      (3 ≤ a ∧ 27 ≤ 3 ^ a) := by
  match a with
  | 0 => exact Or.inl ⟨rfl, by decide⟩
  | 1 => exact Or.inr (Or.inl ⟨rfl, by decide⟩)
  | 2 => exact Or.inr (Or.inr (Or.inl ⟨rfl, by decide⟩))
  | (k + 3) =>
    refine Or.inr (Or.inr (Or.inr ⟨by omega, ?_⟩))
    have h := Arith.three_pow_le_three_pow (show 3 ≤ k + 3 by omega)
    have h27 : (3 : Nat) ^ 3 = 27 := by decide
    omega

/-- `3 ^ a = 1` forces `a = 0`. -/
theorem three_pow_eq_one {a : Nat} (h : 3 ^ a = 1) : a = 0 := by
  rcases three_pow_cases a with ⟨h0, _⟩ | ⟨_, h1⟩ | ⟨_, h1⟩ | ⟨_, h1⟩ <;> omega

/-- `3 ^ a = 3` forces `a = 1`. -/
theorem three_pow_eq_three {a : Nat} (h : 3 ^ a = 3) : a = 1 := by
  rcases three_pow_cases a with ⟨_, h1⟩ | ⟨h0, _⟩ | ⟨_, h1⟩ | ⟨_, h1⟩ <;> omega

/-- `3 ^ a = 9` forces `a = 2`. -/
theorem three_pow_eq_nine {a : Nat} (h : 3 ^ a = 9) : a = 2 := by
  rcases three_pow_cases a with ⟨_, h1⟩ | ⟨_, h1⟩ | ⟨h0, _⟩ | ⟨_, h1⟩ <;> omega

/-! ## Periodicity in small moduli

Each of these is one induction whose step is a single multiplication, and the
whole content is that the residue cycles. -/

/-- **Powers of three mod eight** alternate between `1` and `3`. -/
theorem three_pow_mod_eight (a : Nat) : 3 ^ a % 8 = 1 ∨ 3 ^ a % 8 = 3 := by
  induction a with
  | zero => left; decide
  | succ a ih =>
    have hs : 3 ^ (a + 1) = 3 * 3 ^ a := Arith.three_pow_succ a
    omega

/-- **Powers of two mod three** are `1` and `2`; never `0`. -/
theorem two_pow_mod_three (j : Nat) : 2 ^ j % 3 = 1 ∨ 2 ^ j % 3 = 2 := by
  induction j with
  | zero => left; decide
  | succ j ih =>
    have hs : 2 ^ (j + 1) = 2 * 2 ^ j := Arith.two_pow_succ j
    omega

/-- **Powers of two mod five** run through `1, 2, 4, 3`; never `0`. -/
theorem two_pow_mod_five (j : Nat) :
    2 ^ j % 5 = 1 ∨ 2 ^ j % 5 = 2 ∨ 2 ^ j % 5 = 4 ∨ 2 ^ j % 5 = 3 := by
  induction j with
  | zero => left; decide
  | succ j ih =>
    have hs : 2 ^ (j + 1) = 2 * 2 ^ j := Arith.two_pow_succ j
    omega

/-- **The coupled residue of a power of three, mod sixteen and mod five.**  The
pair `(3 ^ a % 16, 3 ^ a % 5)` takes exactly four values, and they move in
lockstep: both cycles have period four, so the mod-`16` residue determines the
mod-`5` residue.  This is the substitute for the factorisation argument. -/
theorem three_pow_mod_sixteen_five (a : Nat) :
    (3 ^ a % 16 = 1 ∧ 3 ^ a % 5 = 1) ∨ (3 ^ a % 16 = 3 ∧ 3 ^ a % 5 = 3) ∨
      (3 ^ a % 16 = 9 ∧ 3 ^ a % 5 = 4) ∨ (3 ^ a % 16 = 11 ∧ 3 ^ a % 5 = 2) := by
  induction a with
  | zero => left; exact ⟨by decide, by decide⟩
  | succ a ih =>
    have hs : 3 ^ (a + 1) = 3 * 3 ^ a := Arith.three_pow_succ a
    rcases ih with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- **Mod sixteen, a power of three that is one is one mod five.**  The only
consequence of the previous lemma that we actually use. -/
theorem three_pow_mod_five_of_mod_sixteen {a : Nat} (h : 3 ^ a % 16 = 1) :
    3 ^ a % 5 = 1 := by
  rcases three_pow_mod_sixteen_five a with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    omega

/-! ## Powers of two are divisible by their own initial segments -/

/-- `2 ^ j` is divisible by `8` once `j ≥ 3`. -/
theorem two_pow_mod_eight {j : Nat} (h : 3 ≤ j) : 2 ^ j % 8 = 0 := by
  obtain ⟨k, hk⟩ : ∃ k, j = 3 + k := ⟨j - 3, by omega⟩
  subst hk
  rw [Arith.two_pow_add]
  have h8 : (2 : Nat) ^ 3 = 8 := by decide
  rw [h8]
  omega

/-- `2 ^ j` is divisible by `16` once `j ≥ 4`. -/
theorem two_pow_mod_sixteen {j : Nat} (h : 4 ≤ j) : 2 ^ j % 16 = 0 := by
  obtain ⟨k, hk⟩ : ∃ k, j = 4 + k := ⟨j - 4, by omega⟩
  subst hk
  rw [Arith.two_pow_add]
  have h16 : (2 : Nat) ^ 4 = 16 := by decide
  rw [h16]
  omega

/-- `3 ^ a` is divisible by `3` once `a ≥ 1`. -/
theorem three_pow_mod_three {a : Nat} (h : 1 ≤ a) : 3 ^ a % 3 = 0 := by
  obtain ⟨k, hk⟩ : ∃ k, a = 1 + k := ⟨a - 1, by omega⟩
  subst hk
  rw [Arith.three_pow_add]
  have h3 : (3 : Nat) ^ 1 = 3 := by decide
  rw [h3]
  omega

/-! ## The classification, first direction -/

/-- **`2 ^ j = 3 ^ a + 1` has exactly two solutions**, namely `2 = 1 + 1` and
`4 = 3 + 1`.  Everything above `j = 2` is killed mod `8`: the left side is
`0` there, so `3 ^ a` would have to be `7`, and it is only ever `1` or `3`. -/
theorem two_pow_eq_three_pow_add_one {j a : Nat} (h : 2 ^ j = 3 ^ a + 1) :
    (j = 1 ∧ a = 0) ∨ (j = 2 ∧ a = 1) := by
  have hj : j < 3 := by
    rcases Nat.lt_or_ge j 3 with hlt | hge
    · exact hlt
    · exfalso
      have h8 := two_pow_mod_eight hge
      have hm := three_pow_mod_eight a
      omega
  have hpos := Arith.three_pow_pos a
  match j, hj with
  | 0, _ =>
    exfalso
    have : (2 : Nat) ^ 0 = 1 := by decide
    omega
  | 1, _ =>
    have h2 : (2 : Nat) ^ 1 = 2 := by decide
    exact Or.inl ⟨rfl, three_pow_eq_one (by omega)⟩
  | 2, _ =>
    have h4 : (2 : Nat) ^ 2 = 4 := by decide
    exact Or.inr ⟨rfl, three_pow_eq_three (by omega)⟩

/-! ## The classification, second direction -/

/-- **`3 ^ a = 2 ^ j + 1` has exactly two solutions**, namely `3 = 2 + 1` and
`9 = 8 + 1`.  For `j ≥ 4` the right side is `1` mod `16`, which forces the left
side to be `1` mod `5` as well, and then `2 ^ j ≡ 0 (mod 5)` — impossible. -/
theorem three_pow_eq_two_pow_add_one {j a : Nat} (h : 3 ^ a = 2 ^ j + 1) :
    (j = 1 ∧ a = 1) ∨ (j = 3 ∧ a = 2) := by
  have hj : j < 4 := by
    rcases Nat.lt_or_ge j 4 with hlt | hge
    · exact hlt
    · exfalso
      have h16 := two_pow_mod_sixteen hge
      have hmod : 3 ^ a % 16 = 1 := by omega
      have h5 := three_pow_mod_five_of_mod_sixteen hmod
      have hpow5 := two_pow_mod_five j
      omega
  have hcases := three_pow_cases a
  match j, hj with
  | 0, _ =>
    exfalso
    have h1 : (2 : Nat) ^ 0 = 1 := by decide
    have hodd := Arith.three_pow_odd a
    omega
  | 1, _ =>
    have h2 : (2 : Nat) ^ 1 = 2 := by decide
    exact Or.inl ⟨rfl, three_pow_eq_three (by omega)⟩
  | 2, _ =>
    exfalso
    have h4 : (2 : Nat) ^ 2 = 4 := by decide
    omega
  | 3, _ =>
    have h8 : (2 : Nat) ^ 3 = 8 := by decide
    exact Or.inr ⟨rfl, three_pow_eq_nine (by omega)⟩

/-- Packaged as a statement about pairs, which is how the classical result is
usually quoted. -/
theorem two_pow_eq_three_pow_add_one_pair {j a : Nat} (h : 2 ^ j = 3 ^ a + 1) :
    (j, a) = (1, 0) ∨ (j, a) = (2, 1) := by
  rcases two_pow_eq_three_pow_add_one h with ⟨hj, ha⟩ | ⟨hj, ha⟩
  · exact Or.inl (by rw [hj, ha])
  · exact Or.inr (by rw [hj, ha])

/-- Packaged as a statement about pairs. -/
theorem three_pow_eq_two_pow_add_one_pair {j a : Nat} (h : 3 ^ a = 2 ^ j + 1) :
    (j, a) = (1, 1) ∨ (j, a) = (3, 2) := by
  rcases three_pow_eq_two_pow_add_one h with ⟨hj, ha⟩ | ⟨hj, ha⟩
  · exact Or.inl (by rw [hj, ha])
  · exact Or.inr (by rw [hj, ha])

/-! ## The gap of a hypothetical cycle -/

/-- For a positive cycle the gap is genuinely `2 ^ L − 3 ^ a` with no truncation:
`3 ^ a < 2 ^ L`, so `gap + 3 ^ a = 2 ^ L`. -/
theorem gap_add {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) :
    (2 ^ L - 3 ^ oddCount n L) + 3 ^ oddCount n L = 2 ^ L := by
  have hlt := (accCycle_bounds hn h).2.2
  omega

/-- **Gap one pins the exponents.**  A positive cycle with gap `1` has length
exactly two and exactly one odd step. -/
theorem gap_one_exponents {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hgap : 2 ^ L - 3 ^ oddCount n L = 1) : L = 2 ∧ oddCount n L = 1 := by
  have hsum := gap_add hn h
  have heq : 2 ^ L = 3 ^ oddCount n L + 1 := by omega
  have hL := two_le_length_of_accCycle hn h
  rcases two_pow_eq_three_pow_add_one heq with ⟨h1, _⟩ | ⟨h1, h2⟩
  · omega
  · exact ⟨h1, h2⟩

/-- **A cycle with gap one is the trivial cycle.**  Its point is `1` or `2`, the
two elements of `1 → 2 → 1`, and both really do occur — so this is sharp. -/
theorem gap_one_forces_trivial {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hgap : 2 ^ L - 3 ^ oddCount n L = 1) :
    L = 2 ∧ oddCount n L = 1 ∧ (n = 1 ∨ n = 2) := by
  obtain ⟨hL, ha⟩ := gap_one_exponents hn h hgap
  refine ⟨hL, ha, ?_⟩
  subst hL
  exact accIsCycleOf_two_length hn h

/-- With the cycle point odd — as the least element of a cycle always is
(`AccCycle.accCycleMin_odd`) — gap one forces `n = 1` exactly. -/
theorem gap_one_odd_forces_one {n L : Nat} (hn : 0 < n) (hodd : n % 2 = 1)
    (h : AccIsCycleOf n L) (hgap : 2 ^ L - 3 ^ oddCount n L = 1) : n = 1 := by
  obtain ⟨_, _, hn12⟩ := gap_one_forces_trivial hn h hgap
  rcases hn12 with h1 | h2
  · exact h1
  · omega

/-- **Gap one means the point is its own accumulator.**  This is the cycle
equation with the gap erased; combined with the classification it says
`n = affineC 2 n`. -/
theorem gap_one_eq_affineC {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hgap : 2 ^ L - 3 ^ oddCount n L = 1) : n = affineC 2 n := by
  have hmul := cycle_gap_mul hn h
  obtain ⟨hL, _⟩ := gap_one_exponents hn h hgap
  rw [hgap, Nat.one_mul] at hmul
  rw [hL] at hmul
  exact hmul

/-- The trivial cycle really has gap one, so the hypothesis of the theorems
above is not vacuous. -/
theorem gap_one_of_trivial : 2 ^ 2 - 3 ^ oddCount 1 2 = 1 := by decide

/-! ## Small gaps that are impossible -/

/-- **No even gap.**  The gap `2 ^ L − 3 ^ a` of a positive cycle is odd, being
even minus odd, so it is never `2` — nor any other even number. -/
theorem gap_ne_two {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) :
    2 ^ L - 3 ^ oddCount n L ≠ 2 := by
  have := cycle_gap_odd hn h
  omega

/-- The gap is odd, stated as a non-divisibility. -/
theorem gap_odd {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) :
    (2 ^ L - 3 ^ oddCount n L) % 2 = 1 := cycle_gap_odd hn h

/-- **The gap is never three.**  A cycle has at least one odd step, so `3 ^ a`
is a multiple of three; a gap of three would make `2 ^ L` one too, and powers of
two are `1` or `2` mod three. -/
theorem gap_ne_three {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) :
    2 ^ L - 3 ^ oddCount n L ≠ 3 := by
  intro hgap
  have hsum := gap_add hn h
  have ha := (accCycle_bounds hn h).1
  have h3 := three_pow_mod_three ha
  have h2 := two_pow_mod_three L
  omega

/-- **The gap of a nontrivial cycle is at least five.**  Gaps `2`, `4`, `6` are
excluded by parity, `3` by divisibility, and `1` by the Catalan classification
together with the fact that the only two-cycle is trivial. -/
theorem gap_ge_five_of_nontrivial {n L : Nat} (hn : 3 ≤ n) (h : AccIsCycleOf n L) :
    5 ≤ 2 ^ L - 3 ^ oddCount n L := by
  have hpos : 0 < n := by omega
  have hodd := cycle_gap_odd hpos h
  have h3 := gap_ne_three hpos h
  have hsum := gap_add hpos h
  have hgt : 0 < 2 ^ L - 3 ^ oddCount n L := by
    have := (accCycle_bounds hpos h).2.2
    omega
  have h1 : 2 ^ L - 3 ^ oddCount n L ≠ 1 := by
    intro hone
    obtain ⟨_, _, hn12⟩ := gap_one_forces_trivial hpos h hone
    omega
  omega

end GapOne
end Collatz
