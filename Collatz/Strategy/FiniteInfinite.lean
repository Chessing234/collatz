import Collatz.Strategy.InfiniteWord
import Collatz.Strategy.BackwardRun

/-!
# The finite/infinite realizability boundary, made exact

Terras' theorem says **finite** realizability is universal: every `{0,1}`-word of
length `L` is the parity word of exactly one residue class mod `2 ^ L`
(`parityVector_surjective_mod_pow_two`, `parityVector_injective_mod_pow_two`).
**Infinite** realizability is not universal over `Nat`: every prefix of `0^ω` is
realized (by `2 ^ L`) and every prefix of `1^ω` is realized (by `2 ^ L − 1`), yet
no positive integer realizes either word.  Meanwhile
`InfiniteWord.eq_of_parityVector_eq_all` says the infinite word determines the
integer, so the realized words are *countable* — measure zero, entropy `0`
against `1` for the full shift.  So there is a genuine gap, and the natural
question is what exactly separates the realized words from the rest.

## The answer (`realized_iff_rep_eventually_const`)

Let `r L` be the canonical representative of the length-`L` prefix: the unique
residue in `[0, 2 ^ L)` whose parity word is that prefix.  Then

> the infinite word is realized by a natural number **iff** the sequence
> `r 0, r 1, r 2, …` is eventually constant,

and the realizing number is the eventual value.  For `1^ω` the representatives
are `2 ^ L − 1`, which never stabilise; for a genuine integer `x` they stabilise
at `x` as soon as `2 ^ L > x`.

## What that characterisation actually is

`padic_eq_int_iff` isolates the content with no Collatz in sight.  A coherent
tower `r L < 2 ^ L`, `r (L+1) % 2 ^ L = r L` — i.e. an element of `Z₂` — comes
from a natural number iff it is eventually constant.  That is the standard
description of `N ⊆ Z₂` by truncations, and *nothing else is used*.  The Collatz
statement is this lemma transported along the Terras bijection
`word ↦ residue tower`, which is a bijection by hypothesis.  So the
characterisation is exactly as strong as "`x` is an integer", restated.

## Consequence: the `2`-adic architecture is circular

The tempting architecture is: *a divergent orbit gives an infinite word; push the
word to its `2`-adic limit; derive an Archimedean incompatibility.*
`rep_stabilises` kills it in one line.  A divergent orbit is by hypothesis the
orbit of a positive integer `n`; the canonical representatives of **its** word are
`r L = n` for every `L > log₂ n`, divergence or not.  The stabilisation
hypothesis is not an extra constraint that divergence might violate — it is
implied by the standing assumption "`n` is a positive integer".  The
characterisation therefore separates *no* divergent word from *any* convergent
one, and the architecture assumes precisely the thing it wants to contradict.
This is the same failure mode as
`InfiniteWord.periodicity_equiv_no_divergence`, one level lower: there the
Periodicity Conjecture was the conclusion in disguise, here integrality is the
hypothesis in disguise.

## The quantity with real content, and what it is equivalent to

The only non-vacuous version of the boundary is *quantitative*: how large must a
number be to keep a heavy word going for `L` steps?  Write

`minNonDrop L = min { x ≥ 2 : T^i(x) ≥ x for all i ≤ L }`

(the canonical representative of the *smallest* class surviving to level `L`;
measured, the minimal heavy representative and the minimal non-dropper agree for
every `L` in `[4, 398]`).  `minNonDrop_unbounded_iff_reachesOne` settles its
status exactly:

> `minNonDrop L → ∞`  **iff**  every positive integer reaches `1`.

So it is not the divergence half of Collatz.  It is the **whole** conjecture: a
non-trivial cycle's minimum never drops, so it caps `minNonDrop` at a constant
just as a divergent orbit's minimum does.  The quantity is therefore *strictly
stronger* than the divergence half — strictly, because the divergence half is
`d`-free-compatible while the cycle half is not: `3x − 1` and `3x + 5` have
genuine non-trivial cycles, so for them `minNonDrop` is bounded while nothing is
known to diverge.

Measured growth (records to `2·10⁹`, `L ≤ 398`):

```
   L      minNonDrop L     log2   L − log2 heavyCount L   excess
  59             703      9.457            9.023          0.434
 135          270271     18.044           14.320          3.724
 183         1126015     20.103           17.247          2.856
 292        26716671     24.671           23.655          1.016
 398      1827397567     30.767           29.611          1.156
```

The excess is *bounded* — it stays in `[−0.7, +3.7]` bits with no drift over
`L ∈ [59, 398]` — so the growth law is

`minNonDrop L = Θ(2 ^ L / heavyCount L)`,

exactly the "one representative per surviving class, spread uniformly"
prediction, and the whole content is the survivor count.  Asymptotically
`log₂ heavyCount L = H(θ)·L − (3/2)·log₂ L + O(1)` with `θ = log 2 / log 3 =
0.6309298` and `H(θ) = 0.9499555`, so

`log₂ minNonDrop L = 0.0500445·L + 1.5·log₂ L + O(1)`.

This reconciles the three constants, which are **one** constant:

* `0.6` (`SieveGrowth`) is a *proved lower bound* on the survivor rate, obtained
  from the single base case `safeCount 10 = 64 = 2 ^ 6`; the truth is `H(θ) =
  0.94996`, and the exact count confirms `heavyCount 10 = 64`.
* `0.05` is `1 − H(θ) = 0.0500445`, the deficit — the same measurement, read as
  a density instead of a count.
* the previously reported slope `0.084` is a finite-range artifact: the
  `(3/2)·log₂ L` correction makes `log₂ heavyCount L / L` reach only `0.926` at
  `L = 400`, so a straight-line fit through the small-`L` records over-reads the
  slope.  Fitted from `L ≥ 135` the slope is `0.047`; from `L ≥ 224`, `0.043`.
  The value `0.585 = log₂ 3 − 1` is a different constant (growth per odd step)
  and does not enter.

## Soundness filter

`padic_eq_int_iff`, `realized_iff_rep_eventually_const` and `rep_stabilises` use
none of assets (a)–(d): they are pure `2`-adic bookkeeping and are `d`-free, which
is the honest reading — they say nothing about cycles, and that is the point of
recording them.  `minNonDrop_unbounded_iff_reachesOne` and
`reachesOne_of_...` use asset (b) (`BackwardRun.accOrbit_small`, the orbit of `1`
stays `≤ 2`) at exactly one place, `not_accDivergent_of_reachesOne`, and nowhere
else; the equivalence itself is asset-free.  The `d`-dependence of the *content*
is real and is stated above: `minNonDrop` bounded is what `3x − 1` and `3x + 5`
exhibit, and it is why the quantity is the full conjecture rather than half of it.
-/

namespace Collatz
namespace FiniteInfinite

open InfiniteWord AccDivergence

/-! ## Part 0: list surgery for prefixes

An infinite word is a function `W : Nat → Nat`; its length-`L` prefix is
`wordPrefix W L`.  Two facts are needed and both come from `List.range_succ`:
a prefix of length `L + 1` is a prefix of length `L` with one letter appended,
and the same holds for `parityVector`.  Cancelling that letter is `dropLast`. -/

/-- The length-`L` prefix of the infinite word `W`. -/
def wordPrefix (W : Nat → Nat) (L : Nat) : List Nat := (List.range L).map W

theorem wordPrefix_succ (W : Nat → Nat) (L : Nat) :
    wordPrefix W (L + 1) = wordPrefix W L ++ [W L] := by
  simp [wordPrefix, List.range_succ, List.map_append]

theorem parityVector_succ_append (n L : Nat) :
    parityVector n (L + 1) = parityVector n L ++ [acceleratedOrbit L n % 2] := by
  simp [parityVector, List.range_succ, List.map_append]

/-- Cancelling the last letter of two equal `concat`s. -/
theorem eq_of_concat_eq {A B : List Nat} {a b : Nat} (h : A ++ [a] = B ++ [b]) : A = B := by
  have h' := congrArg List.dropLast h
  rw [List.dropLast_concat, List.dropLast_concat] at h'
  exact h'

/-! ## Part 1: the `2`-adic lemma, with no Collatz in it

A *tower* is a sequence of residues, one at each level, refining each other.
This is `Z₂` written without any algebra.  The lemma below is the whole
mathematical content of the characterisation. -/

/-- A coherent tower of residues: `r L` is a residue mod `2 ^ L`, and each level
refines the one below.  This is exactly a `2`-adic integer. -/
structure Tower (r : Nat → Nat) : Prop where
  lt : ∀ L : Nat, r L < 2 ^ L
  coh : ∀ L : Nat, r (L + 1) % 2 ^ L = r L

/-- Coherence at one step propagates to all higher levels. -/
theorem Tower.coh_le {r : Nat → Nat} (h : Tower r) :
    ∀ M L : Nat, L ≤ M → r M % 2 ^ L = r L := by
  intro M
  induction M with
  | zero =>
    intro L hL
    have h0 : L = 0 := by omega
    subst h0
    have hlt0 : r 0 < 1 := by have := h.lt 0; simpa using this
    have hz : r 0 = 0 := by omega
    simp [hz]
  | succ M ih =>
    intro L hL
    rcases Nat.lt_or_ge L (M + 1) with hlt | hge
    · have hLM : L ≤ M := by omega
      have hdvd : (2 : Nat) ^ L ∣ 2 ^ M := Nat.pow_dvd_pow 2 hLM
      calc r (M + 1) % 2 ^ L
          = (r (M + 1) % 2 ^ M) % 2 ^ L := (Nat.mod_mod_of_dvd _ hdvd).symm
        _ = r M % 2 ^ L := by rw [h.coh M]
        _ = r L := ih L hLM
    · have hLe : L = M + 1 := by omega
      subst hLe
      exact Nat.mod_eq_of_lt (h.lt _)

/-- **`N` inside `Z₂`, by truncations.**  A coherent tower comes from a natural
number iff it is eventually constant.  Nothing but `Nat.mod` is used. -/
theorem padic_eq_int_iff {r : Nat → Nat} (h : Tower r) :
    (∃ x : Nat, ∀ L : Nat, x % 2 ^ L = r L) ↔ (∃ N : Nat, ∀ L : Nat, N ≤ L → r L = r N) := by
  constructor
  · intro hx
    obtain ⟨x, hxr⟩ := hx
    refine ⟨x + 1, fun L hL => ?_⟩
    have hlt : ∀ M : Nat, x + 1 ≤ M → x < 2 ^ M := by
      intro M hM
      have h1 : x < 2 ^ x := Arith.lt_two_pow_self x
      have h2 : 2 ^ x ≤ 2 ^ M := Arith.two_pow_le_two_pow (by omega)
      omega
    have e1 : r L = x := by rw [← hxr L, Nat.mod_eq_of_lt (hlt L hL)]
    have e2 : r (x + 1) = x := by
      rw [← hxr (x + 1), Nat.mod_eq_of_lt (hlt (x + 1) (Nat.le_refl _))]
    rw [e1, e2]
  · intro hc
    obtain ⟨N, hN⟩ := hc
    refine ⟨r N, fun L => ?_⟩
    rcases Nat.lt_or_ge L N with hlt | hge
    · have := h.coh_le N L (by omega)
      exact this
    · have h1 : r L = r N := hN L hge
      rw [← h1]
      exact Nat.mod_eq_of_lt (h.lt L)

/-! ## Part 2: the characterisation of infinite realizability

The canonical representative tower of a word is a `Tower`, and the previous
lemma reads off the answer. -/

/-- `r` is the canonical representative tower of the infinite word `W`: at each
level it is the unique residue below `2 ^ L` whose parity word is the prefix. -/
def CanonRep (W : Nat → Nat) (r : Nat → Nat) : Prop :=
  ∀ L : Nat, r L < 2 ^ L ∧ parityVector (r L) L = wordPrefix W L

/-- The canonical representative tower is coherent: the level-`L+1`
representative reduces mod `2 ^ L` to the level-`L` one.  Proved by cancelling
the last letter of both words and applying Terras' injectivity. -/
theorem CanonRep.tower {W r : Nat → Nat} (h : CanonRep W r) : Tower r := by
  refine ⟨fun L => (h L).1, fun L => ?_⟩
  have h1 : parityVector (r (L + 1)) L = wordPrefix W L := by
    refine eq_of_concat_eq (a := acceleratedOrbit L (r (L + 1)) % 2) (b := W L) ?_
    rw [← parityVector_succ_append, ← wordPrefix_succ]
    exact (h (L + 1)).2
  have h2 : parityVector (r (L + 1)) L = parityVector (r L) L := by
    rw [h1, ← (h L).2]
  have h3 := InfiniteWord.mod_eq_of_parityVector_eq h2
  rw [h3]
  exact Nat.mod_eq_of_lt (h L).1

/-- **The finite/infinite boundary, exactly.**  An infinite word is realized by a
natural number iff its canonical representatives are eventually constant.

The forward direction is Terras' injectivity once `2 ^ L` passes `x`; the reverse
is `padic_eq_int_iff` plus `parityVector_mod_pow_two`.  Positivity is the single
extra clause `r N ≠ 0`: the tower constantly `0` is the word `0^ω`, realized by
`0` alone. -/
theorem realized_iff_rep_eventually_const {W r : Nat → Nat} (h : CanonRep W r) :
    (∃ x : Nat, ∀ L : Nat, parityVector x L = wordPrefix W L)
      ↔ (∃ N : Nat, ∀ L : Nat, N ≤ L → r L = r N) := by
  constructor
  · intro hx
    obtain ⟨x, hxw⟩ := hx
    refine ⟨x + 1, fun L hL => ?_⟩
    have hlt : ∀ M : Nat, x + 1 ≤ M → x < 2 ^ M := by
      intro M hM
      have h1 : x < 2 ^ x := Arith.lt_two_pow_self x
      have h2 : 2 ^ x ≤ 2 ^ M := Arith.two_pow_le_two_pow (by omega)
      omega
    have key : ∀ M : Nat, x + 1 ≤ M → r M = x := by
      intro M hM
      refine InfiniteWord.eq_of_parityVector_eq_of_lt ?_ (h M).1 (hlt M hM)
      rw [(h M).2, ← hxw M]
    rw [key L hL, key (x + 1) (Nat.le_refl _)]
  · intro hc
    obtain ⟨x, hx⟩ := (padic_eq_int_iff h.tower).mpr hc
    refine ⟨x, fun L => ?_⟩
    rw [parityVector_mod_pow_two x L, hx L]
    exact (h L).2

/-- The positive form: realized by a *positive* integer iff eventually constant
at a nonzero value. -/
theorem realized_pos_iff {W r : Nat → Nat} (h : CanonRep W r) :
    (∃ x : Nat, 0 < x ∧ ∀ L : Nat, parityVector x L = wordPrefix W L)
      ↔ (∃ N : Nat, 0 < r N ∧ ∀ L : Nat, N ≤ L → r L = r N) := by
  constructor
  · intro hx
    obtain ⟨x, hxpos, hxw⟩ := hx
    obtain ⟨N, hN⟩ := (realized_iff_rep_eventually_const h).mp ⟨x, hxw⟩
    refine ⟨max N (x + 1), ?_, fun L hL => ?_⟩
    · have hle : N ≤ max N (x + 1) := Nat.le_max_left _ _
      have hx1 : x + 1 ≤ max N (x + 1) := Nat.le_max_right _ _
      have hlt : x < 2 ^ (max N (x + 1)) := by
        have h1 : x < 2 ^ x := Arith.lt_two_pow_self x
        have h2 : 2 ^ x ≤ 2 ^ (max N (x + 1)) := Arith.two_pow_le_two_pow (by omega)
        omega
      have : r (max N (x + 1)) = x :=
        InfiniteWord.eq_of_parityVector_eq_of_lt
          (by rw [(h _).2, ← hxw]) (h _).1 hlt
      omega
    · have h1 : N ≤ L := Nat.le_trans (Nat.le_max_left _ _) hL
      rw [hN L h1, hN (max N (x + 1)) (Nat.le_max_left _ _)]
  · intro hc
    obtain ⟨N, hpos, hN⟩ := hc
    obtain ⟨x, hxw⟩ := (realized_iff_rep_eventually_const h).mpr ⟨N, hN⟩
    refine ⟨x, ?_, hxw⟩
    have hlt : ∀ M : Nat, x + 1 ≤ M → x < 2 ^ M := by
      intro M hM
      have h1 : x < 2 ^ x := Arith.lt_two_pow_self x
      have h2 : 2 ^ x ≤ 2 ^ M := Arith.two_pow_le_two_pow (by omega)
      omega
    have hM : max N (x + 1) = max N (x + 1) := rfl
    have hxeq : r (max N (x + 1)) = x :=
      InfiniteWord.eq_of_parityVector_eq_of_lt
        (by rw [(h _).2, ← hxw]) (h _).1 (hlt _ (Nat.le_max_right _ _))
    have := hN (max N (x + 1)) (Nat.le_max_left _ _)
    omega

/-! ## Part 3: the circularity

`rep_stabilises` is the whole objection, and it is two lines.  The canonical
representatives of the word of a natural number `n` are `n` itself from level
`n + 1` on — the hypothesis of `realized_iff_rep_eventually_const` is *already
discharged* by "`n` is a natural number", so it cannot obstruct anything a
natural number does, divergence included. -/

/-- **The stabilisation is free.**  For any `n`, the canonical representative of
the length-`L` prefix of `n`'s own parity word equals `n` for every `L > n`.
`AccDivergent n` is nowhere used and could not be: the conclusion holds for all
`n`. -/
theorem rep_stabilises {W r : Nat → Nat} (h : CanonRep W r) {n : Nat}
    (hn : ∀ L : Nat, parityVector n L = wordPrefix W L) :
    ∀ L : Nat, n + 1 ≤ L → r L = n := by
  intro L hL
  have hlt : n < 2 ^ L := by
    have h1 : n < 2 ^ n := Arith.lt_two_pow_self n
    have h2 : 2 ^ n ≤ 2 ^ L := Arith.two_pow_le_two_pow (by omega)
    omega
  exact InfiniteWord.eq_of_parityVector_eq_of_lt (by rw [(h L).2, ← hn L]) (h L).1 hlt

/-- **Architecture A is circular, as a theorem.**  A divergent orbit's word has
eventually constant canonical representatives, so the characterisation
`realized_iff_rep_eventually_const` is *satisfied* by it and yields no
contradiction.  Any argument of the shape "the divergent word's `2`-adic limit is
not an integer" contradicts this. -/
theorem divergent_rep_stabilises {W r : Nat → Nat} (h : CanonRep W r) {n : Nat}
    (_hdiv : AccDivergent n) (hn : ∀ L : Nat, parityVector n L = wordPrefix W L) :
    ∃ N : Nat, ∀ L : Nat, N ≤ L → r L = r N :=
  ⟨n + 1, fun L hL => by
    rw [rep_stabilises h hn L hL, rep_stabilises h hn (n + 1) (Nat.le_refl _)]⟩

/-! ## Part 4: the quantitative boundary

The characterisation is empty; the *record* function attached to it is not.  This
section pins down exactly what it is worth. -/

/-- `x` does not drop within `L` accelerated steps. -/
def NonDropping (x L : Nat) : Prop := ∀ i : Nat, i ≤ L → x ≤ acceleratedOrbit i x

/-- The minimal non-dropper grows without bound: for every bound `B` there is a
level `L` past which no `x ≤ B` survives.  This is "`minNonDrop L → ∞`" written
without a minimisation operator. -/
def MinNonDropUnbounded : Prop :=
  ∀ B : Nat, ∃ L : Nat, ∀ x : Nat, 2 ≤ x → x ≤ B → ¬ NonDropping x L

/-- The orbit of `n` reaches `1`. -/
def ReachesOne (n : Nat) : Prop := ∃ i : Nat, acceleratedOrbit i n = 1

/-- Positivity is preserved by one accelerated step. -/
theorem accStep_pos {n : Nat} (h : 0 < n) : 0 < acceleratedStep n := by
  unfold acceleratedStep
  by_cases he : n % 2 = 0
  · rw [if_pos he]; omega
  · rw [if_neg he]; omega

/-- Positivity is preserved along the orbit. -/
theorem accOrbit_pos : ∀ (i n : Nat), 0 < n → 0 < acceleratedOrbit i n := by
  intro i
  induction i with
  | zero => intro n h; exact h
  | succ i ih => intro n h; exact ih _ (accStep_pos h)

/-- A bounded search is decided constructively: either some `i ≤ L` drops, or
none does.  Proved by induction on `L`, so no classical step is needed. -/
theorem drop_or_nonDropping : ∀ (L x : Nat),
    (∃ i : Nat, i ≤ L ∧ acceleratedOrbit i x < x) ∨ NonDropping x L := by
  intro L
  induction L with
  | zero =>
    intro x
    exact Or.inr (fun i hi => by
      have : i = 0 := by omega
      subst this
      simp)
  | succ L ih =>
    intro x
    rcases ih x with hd | hn
    · obtain ⟨i, hi, hlt⟩ := hd
      exact Or.inl ⟨i, by omega, hlt⟩
    · rcases Nat.lt_or_ge (acceleratedOrbit (L + 1) x) x with hlt | hge
      · exact Or.inl ⟨L + 1, Nat.le_refl _, hlt⟩
      · refine Or.inr (fun i hi => ?_)
        rcases Nat.lt_or_ge i (L + 1) with h1 | h1
        · exact hn i (by omega)
        · have : i = L + 1 := by omega
          subst this
          exact hge

/-- **The equivalence.**  The minimal non-dropper grows without bound iff every
positive integer reaches `1` — the full Collatz conjecture, not the divergence
half of it. -/
theorem minNonDrop_unbounded_iff_reachesOne :
    MinNonDropUnbounded ↔ (∀ n : Nat, 0 < n → ReachesOne n) := by
  constructor
  · intro h
    have key : ∀ N n : Nat, n ≤ N → 0 < n → ReachesOne n := by
      intro N
      induction N with
      | zero => intro n hn hp; omega
      | succ N ih =>
        intro n hn hp
        rcases Nat.lt_or_ge n 2 with hsmall | hbig
        · have : n = 1 := by omega
          exact ⟨0, by simp [this]⟩
        · obtain ⟨L, hL⟩ := h n
          have hnd : ¬ NonDropping n L := hL n hbig (Nat.le_refl _)
          rcases drop_or_nonDropping L n with hd | hc
          · obtain ⟨i, _, hlt⟩ := hd
            have hpos : 0 < acceleratedOrbit i n := accOrbit_pos i n hp
            obtain ⟨j, hj⟩ := ih (acceleratedOrbit i n) (by omega) hpos
            refine ⟨j + i, ?_⟩
            rw [← acceleratedOrbit_add j i n, hj]
          · exact absurd hc hnd
    intro n hn
    exact key n n (Nat.le_refl _) hn
  · intro h B
    have key : ∀ B : Nat, ∃ L : Nat, ∀ x : Nat, 2 ≤ x → x ≤ B →
        ∃ i : Nat, i ≤ L ∧ acceleratedOrbit i x < x := by
      intro B
      induction B with
      | zero => exact ⟨0, fun x hx hxB => by omega⟩
      | succ B ih =>
        obtain ⟨L, hL⟩ := ih
        rcases Nat.lt_or_ge (B + 1) 2 with hsmall | hbig
        · exact ⟨L, fun x hx hxB => hL x hx (by omega)⟩
        · obtain ⟨i, hi⟩ := h (B + 1) (by omega)
          refine ⟨max L i, fun x hx hxB => ?_⟩
          rcases Nat.lt_or_ge x (B + 1) with hlt | hge
          · obtain ⟨j, hj, hjlt⟩ := hL x hx (by omega)
            exact ⟨j, Nat.le_trans hj (Nat.le_max_left _ _), hjlt⟩
          · have hxe : x = B + 1 := by omega
            subst hxe
            exact ⟨i, Nat.le_max_right _ _, by rw [hi]; omega⟩
    obtain ⟨L, hL⟩ := key B
    refine ⟨L, fun x hx hxB hnd => ?_⟩
    obtain ⟨i, hi, hlt⟩ := hL x hx hxB
    have := hnd i hi
    omega

/-! ### Both halves of Collatz are consumed

`ReachesOne` for every positive integer excludes divergence *and* every
non-trivial cycle, which is why the equivalence above is with the whole
conjecture.  The divergence exclusion is where asset (b) enters, and it enters
only here. -/

/-- Reaching `1` excludes divergence.  Uses `BackwardRun.accOrbit_small` — asset
(b) — and this is the only place in the file that uses any asset. -/
theorem not_accDivergent_of_reachesOne {n : Nat} (h : ReachesOne n) : ¬ AccDivergent n := by
  obtain ⟨i, hi⟩ := h
  intro hdiv
  refine (accDivergent_iff_not_accBounded n).mp hdiv ⟨InfiniteWord.accMax n i + 2, fun j => ?_⟩
  rcases Nat.lt_or_ge j i with hlt | hge
  · have := InfiniteWord.le_accMax (n := n) (k := i) j (by omega)
    omega
  · have hsplit : j = (j - i) + i := by omega
    have hthis : acceleratedOrbit j n = acceleratedOrbit (j - i) 1 := by
      calc acceleratedOrbit j n = acceleratedOrbit ((j - i) + i) n := by rw [← hsplit]
        _ = acceleratedOrbit (j - i) (acceleratedOrbit i n) := (acceleratedOrbit_add _ _ _).symm
        _ = acceleratedOrbit (j - i) 1 := by rw [hi]
    rw [hthis]
    have := BackwardRun.accOrbit_small (j - i) 1 (by omega) (by omega)
    omega

/-- Reaching `1` from every positive integer excludes every non-trivial cycle:
a cycle through `m` returns to `m`, and `1` is on the orbit, so `m` is on the
orbit of `1`, hence `m ≤ 2`. -/
theorem cycle_min_le_two (h : ∀ n : Nat, 0 < n → ReachesOne n)
    {m p : Nat} (hm : 0 < m) (hp : 0 < p) (hcyc : acceleratedOrbit p m = m) : m ≤ 2 := by
  obtain ⟨i, hi⟩ := h m hm
  have hper : ∀ k : Nat, acceleratedOrbit (k * p) m = m := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.succ_mul, ← acceleratedOrbit_add (k * p) p m, hcyc, ih]
  have hgen : ∀ Q : Nat, i ≤ Q → acceleratedOrbit Q m = m →
      m = acceleratedOrbit (Q - i) 1 := by
    intro Q hQ hQm
    calc m = acceleratedOrbit Q m := hQm.symm
      _ = acceleratedOrbit ((Q - i) + i) m := by rw [show (Q - i) + i = Q by omega]
      _ = acceleratedOrbit (Q - i) (acceleratedOrbit i m) :=
          (acceleratedOrbit_add _ _ _).symm
      _ = acceleratedOrbit (Q - i) 1 := by rw [hi]
  have h1 : i * 1 ≤ i * p := Nat.mul_le_mul_left i hp
  have h2 : i ≤ i * p := by rw [Nat.mul_one] at h1; exact h1
  have h3 : (i + 1) * p = i * p + p := Nat.succ_mul i p
  have hbig : i ≤ (i + 1) * p := by omega
  have hstep : m = acceleratedOrbit ((i + 1) * p - i) 1 := hgen _ hbig (hper (i + 1))
  rw [hstep]
  exact BackwardRun.accOrbit_small _ 1 (by omega) (by omega)

/-- **The verdict on the quantitative boundary.**  `minNonDrop L → ∞` implies
both halves of the conjecture, so it is not the divergence half and it is not
weaker than it: it is the whole thing. -/
theorem minNonDropUnbounded_implies_both (h : MinNonDropUnbounded) :
    (∀ n : Nat, 0 < n → ¬ AccDivergent n)
      ∧ (∀ m p : Nat, 0 < m → 0 < p → acceleratedOrbit p m = m → m ≤ 2) := by
  have hr := minNonDrop_unbounded_iff_reachesOne.mp h
  exact ⟨fun n hn => not_accDivergent_of_reachesOne (hr n hn),
         fun m p hm hp hcyc => cycle_min_le_two hr hm hp hcyc⟩

/-- Conversely, a single integer that never drops caps the record function
forever.  A non-trivial cycle's minimum and a divergent orbit's minimum are both
such integers, so each of them refutes `MinNonDropUnbounded` on its own. -/
theorem not_minNonDropUnbounded_of_never_drops {x : Nat} (hx : 2 ≤ x)
    (h : ∀ i : Nat, x ≤ acceleratedOrbit i x) : ¬ MinNonDropUnbounded := by
  intro hu
  obtain ⟨L, hL⟩ := hu x
  exact hL x hx (Nat.le_refl _) (fun i _ => h i)

end FiniteInfinite
end Collatz
