import Collatz.Structure.Congruence
import Collatz.Structure.AccDivergence
import Collatz.Core.Arith

/-!
# The infinite parity word: what eventual periodicity does and does not give

`CycleLanguage.heavy_pad` closed the *finite* symbolic question: the factor set of
the heavy language is all of `{0,1}^*`, so no forbidden block exists at any fixed
length, and `NewModels.word_is_cycle_word` closed it again from the other side —
every word with a positive gap is a cycle word of some `3x + d`.  The one gap left
open in the symbolic direction was whether a constraint could **emerge in the
limit**: something invisible at every finite length but forced by infinite
compatibility.  This file settles that, and the answer is a closure, not a lever.

## The classical picture, stated correctly

Terras' map `Q∞ : Z₂ → Z₂`, `Q∞(x) = Σ (Tⁱ(x) mod 2)·2ⁱ`, sends a `2`-adic
integer to its parity word.  Bernstein–Lagarias, *The 3x+1 conjugacy map*,
Canad. J. Math. **48** (1996) 1154–1169, write `Φ = Q∞⁻¹`; equation (1.5) of that
paper is exactly the display above, and (1.3) is `Φ ∘ S ∘ Φ⁻¹ = T`, where `S` is
the `2`-adic shift.  `Φ` is a measure-preserving homeomorphism, unique once one
adds `Φ(0) = 0`.  So:

* **every** infinite word in `{0,1}^ℕ` is the parity word of exactly one `2`-adic
  integer (this is Terras' congruence theorem in the limit, and it is why no
  word-level constraint can exist);
* a `2`-adic integer is rational **iff its binary expansion is eventually
  periodic** — and the binary expansion is the *other* coordinate, the one `Φ`
  reads, not the parity word.

The two coordinates are exchanged by `Φ`, and `Φ` is only a homeomorphism: it
carries no rational structure across for free.  What *is* known (Bernstein–
Lagarias, §1, "it is known that `Φ(Q ∩ Z₂) ⊆ Q ∩ Z₂`") is one inclusion:

> eventually periodic parity word ⟹ the number is rational.

The converse, `Φ(Q ∩ Z₂) = Q ∩ Z₂`, is their **Periodicity Conjecture**, and it is
open.  They record precisely what it would buy: *"This would imply that the 3x+1
function T has no divergent trajectories on Z"*, and in fact that it is
**equivalent** to the assertion that `3x + k` has no divergent trajectory on `Z`
for every `k ≡ ±1 (mod 6)`.

## The trap

The tempting argument runs: a divergent orbit gives an aperiodic parity word; but
the word belongs to an integer, integers are rational, and rationals have
eventually periodic expansions; contradiction; hence no divergence.  Every step is
true except the third, which silently swaps the two coordinates.  "Rational ⟹
eventually periodic parity word" is not a theorem about `Z₂`; it is the
Periodicity Conjecture, which is *strictly stronger than the statement being
proved*.  The argument is circular, and this file records why with a theorem
rather than a remark: `wordEventuallyPeriodic_iff_eventuallyCyclic` shows that for
a natural number, eventual periodicity of the parity word is **equivalent to the
orbit being eventually cyclic** — it is a restatement of the conclusion, carrying
no independent information.  `periodicity_equiv_no_divergence` states the
circularity in the form it will be met.

The mechanism is `orbit_eq_of_parityVector_eq`: two naturals with the same parity
word of length `j` are congruent mod `2ⁱ`, so agreement of the *whole* word forces
equality of the two orbit points.  Periodicity of the word is periodicity of the
orbit; there is nothing extra in the limit.

## What survives

1. **The denominator is the whole story, and the `2`-adic picture says why.**  A
   *purely* periodic word is exactly a cycle, and the number it names is the
   rational `x_w = C(w) / G(w)` with `G = 2^L − 3^a` odd — a rational with odd
   denominator, i.e. an element of `Q ∩ Z₂`.  Its denominator in lowest terms is
   `δ(w) = G / gcd(C, G)`, the quantity `NewModels.denominator_one_iff` and
   `NewModels.word_is_cycle_word` already isolate: `δ(w) = 1` iff `x_w` is an
   integer, i.e. iff `w` is a cycle word of `3x + 1` rather than of `3x + δ(w)`.
   Bernstein–Lagarias state the conjecture in exactly this coordinate —
   *"3x + 1 Conjecture. `Z⁺ ⊆ Φ(⅓ Z)`"* — the `⅓` being the denominator of the
   trivial cycle's word `(10)^∞`, whose `2`-adic value is `Σ 4ⁱ = −1/3`.  The
   classical home of `word_is_cycle_word` is their reference [9], Lagarias,
   *The set of rational cycles for the 3x+1 problem*, Acta Arith. **56** (1990).
   So the `2`-adic route arrives at the same target as the rest of the repo:
   bound `δ(w)` away from `1`.  It supplies the coordinate, not a new lever.

2. **Blocks are residue classes.** `avoids_block_iff_avoids_class`: the word of `n`
   avoids a block of length `k` iff the orbit avoids one residue class mod `2ᵏ`
   forever.  So "which blocks a single divergent orbit must contain" is a question
   about orbits, not about the language of words — which is why
   `CycleLanguage.heavy_pad`, a statement about the language, does not decide it.

3. **One block is forced, by magnitude, on the divergence side.**
   `three_pow_lt_two_pow_of_noAdjOdd`: a window of length `j ≥ 4` in which no two
   consecutive steps are both odd has `2·a ≤ j + 1`, hence `3^a < 2^j`, so the
   window is light.  So `11` occurs in every window of length `4` or more across
   which the orbit does not drop (`2^j ≤ 3^a`); in particular every heavy word
   of length `≥ 4` (`HeavyWord`, the words a never-dropper is confined to)
   contains `11`.  Outside Lean the sharp form is: avoiding a block `b`
   caps the achievable `1`-density of the word at the maximal mean cycle of the
   `b`-avoiding subshift, and non-dropping needs density `≥ log 2 / log 3 =
   0.63093`.  A max-mean-cycle computation over every block of length `≤ 6` finds
   **exactly two** blocks whose avoidance is incompatible with that density: `1`
   (cap `0`) and `11` (cap `1/2`).  From length `3` on, avoidance is compatible —
   `111` has cap `2/3 = 0.6667` — so no longer block is forced by density, and the
   `11` case is the one Lean can carry.

Items 2 and 3 are invariant under `C ↦ d·C`, so by the repo's soundness filter they
say nothing about cycles.  They are not thereby unsound: they belong to the
*divergence* half, where `d`-freeness is legitimate — no `3x + d` map has a known
divergent trajectory, and Bernstein–Lagarias' Periodicity Conjecture is itself
`d`-uniform, equivalent to "no divergent trajectory for `3x + k`, all `k ≡ ±1
(mod 6)`".  They are weak, not wrong.  Item 1 is the only one that touches `C`
against `G` multiplicatively, and it is a change of coordinates on a known target.

## Soundness filter

Nothing here uses the verified range (a) or `accOrbit_small` (b), and every
statement is `d`-free.  For the divergence-side results that is the correct
verdict rather than a defect, for the reason given above.  For the cycle side it is
fatal, and that is the honest reading: nothing in this file constrains a cycle.
The `d`-specific content the cycle side needs sits in `δ(w)`, and this file
locates `δ(w)` in the classical picture without bounding it.
-/

namespace Collatz
namespace InfiniteWord

open Congruence AccDivergence

/-! ## Words determine residues -/

/-- Equal parity words of length `k` force equal residues mod `2 ^ k`.  This is
Terras' theorem read as an injectivity statement about the word, with no bound on
the arguments. -/
theorem mod_eq_of_parityVector_eq {a b k : Nat}
    (h : parityVector a k = parityVector b k) : a % 2 ^ k = b % 2 ^ k := by
  have hpos : 0 < 2 ^ k := Arith.two_pow_pos k
  have ha : a % 2 ^ k < 2 ^ k := Nat.mod_lt _ hpos
  have hb : b % 2 ^ k < 2 ^ k := Nat.mod_lt _ hpos
  have h' : parityVector (a % 2 ^ k) k = parityVector (b % 2 ^ k) k := by
    rw [← parityVector_mod_pow_two, ← parityVector_mod_pow_two]
    exact h
  exact parityVector_injective_mod_pow_two k _ _ ha hb h'

/-- Two naturals below `2 ^ k` with the same parity word of length `k` are equal. -/
theorem eq_of_parityVector_eq_of_lt {a b k : Nat}
    (h : parityVector a k = parityVector b k) (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    a = b :=
  parityVector_injective_mod_pow_two k a b ha hb h

/-- **Agreement of the whole word is equality.**  If every finite prefix of the
parity words of `a` and `b` agrees, then `a = b`.  A single well-chosen length
already suffices, which is the content of the proof: take `k = a + b`. -/
theorem eq_of_parityVector_eq_all {a b : Nat}
    (h : ∀ k : Nat, parityVector a k = parityVector b k) : a = b := by
  have ha : a < 2 ^ (a + b) := by
    have h1 : a < 2 ^ a := Arith.lt_two_pow_self a
    have h2 : 2 ^ a ≤ 2 ^ (a + b) := Arith.two_pow_le_two_pow (Nat.le_add_right a b)
    omega
  have hb : b < 2 ^ (a + b) := by
    have h1 : b < 2 ^ b := Arith.lt_two_pow_self b
    have h2 : 2 ^ b ≤ 2 ^ (a + b) := Arith.two_pow_le_two_pow (Nat.le_add_left b a)
    omega
  exact eq_of_parityVector_eq_of_lt (h (a + b)) ha hb

/-! ## Eventual periodicity of the word -/

/-- The parity word of `n` is eventually periodic with preperiod `m` and period
`p`: the word read from time `m` equals the word read from time `m + p`. -/
def WordEventuallyPeriodic (n : Nat) : Prop :=
  ∃ m p : Nat, 0 < p ∧
    ∀ k : Nat, parityVector (acceleratedOrbit m n) k
      = parityVector (acceleratedOrbit (m + p) n) k

/-- The orbit of `n` is eventually cyclic. -/
def EventuallyCyclic (n : Nat) : Prop :=
  ∃ m p : Nat, 0 < p ∧ acceleratedOrbit (m + p) n = acceleratedOrbit m n

/-- **The whole content of the limit.**  Eventual periodicity of the infinite
parity word is *equivalent to* the orbit being eventually cyclic.  It is not a
consequence of the starting value being rational; it is a restatement of the
conclusion one would want to draw from it. -/
theorem wordEventuallyPeriodic_iff_eventuallyCyclic (n : Nat) :
    WordEventuallyPeriodic n ↔ EventuallyCyclic n := by
  constructor
  · intro h
    obtain ⟨m, p, hp, hword⟩ := h
    exact ⟨m, p, hp, (eq_of_parityVector_eq_all hword).symm⟩
  · intro h
    obtain ⟨m, p, hp, hcyc⟩ := h
    exact ⟨m, p, hp, fun k => by rw [hcyc]⟩

/-- The finite certificate behind the equivalence: agreement of the word at one
length `k` large enough to separate the two orbit points already forces the
cycle.  No infinite hypothesis is needed. -/
theorem orbit_eq_of_parityVector_eq {n m p k : Nat}
    (h : parityVector (acceleratedOrbit m n) k
        = parityVector (acceleratedOrbit (m + p) n) k)
    (h1 : acceleratedOrbit m n < 2 ^ k) (h2 : acceleratedOrbit (m + p) n < 2 ^ k) :
    acceleratedOrbit (m + p) n = acceleratedOrbit m n :=
  (eq_of_parityVector_eq_of_lt h h1 h2).symm

/-! ## An eventually cyclic orbit is bounded -/

/-- The largest orbit value in the first `k` steps. -/
def accMax (n : Nat) : Nat → Nat
  | 0 => n
  | k + 1 => max (accMax n k) (acceleratedOrbit (k + 1) n)

theorem le_accMax {n k : Nat} (i : Nat) (hi : i ≤ k) : acceleratedOrbit i n ≤ accMax n k := by
  induction k with
  | zero =>
    have : i = 0 := by omega
    rw [this]
    exact Nat.le_refl _
  | succ k ih =>
    by_cases h : i ≤ k
    · have := ih h
      have : accMax n k ≤ accMax n (k + 1) := Nat.le_max_left _ _
      omega
    · have hik : i = k + 1 := by omega
      rw [hik, accMax]
      exact Nat.le_max_right _ _

/-- Every orbit point of an eventually cyclic orbit equals one of the first
`m + p` orbit points. -/
theorem exists_le_of_cycle {n m p : Nat} (hp : 0 < p)
    (hcyc : acceleratedOrbit (m + p) n = acceleratedOrbit m n) :
    ∀ i : Nat, ∃ i' : Nat, i' ≤ m + p ∧ acceleratedOrbit i n = acceleratedOrbit i' n := by
  have key : ∀ q i : Nat, i ≤ m + p + q →
      ∃ i' : Nat, i' ≤ m + p ∧ acceleratedOrbit i n = acceleratedOrbit i' n := by
    intro q
    induction q with
    | zero => intro i hi; exact ⟨i, by omega, rfl⟩
    | succ q ih =>
      intro i hi
      by_cases h : i ≤ m + p + q
      · exact ih i h
      · have hbig : m + p < i := by omega
        have hsplit : i = (i - p - m) + (m + p) := by omega
        have hstep : acceleratedOrbit i n = acceleratedOrbit (i - p) n := by
          calc acceleratedOrbit i n
              = acceleratedOrbit ((i - p - m) + (m + p)) n := by rw [← hsplit]
            _ = acceleratedOrbit (i - p - m) (acceleratedOrbit (m + p) n) :=
                (acceleratedOrbit_add _ _ _).symm
            _ = acceleratedOrbit (i - p - m) (acceleratedOrbit m n) := by rw [hcyc]
            _ = acceleratedOrbit ((i - p - m) + m) n := acceleratedOrbit_add _ _ _
            _ = acceleratedOrbit (i - p) n := by
                have : (i - p - m) + m = i - p := by omega
                rw [this]
        obtain ⟨i', hi', heq⟩ := ih (i - p) (by omega)
        exact ⟨i', hi', by rw [hstep, heq]⟩
  intro i
  exact key i i (by omega)

/-- An eventually cyclic orbit is bounded. -/
theorem accBounded_of_eventuallyCyclic {n : Nat} (h : EventuallyCyclic n) : AccBounded n := by
  obtain ⟨m, p, hp, hcyc⟩ := h
  refine ⟨accMax n (m + p), fun i => ?_⟩
  obtain ⟨i', hi', heq⟩ := exists_le_of_cycle hp hcyc i
  rw [heq]
  exact le_accMax i' hi'

/-- A bounded orbit is eventually cyclic. -/
theorem eventuallyCyclic_of_accBounded {n : Nat} (h : AccBounded n) : EventuallyCyclic n := by
  obtain ⟨B, hB⟩ := h
  obtain ⟨i, j, hij, hfij⟩ :=
    Pigeonhole.exists_repeat_of_le (f := fun k => acceleratedOrbit k n) (B := B) hB
  refine ⟨i, j - i, by omega, ?_⟩
  have : i + (j - i) = j := by omega
  rw [this]
  exact hfij.symm

/-! ## The circularity, as a theorem -/

/-- **The Periodicity Conjecture is the conclusion, not a step towards it.**
"Every positive integer has an eventually periodic parity word" is *equivalent*
to "no positive integer has a divergent orbit".  Deducing the first from
rationality of the integer — the classical trap — therefore assumes the second.

This is the Lean shadow of Bernstein–Lagarias' remark that
`Φ(Q ∩ Z₂) = Q ∩ Z₂` "would imply that the 3x+1 function T has no divergent
trajectories on Z", specialised to `Z` where the implication is an equivalence. -/
theorem periodicity_equiv_no_divergence :
    (∀ n : Nat, 0 < n → WordEventuallyPeriodic n)
      ↔ (∀ n : Nat, 0 < n → ¬ AccDivergent n) := by
  constructor
  · intro h n hn hdiv
    have hcyc : EventuallyCyclic n :=
      (wordEventuallyPeriodic_iff_eventuallyCyclic n).mp (h n hn)
    exact (accDivergent_iff_not_accBounded n).mp hdiv (accBounded_of_eventuallyCyclic hcyc)
  · intro h n hn
    refine (wordEventuallyPeriodic_iff_eventuallyCyclic n).mpr ?_
    exact eventuallyCyclic_of_accBounded (accBounded_of_not_accDivergent (h n hn))

/-- A divergent orbit has an aperiodic parity word — and that is all it has.  No
contradiction follows, because aperiodic words are exactly as plentiful as `2`-adic
integers. -/
theorem not_wordEventuallyPeriodic_of_accDivergent {n : Nat} (h : AccDivergent n) :
    ¬ WordEventuallyPeriodic n := by
  intro hw
  exact (accDivergent_iff_not_accBounded n).mp h
    (accBounded_of_eventuallyCyclic ((wordEventuallyPeriodic_iff_eventuallyCyclic n).mp hw))

/-! ## Blocks are residue classes -/

/-- A block of length `k` occurs in the word of `n` at time `i` exactly when the
orbit point at time `i` lies in the corresponding residue class mod `2 ^ k`. -/
theorem parityVector_eq_iff_mod_eq {n i k r : Nat} (hr : r < 2 ^ k) :
    parityVector (acceleratedOrbit i n) k = parityVector r k
      ↔ acceleratedOrbit i n % 2 ^ k = r := by
  constructor
  · intro h
    have := mod_eq_of_parityVector_eq h
    rwa [Nat.mod_eq_of_lt hr] at this
  · intro h
    rw [parityVector_mod_pow_two (acceleratedOrbit i n) k, h]

/-- **Block avoidance is class avoidance.**  The word of `n` avoids the block of
`r` iff the orbit never meets the class of `r` mod `2 ^ k`.  So a question about
which blocks a *single* divergent orbit must contain is a question about orbits,
not about the language of words — which is why `CycleLanguage.heavy_pad`, a
statement about the language, does not decide it. -/
theorem avoids_block_iff_avoids_class (n k r : Nat) (hr : r < 2 ^ k) :
    (∀ i : Nat, parityVector (acceleratedOrbit i n) k ≠ parityVector r k)
      ↔ (∀ i : Nat, acceleratedOrbit i n % 2 ^ k ≠ r) := by
  constructor
  · intro h i hc
    exact h i ((parityVector_eq_iff_mod_eq hr).mpr hc)
  · intro h i hc
    exact h i ((parityVector_eq_iff_mod_eq hr).mp hc)

/-! ## The one block that magnitude forces: `11` -/

/-- No two consecutive odd steps inside the first `j` steps. -/
def NoAdjOdd (n j : Nat) : Prop :=
  ∀ i : Nat, i + 1 < j →
    ¬ (acceleratedOrbit i n % 2 = 1 ∧ acceleratedOrbit (i + 1) n % 2 = 1)

theorem noAdjOdd_step {n j : Nat} (h : NoAdjOdd n (j + 1)) :
    NoAdjOdd (acceleratedStep n) j := by
  intro i hi hc
  refine h (i + 1) (by omega) ?_
  have e1 : acceleratedOrbit (i + 1) n = acceleratedOrbit i (acceleratedStep n) := rfl
  have e2 : acceleratedOrbit (i + 2) n = acceleratedOrbit (i + 1) (acceleratedStep n) := rfl
  rw [e1, e2]
  exact hc

/-- **The count bound.**  A window with no two adjacent odd steps has at most
`(j + 1) / 2` odd steps: `2 · a ≤ j + 1`.  Proved by a two-step induction, carried
as a pair so that ordinary `Nat` recursion suffices. -/
theorem two_mul_oddCount_le_pair : ∀ j : Nat,
    (∀ n : Nat, NoAdjOdd n j → 2 * oddCount n j ≤ j + 1) ∧
    (∀ n : Nat, NoAdjOdd n (j + 1) → 2 * oddCount n (j + 1) ≤ j + 2) := by
  intro j
  induction j with
  | zero =>
    refine ⟨fun n _ => by simp [oddCount_zero], fun n _ => ?_⟩
    rcases Arith.mod_two_eq_zero_or_one n with hn | hn
    · rw [oddCount_succ_of_even hn, oddCount_zero]; omega
    · rw [oddCount_succ_of_odd hn, oddCount_zero]; omega
  | succ j ih =>
    refine ⟨ih.2, fun n h => ?_⟩
    rcases Arith.mod_two_eq_zero_or_one n with hn | hn
    · have := ih.2 (acceleratedStep n) (noAdjOdd_step h)
      rw [oddCount_succ_of_even hn]
      omega
    · have hstep : acceleratedStep n % 2 = 0 := by
        have h0 : ¬ (acceleratedOrbit 0 n % 2 = 1 ∧ acceleratedOrbit 1 n % 2 = 1) :=
          h 0 (by omega)
        have e0 : acceleratedOrbit 0 n = n := rfl
        have e1 : acceleratedOrbit 1 n = acceleratedStep n := rfl
        rw [e0, e1] at h0
        rcases Arith.mod_two_eq_zero_or_one (acceleratedStep n) with he | he
        · exact he
        · exact absurd ⟨hn, he⟩ h0
      have hrest : NoAdjOdd (acceleratedStep (acceleratedStep n)) j :=
        noAdjOdd_step (noAdjOdd_step h)
      have := ih.1 (acceleratedStep (acceleratedStep n)) hrest
      rw [oddCount_succ_of_odd hn, oddCount_succ_of_even hstep]
      omega

theorem two_mul_oddCount_le {n j : Nat} (h : NoAdjOdd n j) : 2 * oddCount n j ≤ j + 1 :=
  (two_mul_oddCount_le_pair j).1 n h

/-! ### The arithmetic that turns the count bound into lightness -/

/-- `3 ^ (j + 1) < 2 ^ (2 * j)` for every `j ≥ 4`.  (It is false at `j = 3`:
`3 ^ 4 = 81 > 64 = 2 ^ 6`.) -/
theorem three_pow_succ_lt_four_pow : ∀ k : Nat, 3 ^ (k + 5) < 2 ^ (2 * (k + 4)) := by
  intro k
  induction k with
  | zero => decide
  | succ k ih =>
    have hstep : 3 ^ (k + 6) = 3 * 3 ^ (k + 5) := by
      rw [show k + 6 = (k + 5) + 1 from rfl, Arith.three_pow_succ]
    have h4 : 2 ^ (2 * (k + 5)) = 4 * 2 ^ (2 * (k + 4)) := by
      rw [show 2 * (k + 5) = 2 * (k + 4) + 2 from by omega, Nat.pow_add]
      omega
    rw [show k + 1 + 5 = k + 6 from rfl, hstep, show k + 1 + 4 = k + 5 from rfl, h4]
    omega

theorem three_pow_succ_lt_four_pow' {j : Nat} (hj : 4 ≤ j) : 3 ^ (j + 1) < 2 ^ (2 * j) := by
  have h := three_pow_succ_lt_four_pow (j - 4)
  have e1 : j - 4 + 5 = j + 1 := by omega
  have e2 : 2 * (j - 4 + 4) = 2 * j := by omega
  rw [e1, e2] at h
  exact h

/-- **The forced block.**  A window of length `j ≥ 4` with no two adjacent odd
steps is light: `3 ^ a < 2 ^ j`.  Hence a never-dropping orbit contains the block
`11` in every window of length `≥ 4` across which it does not drop — the one block
that is genuinely forced, and it is forced by magnitude, not by the combinatorics
of the language. -/
theorem three_pow_lt_two_pow_of_noAdjOdd {n j : Nat} (hj : 4 ≤ j) (h : NoAdjOdd n j) :
    3 ^ oddCount n j < 2 ^ j := by
  have hcount : 2 * oddCount n j ≤ j + 1 := two_mul_oddCount_le h
  have hsq : 3 ^ oddCount n j * 3 ^ oddCount n j < 2 ^ j * 2 ^ j := by
    have h1 : 3 ^ oddCount n j * 3 ^ oddCount n j = 3 ^ (2 * oddCount n j) := by
      rw [show 2 * oddCount n j = oddCount n j + oddCount n j from by omega, Nat.pow_add]
    have h2 : 3 ^ (2 * oddCount n j) ≤ 3 ^ (j + 1) :=
      Arith.three_pow_le_three_pow hcount
    have h3 : 3 ^ (j + 1) < 2 ^ (2 * j) := three_pow_succ_lt_four_pow' hj
    have h4 : 2 ^ (2 * j) = 2 ^ j * 2 ^ j := by
      rw [show 2 * j = j + j from by omega, Nat.pow_add]
    omega
  rcases Nat.lt_or_ge (3 ^ oddCount n j) (2 ^ j) with hlt | hge
  · exact hlt
  · have : 2 ^ j * 2 ^ j ≤ 3 ^ oddCount n j * 3 ^ oddCount n j :=
      Nat.mul_le_mul hge hge
    omega

/-- Contrapositive, in the form the never-dropping analysis meets it: a heavy
window of length `≥ 4` must contain two adjacent odd steps. -/
theorem not_noAdjOdd_of_heavy {n j : Nat} (hj : 4 ≤ j) (hheavy : 2 ^ j ≤ 3 ^ oddCount n j) :
    ¬ NoAdjOdd n j := by
  intro h
  have := three_pow_lt_two_pow_of_noAdjOdd hj h
  omega

end InfiniteWord
end Collatz

