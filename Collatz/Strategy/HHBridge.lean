import Collatz.Strategy.AffineExact
import Collatz.Strategy.CycleLemma
import Collatz.Strategy.AccumulatorAutomaton
import Collatz.Structure.AccCycle
import Collatz.Structure.Density

/-!
# The bridge between the two halves of the development

The repository grew two descriptions of the same object and never joined them.

* The **word** side — `DeltaSpectrum.accC`, `DeltaSpectrum.C`, `gap`,
  `AccumulatorAutomaton` — takes a `List Bool` and folds the accumulator
  recursion `c ↦ 3c + 2 ^ j` (odd letter), `c ↦ c` (even letter) along it.
* The **orbit** side — `AffineExact.affineC`, `oddCount`, `CycleLemma` — takes a
  starting integer `x` and reads the same recursion off the parities of
  `acceleratedOrbit i x`.

They are the same recursion driven by two different sources of parity bits.
Nothing in the repository said so, and that missing sentence is what stopped
`CycleLemma`'s conclusions from reaching `HalbeisenHungerbuhler.HHExtremal`:
`cycle_lemma` speaks about a `w : Nat → Nat`, while the Halbeisen–Hungerbühler
apparatus speaks about words.

This file supplies the sentence.

## What is proved

* `w x i` — the parity bit at accelerated step `i`, the `Nat → Nat` word of `x`.
* `w_periodic` — on a cycle the word is periodic, which is the hypothesis
  `CycleLemma` needs.
* `partialSum_eq_oddCount` — `CycleLemma`'s partial sum of `w x` *is* `oddCount`.
* `word x L` — the same bits as a `List Bool`.
* **`affineC_eq_C` — `affineC L x = C (word x L)`.**  The two accumulators agree.
* `oddCount_word` — and the two odd-counts agree, so `gap (word x L)` is the
  familiar `2 ^ L − 3 ^ oddCount x L`.

## What is *not* proved

This is one of the four gaps between `CycleLemma` and `HHExtremal`, and closing
it does not close the others.  Still missing, and stated here so the boundary is
not mistaken: `ExtremalTime.hhMinTime l n n = hhMin l n l` (numerically true for
`2 ≤ l ≤ 17` after the ceiling-word fix, but a genuine sum-reindexing induction
in Lean), and the rotation law that transports minimality of `x` across the
rotation `cycle_lemma` chooses for itself.  `HHExtremal` remains an assumed
`Prop`; nothing downstream of it has become unconditional.
-/

namespace Collatz
namespace HHBridge

open AccCycle DeltaSpectrum AccumulatorAutomaton

/-! ## The word of an orbit, as a function -/

/-- The parity bit at accelerated step `i` of `x`: the `Nat → Nat` word that
`CycleLemma` takes as input. -/
def w (x i : Nat) : Nat := acceleratedOrbit i x % 2

theorem w_le_one (x i : Nat) : w x i ≤ 1 := by
  have := Arith.mod_two_eq_zero_or_one (acceleratedOrbit i x)
  unfold w; omega

/-- **On a cycle the word is periodic.**  This is exactly the hypothesis
`CycleLemma.disc_period` and `cycle_lemma` require. -/
theorem w_periodic {x L : Nat} (h : AccIsCycleOf x L) (i : Nat) :
    w x (i + L) = w x i := by
  unfold w
  rw [← acceleratedOrbit_add i L x, h.2]

/-- **`CycleLemma`'s partial sum is `oddCount`.**  Both count the odd steps in
the first `L` accelerated iterates; one by summing parities, the other by
counting `1`s in the parity vector. -/
theorem partialSum_eq_oddCount (x : Nat) :
    ∀ L, CycleLemma.partialSum (w x) L = oddCount x L := by
  intro L
  induction L with
  | zero => simp [oddCount, parityVector]
  | succ L ih =>
    show w x L + CycleLemma.partialSum (w x) L = oddCount x (L + 1)
    rw [ih, Density.oddCount_succ_last x L]
    unfold w
    omega

/-! ## The word of an orbit, as a list -/

/-- The first `L` parity bits of `x` as a `List Bool`, the form the word side
of the development consumes. -/
def word (x L : Nat) : List Bool :=
  (List.range L).map (fun i => decide (w x i = 1))

@[simp] theorem word_length (x L : Nat) : (word x L).length = L := by
  simp [word]

theorem word_succ (x L : Nat) :
    word x (L + 1) = word x L ++ [decide (w x L = 1)] := by
  unfold word
  rw [List.range_succ, List.map_append]
  rfl

/-- **The bridge.**  The orbit accumulator and the word accumulator are the same
number.  `affineC` reads its parity bits off `acceleratedOrbit`, `C` reads them
off a list; `word` is the list of those bits, and the two folds coincide letter
by letter. -/
theorem affineC_eq_C (x : Nat) : ∀ L, AffineExact.affineC L x = C (word x L) := by
  intro L
  induction L with
  | zero => rfl
  | succ L ih =>
    rw [word_succ, C_snoc, word_length, ← ih]
    show (if acceleratedOrbit L x % 2 = 1 then _ else _) = _
    unfold w
    by_cases h : acceleratedOrbit L x % 2 = 1 <;> simp [h]

/-- And the two odd-counts agree, so the word's `gap` is the familiar
`2 ^ L − 3 ^ oddCount x L`. -/
theorem oddCount_word (x : Nat) : ∀ L, DeltaSpectrum.oddCount (word x L) = oddCount x L := by
  intro L
  induction L with
  | zero => rfl
  | succ L ih =>
    rw [word_succ, oddCount_append, ih, Density.oddCount_succ_last x L]
    show oddCount x L + ((if decide (w x L = 1) then 1 else 0) + 0) = _
    unfold w
    by_cases h : acceleratedOrbit L x % 2 = 1 <;> simp [h] <;> omega

theorem gap_word (x L : Nat) : gap (word x L) = 2 ^ L - 3 ^ oddCount x L := by
  rw [gap, word_length, oddCount_word]

end HHBridge
end Collatz
