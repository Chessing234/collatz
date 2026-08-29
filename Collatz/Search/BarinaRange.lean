import Collatz.Search.VerifiedExtended
import Collatz.Strategy.CycleProduct

/-!
# Barina's verified range, as an explicit external hypothesis

**Read this before using anything in this file.**

`Search.reachesOne_of_lt_1086464` is a **theorem** of this development.  It is
established by kernel-checked `decide` over `1061` sieve blocks — about `1.09`
million values, minutes of build time — and its axiom footprint is
`propext, Quot.sound`.  No `sorry`, no `native_decide`.

Barina's range, `704 · 2 ^ 60 ≈ 8.12 · 10 ^ 20`, is an **external computation** (a
C/GPU program, Barina 2025).  It is not proved here and cannot be: reproducing it
by the method above needs about `7.9 · 10 ^ 17` blocks instead of `1061`, a factor
of `7 · 10 ^ 14`, which is on the order of `10 ^ 10` years of kernel time.

So this file does **not** replace the proved constant.  It names Barina's result as
an explicit hypothesis, in the style this development already uses for
`BakerConditional.EffectiveGap`, and derives what follows from it.  Every theorem
here that depends on `BarinaVerified` says so in its statement.  The proved
`1 086 464` results are untouched and remain unconditional.

## The constant

`barinaBound` is the single canonical definition; nothing below repeats the
numeral.  `barina_value` pins it to `811 656 739 243 220 271 104` and
`barina_gt_verified` records that it strictly exceeds the proved range, so this is
a genuine widening and not a restatement.

## What the widening buys

`CycleProduct.excludedLength` is **monotone in the verified range**
(`excludedLength_mono`): a length excluded at `c` is excluded at every `c' ≥ c`.
That is the mechanism by which computation converts into a stronger cycle bound,
and it is the reason the repository's bound moved `520 → 1539 → 2593` as the range
grew.  Measured with exact integer arithmetic outside Lean: the raw product bound
first fails at `L = 2593` at the proved range, and fails nowhere below `L = 40 000`
at Barina's — so `BarinaVerified` would move the cycle-length bound by more than an
order of magnitude.  That measurement is **not** a theorem here; only the
monotonicity is.

`excludedLength_mono_witness` shows the monotonicity is not vacuous, on numbers
small enough for the kernel.
-/

namespace Collatz
namespace BarinaRange

open Reach Search CycleProduct

/-! ## The constant -/

/-- **Barina's verified range**, `704 · 2 ^ 60`.  The single canonical definition;
no other numeral for it appears in this development. -/
def barinaBound : Nat := 704 * 2 ^ 60

/-- Its decimal value. -/
theorem barina_value : barinaBound = 811656739243220271104 := by decide

/-- It strictly exceeds the range this development **proves**, so adopting it is a
genuine widening. -/
theorem barina_gt_verified : 1086464 < barinaBound := by decide

/-! ## The hypothesis

Named, not proved.  Anything below that consumes it carries it in its statement. -/

/-- **Barina's computation, as a hypothesis.**  Every positive integer below
`704 · 2 ^ 60` reaches `1`.  External to this development; see the file header. -/
def BarinaVerified : Prop := ∀ n : Nat, 0 < n → n < barinaBound → ReachesOne n

/-- The hypothesis subsumes the proved range — a consistency check, not a proof of
the hypothesis. -/
theorem barina_subsumes (h : BarinaVerified) {n : Nat} (hn : 0 < n)
    (hlt : n < 1086464) : ReachesOne n :=
  h n hn (by have := barina_gt_verified; omega)

/-- Conversely the proved range is a special case of what `BarinaVerified` asserts,
so the hypothesis is a strict strengthening rather than a different claim. -/
theorem proved_range_is_weaker {n : Nat} (hn : 0 < n) (hlt : n < 1086464) :
    ReachesOne n := reachesOne_of_lt_1086464 hn hlt

/-! ## What follows from it -/

/-- A counterexample is at least `704 · 2 ^ 60`. -/
theorem counterexample_ge_barina (h : BarinaVerified) {n : Nat} (hn : 0 < n)
    (hnr : ¬ ReachesOne n) : barinaBound ≤ n := by
  rcases Nat.lt_or_ge n barinaBound with hlt | hge
  · exact absurd (h n hn hlt) hnr
  · exact hge

/-- **Every point on the orbit of a counterexample is at least `704 · 2 ^ 60`.**
The shape is `CycleLength2593.ge_verified_768000`, evaluated at the wider range —
the repository's own comment there notes the proof is insensitive to the
constant. -/
theorem ge_verified_barina (h : BarinaVerified) {n m : Nat} (hn : 0 < n)
    (hnr : ¬ ReachesOne n) (hm : ∃ i : Nat, acceleratedOrbit i n = m) :
    barinaBound ≤ m := by
  obtain ⟨i, hi⟩ := hm
  rcases Nat.lt_or_ge m barinaBound with hlt | hge
  · exfalso
    have hpos : 0 < m := by rw [← hi]; exact acceleratedOrbit_positive hn i
    have hreach : ReachesOne m := h m hpos hlt
    rw [← hi] at hreach
    exact hnr (reachesOne_of_accOrbit hn hreach)
  · exact hge

/-! ## Why a wider range is worth having

The verified range enters the cycle bound through `excludedLength`, and it enters
monotonically. -/

/-- **The exclusion test is monotone in the verified range.**  A length excluded at
`c` is excluded at every `c' ≥ c`.  This is the mechanism that turns computation
into a stronger cycle-length bound. -/
theorem excludedLength_mono {c c' L : Nat} (hc : 0 < c) (hcc : c ≤ c')
    (h : excludedLength c L = true) : excludedLength c' L = true := by
  rw [excludedLength, List.all_eq_true] at h ⊢
  intro a ha
  have hstep := h a ha
  rcases Nat.lt_or_ge (3 ^ a) (2 ^ L) with hlt | hge
  · -- the clause is live: transfer the strict inequality
    simp only [decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      Nat.not_lt] at hstep ⊢
    rcases hstep with hbad | hgood
    · omega
    · right
      -- `3 ^ a · 2a < 3c (2^L − 3^a) ≤ 3c' (2^L − 3^a)`
      have hslack : 3 ^ a * (2 * a) < 3 * c * (2 ^ L - 3 ^ a) := by
        have hexp : 3 ^ a * (3 * c + 2 * a) = 3 ^ a * (3 * c) + 3 ^ a * (2 * a) := by
          rw [Nat.mul_add]
        have hsub : 3 * c * (2 ^ L - 3 ^ a) = 3 * c * 2 ^ L - 3 * c * 3 ^ a := by
          rw [Nat.mul_sub]
        have hle : 3 * c * 3 ^ a ≤ 3 * c * 2 ^ L :=
          Nat.mul_le_mul_left _ (Nat.le_of_lt hlt)
        have hcomm : 3 ^ a * (3 * c) = 3 * c * 3 ^ a := Nat.mul_comm _ _
        omega
      have hgrow : 3 * c * (2 ^ L - 3 ^ a) ≤ 3 * c' * (2 ^ L - 3 ^ a) :=
        Nat.mul_le_mul_right _ (by omega)
      have hexp : 3 ^ a * (3 * c' + 2 * a) = 3 ^ a * (3 * c') + 3 ^ a * (2 * a) := by
        rw [Nat.mul_add]
      have hsub : 3 * c' * (2 ^ L - 3 ^ a) = 3 * c' * 2 ^ L - 3 * c' * 3 ^ a := by
        rw [Nat.mul_sub]
      have hle : 3 * c' * 3 ^ a ≤ 3 * c' * 2 ^ L :=
        Nat.mul_le_mul_left _ (Nat.le_of_lt hlt)
      have hcomm : 3 ^ a * (3 * c') = 3 * c' * 3 ^ a := Nat.mul_comm _ _
      omega
  · -- the clause is dead
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt]
    exact Or.inl hge

/-- Monotonicity is not vacuous: `L = 2` is excluded at the proved range and not at
`c = 1`.  Small enough for the kernel; the same phenomenon at `L = 2593` is what
`BarinaVerified` would buy, and is recorded in the header as a measurement rather
than a theorem. -/
theorem excludedLength_mono_witness :
    excludedLength 1 2 = false ∧ excludedLength 1086464 2 = true := by
  refine ⟨by decide, by decide⟩

/-- The upgrade is available to every consumer of the exclusion test: a length
excluded at the **proved** range is excluded at Barina's. -/
theorem excludedLength_at_barina {L : Nat} (h : excludedLength 1086464 L = true) :
    excludedLength barinaBound L = true :=
  excludedLength_mono (by omega) (by have := barina_gt_verified; omega) h

end BarinaRange
end Collatz
