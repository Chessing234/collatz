import Collatz.Strategy.DeltaSpectrum

/-!
# Round XI — decomposition of the Round X divergence-half soundness filter

Round X built `expStep x = 3x/2` (even), `(3x+1)/2` (odd): it agrees with the
Collatz map on every odd input, obeys the same affine law `2^j f^j x = 3^j x + b`,
and every one of its orbits provably diverges.  The stated weakness was that it
"differs on a whole branch", so it kills a coarser class of mechanisms than the
cycle filter does.

This file **decomposes** the filter rather than strengthening its constants.  The
whole difference between the two maps is one line of word arithmetic:

* Collatz: `accC` multiplies the accumulator by `3` **only on an odd letter**;
* expStep: `accB` multiplies the accumulator by `3` **on every letter**.

Both add `2^j` exactly on the odd letters.  So

    C(w) = Σ_{k odd}  3 ^ (#odd letters after k) · 2^k
    B(w) = Σ_{k odd}  3 ^ (#letters       after k) · 2^k

and `B` is `C` with each term reweighted by `3 ^ (#even letters after k)`.  That
reweighting *is* the even branch's contraction, and it is the only coordinate the
filter moves.

## The two telescopes (Part 1)

`collatz_telescope`   `C w + 2 ^ |w| = D w + 3 ^ a(w)`
`exp_telescope`       `B w + E w + 2 ^ |w| = 3 ^ |w|`

where `D`/`E` are the complementary accumulators over the **even** letters.  The
sign asymmetry between them is the whole content: in the Collatz telescope the
complement sits on the far side of the accumulator, in the expStep telescope it
sits on the same side.

## The minimal separator (Part 2)

Dropping `D ≥ 0` and `E ≥ 0` leaves a single affine inequality between
`C`, `2^L`, `3^a`, mentioning **no word structure at all**:

`sep_collatz` : `3 ^ a(w) ≤ C w + 2 ^ |w|`  — true for *every* word;
`sep_exp`     : `3 ^ |w| ≤ B w + 2 ^ |w| ↔ w = 1^L`.

So the exact minimal piece of information defeating the filter is the one
inequality `accumulator ≥ −gap`, and its expStep survivor class is the single
word `1^L`, which `ScaleRecord.mersenne_nonDropping` already handles.

## The classification (Part 3)

`eq_iff_zerosThenOnes` : `B w = C w ↔ w ∈ 0*1*` (avoids the factor `10`).
Cardinality `L + 1`, entropy `0`, and **not closed under concatenation**:
`concat_fails` exhibits `[true] ++ [false]` with both factors in the class and
the product outside it.  The obstruction is exactly the factor `10` — an even
step following an odd step.

## The cycle criterion (Part 4, section XXII)

`exp_gap_dvd_collapse` : `(3^L − 2^L) ∣ B w → w = 0^L ∨ w = 1^L`.
The expStep gap is the *maximal* gap and the expStep accumulator is bounded by
exactly that gap, so the divisibility hypothesis of the cycle criterion is the
one hypothesis expStep can never satisfy non-trivially.

## Soundness filter (assets used)

Everything here is word arithmetic proved by induction from the two definitions.
No asset, no property of `d`, no numerical input.
-/

namespace Collatz
namespace FilterDecomposition

open DeltaSpectrum

/-! ## Part 0: the four accumulators -/

/-- **expStep's accumulator.**  Identical to `DeltaSpectrum.accC` except that the
`3` is applied on *every* letter, not only on the odd ones. -/
def accB : List Bool → Nat → Nat → Nat
  | [], _, c => c
  | b :: w, j, c => accB w (j + 1) (3 * c + (if b then 2 ^ j else 0))

/-- `B(w)`: the expStep affine accumulator of the word. -/
def B (w : List Bool) : Nat := accB w 0 0

/-- **Collatz's complementary accumulator**: same `3`-schedule as `accC` (odd
letters only) but adding `2 ^ j` on the *even* letters. -/
def accD : List Bool → Nat → Nat → Nat
  | [], _, c => c
  | b :: w, j, c => accD w (j + 1) (if b then 3 * c else c + 2 ^ j)

/-- `D(w)`. -/
def D (w : List Bool) : Nat := accD w 0 0

/-- **expStep's complementary accumulator**: `3` on every letter, adding `2 ^ j`
on the even letters. -/
def accE : List Bool → Nat → Nat → Nat
  | [], _, c => c
  | b :: w, j, c => accE w (j + 1) (3 * c + (if b then 0 else 2 ^ j))

/-- `E(w)`. -/
def E (w : List Bool) : Nat := accE w 0 0

/-! ## Part 1: the two telescopes -/

/-- Generalised expStep telescope. -/
theorem accB_accE_telescope :
    ∀ (w : List Bool) (j cB cE : Nat),
      accB w j cB + accE w j cE + 2 ^ (j + w.length)
        = 3 ^ w.length * (cB + cE + 2 ^ j) := by
  intro w
  induction w with
  | nil => intro j cB cE; simp [accB, accE]
  | cons b w ih =>
    intro j cB cE
    have hlen : (b :: w).length = w.length + 1 := rfl
    have hj : j + (b :: w).length = (j + 1) + w.length := by
      rw [hlen]; omega
    rw [hj]
    show accB w (j + 1) (3 * cB + (if b then 2 ^ j else 0))
        + accE w (j + 1) (3 * cE + (if b then 0 else 2 ^ j))
        + 2 ^ ((j + 1) + w.length) = _
    rw [ih (j + 1) (3 * cB + (if b then 2 ^ j else 0))
          (3 * cE + (if b then 0 else 2 ^ j))]
    have hpow : (2 : Nat) ^ (j + 1) = 2 ^ j + 2 ^ j := by
      rw [Nat.pow_succ]; omega
    have hsum :
        (3 * cB + (if b then 2 ^ j else 0)) + (3 * cE + (if b then 0 else 2 ^ j))
          + 2 ^ (j + 1) = 3 * (cB + cE + 2 ^ j) := by
      cases b <;> simp <;> omega
    rw [hsum, hlen, Nat.pow_succ, Nat.mul_comm (3 ^ w.length) 3, Nat.mul_assoc]
    exact Nat.mul_left_comm _ _ _

/-- **The expStep telescope**: `B w + E w + 2 ^ L = 3 ^ L`. -/
theorem exp_telescope (w : List Bool) :
    B w + E w + 2 ^ w.length = 3 ^ w.length := by
  have h := accB_accE_telescope w 0 0 0
  simpa [B, E] using h

/-- Generalised Collatz telescope. -/
theorem accC_accD_telescope :
    ∀ (w : List Bool) (j c c' : Nat),
      accC w j c + 2 ^ (j + w.length) + 3 ^ oddCount w * c'
        = accD w j c' + 3 ^ oddCount w * (c + 2 ^ j) := by
  intro w
  induction w with
  | nil => intro j c c'; simp [accC, accD, oddCount]; omega
  | cons b w ih =>
    intro j c c'
    have hlen : (b :: w).length = w.length + 1 := rfl
    have hj : j + (b :: w).length = (j + 1) + w.length := by rw [hlen]; omega
    have hpow : (2 : Nat) ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [Nat.pow_succ]; omega
    cases b with
    | false =>
      have hodd : oddCount (false :: w) = oddCount w := by simp [oddCount]
      show accC w (j + 1) c + 2 ^ (j + (false :: w).length)
          + 3 ^ oddCount (false :: w) * c'
          = accD w (j + 1) (c' + 2 ^ j) + 3 ^ oddCount (false :: w) * (c + 2 ^ j)
      rw [hj, hodd]
      have hih := ih (j + 1) c (c' + 2 ^ j)
      rw [Nat.mul_add] at hih
      rw [Nat.mul_add (3 ^ oddCount w) c (2 ^ (j + 1))] at hih
      rw [Nat.mul_add (3 ^ oddCount w) c (2 ^ j)]
      rw [hpow] at hih
      rw [Nat.mul_add (3 ^ oddCount w) (2 ^ j) (2 ^ j)] at hih
      omega
    | true =>
      have hodd : oddCount (true :: w) = oddCount w + 1 := by simp [oddCount]; omega
      show accC w (j + 1) (3 * c + 2 ^ j) + 2 ^ (j + (true :: w).length)
          + 3 ^ oddCount (true :: w) * c'
          = accD w (j + 1) (3 * c') + 3 ^ oddCount (true :: w) * (c + 2 ^ j)
      rw [hj, hodd, Nat.pow_succ]
      have hih := ih (j + 1) (3 * c + 2 ^ j) (3 * c')
      have hcong : 3 * c + 2 ^ j + 2 ^ (j + 1) = 3 * (c + 2 ^ j) := by
        rw [hpow]; omega
      rw [hcong] at hih
      have e1 : 3 ^ oddCount w * 3 * c' = 3 ^ oddCount w * (3 * c') := by
        rw [Nat.mul_assoc]
      have e2 : 3 ^ oddCount w * 3 * (c + 2 ^ j)
          = 3 ^ oddCount w * (3 * (c + 2 ^ j)) := by
        rw [Nat.mul_assoc]
      rw [e1, e2]
      exact hih

/-- **The Collatz telescope**: `C w + 2 ^ L = D w + 3 ^ a`. -/
theorem collatz_telescope (w : List Bool) :
    C w + 2 ^ w.length = D w + 3 ^ oddCount w := by
  have h := accC_accD_telescope w 0 0 0
  simpa [C, D] using h

/-! ## Part 2: the minimal separator

One affine inequality between `C`, `2 ^ L`, `3 ^ a`, with no word structure. -/

/-- **True for every Collatz word**: `3 ^ a ≤ C + 2 ^ L`, i.e. `C ≥ −G`. -/
theorem sep_collatz (w : List Bool) : 3 ^ oddCount w ≤ C w + 2 ^ w.length := by
  have h := collatz_telescope w
  omega

/-- **The expStep bound is the reverse**: `B + 2 ^ L ≤ 3 ^ L`, i.e. `B ≤ −G_E`. -/
theorem exp_bound (w : List Bool) : B w + 2 ^ w.length ≤ 3 ^ w.length := by
  have h := exp_telescope w
  omega

/-- `w` is `1 ^ L`. -/
def allOdd : List Bool → Prop
  | [] => True
  | b :: w => b = true ∧ allOdd w

/-- `w` is `0 ^ L`. -/
def allEven : List Bool → Prop
  | [] => True
  | b :: w => b = false ∧ allEven w

theorem accE_ge : ∀ (w : List Bool) (j c : Nat), c ≤ accE w j c := by
  intro w
  induction w with
  | nil => intro j c; exact Nat.le_refl c
  | cons b w ih =>
    intro j c
    show c ≤ accE w (j + 1) (3 * c + (if b then 0 else 2 ^ j))
    have h0 : c ≤ 3 * c := by omega
    have h1 : c ≤ 3 * c + (if b then 0 else 2 ^ j) :=
      Nat.le_trans h0 (Nat.le_add_right _ _)
    exact Nat.le_trans h1 (ih (j + 1) _)

theorem accE_eq_zero_iff : ∀ (w : List Bool) (j : Nat), accE w j 0 = 0 ↔ allOdd w := by
  intro w
  induction w with
  | nil => intro j; simp [accE, allOdd]
  | cons b w ih =>
    intro j
    cases b with
    | true =>
      show accE w (j + 1) (3 * 0 + 0) = 0 ↔ _
      rw [show 3 * 0 + 0 = 0 from rfl, ih (j + 1)]
      simp [allOdd]
    | false =>
      show accE w (j + 1) (3 * 0 + 2 ^ j) = 0 ↔ _
      constructor
      · intro h
        exfalso
        have hpos : (1 : Nat) ≤ 2 ^ j := Nat.one_le_two_pow
        have hge := accE_ge w (j + 1) (3 * 0 + 2 ^ j)
        omega
      · intro h
        exact absurd h.1 (by simp)


/-- **The separator, expStep side**: the inequality `3 ^ L ≤ B + 2 ^ L` — which is
`sep_collatz` transported to expStep — holds for **exactly one** word, `1 ^ L`.
So the single affine inequality `accumulator ≥ −gap` defeats the whole filter,
and its survivor class is the Mersenne word. -/
theorem sep_exp (w : List Bool) :
    3 ^ w.length ≤ B w + 2 ^ w.length ↔ allOdd w := by
  have ht := exp_telescope w
  constructor
  · intro h
    have hE : E w = 0 := by omega
    exact (accE_eq_zero_iff w 0).mp hE
  · intro h
    have hE : E w = 0 := (accE_eq_zero_iff w 0).mpr h
    omega

/-! ## Part 3: `B = 0` and the accumulator domination -/

theorem accB_ge : ∀ (w : List Bool) (j c : Nat), c ≤ accB w j c := by
  intro w
  induction w with
  | nil => intro j c; exact Nat.le_refl c
  | cons b w ih =>
    intro j c
    show c ≤ accB w (j + 1) (3 * c + (if b then 2 ^ j else 0))
    have h0 : c ≤ 3 * c := by omega
    exact Nat.le_trans (Nat.le_trans h0 (Nat.le_add_right _ _)) (ih (j + 1) _)

theorem accB_mono : ∀ (w : List Bool) (j c c' : Nat), c ≤ c' →
    accB w j c ≤ accB w j c' := by
  intro w
  induction w with
  | nil => intro j c c' h; exact h
  | cons b w ih =>
    intro j c c' h
    show accB w (j + 1) (3 * c + (if b then 2 ^ j else 0))
        ≤ accB w (j + 1) (3 * c' + (if b then 2 ^ j else 0))
    exact ih (j + 1) _ _ (by omega)

theorem accB_strictMono : ∀ (w : List Bool) (j c c' : Nat), c < c' →
    accB w j c < accB w j c' := by
  intro w
  induction w with
  | nil => intro j c c' h; exact h
  | cons b w ih =>
    intro j c c' h
    show accB w (j + 1) (3 * c + (if b then 2 ^ j else 0))
        < accB w (j + 1) (3 * c' + (if b then 2 ^ j else 0))
    exact ih (j + 1) _ _ (by omega)

theorem accB_eq_zero_iff : ∀ (w : List Bool) (j : Nat), accB w j 0 = 0 ↔ allEven w := by
  intro w
  induction w with
  | nil => intro j; simp [accB, allEven]
  | cons b w ih =>
    intro j
    cases b with
    | false =>
      show accB w (j + 1) (3 * 0 + 0) = 0 ↔ _
      rw [show 3 * 0 + 0 = 0 from rfl, ih (j + 1)]
      simp [allEven]
    | true =>
      show accB w (j + 1) (3 * 0 + 2 ^ j) = 0 ↔ _
      constructor
      · intro h
        exfalso
        have hpos : (1 : Nat) ≤ 2 ^ j := Nat.one_le_two_pow
        have hge := accB_ge w (j + 1) (3 * 0 + 2 ^ j)
        omega
      · intro h; exact absurd h.1 (by simp)

/-- `B w = 0` exactly on the all-even word. -/
theorem B_eq_zero_iff (w : List Bool) : B w = 0 ↔ allEven w := accB_eq_zero_iff w 0

/-- **Accumulator domination**: `C ≤ B`, pointwise on every word.  expStep's
accumulator is Collatz's with each term reweighted by `3 ^ (#even letters after
it)`. -/
theorem accC_le_accB : ∀ (w : List Bool) (j c : Nat), accC w j c ≤ accB w j c := by
  intro w
  induction w with
  | nil => intro j c; exact Nat.le_refl c
  | cons b w ih =>
    intro j c
    cases b with
    | true =>
      show accC w (j + 1) (3 * c + 2 ^ j) ≤ accB w (j + 1) (3 * c + 2 ^ j)
      exact ih (j + 1) _
    | false =>
      show accC w (j + 1) c ≤ accB w (j + 1) (3 * c + 0)
      exact Nat.le_trans (ih (j + 1) c) (accB_mono w (j + 1) c (3 * c + 0) (by omega))

theorem C_le_B (w : List Bool) : C w ≤ B w := accC_le_accB w 0 0

/-! ## Part 4: the classification of the survivors

`B w = C w` holds exactly on the words of `0*1*`, i.e. the words avoiding the
factor `10`.  There are `L + 1` of them at length `L`: entropy `0`. -/

/-- `w` avoids the factor `10`: every odd letter is followed only by odd letters. -/
def zeroOnes : List Bool → Prop
  | [] => True
  | true :: w => allOdd w
  | false :: w => zeroOnes w

/-- `w` contains an even letter. -/
def hasEven : List Bool → Prop
  | [] => False
  | true :: w => hasEven w
  | false :: _ => True

/-- `w` contains the factor `10`. -/
def hasDesc : List Bool → Prop
  | [] => False
  | true :: w => hasEven w
  | false :: w => hasDesc w

theorem allOdd_or_hasEven : ∀ w : List Bool, allOdd w ∨ hasEven w := by
  intro w
  induction w with
  | nil => exact Or.inl trivial
  | cons b w ih =>
    cases b with
    | true => exact ih.imp (fun h => ⟨rfl, h⟩) (fun h => h)
    | false => exact Or.inr trivial

theorem zeroOnes_or_hasDesc : ∀ w : List Bool, zeroOnes w ∨ hasDesc w := by
  intro w
  induction w with
  | nil => exact Or.inl trivial
  | cons b w ih =>
    cases b with
    | true => exact allOdd_or_hasEven w
    | false => exact ih

/-- On an all-odd word the two accumulators are literally the same computation. -/
theorem accC_eq_accB_of_allOdd : ∀ (w : List Bool), allOdd w →
    ∀ (j c : Nat), accC w j c = accB w j c := by
  intro w
  induction w with
  | nil => intro _ j c; rfl
  | cons b w ih =>
    intro h j c
    have hb : b = true := h.1
    subst hb
    show accC w (j + 1) (3 * c + 2 ^ j) = accB w (j + 1) (3 * c + 2 ^ j)
    exact ih h.2 (j + 1) _

/-- **Survivors agree.** -/
theorem accC_eq_accB_of_zeroOnes : ∀ (w : List Bool), zeroOnes w →
    ∀ j : Nat, accC w j 0 = accB w j 0 := by
  intro w
  induction w with
  | nil => intro _ j; rfl
  | cons b w ih =>
    intro h j
    cases b with
    | true =>
      show accC w (j + 1) (3 * 0 + 2 ^ j) = accB w (j + 1) (3 * 0 + 2 ^ j)
      exact accC_eq_accB_of_allOdd w h (j + 1) _
    | false =>
      show accC w (j + 1) 0 = accB w (j + 1) (3 * 0 + 0)
      rw [show 3 * 0 + 0 = 0 from rfl]
      exact ih h (j + 1)

/-- An even letter anywhere, together with a positive carry, makes the gap strict:
the even branch's contraction, visible in one step. -/
theorem accC_lt_accB_of_hasEven : ∀ (w : List Bool), hasEven w →
    ∀ (j c : Nat), 0 < c → accC w j c < accB w j c := by
  intro w
  induction w with
  | nil => intro h; exact absurd h (fun x => x)
  | cons b w ih =>
    intro h j c hc
    cases b with
    | false =>
      show accC w (j + 1) c < accB w (j + 1) (3 * c + 0)
      exact Nat.lt_of_le_of_lt (accC_le_accB w (j + 1) c)
        (accB_strictMono w (j + 1) c (3 * c + 0) (by omega))
    | true =>
      show accC w (j + 1) (3 * c + 2 ^ j) < accB w (j + 1) (3 * c + 2 ^ j)
      have hb : (1 : Nat) ≤ 2 ^ j := Nat.one_le_two_pow
      exact ih h (j + 1) _ (by omega)

/-- **Non-survivors are strictly separated.** -/
theorem accC_lt_accB_of_hasDesc : ∀ (w : List Bool), hasDesc w →
    ∀ j : Nat, accC w j 0 < accB w j 0 := by
  intro w
  induction w with
  | nil => intro h; exact absurd h (fun x => x)
  | cons b w ih =>
    intro h j
    cases b with
    | false =>
      show accC w (j + 1) 0 < accB w (j + 1) (3 * 0 + 0)
      rw [show 3 * 0 + 0 = 0 from rfl]
      exact ih h (j + 1)
    | true =>
      show accC w (j + 1) (3 * 0 + 2 ^ j) < accB w (j + 1) (3 * 0 + 2 ^ j)
      refine accC_lt_accB_of_hasEven w h (j + 1) _ ?_
      have : (1 : Nat) ≤ 2 ^ j := Nat.one_le_two_pow
      omega

/-- **THE CLASSIFICATION THEOREM.**  The surviving class of the sharpened
divergence filter — the words on which expStep's accumulator is
indistinguishable from Collatz's — is exactly `0*1*`, the words avoiding the
factor `10`.  There are `L + 1` of them, so the class has zero entropy. -/
theorem eq_iff_zeroOnes (w : List Bool) : B w = C w ↔ zeroOnes w := by
  constructor
  · intro h
    rcases zeroOnes_or_hasDesc w with hz | hd
    · exact hz
    · exfalso
      have hlt : C w < B w := accC_lt_accB_of_hasDesc w hd 0
      omega
  · intro h
    exact ((accC_eq_accB_of_zeroOnes w h 0)).symm

/-! ## Part 5: concatenation — closure DISPROVED

The obstruction is the factor `10`: an even step following an odd step.  It is
created by concatenation whenever the left factor contains an odd letter and the
right factor contains an even one. -/

theorem allOdd_append : ∀ (u v : List Bool), allOdd (u ++ v) ↔ (allOdd u ∧ allOdd v) := by
  intro u
  induction u with
  | nil => intro v; exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | cons b u ih =>
    intro v
    constructor
    · intro h
      have := (ih v).mp h.2
      exact ⟨⟨h.1, this.1⟩, this.2⟩
    · intro h
      exact ⟨h.1.1, (ih v).mpr ⟨h.1.2, h.2⟩⟩

/-- **The exact closure rule.**  For `u, v` both in the surviving class, the
concatenation survives **iff** `u` has no odd letter or `v` has no even letter.
Closure therefore fails: of the `(L+1)²` pairs at length `L` only `2L+1` compose. -/
theorem concat_rule : ∀ (u v : List Bool), zeroOnes u → zeroOnes v →
    (zeroOnes (u ++ v) ↔ (allEven u ∨ allOdd v)) := by
  intro u
  induction u with
  | nil => intro v _ hv; exact ⟨fun _ => Or.inl trivial, fun _ => hv⟩
  | cons b u ih =>
    intro v hu hv
    cases b with
    | false =>
      have := ih v hu hv
      constructor
      · intro h
        rcases this.mp h with h1 | h2
        · exact Or.inl ⟨rfl, h1⟩
        · exact Or.inr h2
      · intro h
        refine this.mpr ?_
        rcases h with h1 | h2
        · exact Or.inl h1.2
        · exact Or.inr h2
    | true =>
      constructor
      · intro h
        exact Or.inr ((allOdd_append u v).mp h).2
      · intro h
        rcases h with h1 | h2
        · exact absurd h1.1 (by simp)
        · exact (allOdd_append u v).mpr ⟨hu, h2⟩

/-- **The concrete failure.**  `[true]` and `[false]` both survive; their
concatenation `10` does not — `C = 1` while `B = 3`. -/
theorem concat_fails :
    zeroOnes [true] ∧ zeroOnes [false] ∧ C [true, false] = 1 ∧ B [true, false] = 3 :=
  ⟨trivial, trivial, rfl, rfl⟩

/-- Not rotation-closed either: `01` survives, its rotation `10` does not. -/
theorem rotation_fails :
    B [false, true] = C [false, true] ∧ B [true, false] ≠ C [true, false] := by
  refine ⟨rfl, ?_⟩
  intro h
  exact absurd h (by decide)

/-! ## Part 6: the cycle criterion collapses the survivors (section XXII)

`G | C ⟹ expStep contradiction`.  The expStep gap is `3^L − 2^L`, the *largest*
gap available, and `exp_bound` says the expStep accumulator never exceeds it.  A
positive multiple of the gap that is at most the gap is the gap itself. -/

/-- **THE COLLAPSE.**  If the expStep gap divides the expStep accumulator then the
word is `0 ^ L` or `1 ^ L`.  So the divisibility hypothesis of the cycle
criterion is exactly the hypothesis expStep cannot satisfy: restricting to
cycle-compatible words leaves a two-element surviving class, both of whose
members are already eliminated (`0^L` has `B = 0`; `1^L` is the Mersenne word of
`ScaleRecord.mersenne_nonDropping`). -/
theorem exp_gap_dvd_collapse (w : List Bool) (k : Nat)
    (hk : k + 2 ^ w.length = 3 ^ w.length) (hdvd : k ∣ B w) :
    allEven w ∨ allOdd w := by
  have hle : B w ≤ k := by have := exp_bound w; omega
  obtain ⟨q, hq⟩ := hdvd
  cases q with
  | zero =>
    left
    exact (B_eq_zero_iff w).mp (by omega)
  | succ q =>
    right
    have hge : k ≤ B w := by
      rw [hq]
      exact Nat.le_mul_of_pos_right k (Nat.succ_pos q)
    refine (sep_exp w).mp ?_
    omega

/-! ## Part 7: the deformation space has exactly two coordinates

Write a step as `2 · f x = m(x) · x + c(x)` with `m(x) ∈ {1,3}` chosen by parity
and `c(x)` the odd-letter constant.  There are exactly two ways to deform the
Collatz map inside this shape:

* deform `c` on odd inputs, `c = d`: the `3x+d` family — the **cycle** filter,
  which refutes `d`-free mechanisms because genuine cycles exist;
* deform `m` on even inputs, `1 ↦ 3`: `expStep` — the **divergence** filter.

There is no third coordinate, and of the four `(m_even, m_odd)` corners only
`(3,3)` grows.  The other two non-Collatz corners fix `1`, so neither is a
divergence witness. -/

/-- Corner `(m_even, m_odd) = (3,1)`. -/
def mix31 (x : Nat) : Nat := if x % 2 = 0 then 3 * x / 2 else (x + 1) / 2

/-- Corner `(m_even, m_odd) = (1,1)`. -/
def mix11 (x : Nat) : Nat := if x % 2 = 0 then x / 2 else (x + 1) / 2

/-- Neither of the two remaining corners can be a divergence witness: both fix
`1`, so `expStep` is the unique growing corner. -/
theorem other_corners_fix_one : mix31 1 = 1 ∧ mix11 1 = 1 := ⟨rfl, rfl⟩


/-! ## Part 8: the survivors are rank one

Every survivor is `0^m 1^p`, and on it the accumulator factors as
`C = 2^m · (3^p − 2^p)` — a scale times a one-run value.  So on the surviving
class the coupling is not genuinely two-variable: the even prefix acts as pure
scale and the odd suffix is the Mersenne run.  Both factors are exactly what the
development already eliminates. -/

theorem accC_replicate_true : ∀ (p j c : Nat),
    accC (List.replicate p true) j c + 2 ^ (j + p) = 3 ^ p * (c + 2 ^ j) := by
  intro p
  induction p with
  | zero => intro j c; simp [accC]
  | succ p ih =>
    intro j c
    have hrep : List.replicate (p + 1) true = true :: List.replicate p true := rfl
    rw [hrep]
    show accC (List.replicate p true) (j + 1) (3 * c + 2 ^ j) + 2 ^ (j + (p + 1)) = _
    have hj : j + (p + 1) = (j + 1) + p := by omega
    rw [hj, ih (j + 1) (3 * c + 2 ^ j)]
    have hpow : (2 : Nat) ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [Nat.pow_succ]; omega
    have hc : 3 * c + 2 ^ j + 2 ^ (j + 1) = 3 * (c + 2 ^ j) := by rw [hpow]; omega
    rw [hc, Nat.pow_succ, Nat.mul_comm (3 ^ p) 3, Nat.mul_assoc]
    exact Nat.mul_left_comm _ _ _

theorem accC_replicate_false : ∀ (m : Nat) (v : List Bool) (j c : Nat),
    accC (List.replicate m false ++ v) j c = accC v (j + m) c := by
  intro m
  induction m with
  | zero => intro v j c; simp
  | succ m ih =>
    intro v j c
    have hrep : List.replicate (m + 1) false = false :: List.replicate m false := rfl
    rw [hrep]
    show accC (List.replicate m false ++ v) (j + 1) c = _
    rw [ih v (j + 1) c]
    have : j + 1 + m = j + (m + 1) := by omega
    rw [this]

/-- **Closed form on the surviving class**: `C(0^m 1^p) + 2^(m+p) = 2^m · 3^p`,
i.e. `C = 2^m (3^p − 2^p)`.  Rank one: a scale `2^m` times the one-run value. -/
theorem survivor_closed_form (m p : Nat) :
    C (List.replicate m false ++ List.replicate p true) + 2 ^ (m + p)
      = 2 ^ m * 3 ^ p := by
  show accC (List.replicate m false ++ List.replicate p true) 0 0 + _ = _
  rw [accC_replicate_false m (List.replicate p true) 0 0]
  have h := accC_replicate_true p (0 + m) 0
  have h0 : (0 : Nat) + m = m := by omega
  rw [h0] at h ⊢
  rw [h]
  have h2 : (0 : Nat) + 2 ^ m = 2 ^ m := by omega
  rw [h2]
  exact Nat.mul_comm _ _

theorem allOdd_replicate : ∀ p : Nat, allOdd (List.replicate p true) := by
  intro p
  induction p with
  | zero => exact trivial
  | succ p ih => exact ⟨rfl, ih⟩

/-- Every survivor is of that shape, and `B` agrees with `C` on it. -/
theorem survivor_zeroOnes (m p : Nat) :
    zeroOnes (List.replicate m false ++ List.replicate p true) := by
  induction m with
  | zero =>
    simp only [List.replicate, List.nil_append]
    cases p with
    | zero => exact trivial
    | succ p =>
      show allOdd (List.replicate p true)
      exact allOdd_replicate p
  | succ m ih => exact ih

end FilterDecomposition
end Collatz
