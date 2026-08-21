import Collatz.Strategy.RealizableBound

/-!
# The Beatty word is the simultaneous extremiser

Two extremal problems over heavy parity words were observed, empirically, to have
the *same* answer:

* **maximise the accumulator** `C = Σ_{i<a} 3 ^ (a−1−i) · 2 ^ (t i)` over heavy
  words with `a` odd steps — the maximum is `RealizableBound.Bcap a` on the nose;
* **minimise the spread** `max_j 3 ^ (oddCount j) / 2 ^ j` over the same set.

This file explains the coincidence, and it is not a coincidence: the heavy words
with `a` odd steps form a *box* in the odd-step-time coordinates,

`heavy  ⟹  t i ≤ fexp i  for every i < a`         (`heavy_le_fexp`)

— **one direction only.**  An earlier version of this header wrote `⟺`, and the
converse is false: `a = 1`, `t₀ = 0`, `J = 2` (the word `100`) lies in the box
(`t₀ = 0 = fexp 0`) but is not heavy, since `2² = 4 > 3 = 3¹`.  The exact statement
is

`heavy on [0, J]  ⟺  (∀ i < a, t i ≤ fexp i)  ∧  2^J ≤ 3^a`,

the missing conjunct being the endpoint.  The box picture is therefore valid **on
the ledge** `L = fexp a + 1`, where `2^(L−1) ≤ 3^a` holds automatically, and only
there.  Measured: at ledge pairs the box count and the true proper-prefix-heavy
count agree exactly (`a = 1..12`: 1, 1, 2, 3, 7, 12, 30, 85, 173, 476, 961, 2652);
at `L = fexp a + 3` the box counts the same numbers while the true count is **zero**
in every case.

`fexp i = ⌊i log₂ 3⌋`, and the Beatty word `t = fexp` is its unique maximal
corner.  The accumulator is strictly increasing in every coordinate
(`Cw_strict`), so it is maximised exactly at the corner; the prefix odd-count
profile is *antitone* in every coordinate (`cnt_anti`), so it is pointwise
minimised at the same corner, and pointwise minimality of the profile implies
minimality of every monotone functional of the profile — the spread among them
(`spread_min`).  One corner, two extremal problems, because the two objectives
are monotone in opposite directions along the *same* partial order and the box
has a top element.

Nothing here is d-specific: the whole file is a statement about words, and
`C(w, d) = d · C(w, 1)`, so by the Round III soundness filter it can obstruct
nothing by itself.  It is recorded as structure, and because it pins the
equality case of `affineC_le_Bcap` exactly.

## The equality case, and why it does not become a mechanism

`Cw_eq_Bcap_iff` says `C = Bcap a` **iff** the word's odd-step times are
`⌊i log₂ 3⌋` — it pins `t i` for `i < a` only, so trailing even letters, and hence
the length, are not determined.  So a
cycle word achieving the ceiling would be completely explicit, and one could
simply read off `gcd(C, G)`.  Computationally (a ≤ 3000, ledge pairs
`L = ⌊a log₂ 3⌋ + 1`): `gcd(Bcap a, 2 ^ L − 3 ^ a) = 1` for 2646 of the 3000
values, and the largest gcd anywhere in the range is `22139` at `a = 2773`,
against a gap of about `2 ^ 4397`.  The Beatty word is never a cycle word.

That is worthless as a mechanism, because a cycle word is **not** forced to be
near-extremal.  On a cycle `C = G · m` with `m` the minimum, so
`C / Bcap a = G · m / Bcap a ≥ G · 1086464 / Bcap a`; that lower bound exceeds
one exactly for `a < 4296`, which is the frontier already known
(`RealizableFrontier6809`), and past the frontier it decays: over the 247
surviving `a ≤ 40000` its median is `0.494` and its minimum `0.0053`.  A word
with `C` half the ceiling is nowhere near the corner, so no structural
consequence of extremality transfers.  Stated plainly: **the near-extremality
premise is false, and this route closes nothing.**
-/

namespace Collatz
namespace ExtremalWord

open RealizableBound

/-! ## Words as odd-step times -/

/-- The accumulator of the word whose `i`-th odd step happens at time `t i`:
`Cw t a = Σ_{i<a} 3 ^ (a−1−i) · 2 ^ (t i)`, written as the same Horner recursion
that `affineC` and `Bcap` use. -/
def Cw (t : Nat → Nat) : Nat → Nat
  | 0 => 0
  | a + 1 => 3 * Cw t a + 2 ^ t a

@[simp] theorem Cw_zero (t : Nat → Nat) : Cw t 0 = 0 := rfl

theorem Cw_succ (t : Nat → Nat) (a : Nat) :
    Cw t (a + 1) = 3 * Cw t a + 2 ^ t a := rfl

/-- The number of odd steps strictly before time `j`, for a word with `a` odd
steps at times `t 0, …, t (a−1)`. -/
def cnt (t : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | a + 1, j => cnt t a j + (if t a < j then 1 else 0)

@[simp] theorem cnt_zero (t : Nat → Nat) (j : Nat) : cnt t 0 j = 0 := rfl

theorem cnt_succ (t : Nat → Nat) (a j : Nat) :
    cnt t (a + 1) j = cnt t a j + (if t a < j then 1 else 0) := rfl

/-- The Beatty word: its `i`-th odd step is at time `⌊i log₂ 3⌋`. -/
theorem Cw_fexp (a : Nat) : Cw fexp a = Bcap a := by
  induction a with
  | zero => rfl
  | succ a ih => rw [Cw_succ, Bcap_succ, ih]

/-! ## Monotonicity of the accumulator in the odd-step times -/

theorem Cw_le (t s : Nat → Nat) :
    ∀ a : Nat, (∀ i : Nat, i < a → t i ≤ s i) → Cw t a ≤ Cw s a := by
  intro a
  induction a with
  | zero => intro _; exact Nat.le_refl _
  | succ a ih =>
    intro h
    have h1 : Cw t a ≤ Cw s a := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have h2 : (2:Nat) ^ t a ≤ 2 ^ s a :=
      Arith.two_pow_le_two_pow (h a (Nat.lt_succ_self a))
    rw [Cw_succ, Cw_succ]
    omega

/-- **Strict** monotonicity: one coordinate strictly below already costs
strictly.  This is what pins the equality case. -/
theorem Cw_strict (t s : Nat → Nat) :
    ∀ a k : Nat, k < a → (∀ i : Nat, i < a → t i ≤ s i) → t k < s k →
      Cw t a < Cw s a := by
  intro a
  induction a with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ a ih =>
    intro k hk h hlt
    have hle : ∀ i : Nat, i < a → t i ≤ s i := fun i hi => h i (Nat.lt_succ_of_lt hi)
    have hbase : Cw t a ≤ Cw s a := Cw_le t s a hle
    have hlast : (2:Nat) ^ t a ≤ 2 ^ s a :=
      Arith.two_pow_le_two_pow (h a (Nat.lt_succ_self a))
    rw [Cw_succ, Cw_succ]
    rcases Nat.lt_or_ge k a with hka | hka
    · have := ih k hka hle hlt
      omega
    · have hka' : k = a := by omega
      have hs : (2:Nat) ^ t a < 2 ^ s a := by
        rw [← hka']; exact Arith.two_pow_lt_two_pow hlt
      omega

/-! ## Heaviness is exactly the box `t i ≤ fexp i` -/

/-- Strict increase of the odd-step times, the only shape hypothesis a word
carries. -/
def StrictInc (t : Nat → Nat) : Prop := ∀ i : Nat, t i < t (i + 1)

theorem strictInc_mono {t : Nat → Nat} (h : StrictInc t) :
    ∀ i j : Nat, i < j → t i < t j := by
  intro i j
  induction j with
  | zero => intro hij; exact absurd hij (Nat.not_lt_zero i)
  | succ j ih =>
    intro hij
    rcases Nat.lt_or_ge i j with hlt | hge
    · exact Nat.lt_trans (ih hlt) (h j)
    · have : i = j := by omega
      rw [this]; exact h j

theorem cnt_all_lt {t : Nat → Nat} {j : Nat} :
    ∀ a : Nat, (∀ k : Nat, k < a → t k < j) → cnt t a j = a := by
  intro a
  induction a with
  | zero => intro _; rfl
  | succ a ih =>
    intro h
    have h1 : cnt t a j = a := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
    rw [cnt_succ, h1, if_pos (h a (Nat.lt_succ_self a))]

/-- At the time of its own `i`-th odd step, a word with strictly increasing
odd-step times has seen exactly `i` odd steps. -/
theorem cnt_at_time {t : Nat → Nat} (hst : StrictInc t) :
    ∀ a i : Nat, i < a → cnt t a (t i) = i := by
  intro a
  induction a with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ a ih =>
    intro i hi
    rcases Nat.lt_or_ge i a with hia | hia
    · have hno : ¬ (t a < t i) := by
        have := strictInc_mono hst i a hia; omega
      rw [cnt_succ, if_neg hno, ih i hia]
      omega
    · have hia' : i = a := by omega
      subst hia'
      have hno : ¬ (t i < t i) := Nat.lt_irrefl _
      have hall : cnt t i (t i) = i :=
        cnt_all_lt i (fun k hk => strictInc_mono hst k i hk)
      rw [cnt_succ, if_neg hno, hall]
      omega

/-- **Heaviness implies the box** (the converse needs the endpoint `2^J ≤ 3^a`; see
the header).  If every prefix up to `J` is heavy and the word's
odd steps all happen by time `J`, then `t i ≤ fexp i` for every `i`: the word
lies in the box whose top corner is the Beatty word. -/
theorem heavy_le_fexp {t : Nat → Nat} (hst : StrictInc t) {a J : Nat}
    (hheavy : ∀ j : Nat, j ≤ J → 2 ^ j ≤ 3 ^ cnt t a j)
    (hlast : ∀ i : Nat, i < a → t i ≤ J) :
    ∀ i : Nat, i < a → t i ≤ fexp i := by
  intro i hi
  have h1 : (2:Nat) ^ t i ≤ 3 ^ cnt t a (t i) := hheavy (t i) (hlast i hi)
  rw [cnt_at_time hst a i hi] at h1
  exact le_fexp_of_pow_le h1

/-! ## The Beatty word is heavy, and is the corner -/

theorem fexp_strictInc : StrictInc fexp := by
  intro i
  rw [fexp]
  by_cases hc : 2 ^ (fexp i + 2) ≤ 3 ^ (i + 1) <;> simp [hc]

/-! ## The two extremal theorems -/

/-- **Maximisation.**  Every heavy word's accumulator is at most `Bcap a`, and
this is `affineC_le_Bcap` in word coordinates, with no verified range used. -/
theorem Cw_le_Bcap {t : Nat → Nat} (hst : StrictInc t) {a J : Nat}
    (hheavy : ∀ j : Nat, j ≤ J → 2 ^ j ≤ 3 ^ cnt t a j)
    (hlast : ∀ i : Nat, i < a → t i ≤ J) :
    Cw t a ≤ Bcap a := by
  rw [← Cw_fexp]
  exact Cw_le t fexp a (heavy_le_fexp hst hheavy hlast)

/-- **The equality case, exactly.**  A word in the box attains the ceiling if and
only if it *is* the Beatty word. -/
theorem Cw_eq_Bcap_iff {t : Nat → Nat} {a : Nat}
    (hbox : ∀ i : Nat, i < a → t i ≤ fexp i) :
    Cw t a = Bcap a ↔ ∀ i : Nat, i < a → t i = fexp i := by
  constructor
  · intro heq i hi
    rcases Nat.lt_or_ge (t i) (fexp i) with hlt | hge
    · have := Cw_strict t fexp a i hi hbox hlt
      rw [Cw_fexp] at this
      omega
    · have := hbox i hi
      omega
  · intro h
    rw [← Cw_fexp]
    have h1 : Cw t a ≤ Cw fexp a := Cw_le t fexp a (fun i hi => Nat.le_of_eq (h i hi))
    have h2 : Cw fexp a ≤ Cw t a := Cw_le fexp t a (fun i hi => Nat.le_of_eq (h i hi).symm)
    omega

/-- **Minimisation.**  The prefix odd-count profile is antitone in the odd-step
times, so the top corner of the box has the pointwise *smallest* profile. -/
theorem cnt_anti {t s : Nat → Nat} :
    ∀ a j : Nat, (∀ i : Nat, i < a → t i ≤ s i) → cnt s a j ≤ cnt t a j := by
  intro a
  induction a with
  | zero => intro j _; exact Nat.le_refl _
  | succ a ih =>
    intro j h
    have h1 : cnt s a j ≤ cnt t a j := ih j (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hstep : (if s a < j then 1 else 0) ≤ (if t a < j then 1 else 0) := by
      by_cases hs : s a < j
      · have ht : t a < j := Nat.lt_of_le_of_lt (h a (Nat.lt_succ_self a)) hs
        simp [hs, ht]
      · simp [hs]
    rw [cnt_succ, cnt_succ]
    omega

/-- The Beatty profile is pointwise minimal among heavy words. -/
theorem beatty_profile_min {t : Nat → Nat} {a : Nat}
    (hbox : ∀ i : Nat, i < a → t i ≤ fexp i) (j : Nat) :
    cnt fexp a j ≤ cnt t a j :=
  cnt_anti a j hbox

/-- **The spread is minimised at the same corner.**  Any uniform bound
`3 ^ (oddCount j) ≤ q · 2 ^ j` — i.e. any ceiling on the spread — that some heavy
word satisfies at a time `j`, the Beatty word satisfies at `j` too.  Since this
holds at every `j`, the Beatty word's maximal spread is minimal. -/
theorem spread_min {t : Nat → Nat} {a : Nat}
    (hbox : ∀ i : Nat, i < a → t i ≤ fexp i) (j q : Nat)
    (h : 3 ^ cnt t a j ≤ q * 2 ^ j) :
    3 ^ cnt fexp a j ≤ q * 2 ^ j :=
  Nat.le_trans (Arith.three_pow_le_three_pow (beatty_profile_min hbox j)) h

/-- **The simultaneous-extremiser theorem.**  For heavy words with `a` odd steps
the Beatty word `t = fexp` maximises the accumulator and minimises the spread,
and it is the unique accumulator-maximiser. -/
theorem beatty_simultaneous {t : Nat → Nat} (hst : StrictInc t) {a J : Nat}
    (hheavy : ∀ j : Nat, j ≤ J → 2 ^ j ≤ 3 ^ cnt t a j)
    (hlast : ∀ i : Nat, i < a → t i ≤ J) :
    Cw t a ≤ Cw fexp a ∧ (∀ j : Nat, cnt fexp a j ≤ cnt t a j) ∧
      (Cw t a = Cw fexp a → ∀ i : Nat, i < a → t i = fexp i) := by
  have hbox := heavy_le_fexp hst hheavy hlast
  refine ⟨Cw_le t fexp a hbox, fun j => beatty_profile_min hbox j, ?_⟩
  intro heq
  rw [Cw_fexp] at heq
  exact (Cw_eq_Bcap_iff hbox).1 heq

end ExtremalWord
end Collatz

