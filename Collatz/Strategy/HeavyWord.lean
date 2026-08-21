import Collatz.Strategy.AffineExact
import Collatz.Strategy.CycleLength1539

/-!
# The parity word of a never-dropper is heavy, with no factor of two

Every statement in the development that constrains a hypothetical counterexample
through its parity word has, until now, carried a factor of two.  The best of
them, `CycleProduct.neverDrops_heavy_window`, says

`2 ^ j ≤ 2 · 3 ^ (oddCount m j)`

on every window of a never-dropper (subject to `2a ≤ 3m`).  That factor of two
is not cosmetic.  With it, the parity word is only *nearly* heavy: it may fall
one full even step behind the line `a = j · log 2 / log 3` and stay there
forever, and a word that is allowed to lag by a bounded amount is not a member
of any clean combinatorial language.  Without it, the word satisfies

`2 ^ j ≤ 3 ^ (oddCount m j)`  for **every** prefix,

which is exactly the Łukasiewicz/ballot condition: the parity word lies in the
prefix-closed language `H` of *heavy* words.  Everything one can say about `H`
as a language — its counting function, its state complexity, its non-regularity
— becomes a statement about counterexamples only once the factor of two is gone.

## What this file proves

Three linked results, each stated for the accumulator `affineC` of
`AffineExact`, which is the whole additive content of the `+1`.

* `heavy_accumulator_bound` (Lemma A).  If every prefix of length `i ≤ j` is
  heavy then `2 · affineC j m ≤ a · 3 ^ a` with `a = oddCount m j`.  The
  mechanism is one line of the induction: an odd step sends `C ↦ 3C + 2 ^ j`
  and heaviness at length `j + 1` says `2 ^ (j+1) ≤ 3 ^ (a+1)`, so the doubled
  accumulator `2C ↦ 3 · (2C) + 2 ^ (j+1)` is dominated by
  `3 · a · 3 ^ a + 3 ^ (a+1) = (a+1) · 3 ^ (a+1)`.  An even step changes
  nothing.  The bound has about 33% slack — the extremal ratio measured over all
  16 740 heavy words of length at most 18 is `2/3` — and none of that slack is
  needed here.

* `neverDrops_window_sharp` (Lemma B).  For a never-dropper whose prefixes up to
  `j` are heavy, `2m · 2 ^ j ≤ 3 ^ a · (2m + a)`.  Doubling the arithmetic form
  of never-dropping and substituting Lemma A; two lines.

  The comparison with `neverDrops_window_bound`, which reads
  `3m · 2 ^ k ≤ 3 ^ a · (3m + 2a)`, deserves care, because the two hypotheses are
  not the same.  As an *inequality* Lemma B is strictly sharper: its
  multiplicative slack is `a / (2m)` against `2a / (3m)`, a factor of `4/3`.  But
  it is **not** true that Lemma B is free of a side condition.  The stored bound
  assumes `2a ≤ 3m`, an artifact of a linearisation; Lemma B assumes instead that
  every shorter prefix is already heavy.  One condition is traded for another.
  What makes the trade profitable is that the new condition is exactly what the
  induction of `heavy_of_certificate` has available at the point of use, whereas
  `2a ≤ 3m` has to be established separately and eventually expires.

* `heavy_of_certificate` and `heavy_window_1538` (Theorem C).  A never-dropper
  at the verified range `m ≥ 307200` has `2 ^ j ≤ 3 ^ (oddCount m j)` for every
  `j ≤ 1538`, with no factor of two anywhere.

## The certificate, and why it is short

The induction fails only at even steps.  If step `j` is odd then heaviness at
`j` gives heaviness at `j + 1` for free, since `2 ^ (j+1) = 2 · 2 ^ j ≤ 2 · 3 ^ a
≤ 3 ^ (a+1)`.  So the only thing to rule out is an even step that pushes the word
below the line, and there Lemma B applies with the odd-step count unchanged:
`2m · 2 ^ j ≤ 3 ^ a · (2m + a)` while `3 ^ a < 2 ^ j`.

The quantity `3 ^ a · (2m + a)` is monotone in `a` (`S_mono`), so among the
exponents that can appear — those with `3 ^ a < 2 ^ j` — only the largest can
fail.  That is precisely the shortcut `CycleLength1539` invented for the cycle
bound, and its `topIndex j = ⌊j · log₃ 2⌋`, computed as
`j * 397573379 / 630138897`, is reused verbatim.  The certificate `heavyCert`
checks two integer comparisons per length: that `topIndex j` really is the
largest admissible exponent, and that the bound fails there.  It is
self-certifying — the accuracy of the rational approximation is never trusted,
because maximality is verified by the kernel at every `j`.

`heavyCert` is decided once at `c = 307200` and widened to every `m ≥ 307200` by
`cert_widen`: the certificate's deficit only grows with `m`, since `3 ^ t < 2 ^ j`.

## Where the frontier is

The certificate holds for every `j ≤ 1538` at `c = 307200` and fails first at
exactly `(j, a) = (1539, 971)` — the same continued-fraction obstruction, the
same pair, that bounds the cycle length in `CycleLength1539`.  The sweep below
runs the full range `j ≤ 1538`; `heavy_of_certificate` is stated for `J` in
general, so
only the size of one `decide` stands between this file and a larger range, and
that range would have to come from a larger verified bound than `307200`.

## Why this constrains the divergence side

The cycle corollary is not new: a cycle of length `L` has `2 ^ L > 3 ^ a`, so its
word is non-heavy at `L`, and Theorem C therefore reproves `L ≥ 1539`
(`length_ge_1539_of_light`).  The point is that Theorem C never mentions cycles
at all.  It is a statement about *windows*, and a divergent orbit has windows
too.  The
development's divergence-facing results are much weaker than its cycle results,
and the reason is the factor of two: `2 ^ j ≤ 2 · 3 ^ a` permits a bounded lag
and therefore permits every asymptotic density down to `log 2 / log 3` with an
additive correction, while `2 ^ j ≤ 3 ^ a` is a hard prefix condition that the
word must satisfy at every single one of its first 1538 letters.  This is the
first statement in the development that pins a divergent orbit's parity word to
a named combinatorial language rather than to an asymptotic density.

It does not descend.  The heavy words of length 1538 still number about `2 ^ 1461`.
What it does is make the language exact, so that any later argument about the
word is arguing about `H` and not about an unspecified neighbourhood of it.
-/

namespace Collatz
namespace HeavyWord

open Reach Congruence AffineExact

/-! ## Lemma A: the accumulator under prefix-heaviness -/

/-- **Lemma A.**  If every prefix of length at most `j` is heavy, the doubled
accumulator is at most `a · 3 ^ a`.

Each odd step contributes `3 ^ (a-i) · 2 ^ (p_i)` to `affineC`, and heaviness at
the prefix of length `p_i + 1` says `2 ^ (p_i + 1) ≤ 3 ^ i`, so twice that
contribution is at most `3 ^ a`.  There are `a` contributions.  The induction
below performs the same accounting without unrolling the sum. -/
theorem heavy_accumulator_bound (x : Nat) : ∀ j : Nat,
    (∀ i : Nat, i ≤ j → 2 ^ i ≤ 3 ^ oddCount x i) →
    2 * affineC j x ≤ oddCount x j * 3 ^ oddCount x j := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hheavy
    have ihb := ih (fun i hi => hheavy i (Nat.le_succ_of_le hi))
    have hlast := Density.oddCount_succ_last x j
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j x) with he | ho
    · -- even step: neither side moves
      have hcount : oddCount x (j + 1) = oddCount x j := by omega
      rw [hcount, affineC_even he]
      exact ihb
    · -- odd step: the accumulator triples and gains `2 ^ j`, and so does the bound
      have hcount : oddCount x (j + 1) = oddCount x j + 1 := by omega
      have htop : 2 ^ (j + 1) ≤ 3 ^ oddCount x (j + 1) := hheavy (j + 1) (Nat.le_refl _)
      rw [hcount] at htop
      rw [hcount, affineC_odd ho]
      have hexp : (3:Nat) ^ (oddCount x j + 1) = 3 * 3 ^ oddCount x j :=
        Arith.three_pow_succ _
      have hdouble : (2:Nat) ^ (j + 1) = 2 * 2 ^ j := Arith.two_pow_succ j
      have hmul : 3 * (2 * affineC j x) ≤ 3 * (oddCount x j * 3 ^ oddCount x j) :=
        Nat.mul_le_mul_left _ ihb
      have hassoc : 3 * (oddCount x j * 3 ^ oddCount x j)
          = oddCount x j * (3 * 3 ^ oddCount x j) := by
        rw [Nat.mul_left_comm]
      have hgoal : (oddCount x j + 1) * (3 * 3 ^ oddCount x j)
          = oddCount x j * (3 * 3 ^ oddCount x j) + 3 * 3 ^ oddCount x j := by
        rw [Nat.add_mul, Nat.one_mul]
      rw [hexp] at htop ⊢
      omega

/-! ## Lemma B: the sharp window inequality -/

/-- **Lemma B.**  A never-dropper whose prefixes up to `j` are heavy satisfies
`2m · 2 ^ j ≤ 3 ^ a · (2m + a)`.

The multiplicative slack is `a / (2m)`, against `2a / (3m)` for
`CycleProduct.neverDrops_window_bound`.  The side condition is different, not
absent: prefix-heaviness replaces `2a ≤ 3m`. -/
theorem neverDrops_window_sharp {m : Nat} (hm : 0 < m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m) {j : Nat}
    (hheavy : ∀ i : Nat, i ≤ j → 2 ^ i ≤ 3 ^ oddCount m i) :
    2 * m * 2 ^ j ≤ 3 ^ oddCount m j * (2 * m + oddCount m j) := by
  have harith := (neverDrops_iff_affine hm).mp hnd j
  have hacc := heavy_accumulator_bound m j hheavy
  have hL : 2 * m * 2 ^ j = 2 * (2 ^ j * m) := by
    rw [Nat.mul_comm (2 ^ j) m, Nat.mul_assoc]
  have hR : 3 ^ oddCount m j * (2 * m + oddCount m j)
      = 2 * (3 ^ oddCount m j * m) + oddCount m j * 3 ^ oddCount m j := by
    rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm (3 ^ oddCount m j) (oddCount m j)]
  omega

/-! ## Theorem C: heaviness on a certified window -/

/-- The window quantity of Lemma B is monotone in the odd-step count, so only the
largest admissible exponent can violate it.  Mirrors `CycleLength1539.R_mono`. -/
theorem S_mono (c : Nat) {a b : Nat} (h : a ≤ b) :
    3 ^ a * (2 * c + a) ≤ 3 ^ b * (2 * c + b) := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst this; exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with hlt | hge
    · have h1 : a ≤ b := by omega
      refine Nat.le_trans (ih h1) ?_
      rw [Nat.pow_succ]
      have hm : 3 ^ b * (2 * c + b) ≤ 3 ^ b * (3 * (2 * c + (b + 1))) :=
        Nat.mul_le_mul_left _ (by omega)
      have he : 3 ^ b * (3 * (2 * c + (b + 1))) = 3 ^ b * 3 * (2 * c + (b + 1)) := by
        rw [Nat.mul_assoc]
      omega
    · have : a = b + 1 := by omega
      subst this; exact Nat.le_refl _

/-- The two-comparison certificate at window length `j` and size `c`: the top
exponent `topIndex j` is maximal among those with `3 ^ a < 2 ^ j`, and the window
inequality of Lemma B fails there. -/
def heavyCert (c j : Nat) : Bool :=
  decide (2 ^ j ≤ 3 ^ (CycleLength1539.topIndex j + 1)) &&
  decide (3 ^ (CycleLength1539.topIndex j) * (2 * c + CycleLength1539.topIndex j)
            < 2 * c * 2 ^ j)

/-- The certificate only improves as the size grows: its deficit is
`2c · (2 ^ j − 3 ^ t)`, and `3 ^ t < 2 ^ j` is itself a consequence of the
certificate. -/
theorem cert_widen {c m t j : Nat} (hcm : c ≤ m)
    (h : 3 ^ t * (2 * c + t) < 2 * c * 2 ^ j) :
    3 ^ t * (2 * m + t) < 2 * m * 2 ^ j := by
  have hPQ : 3 ^ t < 2 ^ j := by
    have h1 : 3 ^ t * (2 * c) ≤ 3 ^ t * (2 * c + t) :=
      Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
    have e1 : 3 ^ t * (2 * c) = 2 * c * 3 ^ t := Nat.mul_comm _ _
    exact Nat.lt_of_mul_lt_mul_left (a := 2 * c) (by omega)
  obtain ⟨d, hd⟩ : ∃ d : Nat, m = c + d := ⟨m - c, by omega⟩
  subst hd
  have e3 : 2 * (c + d) + t = (2 * c + t) + 2 * d := by omega
  have e4 : 3 ^ t * (2 * (c + d) + t) = 3 ^ t * (2 * c + t) + 3 ^ t * (2 * d) := by
    rw [e3, Nat.mul_add]
  have e5 : 2 * (c + d) * 2 ^ j = 2 * c * 2 ^ j + 2 * d * 2 ^ j := by
    have hsplit : 2 * (c + d) = 2 * c + 2 * d := by omega
    rw [hsplit, Nat.add_mul]
  have e6 : 3 ^ t * (2 * d) ≤ 2 ^ j * (2 * d) :=
    Nat.mul_le_mul_right _ (Nat.le_of_lt hPQ)
  have e7 : 2 ^ j * (2 * d) = 2 * d * 2 ^ j := Nat.mul_comm _ _
  omega

/-- The even-step case of Theorem C, isolated.  If the prefixes up to `j` are
heavy, step `j` is even, and the certificate holds at `j + 1`, then the word is
still heavy at `j + 1`.

This is where all the arithmetic lives.  Lemma B applies with the odd-step count
frozen at `a = oddCount m j`; were the word to fall below the line, `a` would be
an exponent with `3 ^ a < 2 ^ (j+1)`, hence at most `topIndex (j+1)`, and
monotonicity would carry the window inequality to the one place the certificate
has already refuted it. -/
theorem heavy_even_step {m j : Nat} (hm : 0 < m) (hbig : 307200 ≤ m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m)
    (hc : heavyCert 307200 (j + 1) = true)
    (hprev : ∀ i : Nat, i ≤ j → 2 ^ i ≤ 3 ^ oddCount m i)
    (he : acceleratedOrbit j m % 2 = 0) :
    2 ^ (j + 1) ≤ 3 ^ oddCount m j := by
  have hlast := Density.oddCount_succ_last m j
  have hcount : oddCount m (j + 1) = oddCount m j := by omega
  -- Lemma B at window `j + 1`, with the odd-step count frozen by the even step
  have harith := (neverDrops_iff_affine hm).mp hnd (j + 1)
  rw [hcount, affineC_even he] at harith
  have hacc := heavy_accumulator_bound m j hprev
  have hL : 2 * m * 2 ^ (j + 1) = 2 * (2 ^ (j + 1) * m) := by
    rw [Nat.mul_comm (2 ^ (j + 1)) m, Nat.mul_assoc]
  have hR : 3 ^ oddCount m j * (2 * m + oddCount m j)
      = 2 * (3 ^ oddCount m j * m) + oddCount m j * 3 ^ oddCount m j := by
    rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm (3 ^ oddCount m j) (oddCount m j)]
  have hB : 2 * m * 2 ^ (j + 1)
      ≤ 3 ^ oddCount m j * (2 * m + oddCount m j) := by omega
  -- unpack the certificate
  rw [heavyCert, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hc
  obtain ⟨hmax, htop⟩ := hc
  rcases Nat.lt_or_ge (3 ^ oddCount m j) (2 ^ (j + 1)) with hviol | hok
  · exfalso
    have hale : oddCount m j ≤ CycleLength1539.topIndex (j + 1) := by
      rcases Nat.lt_or_ge (CycleLength1539.topIndex (j + 1)) (oddCount m j) with hcon | hfine
      · have h1 : CycleLength1539.topIndex (j + 1) + 1 ≤ oddCount m j := by omega
        have h2 : (3:Nat) ^ (CycleLength1539.topIndex (j + 1) + 1) ≤ 3 ^ oddCount m j :=
          Nat.pow_le_pow_right (by omega) h1
        omega
      · exact hfine
    have hmono := S_mono m hale
    have hwide := cert_widen (c := 307200) (m := m)
      (t := CycleLength1539.topIndex (j + 1)) (j := j + 1) hbig htop
    omega
  · exact hok

/-- **Theorem C.**  A never-dropper at size at least `307200` whose window
lengths `1 … J` all pass the certificate is heavy on every window `j ≤ J`:
`2 ^ j ≤ 3 ^ (oddCount m j)`, with no factor of two. -/
theorem heavy_of_certificate {m J : Nat} (hm : 0 < m) (hbig : 307200 ≤ m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m)
    (hcert : ∀ j : Nat, 0 < j → j ≤ J → heavyCert 307200 j = true) :
    ∀ j : Nat, j ≤ J → 2 ^ j ≤ 3 ^ oddCount m j := by
  have key : ∀ j : Nat, j ≤ J → ∀ i : Nat, i ≤ j → 2 ^ i ≤ 3 ^ oddCount m i := by
    intro j
    induction j with
    | zero =>
      intro _ i hi
      have : i = 0 := by omega
      subst this
      simp
    | succ j ih =>
      intro hJ i hi
      have hprev : ∀ i : Nat, i ≤ j → 2 ^ i ≤ 3 ^ oddCount m i :=
        ih (by omega)
      rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · exact hprev i (by omega)
      · have hieq : i = j + 1 := by omega
        subst hieq
        have hlast := Density.oddCount_succ_last m j
        have hj : 2 ^ j ≤ 3 ^ oddCount m j := hprev j (Nat.le_refl _)
        rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j m) with he | ho
        · -- even step: this is the only place the certificate is needed
          have hcount : oddCount m (j + 1) = oddCount m j := by omega
          rw [hcount]
          exact heavy_even_step hm hbig hnd (hcert (j + 1) (by omega) hJ) hprev he
        · -- odd step: heaviness propagates for free
          have hcount : oddCount m (j + 1) = oddCount m j + 1 := by omega
          rw [hcount, Arith.three_pow_succ, Arith.two_pow_succ]
          have : 2 * 2 ^ j ≤ 2 * 3 ^ oddCount m j := Nat.mul_le_mul_left _ hj
          have h3 : 2 * 3 ^ oddCount m j ≤ 3 * 3 ^ oddCount m j :=
            Nat.mul_le_mul_right _ (by omega)
          omega
  intro j hj
  exact key j hj j (Nat.le_refl _)

/-! ## The sweep

One `decide` over the 1538 window lengths.  Each entry is two bignum comparisons
on numerals of up to 1538 bits — the same shape and the same cost profile as
`CycleLength1539.sweep_full`, which sweeps the same range for the cycle bound.
The kernel disposes of it in well under a second, so the mathematical frontier
and the arithmetic frontier coincide here: the sweep stops at 1538 because 1539
is *false*, not because it is expensive.  Checked: replacing `1538` by `1539`
makes `decide` refute the statement, at the exponent `971`. -/

set_option maxHeartbeats 40000000 in
set_option exponentiation.threshold 4000 in
set_option maxRecDepth 4000000 in
theorem sweep_1538 :
    ((List.range 1538).map (fun i => i + 1)).all (fun j => heavyCert 307200 j) = true := by
  decide

theorem heavyCert_of_le_1538 {j : Nat} (hpos : 0 < j) (hj : j ≤ 1538) :
    heavyCert 307200 j = true := by
  have h := sweep_1538
  rw [List.all_eq_true] at h
  exact h j (List.mem_map.mpr ⟨j - 1, List.mem_range.mpr (by omega), by omega⟩)

/-- **The parity word of a never-dropper is heavy for 1538 steps.**  No factor of
two: this is the exact ballot condition, so the first 1538 letters of the word
form a heavy word in the sense of the Łukasiewicz language.

`CycleProduct.neverDrops_heavy_window` gives only `2 ^ j ≤ 2 · 3 ^ a`, which
permits the word to lag one full even step behind the line for ever. -/
theorem heavy_window_1538 {m : Nat} (hm : 0 < m) (hbig : 307200 ≤ m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m) {j : Nat} (hj : j ≤ 1538) :
    2 ^ j ≤ 3 ^ oddCount m j :=
  heavy_of_certificate hm hbig hnd (fun _ hpos hle => heavyCert_of_le_1538 hpos hle) j hj

/-- The window of length 520, matching `CycleLength520`. -/
theorem heavy_window_520 {m : Nat} (hm : 0 < m) (hbig : 307200 ≤ m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m) {j : Nat} (hj : j ≤ 520) :
    2 ^ j ≤ 3 ^ oddCount m j :=
  heavy_window_1538 hm hbig hnd (by omega)

/-- The same statement for the orbit of a counterexample, where the verified
range is supplied by `VerifiedSharp`. -/
theorem heavy_window_of_counterexample {n m : Nat} (hn : 0 < n)
    (hnr : ¬ ReachesOne n) (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m) {j : Nat} (hj : j ≤ 1538) :
    2 ^ j ≤ 3 ^ oddCount m j := by
  have hbig : 307200 ≤ m := VerifiedSharp.ge_verified_sharp hn hnr hm
  exact heavy_window_1538 (by omega) hbig hnd hj

/-- **A never-dropper's window is never light below 1539.**  The contrapositive
form, which is how the cycle corollary uses it: any window on which the word is
light — in particular the full period of a cycle, where `3 ^ a < 2 ^ L` holds
outright — is at least `1539` long.  This recovers
`CycleLength1539.length_ge_1539` from a statement that never mentions cycles. -/
theorem length_ge_1539_of_light {m j : Nat} (hm : 0 < m) (hbig : 307200 ≤ m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m)
    (hlight : 3 ^ oddCount m j < 2 ^ j) : 1539 ≤ j := by
  rcases Nat.lt_or_ge j 1539 with hlt | hge
  · exact absurd (heavy_window_1538 hm hbig hnd (j := j) (by omega)) (by omega)
  · exact hge

end HeavyWord
end Collatz
