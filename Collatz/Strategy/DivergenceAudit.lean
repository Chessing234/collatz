import Collatz.Structure.Divergence
import Collatz.Search.Sieved
import Collatz.Strategy.Escape

/-!
# Audit of the "divergence = distinctness = escape" chain

Round X's foundational claim is:

> for a deterministic map on `ℕ`: orbit unbounded ⟺ never repeats a value ⟺ all
> values distinct ⟺ `x_n → ∞`; hence a divergent orbit visits `[1, B]` at most
> `B + 1` times.

This file settles three questions about it.

**1. It is true.**  All four conditions are equivalent.

**2. It has no Collatz content whatsoever.**  Everything here is proved for an
*arbitrary* `f : ℕ → ℕ` — `iter_unbounded_iff_distinct`,
`tendsto_of_distinct`, `distinct_of_unbounded`.  The Collatz statements are
one-line instances at `f = step`.  A statement that holds for every self-map of
`ℕ` cannot separate Collatz from anything, so it cannot be a component of a
divergence *filter*: it does not distinguish `3x+1` from `x ↦ x+1`.

**3. The constant `B + 1` is wrong.**  `visits_le` proves the sharp bound: an
orbit with distinct values visits a window `[m, B]` at most `B - m + 1` times.
For `[1, B]` that is `B`, not `B + 1`.

And the Collatz-specific bound is far better than either, by a theorem already
in the development: `divergent_avoids_verified`, an immediate corollary of
`Search.reachesOne_of_lt_102400`, says a divergent orbit visits `[1, 102399]`
**zero** times.  So at every `B` the Lean development can currently speak about,
the true visit count is `0` and the proposed bound is `B + 1`.
-/

namespace Collatz
namespace DivergenceAudit

open Reach Divergence

/-! ## Iteration of an arbitrary map -/

/-- Iterating an arbitrary `f : ℕ → ℕ`. -/
def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | k + 1, x => f (iter f k x)

theorem iter_add (f : Nat → Nat) (j k x : Nat) :
    iter f (j + k) x = iter f j (iter f k x) := by
  induction j with
  | zero =>
    have h0 : 0 + k = k := by omega
    rw [h0]
    rfl
  | succ j ih =>
    have hidx : j + 1 + k = (j + k) + 1 := by omega
    rw [hidx]
    show f (iter f (j + k) x) = f (iter f j (iter f k x))
    rw [ih]

/-- The running maximum of an arbitrary iteration. -/
def maxTo (f : Nat → Nat) (x : Nat) : Nat → Nat
  | 0 => x
  | k + 1 => max (maxTo f x k) (iter f (k + 1) x)

theorem le_maxTo (f : Nat → Nat) (x : Nat) {i k : Nat} (hi : i ≤ k) :
    iter f i x ≤ maxTo f x k := by
  induction k with
  | zero =>
    have : i = 0 := by omega
    rw [this]
    exact Nat.le_refl _
  | succ k ih =>
    by_cases h : i ≤ k
    · exact Nat.le_trans (ih h) (Nat.le_max_left _ _)
    · have hik : i = k + 1 := by omega
      rw [hik]
      exact Nat.le_max_right _ _

/-! ## The three conditions -/

/-- The orbit of `x` under `f` is unbounded. -/
def IterUnbounded (f : Nat → Nat) (x : Nat) : Prop := ∀ B : Nat, ∃ i : Nat, B < iter f i x

/-- The orbit of `x` under `f` never repeats a value. -/
def IterDistinct (f : Nat → Nat) (x : Nat) : Prop :=
  ∀ i j : Nat, i < j → iter f i x ≠ iter f j x

/-- The orbit of `x` under `f` escapes every window permanently. -/
def IterTendsto (f : Nat → Nat) (x : Nat) : Prop :=
  ∀ B : Nat, ∃ N : Nat, ∀ k : Nat, N ≤ k → B < iter f k x

/-! ## unbounded ⇒ distinct -/

/-- A repeat makes every later value equal to an early one. -/
theorem exists_le_of_repeat {f : Nat → Nat} {x i p : Nat} (hp : 0 < p)
    (hrep : iter f (i + p) x = iter f i x) (t : Nat) :
    ∃ s : Nat, s ≤ i + p ∧ iter f t x = iter f s x := by
  have key : ∀ q t : Nat, t ≤ i + p + q → ∃ s : Nat, s ≤ i + p ∧ iter f t x = iter f s x := by
    intro q
    induction q with
    | zero => intro t ht; exact ⟨t, by omega, rfl⟩
    | succ q ih =>
      intro t ht
      by_cases h : t ≤ i + p + q
      · exact ih t h
      · have hbig : i + p < t := by omega
        have hsplit : t = (t - p - i) + (i + p) := by omega
        have hstep : iter f t x = iter f (t - p) x := by
          calc iter f t x
              = iter f ((t - p - i) + (i + p)) x := by rw [← hsplit]
            _ = iter f (t - p - i) (iter f (i + p) x) := iter_add _ _ _ _
            _ = iter f (t - p - i) (iter f i x) := by rw [hrep]
            _ = iter f ((t - p - i) + i) x := (iter_add _ _ _ _).symm
            _ = iter f (t - p) x := by
                have : (t - p - i) + i = t - p := by omega
                rw [this]
        obtain ⟨s, hs, heq⟩ := ih (t - p) (by omega)
        exact ⟨s, hs, by rw [hstep, heq]⟩
  exact key t t (by omega)

/-- **Unbounded orbits never repeat.**  True for every `f : ℕ → ℕ`. -/
theorem distinct_of_unbounded {f : Nat → Nat} {x : Nat} (h : IterUnbounded f x) :
    IterDistinct f x := by
  intro i j hij heq
  have hrep : iter f (i + (j - i)) x = iter f i x := by
    have : i + (j - i) = j := by omega
    rw [this, heq]
  obtain ⟨k, hk⟩ := h (maxTo f x (i + (j - i)))
  obtain ⟨s, hs, hks⟩ := exists_le_of_repeat (by omega : 0 < j - i) hrep k
  rw [hks] at hk
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hk (le_maxTo f x hs))

/-! ## distinct ⇒ escapes permanently -/

/-- **Distinct values force permanent escape.**  True for every `f : ℕ → ℕ`. -/
theorem tendsto_of_distinct {f : Nat → Nat} {x : Nat} (h : IterDistinct f x) :
    IterTendsto f x := by
  intro B
  refine Classical.byContradiction ?_
  intro hno
  have hstep : ∀ N : Nat, ∃ k : Nat, N < k ∧ iter f k x ≤ B := by
    intro N
    have h1 : ¬ ∀ k : Nat, N + 1 ≤ k → B < iter f k x := fun hc => hno ⟨N + 1, hc⟩
    refine Classical.byContradiction ?_
    intro h2
    exact h1 (fun k hk => Nat.lt_of_not_le (fun hc => h2 ⟨k, by omega, hc⟩))
  let nxt : Nat → Nat := fun N => Classical.choose (hstep N)
  have hnxt : ∀ N : Nat, N < nxt N ∧ iter f (nxt N) x ≤ B :=
    fun N => Classical.choose_spec (hstep N)
  let seq : Nat → Nat := fun t => Nat.rec (nxt 0) (fun _ s => nxt s) t
  have hseq_lt : ∀ t : Nat, seq t < seq (t + 1) := fun t => (hnxt (seq t)).1
  have hseq_val : ∀ t : Nat, iter f (seq t) x ≤ B := by
    intro t
    cases t with
    | zero => exact (hnxt 0).2
    | succ t => exact (hnxt (seq t)).2
  have hmono : ∀ s t : Nat, s < t → seq s < seq t := by
    intro s t hst
    induction t with
    | zero => omega
    | succ t ih =>
      by_cases hs : s < t
      · exact Nat.lt_trans (ih hs) (hseq_lt t)
      · have : s = t := by omega
        rw [this]
        exact hseq_lt t
  obtain ⟨u, v, huv, _, hfuv⟩ :=
    Pigeonhole.exists_repeat (f := fun t => iter f (seq t) x) (B := B + 1) (N := B + 1)
      (fun t _ => Nat.lt_succ_of_le (hseq_val t)) (Nat.le_refl _)
  exact h (seq u) (seq v) (hmono u v huv) hfuv

/-- **Permanent escape ⇒ unbounded.**  True for every `f : ℕ → ℕ`. -/
theorem unbounded_of_tendsto {f : Nat → Nat} {x : Nat} (h : IterTendsto f x) :
    IterUnbounded f x := by
  intro B
  obtain ⟨N, hN⟩ := h B
  exact ⟨N, hN N (Nat.le_refl _)⟩

/-- **The chain closes, for an arbitrary self-map of `ℕ`.**  This is the whole
content of the Round X foundational claim: it mentions no Collatz-specific
structure and holds for `x ↦ x + 1` verbatim. -/
theorem unbounded_iff_distinct {f : Nat → Nat} {x : Nat} :
    IterUnbounded f x ↔ IterDistinct f x := by
  constructor
  · exact distinct_of_unbounded
  · intro h; exact unbounded_of_tendsto (tendsto_of_distinct h)

theorem unbounded_iff_tendsto {f : Nat → Nat} {x : Nat} :
    IterUnbounded f x ↔ IterTendsto f x := by
  constructor
  · intro h; exact tendsto_of_distinct (distinct_of_unbounded h)
  · exact unbounded_of_tendsto

/-! ## The sharp visit count -/

/-- **The sharp window bound.**  If the orbit values are distinct, there is no
strictly increasing family of `B - m + 2` indices whose values all lie in
`[m, B]`.  Equivalently: the orbit visits `[m, B]` at most `B - m + 1` times.
Taking `m = 1` gives `B`, not `B + 1`. -/
theorem visits_le {f : Nat → Nat} {x m B : Nat} (h : IterDistinct f x)
    (idx : Nat → Nat) (hmono : ∀ s t : Nat, s < t → idx s < idx t)
    (hwin : ∀ t : Nat, t ≤ B - m + 1 → m ≤ iter f (idx t) x ∧ iter f (idx t) x ≤ B) :
    False := by
  obtain ⟨u, v, huv, hvN, hfuv⟩ :=
    Pigeonhole.exists_repeat (f := fun t => iter f (idx t) x - m)
      (B := B - m + 1) (N := B - m + 1)
      (fun t ht => by
        obtain ⟨h1, h2⟩ := hwin t ht
        omega)
      (Nat.le_refl _)
  have hu := hwin u (by omega)
  have hv := hwin v hvN
  exact h (idx u) (idx v) (hmono u v huv) (by omega)

/-! ## The Collatz instances -/

/-- The Collatz orbit is an instance of `iter`. -/
theorem iter_step (k n : Nat) : iter step k n = orbit k n := by
  induction k with
  | zero => rfl
  | succ k ih =>
    calc iter step (k + 1) n
        = step (iter step k n) := rfl
      _ = step (orbit k n) := by rw [ih]
      _ = orbit 1 (orbit k n) := rfl
      _ = orbit (1 + k) n := (orbit_add 1 k n).symm
      _ = orbit (k + 1) n := by rw [Nat.add_comm]

/-- A divergent Collatz orbit has distinct values — an instance of a theorem
about arbitrary self-maps of `ℕ`. -/
theorem divergent_distinct {n : Nat} (h : Divergent n) :
    ∀ i j : Nat, i < j → orbit i n ≠ orbit j n := by
  have hu : IterUnbounded step n := by
    intro B
    obtain ⟨i, hi⟩ := h B
    exact ⟨i, by rw [iter_step]; exact hi⟩
  intro i j hij heq
  refine distinct_of_unbounded hu i j hij ?_
  rw [iter_step, iter_step]
  exact heq

/-- A divergent Collatz orbit escapes every window permanently. -/
theorem divergent_tendsto {n : Nat} (h : Divergent n) :
    ∀ B : Nat, ∃ N : Nat, ∀ k : Nat, N ≤ k → B < orbit k n := by
  intro B
  have hu : IterUnbounded step n := by
    intro B'
    obtain ⟨i, hi⟩ := h B'
    exact ⟨i, by rw [iter_step]; exact hi⟩
  obtain ⟨N, hN⟩ := tendsto_of_distinct (distinct_of_unbounded hu) B
  exact ⟨N, fun k hk => by rw [← iter_step]; exact hN k hk⟩

/-- **The bound that actually matters, and it was already in the development.**
A divergent orbit visits `[1, 102399]` exactly `0` times, because every positive
integer below `102400` reaches `1`.  Compare the proposed bound `B + 1`, which
at `B = 102399` reads `102400`. -/
theorem divergent_avoids_verified {n : Nat} (hn : 0 < n) (h : Divergent n) (k : Nat) :
    102400 ≤ orbit k n := by
  refine Classical.byContradiction ?_
  intro hlt
  have hpos : 0 < orbit k n := orbit_positive hn k
  have hreach : ReachesOne (orbit k n) :=
    Search.reachesOne_of_lt_102400 hpos (Nat.lt_of_not_le hlt)
  exact not_reachesOne_of_divergent h ((reachesOne_iff_orbit k n).mpr hreach)

/-- Consequently the sharp visit count for a divergent Collatz orbit in `[1, B]`
is at most `B - 102399`, and is `0` for `B < 102400` — for every `B` this
development can currently name. -/
theorem divergent_visits_le {n B : Nat} (hn : 0 < n) (h : Divergent n)
    (idx : Nat → Nat) (hmono : ∀ s t : Nat, s < t → idx s < idx t)
    (hwin : ∀ t : Nat, t ≤ B - 102400 + 1 → orbit (idx t) n ≤ B) :
    False := by
  refine visits_le (f := step) (x := n) (m := 102400) (B := B) ?_ idx hmono ?_
  · intro i j hij heq
    refine divergent_distinct h i j hij ?_
    rw [← iter_step, ← iter_step]
    exact heq
  · intro t ht
    refine ⟨?_, ?_⟩
    · rw [iter_step]; exact divergent_avoids_verified hn h (idx t)
    · rw [iter_step]; exact hwin t ht

/-! ## The two "quantitative consequences" are the hypothesis again

`Escape.lean` says of `divergent_window` and `divergent_escapes` that they are "not
merely a repackaging of unbounded".  They are.  Each is *logically equivalent* to
`Divergent n`, so neither is a proposition strictly between divergence and anything
else, and neither can appear as the `F` of a divergence filter: step (1)
"divergence ⇒ F" and step (2) "F ⇒ divergence" are both trivial, and no independent
principle is invoked in either. -/

/-- The window statement **is** divergence. -/
theorem window_iff_divergent (n : Nat) :
    Divergent n ↔ ∀ N B : Nat, ∃ k : Nat, k ≤ B + 1 ∧ B < orbit (N + k) n := by
  constructor
  · intro h N B; exact Escape.divergent_window h N B
  · intro h B
    obtain ⟨k, _, hk⟩ := h 0 B
    exact ⟨0 + k, hk⟩

/-- The escape statement **is** divergence. -/
theorem escapes_iff_divergent (n : Nat) :
    Divergent n ↔ ∀ B : Nat, ∃ N : Nat, ∀ i : Nat, N ≤ i → B < orbit i n := by
  constructor
  · intro h; exact Escape.divergent_escapes h
  · intro h B
    obtain ⟨N, hN⟩ := h B
    exact ⟨N, hN N (Nat.le_refl _)⟩

/-- Injectivity **is** divergence too. -/
theorem inj_iff_divergent (n : Nat) :
    Divergent n ↔ ∀ i j : Nat, orbit i n = orbit j n → i = j := by
  constructor
  · intro h i j heq; exact Escape.orbit_inj_of_divergent h heq
  · intro h
    refine Classical.byContradiction ?_
    intro hnd
    obtain ⟨i, L, hL, hrep⟩ := eventuallyPeriodic_of_bounded (bounded_of_not_divergent hnd)
    have := h (i + L) i hrep
    omega

/-- **The window constant is not sharp, and the repair is one line.**  A divergent
orbit exceeds `B` at *every* index for every `B < 102400`, so the window length
`B + 2` should be `1`.  At `B = 102399` the file's bound asks for a window of
`102401` indices; the truth needs one. -/
theorem window_one_below_verified {n : Nat} (hn : 0 < n) (h : Divergent n)
    {B : Nat} (hB : B < 102400) (N : Nat) : B < orbit N n :=
  Nat.lt_of_lt_of_le hB (divergent_avoids_verified hn h N)

end DivergenceAudit
end Collatz
