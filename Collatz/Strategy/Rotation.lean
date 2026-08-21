import Collatz.Strategy.AccumulatorCap
import Collatz.Strategy.CycleAccumulator

/-!
# Cyclic rotation: the maximum of a cycle, and what it forces on the word

A cycle has no distinguished starting point.  Every rotation of its parity word
is the same cycle read from another of its `L` points, and the gap
`G = 2 ^ L − 3 ^ a` is a rotation invariant: `oddCount` of a full turn does not
depend on where the turn starts (`AccumulatorCap.oddCount_shift`), so all `L`
rotations share one `L`, one `a` and one `G`, and

`G · T^k(n) = C_L(T^k(n))`   (`gap_mul_orbit`)

— **one gap, `L` different accumulators, `L` different quotients**, which are
exactly the `L` points of the cycle.

## What rotation does *not* give

`AccumulatorCap.dvd_affineC_shift` already proves that `M ∣ C_L(n)` holds at one
point of the cycle iff it holds at every point, for every divisor `M` of the gap.
That theorem is stronger than it looks: its proof is a pure identity
(`2 ^ k · C_L(T^k n) = 3 ^ (oddCount n k) · C_L(n) + G · C_k(n)`) together with
`G` odd and `3 ∤ G`, so it needs no cycle hypothesis beyond periodicity.  The
consequence is negative and worth stating flatly:

**Requiring the gap to divide the accumulator of *all* `L` rotations is exactly
as restrictive as requiring it for one.**  Verified exhaustively: for every
`L ≤ 22` and every `a` with `2 ^ L > 3 ^ a`, the set of words of length `L` with
`a` odd letters whose accumulator is divisible by `G` coincides with the set
whose *every* rotation is divisible by `G` (both sets are empty unless
`L = 2a`, where both have exactly two elements — the rotations of the trivial
cycle).  No pigeonhole over rotations exists to be exploited.

## What rotation does give: the maximum

The point of the cycle that is *largest* is as canonical as the one that is
smallest, and it has not been used.  From it the word is **light at every
prefix**:

`∀ p, 3 ^ (oddCount y p) ≤ 2 ^ p`   (`light_of_max`),

because `2 ^ p · T^p(y) = 3 ^ (oddCount y p) · y + C_p ≥ 3 ^ (oddCount y p) · y`
while `T^p(y) ≤ y` forces the left side below `2 ^ p · y`.  The accumulator is
used only through `C_p ≥ 0`; this is the exact dual of the minimum, where the
accumulator points the wrong way and only the two-fold bound
`2 ^ k < 2 · 3 ^ (oddCount x k)` survives (`NeverDrops.heavy_of_neverDrops`).

Specialising to `p = 1` gives `max % 2 = 0` (`max_even`): the largest point of a
cycle is even, and dually the smallest is odd (`min_odd`).  Specialising to
`p = L` recovers `3 ^ a < 2 ^ L` without the counting argument of `AccCycle`.

The maximum exists: `exists_cycle_max` builds it from `bestIdx`, a plain
recursive argmax over the first `L` orbit points, together with the periodicity
`orbit_mod`.

## Where the minimum's exact heaviness comes from

`heavy_of_min` is the sharp form of "a cycle is heavy from its minimum": the
prefix inequality `2 ^ p ≤ 3 ^ (oddCount n p)` holds at every `p` for which the
accumulator cap `AccumulatorCap.affineC_cap` is smaller than the minimum,

`3 ^ (oddCount n p) · 2 ^ (p − oddCount n p) < n + 2 ^ p  →  2 ^ p ≤ 3 ^ (oddCount n p)`.

The threshold is not an artifact: at `p = L` the hypothesis reads
`(2 ^ L − 3 ^ a) · n + 2 ^ L ≤ 3 ^ a · 2 ^ (L−a)` reversed, which is exactly
`AccumulatorCap.cycle_gap_cap`.  So the heaviness criterion and the cycle cap are
the same inequality read in opposite directions, and the criterion saturates
precisely where the cap does.  That is the reason no free lunch is available here.

## The Diophantine payoff of heaviness at the far end

Heaviness at the single prefix `L − 1` is worth a constraint on `(L, a)` alone:

`2 ^ (L−1) ≤ 3 ^ a < 2 ^ L`   (`gap_lt_of_heavy_end`),

i.e. `G < 2 ^ (L−1)`: there must be a power of three inside `[2 ^ (L−1), 2 ^ L)`.
For each `L` at most one `a` qualifies, and for roughly a third of all `L` none
does.  Combined with a heaviness certificate valid out to length `L − 1` this
excludes those lengths outright.  Exhaustive word search confirms the criterion is
exactly right, in both directions: for every `L ≤ 18` and every `a` with
`2 ^ L > 3 ^ a`, some word of length `L` with `a` odd letters has a heavy rotation
**iff** `3 ^ a ∈ [2 ^ (L−1), 2 ^ L)`.  The qualifying pairs up to `L = 18` are
`(2,1) (4,2) (5,3) (7,4) (8,5) (10,6) (12,7) (13,8) (15,9) (16,10) (18,11)`, and
at `L = 10, a = 6` only 120 of the 210 words qualify, at `L = 18, a = 11` only
17298 of 31824 — so heaviness is a proper restriction on top of the `(L, a)` one.

## Soundness

Every statement in this file is proved from `T(x) = x/2 | (3x+1)/2` through the
accumulator, and `DenominatorScalar` says `C(w, d) = d · C(w, 1)`.  All of them
therefore survive for every **positive** `d`, and the genuine `d = 5` cycles
satisfy them: `19 → 31 → 49 → 76 → 38` has maximum `76`, even, with `3 ^ a ≤ 2 ^ p`
at every prefix from `76`, and minimum `19`, odd and heavy.  What does *not*
survive is `d < 0`: `light_of_max` uses `C_p ≥ 0`, and for `d = −1` the
accumulator is negative — the `3x−1` cycle `17 → 25 → … → 34` has maximum `136`,
and reading its word from `136` lightness holds at every proper prefix but fails
at `p = L = 11`, where `3 ^ 7 = 2187 > 2048 = 2 ^ 11`.  That failure is exactly
the sign of the gap: for `d < 0` a cycle has `3 ^ a > 2 ^ L`.
So this family separates `d > 0` from `d < 0`, and no further; it cannot
distinguish `d = 1` from `d = 5`, and is not by itself a route to a proof.
-/

namespace Collatz
namespace Rotation

open Reach Congruence AffineExact AccCycle

/-! ## Periodicity of the orbit -/

/-- Adding a whole number of periods does not move the orbit point. -/
theorem orbit_period {n L : Nat} (hc : acceleratedOrbit L n = n) :
    ∀ k i : Nat, acceleratedOrbit (i + k * L) n = acceleratedOrbit i n := by
  intro k
  induction k with
  | zero => intro i; simp
  | succ k ih =>
    intro i
    have hs : (k + 1) * L = k * L + L := by rw [Nat.succ_mul]
    have h1 : i + (k + 1) * L = (i + k * L) + L := by rw [hs]; omega
    rw [h1, ← acceleratedOrbit_add (i + k * L) L n, hc]
    exact ih i

/-- The orbit point depends only on the index modulo the period. -/
theorem orbit_mod {n L : Nat} (hc : acceleratedOrbit L n = n) (i : Nat) :
    acceleratedOrbit i n = acceleratedOrbit (i % L) n := by
  have hp := orbit_period hc (i / L) (i % L)
  have h2 : i % L + (i / L) * L = i := by
    rw [Nat.mul_comm]; exact Nat.mod_add_div i L
  rw [h2] at hp
  exact hp

/-! ## An argmax over the first `m + 1` orbit points -/

/-- The index at most `m` at which the orbit of `n` is largest (earliest such). -/
def bestIdx (n : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 =>
      if acceleratedOrbit (bestIdx n m) n < acceleratedOrbit (m + 1) n then m + 1
      else bestIdx n m

/-- The argmax lies in range. -/
theorem bestIdx_le (n : Nat) : ∀ m : Nat, bestIdx n m ≤ m := by
  intro m
  induction m with
  | zero => exact Nat.le_refl _
  | succ m ih =>
    rw [bestIdx]
    split
    · exact Nat.le_refl _
    · omega

/-- The argmax dominates every orbit point in range. -/
theorem le_bestIdx (n : Nat) : ∀ m i : Nat, i ≤ m →
    acceleratedOrbit i n ≤ acceleratedOrbit (bestIdx n m) n := by
  intro m
  induction m with
  | zero =>
    intro i hi
    have : i = 0 := by omega
    subst this
    exact Nat.le_refl _
  | succ m ih =>
    intro i hi
    rw [bestIdx]
    split
    · rename_i hlt
      rcases Nat.lt_or_ge i (m + 1) with h | h
      · exact Nat.le_trans (ih i (by omega)) (Nat.le_of_lt hlt)
      · have : i = m + 1 := by omega
        subst this
        exact Nat.le_refl _
    · rename_i hge
      rcases Nat.lt_or_ge i (m + 1) with h | h
      · exact ih i (by omega)
      · have : i = m + 1 := by omega
        subst this
        omega

/-- **Every cycle attains a maximum.**  There is an index below `L` whose orbit
point dominates the whole orbit. -/
theorem exists_cycle_max {n L : Nat} (hL : 0 < L) (hc : acceleratedOrbit L n = n) :
    ∃ k : Nat, k < L ∧ ∀ i : Nat, acceleratedOrbit i n ≤ acceleratedOrbit k n := by
  refine ⟨bestIdx n (L - 1), by have := bestIdx_le n (L - 1); omega, ?_⟩
  intro i
  rw [orbit_mod hc i]
  exact le_bestIdx n (L - 1) (i % L) (by have := Nat.mod_lt i hL; omega)

/-! ## Lightness at the maximum -/

/-- **The word is light at every prefix, read from an orbit maximum.**  Only
`C_p ≥ 0` is used, so this is the exact statement the minimum cannot supply. -/
theorem light_of_max {y : Nat} (hy : 0 < y)
    (hmax : ∀ i : Nat, acceleratedOrbit i y ≤ y) (p : Nat) :
    3 ^ oddCount y p ≤ 2 ^ p := by
  have hex := affine_exact y p
  have hmono : 2 ^ p * acceleratedOrbit p y ≤ 2 ^ p * y :=
    Nat.mul_le_mul_left _ (hmax p)
  have hkey : 3 ^ oddCount y p * y ≤ 2 ^ p * y := by omega
  refine Nat.le_of_mul_le_mul_right ?_ hy
  omega

/-- **The largest point of a cycle is even.**  If it were odd the accelerated
step would strictly increase it. -/
theorem max_even {y : Nat} (hy : 0 < y)
    (hmax : ∀ i : Nat, acceleratedOrbit i y ≤ y) : y % 2 = 0 := by
  have h1 := light_of_max hy hmax 1
  have hlast := Density.oddCount_succ_last y 0
  rw [acceleratedOrbit_zero] at hlast
  have h0 : oddCount y 0 = 0 := Congruence.oddCount_zero y
  rcases Arith.mod_two_eq_zero_or_one y with he | ho
  · exact he
  · exfalso
    rw [h0, ho] at hlast
    rw [hlast] at h1
    have hno : ¬ ((3:Nat) ^ (0 + 1) ≤ 2 ^ 1) := by decide
    exact hno h1

/-- **The smallest point of a cycle is odd.**  If it were even the next point
would be strictly smaller. -/
theorem min_odd {y : Nat} (hy : 0 < y)
    (hmin : ∀ i : Nat, y ≤ acceleratedOrbit i y) : y % 2 = 1 := by
  rcases Arith.mod_two_eq_zero_or_one y with he | ho
  · exfalso
    have h1 := hmin 1
    have hstep : acceleratedOrbit 1 y = acceleratedStep y := by
      have := acceleratedOrbit_succ_step 0 y
      rw [acceleratedOrbit_zero] at this
      exact this
    have hval : acceleratedStep y = y / 2 := by
      rw [acceleratedStep, if_pos he]
    rw [hstep, hval] at h1
    omega
  · exact ho

/-! ## The gap is the rotation invariant -/

/-- **One gap, `L` accumulators.**  Every point of the cycle satisfies the cycle
equation with the *same* gap; only the accumulator changes. -/
theorem gap_mul_orbit {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) (k : Nat) :
    (2 ^ L - 3 ^ oddCount n L) * acceleratedOrbit k n
      = affineC L (acceleratedOrbit k n) := by
  have hshift := AccumulatorCap.accCycle_shift h k
  have hpos : 0 < acceleratedOrbit k n := acceleratedOrbit_positive hn k
  have hcount := AccumulatorCap.oddCount_shift h.2 k
  have hmul := CycleAccumulator.cycle_gap_mul hpos hshift
  rw [hcount] at hmul
  exact hmul

/-- The cycle, read from its maximum: light everywhere, and even. -/
theorem cycle_light_rotation {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L) :
    ∃ k : Nat, k < L ∧ acceleratedOrbit k n % 2 = 0 ∧
      ∀ p : Nat, 3 ^ oddCount (acceleratedOrbit k n) p ≤ 2 ^ p := by
  obtain ⟨k, hk, hmax⟩ := exists_cycle_max h.1 h.2
  have hpos : 0 < acceleratedOrbit k n := acceleratedOrbit_positive hn k
  have hmax' : ∀ i : Nat, acceleratedOrbit i (acceleratedOrbit k n)
      ≤ acceleratedOrbit k n := by
    intro i
    rw [acceleratedOrbit_add i k n]
    exact hmax (i + k)
  exact ⟨k, hk, max_even hpos hmax', light_of_max hpos hmax'⟩

/-! ## Exact heaviness at the minimum, and its exact threshold -/

/-- **Heaviness from the minimum, sharp form.**  At every prefix whose
accumulator cap is below the minimum, the prefix is heavy on the nose. -/
theorem heavy_of_min {n p : Nat} (hn : 0 < n)
    (hmin : ∀ i : Nat, n ≤ acceleratedOrbit i n)
    (hbig : 3 ^ oddCount n p * 2 ^ (p - oddCount n p) < n + 2 ^ p) :
    2 ^ p ≤ 3 ^ oddCount n p := by
  have harith := (neverDrops_iff_affine hn).mp hmin p
  have hcap := AccumulatorCap.affineC_cap n p
  rcases Nat.lt_or_ge (3 ^ oddCount n p) (2 ^ p) with hlt | hge
  · exfalso
    have hstep : 3 ^ oddCount n p + 1 ≤ 2 ^ p := by omega
    have hgrow : (3 ^ oddCount n p + 1) * n ≤ 2 ^ p * n :=
      Nat.mul_le_mul_right _ hstep
    have hexp : (3 ^ oddCount n p + 1) * n = 3 ^ oddCount n p * n + n := by
      rw [Nat.add_mul, Nat.one_mul]
    omega
  · exact hge

/-- **The Diophantine consequence of heaviness at the far end.**  If the word of
a cycle is heavy at the prefix of length `L − 1`, then `3 ^ a` lies in
`[2 ^ (L−1), 2 ^ L)`, so the gap is smaller than half of `2 ^ L`. -/
theorem gap_lt_of_heavy_end {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hheavy : 2 ^ (L - 1) ≤ 3 ^ oddCount n (L - 1)) :
    2 ^ (L - 1) ≤ 3 ^ oddCount n L ∧ 3 ^ oddCount n L < 2 ^ L := by
  have hb := accCycle_bounds hn h
  refine ⟨Nat.le_trans hheavy ?_, hb.2.2⟩
  refine Arith.three_pow_le_three_pow ?_
  have hL : 0 < L := h.1
  have hlast := Density.oddCount_succ_last n (L - 1)
  have hLe : L - 1 + 1 = L := by omega
  rw [hLe] at hlast
  omega

/-- The same, as a criterion on `(L, a)` alone: no power of three in the dyadic
window means no heavy-at-the-end cycle of that length. -/
theorem no_cycle_of_no_three_power {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hheavy : 2 ^ (L - 1) ≤ 3 ^ oddCount n (L - 1))
    (hwindow : ∀ a : Nat, 3 ^ a < 2 ^ (L - 1) ∨ 2 ^ L ≤ 3 ^ a) : False := by
  obtain ⟨h1, h2⟩ := gap_lt_of_heavy_end hn h hheavy
  rcases hwindow (oddCount n L) with hlt | hge <;> omega

end Rotation
end Collatz
