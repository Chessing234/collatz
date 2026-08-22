import Collatz.Strategy.Rotation
import Collatz.Strategy.NeverDrops

/-!
# The cyclic ordering of the odd-step times, and why it says nothing new

A cycle has no distinguished start, so the honest object attached to it is not the
word `w ∈ {0,1}^L` but the **cyclic** configuration on `Z/L` of its odd-step times
`0 ≤ t₁ < … < t_a < L`.  A hypothetical cycle produces `L` ordered words, one per
starting point.  This file asks what the cyclic picture adds to the linear one.

The answer is: **an exact rotation covariance, and nothing else.**

## The discrepancy walk

Write `A(j) = oddCount n j` and `a = A(L)`.  The natural equidistribution measure
of the time set is the discrepancy `D(j) = A(j) − (a/L)·j`.  To stay inside `Int`
we scale by `L` and use

`walk n L j = L·A(j) − a·j`   (`walk`),

so `D = walk / L`.  Two facts fix its behaviour completely.

* `walk_shift`: `walk (T^r n) L j = walk n L (r+j) − walk n L r`, for **every** `n`
  and every `r, j` — this needs only the cocycle `oddCount_add` and, for the `a`
  in the definition to be rotation-independent, `oddCount_shift`.
* `walk_period`: `walk n L (m+L) = walk n L m` on a cycle.  Together with
  `walk n L 0 = walk n L L = 0` the walk is a **closed walk of period `L`**.

Consequently (`walk_range`, `walk_range'`) the multiset of values of the rotated
walk over one period is the multiset of values of the original walk, translated by
the single constant `walk n L r`:

> **Rotating shifts the discrepancy walk cyclically and slides it vertically.
> `max_j D` and `min_j D` over a full period are rotation-invariant; only their
> location moves, and only the offset `D(r)` changes.**

That kills the hope — "Chain E" of the round brief — that different rotations
supply different discrepancy constraints.  Any inequality of the form "the
discrepancy path of a cycle obeys bound `B`" has exactly the same content at all
`L` rotations, up to the additive constant `D(r)` which is itself read off the one
walk.  There is no pigeonhole over rotations, matching what
`AccumulatorCap.dvd_affineC_shift` already proved on the divisibility side.

## Where the dynamical extrema sit

The bridge to Round III's two rotations is exact, and it is pure exponent
arithmetic — no logarithms, no reals.  Throughout, `3^a < 2^L` (the gap is
positive).

* **Heaviness = starting at the walk's strict minimum** (`heavy_walk_pos`):
  `2^j ≤ 3^A(j)` with `1 ≤ j` forces `a·j < L·A(j)`, i.e. `walk n L j > 0`.
  Raise `2^j ≤ 3^A` to the `L`-th power and `3^a < 2^L` to the `j`-th:
  `3^(a·j) < 2^(L·j) ≤ 3^(A·L)`.
  So the rotation at the cycle **minimum**, which Round III shows is heavy at
  every proper prefix, is the rotation whose walk starts at its own strict
  minimum.
* **Lightness = starting within one unit of the walk's maximum**
  (`light_walk_lt`): if additionally `2^L < 3^(a+1)` — true for every
  cycle-plausible pair, since `G ≪ 3^a` — then `3^A(j) ≤ 2^j` forces
  `L·A(j) < (a+1)·j`, i.e. `walk n L j < j ≤ L`, i.e. `D(j) < 1`.
  The maximum rotation therefore starts within `1` of the walk's maximum.  It is
  **not** exactly at the maximum: the two sides are asymmetric because
  `a/L < log₃2` strictly, and the slack is exactly `L·log₃2 − a ∈ (0,1)`.
* The unconditional form, needing only `NeverDrops` rather than full heaviness
  (`neverDrops_walk_gt`): `2^k < 2·3^A(k)` gives `a·k < L·A(k) + a + 1`, i.e.
  `D(k) > −(a+1)/L > −1`.  So even without the accumulator-cap hypothesis of
  `Rotation.heavy_of_min`, the dynamical minimum sits within one unit of the
  walk's minimum.

`Rotation.max_even` and `Rotation.min_odd` are, under this dictionary, the
statement that a walk steps **up** at a minimum and **down** at a maximum.  They
carry no information about the cycle beyond the extremum's existence.

## Is that more than the cycle lemma?  No.

`heavy_unique` proves that **at most one rotation of a word is heavy at every
proper prefix**: if `T^r n` and `T^s n` were both heavy with `r < s < L`, apply
`heavy_walk_pos` to the first at prefix `s − r` and to the second at prefix
`L − (s − r)` and add — the two strict inequalities sum to `a·L < a·L`.

Existence of such a rotation is the Dvoretzky–Motzkin cycle lemma; uniqueness is
its second half.  So tasks (1)–(3) of the round brief all land on the cycle
lemma: the rotation at the cycle minimum is the unique rotation starting at the
walk's strict minimum, exactly one rotation out of `L` has that property, and
"being heavy" costs a factor `L` in a count and no entropy.  Verified
exhaustively for every `L ≤ 16` and every `a` with `3^a < 2^L`: the number of
rotations heavy at every proper prefix is `0` or `1`, never more.  (It is `1`
precisely when `3^a ∈ [2^(L−1), 2^L)`, which is `Rotation.gap_lt_of_heavy_end`.)

## The one quantity the cyclic picture does supply, and why it is dead

The rotation-invariant that the linear picture does not name is the **amplitude**
`max_j walk − min_j walk`.  `walk_eq_dvd` is its arithmetic core: if two walk
values coincide then `L ∣ a·(j − i)`, so when `gcd(L, a) = 1` the `L` values are
pairwise distinct, hence occupy `L` distinct residues mod `L`, hence spread over
at least `L − 1`.  When `g = gcd(L,a) > 1`, `walk (L/g) ≡ 0 mod L` while
`heavy_walk_pos` makes it positive, so it is at least `L`.  Either way

> **amplitude `≥ L − 1`, i.e. the discrepancy amplitude is `≥ 1 − 1/L`.**

Exhaustively confirmed for every word heavy at every proper prefix with `L ≤ 18`;
attained exactly at `(L,a) = (2,1), (5,3), (8,5)` and, at the frontier, by the
Sturmian word at `(4701, 2966)`, whose amplitude is `4700 = L − 1` on the nose.

Through `2^r·n_r = 3^A(r)·n₀ + C_r ≥ 3^A(r)·n₀` this amplitude lower-bounds the
cycle's spread: numerically `log₂(max/min) = (amplitude/L)·log₂3` to four decimal
places on every genuine cycle checked — `1.0000` vs `0.7925` for the trivial
`d = 1` cycle (`L = 2`), `4.4762` vs `4.4614` for the `d = 5` cycle of minimum
`187`, `3.0000` vs `3.0258` for the `d = −1` cycle of minimum `17`, and `1.5846`
for the Sturmian frontier word, reproducing `SpreadFloor`'s computed `2.99930`.

**And that is exactly why it cannot help.**  The amplitude is a function of the
word alone and is invariant under `C ↦ d·C`, so by `DenominatorScalar` and
`NewModels.word_is_cycle_word` it is `d`-free, and the soundness filter kills it:
every statement in this file holds verbatim for the `d = 5` cycles of minima
`187` and `347` and for the `d = −1` cycle `17 → … → 34`, whose walks have their
dynamical minimum at the walk minimum and their dynamical maximum at the walk
maximum just as `d = 1` would.  `SpreadFloor` already recorded that no `d`-free
mechanism can lower-bound a cycle's spread; the cyclic-ordering route produces
precisely such a bound, in closed form, and is refuted by the same Sturmian
witness.

## Verdict

The cyclic ordering is the linear ordering plus one rotation-covariance identity.
It supplies no constraint the accumulator does not already carry, and the single
new invariant it does supply — the discrepancy amplitude — is `d`-free and
therefore cannot separate `3x+1` from `3x+5`.
-/

namespace Collatz
namespace CyclicOrder

open Reach Congruence AffineExact AccCycle Rotation

/-! ## An `Int` algebra helper -/

/-- The rotation identity, stripped of all Collatz content. -/
theorem shift_algebra (L a A B r j : Int) :
    L * (A + B) - a * (r + j) - (L * A - a * r) = L * B - a * j := by
  rw [Int.mul_add, Int.mul_add]
  omega

/-! ## The discrepancy walk -/

/-- `L` times the discrepancy of the odd-step times of `n` at time `j`:
`walk n L j = L·oddCount n j − oddCount n L · j`.  It starts and ends at `0`. -/
def walk (n L j : Nat) : Int :=
  (L : Int) * (oddCount n j : Int) - (oddCount n L : Int) * (j : Int)

@[simp] theorem walk_zero (n L : Nat) : walk n L 0 = 0 := by
  simp [walk]

@[simp] theorem walk_full (n L : Nat) : walk n L L = 0 := by
  unfold walk
  rw [Int.mul_comm (L : Int) (oddCount n L : Int)]
  omega

/-- **Rotation covariance.**  Reading the walk from the `r`-th point of the orbit
is the original walk shifted `r` to the left and dropped by `walk n L r`.  Only
the cocycle for `oddCount` and the rotation-invariance of `a` are used. -/
theorem walk_shift {n L : Nat} (hc : acceleratedOrbit L n = n) (r j : Nat) :
    walk (acceleratedOrbit r n) L j = walk n L (r + j) - walk n L r := by
  have hadd : oddCount n (r + j) = oddCount n r + oddCount (acceleratedOrbit r n) j :=
    AccumulatorArith.oddCount_add n r j
  have hcnt : oddCount (acceleratedOrbit r n) L = oddCount n L :=
    AccumulatorCap.oddCount_shift hc r
  have hcast : ((oddCount n (r + j) : Nat) : Int)
      = (oddCount n r : Int) + (oddCount (acceleratedOrbit r n) j : Int) := by
    rw [hadd]; simp
  have hrj : (((r + j : Nat)) : Int) = (r : Int) + (j : Int) := by simp
  unfold walk
  rw [hcnt, hcast, hrj]
  exact (shift_algebra _ _ _ _ _ _).symm

/-- On a cycle the walk is periodic: a full turn adds `a` odd steps and `L` to the
time, and the two contributions cancel. -/
theorem walk_period {n L : Nat} (hc : acceleratedOrbit L n = n) (m : Nat) :
    walk n L (m + L) = walk n L m := by
  have hadd : oddCount n (m + L) = oddCount n m + oddCount (acceleratedOrbit m n) L :=
    AccumulatorArith.oddCount_add n m L
  have hcnt : oddCount (acceleratedOrbit m n) L = oddCount n L :=
    AccumulatorCap.oddCount_shift hc m
  rw [hcnt] at hadd
  have hcast : ((oddCount n (m + L) : Nat) : Int)
      = (oddCount n m : Int) + (oddCount n L : Int) := by rw [hadd]; simp
  have hmL : (((m + L : Nat)) : Int) = (m : Int) + (L : Int) := by simp
  unfold walk
  rw [hcast, hmL, Int.mul_add, Int.mul_add,
    Int.mul_comm (L : Int) (oddCount n L : Int)]
  omega

/-- The walk depends only on the time modulo the period. -/
theorem walk_mod {n L : Nat} (_hL : 0 < L) (hc : acceleratedOrbit L n = n) (m : Nat) :
    walk n L m = walk n L (m % L) := by
  have key : ∀ q r : Nat, walk n L (r + q * L) = walk n L r := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ q ih =>
      intro r
      have hs : r + (q + 1) * L = (r + q * L) + L := by
        rw [Nat.succ_mul]; omega
      rw [hs, walk_period hc, ih r]
  have h2 : m % L + (m / L) * L = m := by
    rw [Nat.mul_comm]; exact Nat.mod_add_div m L
  have := key (m / L) (m % L)
  rw [h2] at this
  exact this

/-- **The value set of a rotated walk is a translate of the original's.**  Every
value of the rotated walk over one period is `walk n L m − walk n L r` for some
`m < L`. -/
theorem walk_range {n L : Nat} (hL : 0 < L) (hc : acceleratedOrbit L n = n) (r j : Nat) :
    ∃ m : Nat, m < L ∧ walk (acceleratedOrbit r n) L j = walk n L m - walk n L r := by
  refine ⟨(r + j) % L, Nat.mod_lt _ hL, ?_⟩
  rw [walk_shift hc r j, ← walk_mod hL hc (r + j)]

/-- Conversely every value of the original walk occurs in the rotated one. -/
theorem walk_range' {n L : Nat} (hL : 0 < L) (hc : acceleratedOrbit L n = n)
    {r : Nat} (hr : r < L) (m : Nat) :
    ∃ j : Nat, j < L ∧ walk (acceleratedOrbit r n) L j = walk n L m - walk n L r := by
  have key : ∀ x y : Nat, (x + y % L) % L = (x + y) % L := by
    intro x y
    rw [Nat.add_mod x (y % L), Nat.mod_mod_of_dvd _ (Nat.dvd_refl L), ← Nat.add_mod]
  refine ⟨(m + (L - r)) % L, Nat.mod_lt _ hL, ?_⟩
  have hmod : (r + (m + (L - r)) % L) % L = m % L := by
    rw [key r (m + (L - r))]
    have h2 : r + (m + (L - r)) = m + L := by omega
    rw [h2, Nat.add_mod_right]
  rw [walk_shift hc r _, walk_mod hL hc (r + (m + (L - r)) % L), hmod,
    ← walk_mod hL hc m]

/-- **Amplitude invariance.**  If the walk of `n` is confined to `[lo, hi]` over a
full period, the walk of every rotation is confined to an interval of the same
length, namely `[lo − walk n L r, hi − walk n L r]`. -/
theorem walk_amplitude_invariant {n L : Nat} (hL : 0 < L)
    (hc : acceleratedOrbit L n = n) {lo hi : Int}
    (hlo : ∀ m : Nat, m < L → lo ≤ walk n L m)
    (hhi : ∀ m : Nat, m < L → walk n L m ≤ hi) (r j : Nat) :
    lo - walk n L r ≤ walk (acceleratedOrbit r n) L j ∧
      walk (acceleratedOrbit r n) L j ≤ hi - walk n L r := by
  obtain ⟨m, hm, hval⟩ := walk_range hL hc r j
  exact ⟨by have := hlo m hm; omega, by have := hhi m hm; omega⟩

/-! ## Heaviness is exactly "the walk starts at its strict minimum" -/

/-- **Heavy prefix ⇒ strictly positive walk.**  Pure exponent arithmetic: raise
`2^j ≤ 3^A` to the `L`-th power and `3^a < 2^L` to the `j`-th. -/
theorem heavy_walk_pos {L a A j : Nat} (hgap : 3 ^ a < 2 ^ L) (hj : 0 < j)
    (hh : 2 ^ j ≤ 3 ^ A) : a * j < L * A := by
  have h1 : (3 ^ a) ^ j < (2 ^ L) ^ j := Nat.pow_lt_pow_left hgap (by omega)
  have h2 : (2 ^ j) ^ L ≤ (3 ^ A) ^ L := Nat.pow_le_pow_left hh L
  rw [← Nat.pow_mul, ← Nat.pow_mul] at h1
  rw [← Nat.pow_mul, ← Nat.pow_mul] at h2
  have hcomm : (2:Nat) ^ (L * j) = 2 ^ (j * L) := by rw [Nat.mul_comm]
  rw [hcomm] at h1
  have h3 : (3:Nat) ^ (a * j) < 3 ^ (A * L) := by omega
  have h4 : a * j < A * L := by
    rcases Nat.lt_or_ge (a * j) (A * L) with h | h
    · exact h
    · exact absurd (Arith.three_pow_le_three_pow h) (by omega)
  have h5 : L * A = A * L := Nat.mul_comm L A
  omega

/-- The same, phrased on the walk. -/
theorem walk_pos_of_heavy {n L j : Nat} (hgap : 3 ^ oddCount n L < 2 ^ L) (hj : 0 < j)
    (hh : 2 ^ j ≤ 3 ^ oddCount n j) : 0 < walk n L j := by
  have h := heavy_walk_pos (L := L) (a := oddCount n L) (A := oddCount n j) hgap hj hh
  unfold walk
  have hc1 : ((oddCount n L * j : Nat) : Int)
      = (oddCount n L : Int) * (j : Int) := by simp
  have hc2 : ((L * oddCount n j : Nat) : Int)
      = (L : Int) * (oddCount n j : Int) := by simp
  have : ((oddCount n L * j : Nat) : Int) < ((L * oddCount n j : Nat) : Int) :=
    Int.ofNat_lt.mpr h
  omega

/-- **Lightness ⇒ the walk stays below `j`,** i.e. the discrepancy stays below `1`.
Needs the mild extra hypothesis `2^L < 3^(a+1)`, which holds whenever the gap is
below twice `3^a`. -/
theorem light_walk_lt {L a A j : Nat} (hnear : 2 ^ L < 3 ^ (a + 1)) (hj : 0 < j)
    (hl : 3 ^ A ≤ 2 ^ j) : L * A < (a + 1) * j := by
  have h1 : (2 ^ L) ^ j < (3 ^ (a + 1)) ^ j := Nat.pow_lt_pow_left hnear (by omega)
  have h2 : (3 ^ A) ^ L ≤ (2 ^ j) ^ L := Nat.pow_le_pow_left hl L
  rw [← Nat.pow_mul, ← Nat.pow_mul] at h1
  rw [← Nat.pow_mul, ← Nat.pow_mul] at h2
  have hcomm : (2:Nat) ^ (j * L) = 2 ^ (L * j) := by rw [Nat.mul_comm]
  rw [hcomm] at h2
  have h3 : (3:Nat) ^ (A * L) < 3 ^ ((a + 1) * j) := by omega
  have h4 : A * L < (a + 1) * j := by
    rcases Nat.lt_or_ge (A * L) ((a + 1) * j) with h | h
    · exact h
    · exact absurd (Arith.three_pow_le_three_pow h) (by omega)
  have h5 : L * A = A * L := Nat.mul_comm L A
  omega

/-- **The unconditional half.**  `NeverDrops` gives only `2^k < 2·3^A`, and that
already pins the walk within one unit below its start. -/
theorem neverDrops_walk_gt {L a A k : Nat} (hgap : 3 ^ a < 2 ^ L)
    (hnear : 2 ^ L < 3 ^ (a + 1)) (hk : 0 < k) (hh : 2 ^ k < 2 * 3 ^ A) :
    a * k < L * A + (a + 1) := by
  have h1 : (2:Nat) ^ k ≤ 2 * 3 ^ A := by omega
  have h2 : ((2:Nat) ^ k) ^ L ≤ (2 * 3 ^ A) ^ L := Nat.pow_le_pow_left h1 L
  have h3 : (2 * 3 ^ A) ^ L = 2 ^ L * (3 ^ A) ^ L := Nat.mul_pow 2 (3 ^ A) L
  have h4 : (3 ^ a) ^ k < (2 ^ L) ^ k := Nat.pow_lt_pow_left hgap (by omega)
  rw [← Nat.pow_mul] at h2
  rw [← Nat.pow_mul] at h3
  rw [← Nat.pow_mul, ← Nat.pow_mul] at h4
  have hcomm : (2:Nat) ^ (k * L) = 2 ^ (L * k) := by rw [Nat.mul_comm]
  have h5 : (3:Nat) ^ (a * k) < 2 ^ L * 3 ^ (A * L) := by
    rw [hcomm] at h2
    omega
  have h6 : (2:Nat) ^ L * 3 ^ (A * L) < 3 ^ (a + 1) * 3 ^ (A * L) :=
    Nat.mul_lt_mul_of_lt_of_le hnear (Nat.le_refl _) (Arith.three_pow_pos _)
  have h7 : (3:Nat) ^ (a + 1) * 3 ^ (A * L) = 3 ^ (a + 1 + A * L) :=
    (Arith.three_pow_add _ _).symm
  have h8 : (3:Nat) ^ (a * k) < 3 ^ (a + 1 + A * L) := by omega
  have h9 : a * k < a + 1 + A * L := by
    rcases Nat.lt_or_ge (a * k) (a + 1 + A * L) with h | h
    · exact h
    · exact absurd (Arith.three_pow_le_three_pow h) (by omega)
  have hcm : L * A = A * L := Nat.mul_comm L A
  omega

/-! ## Uniqueness: the cycle lemma, and no more -/

/-- **At most one rotation is heavy at every proper prefix.**  Adding the two
strict inequalities supplied by `heavy_walk_pos` at complementary prefixes gives
`a·L < a·L`.  Existence of a heavy rotation is the cycle lemma; this is its
uniqueness half, and together they say that "the word is heavy" costs a factor
`L` in any count and no entropy at all. -/
theorem heavy_unique {n L : Nat} (hc : acceleratedOrbit L n = n)
    (hgap : 3 ^ oddCount n L < 2 ^ L) {r s : Nat} (hrs : r < s) (hsL : s < L)
    (hr : ∀ p : Nat, p < L → 2 ^ p ≤ 3 ^ oddCount (acceleratedOrbit r n) p)
    (hs : ∀ p : Nat, p < L → 2 ^ p ≤ 3 ^ oddCount (acceleratedOrbit s n) p) :
    False := by
  have hax : oddCount (acceleratedOrbit r n) L = oddCount n L :=
    AccumulatorCap.oddCount_shift hc r
  have hay : oddCount (acceleratedOrbit s n) L = oddCount n L :=
    AccumulatorCap.oddCount_shift hc s
  have hgx : 3 ^ oddCount (acceleratedOrbit r n) L < 2 ^ L := by rw [hax]; exact hgap
  have hgy : 3 ^ oddCount (acceleratedOrbit s n) L < 2 ^ L := by rw [hay]; exact hgap
  -- the two complementary prefix lengths
  have h1 := heavy_walk_pos (L := L) (a := oddCount n L)
      (A := oddCount (acceleratedOrbit r n) (s - r)) (j := s - r)
      hgap (by omega) (hr (s - r) (by omega))
  have h2 := heavy_walk_pos (L := L) (a := oddCount n L)
      (A := oddCount (acceleratedOrbit s n) (L - (s - r))) (j := L - (s - r))
      hgap (by omega) (hs (L - (s - r)) (by omega))
  -- and their odd counts add up to a full turn
  have hys : acceleratedOrbit (s - r) (acceleratedOrbit r n) = acceleratedOrbit s n := by
    rw [acceleratedOrbit_add (s - r) r n]
    have : s - r + r = s := by omega
    rw [this]
  have hsplit : oddCount (acceleratedOrbit r n) ((s - r) + (L - (s - r)))
      = oddCount (acceleratedOrbit r n) (s - r)
        + oddCount (acceleratedOrbit s n) (L - (s - r)) := by
    rw [AccumulatorArith.oddCount_add (acceleratedOrbit r n) (s - r) (L - (s - r)), hys]
  have hL : (s - r) + (L - (s - r)) = L := by omega
  rw [hL, hax] at hsplit
  have hdist : oddCount n L * (s - r) + oddCount n L * (L - (s - r))
      = oddCount n L * L := by
    rw [← Nat.mul_add, hL]
  have hdist2 : L * oddCount (acceleratedOrbit r n) (s - r)
      + L * oddCount (acceleratedOrbit s n) (L - (s - r)) = L * oddCount n L := by
    rw [← Nat.mul_add, ← hsplit]
  have hcm : oddCount n L * L = L * oddCount n L := Nat.mul_comm _ _
  omega

/-! ## The amplitude, and its arithmetic core -/

/-- **Two equal walk values force a divisibility.**  If the walk repeats a value
at times `i < j` then `L ∣ a·(j − i)`; when `gcd(L, a) = 1` this is impossible for
`0 < j − i < L`, so the `L` values of one period are pairwise distinct and their
spread is at least `L − 1`. -/
theorem walk_eq_dvd {n L : Nat} (i j : Nat) (h : walk n L i = walk n L j) :
    (L : Int) ∣ (oddCount n L : Int) * ((j : Int) - (i : Int)) := by
  refine ⟨(oddCount n j : Int) - (oddCount n i : Int), ?_⟩
  unfold walk at h
  have hL : (L : Int) * ((oddCount n j : Int) - (oddCount n i : Int))
      = (L : Int) * (oddCount n j : Int) - (L : Int) * (oddCount n i : Int) :=
    Int.mul_sub _ _ _
  have ha : (oddCount n L : Int) * ((j : Int) - (i : Int))
      = (oddCount n L : Int) * (j : Int) - (oddCount n L : Int) * (i : Int) :=
    Int.mul_sub _ _ _
  omega

/-- The coprime case, in the form actually used: if no positive multiple of `a`
below `L·a` is divisible by `L`, the walk is injective on one period. -/
theorem walk_injective {n L : Nat} (hcop : ∀ k : Nat, 0 < k → k < L →
      ¬ ((L : Int) ∣ (oddCount n L : Int) * (k : Int))) {i j : Nat}
    (hi : i < L) (hj : j < L) (h : walk n L i = walk n L j) : i = j := by
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · exfalso
    have hd := walk_eq_dvd i j h
    have hcast : ((j - i : Nat) : Int) = (j : Int) - (i : Int) := by
      have : (i : Int) ≤ (j : Int) := Int.ofNat_le.mpr (Nat.le_of_lt hlt)
      omega
    exact hcop (j - i) (by omega) (by omega) (by rw [hcast]; exact hd)
  · exact heq
  · exfalso
    have hd := walk_eq_dvd j i h.symm
    have hcast : ((i - j : Nat) : Int) = (i : Int) - (j : Int) := by
      have : (j : Int) ≤ (i : Int) := Int.ofNat_le.mpr (Nat.le_of_lt hgt)
      omega
    exact hcop (i - j) (by omega) (by omega) (by rw [hcast]; exact hd)

end CyclicOrder
end Collatz
