import Collatz.Strategy.FloorSchedule

/-!
# The pin constant tends to `1`: an archimedean law that only a divergent orbit obeys

`Height.lean` closed the canonical-height route.  Its diagnosis was that the
topological degree of `T` on `ℤ₂` is `2` while the archimedean expansion is `1`,
and that for a degree-`d` morphism those are forced to agree.  This file does
**not** try to repair that.  It takes the one hypothesis a divergent orbit
supplies and no cycle ever does — *the orbit is eventually above every bound* —
and shows that this hypothesis alone pins the archimedean coordinate to the
parity word with a multiplicative error tending to `1`.

## The statement

`FloorSchedule.sched_pin` already traps `2 ^ k · T^k(x)` between
`3 ^ (a k) · x` and `(S/P) · 3 ^ (a k) · x`, but leaves `S/P` as an unevaluated
product; its own header can only say the product converges "along any orbit
growing at least geometrically".  The arithmetic lemma `pow_step_bound` below
evaluates it:

> `c · (3c + 1) ^ a ≤ (c + 2a) · 3 ^ a · c ^ a`   whenever `2a ≤ 5c`.

So a constant floor `c` below the orbit gives the **explicit** pin

> `c · (2 ^ k · T^k(x)) ≤ (c + 2·a k) · (3 ^ (a k) · x)`   (`pin_explicit`),

with pin constant `1 + 2·a k / c`.  Along a divergent orbit `c` may be taken as
large as one likes on a tail, so:

> **the pin constant tends to `1`.**  For every `k` and every `j` there is a
> tail window of length `k` on which `2 ^ k · T^k(x)` and `3 ^ (a k) · x` agree
> to within `1 + 1/j` (`pin_ratio`, and `pin_tends_to_one` from the divergence
hypothesis itself).

In logarithmic form: `log₂ x_{N+k} − log₂ x_N = a·log₂3 − k + O(1/j)`.  The
archimedean coordinate of a divergent orbit is *not one bit away* from the word
datum — it **is** the word datum in the limit.

## The hypothesis, and where it comes from

`pin_tends_to_one` takes divergence in the escape form
`∀ B, ∃ N, ∀ i ≥ N, B ≤ T^i(x)`.  `Escape.divergent_escapes` proves exactly this
shape from mere unboundedness — for the unaccelerated orbit; the accelerated
statement `AccDivergent n → ∀ B, ∃ N, ∀ i ≥ N, B < T^i n` is the one missing
link, and it is a transcription, not a new idea (an accelerated orbit that
repeats a value is periodic, hence bounded).  Until it is transcribed the
hypothesis is carried explicitly, which is also the honest form: every theorem
below states what it consumes.

## Non-circularity

The hypothesis consumed is `∀ i, c ≤ T^i(x)` — a lower bound on the forward
orbit.  A divergent orbit supplies it on every tail (unbounded ⇒ all values
distinct ⇒ tail minima → ∞, the foundational fact).  Nothing here assumes the
conjecture: `pin_explicit` is a theorem about *every* `x` and *every* `c` below
its orbit, and its proof is the affine identity plus `pow_step_bound`.  Neither
half mentions termination.

## Why this is not a cycle detector

`cycle_hypothesis_fails` : on the orbit of `1` the values never exceed `2`, so
the hypothesis `2k ≤ c` fails for every `k ≥ 2`.  The device is *vacuous* on
bounded orbits by construction — the opposite polarity to every other filter in
this development, all of which are cycle witnesses.

## What it sees in an orbit that never returns

`deficit_of_growth` : under the same hypothesis, `2 ^ k · T^k(x) ≤ 2·3^(a k)·x`,
so the 2-adic deficit obeys `3 ^ (a k) / 2 ^ k ≥ T^k(x) / (2x)`.  On a cycle the
deficit is bounded (`3^a/2^k ∈ (1/2, 1)` after normalisation); on a divergent
orbit it grows **proportionally to the archimedean size**.  That is the
observable the divergence half was missing: an unbounded, quantitatively
growing 2-adic deficit.

## Where it stops, stated as sharply as it can be

`heavy_of_never_drop` turns the pin into `2 ^ k ≤ 2 · 3 ^ (a k)` for every high
never-dropping window: the word of such a window is heavy with a *bounded*
additive slack, uniformly in `k`.  Closing the argument needs the converse — a
window in which `2 ^ k > 2 · 3 ^ (a k)`, i.e. a lower bound on the accumulated
2-adic valuation `Σ v₂(3y+1)`.  By Terras every finite valuation vector is
realised, so no finite computation can supply one; the missing principle is a
*normality* statement for the 2-adic expansion of `x`, and it is exactly the
open part.  This file therefore delivers step (1) of the non-circularity test in
its sharpest known form, and states precisely what step (2) would have to be.
-/

namespace Collatz
namespace GlobalHeight

open Reach Congruence AffineExact CycleProduct FloorSchedule

/-! ## The arithmetic core: evaluating the schedule product -/

/-- **The pin product, evaluated.**  `(3c+1)^a` exceeds `3^a·c^a` by the factor
`(1 + 1/(3c))^a`, and this bounds that factor by `1 + 2a/c` in the range
`2a ≤ 5c`.  It is the whole content of the file: the defect product of
`FloorSchedule` is *linear*, not exponential, once the floor exceeds the window
length. -/
theorem pow_step_bound (c : Nat) : ∀ a : Nat, 2 * a ≤ 5 * c →
    c * (3 * c + 1) ^ a ≤ (c + 2 * a) * (3 ^ a * c ^ a) := by
  intro a
  induction a with
  | zero => intro _; simp
  | succ a ih =>
    intro hle
    have hprev : 2 * a ≤ 5 * c := by omega
    have h1 := ih hprev
    -- multiply the inductive bound by `3c + 1`
    have h2 : (3 * c + 1) * (c * (3 * c + 1) ^ a)
        ≤ (3 * c + 1) * ((c + 2 * a) * (3 ^ a * c ^ a)) := Nat.mul_le_mul_left _ h1
    -- the numeric step `(3c+1)(c+2a) ≤ 3c(c+2a+2)`
    have h3 : (3 * c + 1) * (c + 2 * a) ≤ (3 * c) * (c + 2 * a + 2) := by
      have e1 : (3 * c + 1) * (c + 2 * a) = 3 * c * (c + 2 * a) + (c + 2 * a) := by
        rw [Nat.add_mul, Nat.one_mul]
      have e2 : (3 * c) * (c + 2 * a + 2) = 3 * c * (c + 2 * a) + 6 * c := by
        rw [Nat.mul_add]
        have : 3 * c * 2 = 6 * c := by omega
        rw [this]
      have hcore : c + 2 * a ≤ 6 * c := by omega
      omega
    have h4 : (3 * c + 1) * ((c + 2 * a) * (3 ^ a * c ^ a))
        ≤ ((3 * c) * (c + 2 * a + 2)) * (3 ^ a * c ^ a) := by
      have e : (3 * c + 1) * ((c + 2 * a) * (3 ^ a * c ^ a))
          = ((3 * c + 1) * (c + 2 * a)) * (3 ^ a * c ^ a) := by
        rw [Nat.mul_assoc]
      rw [e]
      exact Nat.mul_le_mul_right _ h3
    have eL : c * (3 * c + 1) ^ (a + 1) = (3 * c + 1) * (c * (3 * c + 1) ^ a) := by
      rw [Nat.pow_succ]
      simp [Nat.mul_comm, Nat.mul_left_comm]
    have eR : (c + 2 * (a + 1)) * (3 ^ (a + 1) * c ^ (a + 1))
        = ((3 * c) * (c + 2 * a + 2)) * (3 ^ a * c ^ a) := by
      rw [Nat.pow_succ, Nat.pow_succ]
      have hc : c + 2 * (a + 1) = c + 2 * a + 2 := by omega
      rw [hc]
      simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    rw [eL, eR]
    exact Nat.le_trans h2 h4

/-! ## The explicit pin -/

/-- **The explicit two-sided pin.**  If a single constant `c` lies below the whole
forward orbit of `x`, then for every window length `k`

`3 ^ (a k) · x ≤ 2 ^ k · T^k(x)`  and  `c · (2 ^ k · T^k(x)) ≤ (c + 2·a k) · (3 ^ (a k) · x)`.

The pin constant is `1 + 2·a k / c`, an explicit rational, where
`FloorSchedule.sched_pin` had an unevaluated product. -/
theorem pin_explicit {x c k : Nat} (hpos : 0 < c)
    (hc : ∀ i : Nat, c ≤ acceleratedOrbit i x)
    (hrange : 2 * oddCount x k ≤ 5 * c) :
    3 ^ oddCount x k * x ≤ 2 ^ k * acceleratedOrbit k x ∧
      c * (2 ^ k * acceleratedOrbit k x)
        ≤ (c + 2 * oddCount x k) * (3 ^ oddCount x k * x) := by
  refine ⟨FloorSchedule.pin_lower x k, ?_⟩
  have hpow : 0 < c ^ oddCount x k := Nat.pow_pos hpos
  have hsched := FloorSchedule.sched_generalises hc k
  -- `c ^ a * (2 ^ k * x_k) ≤ (3c+1) ^ a * x`
  have h1 : c ^ oddCount x k * (2 ^ k * acceleratedOrbit k x)
      ≤ (3 * c + 1) ^ oddCount x k * x := by
    have e : c ^ oddCount x k * (2 ^ k * acceleratedOrbit k x)
        = 2 ^ k * c ^ oddCount x k * acceleratedOrbit k x := by
      simp [Nat.mul_comm, Nat.mul_left_comm]
    rw [e]
    exact hsched
  have h2 : c * (c ^ oddCount x k * (2 ^ k * acceleratedOrbit k x))
      ≤ c * ((3 * c + 1) ^ oddCount x k * x) := Nat.mul_le_mul_left _ h1
  have h3 : c * ((3 * c + 1) ^ oddCount x k * x)
      ≤ ((c + 2 * oddCount x k) * (3 ^ oddCount x k * c ^ oddCount x k)) * x := by
    have e : c * ((3 * c + 1) ^ oddCount x k * x)
        = (c * (3 * c + 1) ^ oddCount x k) * x := by rw [Nat.mul_assoc]
    rw [e]
    exact Nat.mul_le_mul_right _ (pow_step_bound c (oddCount x k) hrange)
  have h4 : c ^ oddCount x k * (c * (2 ^ k * acceleratedOrbit k x))
      ≤ c ^ oddCount x k * ((c + 2 * oddCount x k) * (3 ^ oddCount x k * x)) := by
    have eL : c ^ oddCount x k * (c * (2 ^ k * acceleratedOrbit k x))
        = c * (c ^ oddCount x k * (2 ^ k * acceleratedOrbit k x)) := by
      simp [Nat.mul_comm, Nat.mul_left_comm]
    have eR : c ^ oddCount x k * ((c + 2 * oddCount x k) * (3 ^ oddCount x k * x))
        = ((c + 2 * oddCount x k) * (3 ^ oddCount x k * c ^ oddCount x k)) * x := by
      simp [Nat.mul_comm, Nat.mul_left_comm]
    rw [eL, eR]
    exact Nat.le_trans h2 h3
  exact Nat.le_of_mul_le_mul_left h4 hpow

/-- **The pin constant is `1 + 1/j` on a floor `2·j·k`.**  Raising the floor
shrinks the pin: any `c ≥ 2 · j · k` with `j ≥ 1` gives an error factor
`≤ 1 + 1/j`, in integer form `j · (2^k · T^k x) ≤ (j+1) · (3^(a k) · x)`. -/
theorem pin_ratio {x c k j : Nat} (hj : 0 < j) (hfloor : 2 * j * k ≤ c)
    (hc : ∀ i : Nat, c ≤ acceleratedOrbit i x) :
    j * (2 ^ k * acceleratedOrbit k x) ≤ (j + 1) * (3 ^ oddCount x k * x) := by
  have hk0 : 0 < k ∨ k = 0 := by omega
  rcases hk0 with hk | hk
  · have hcpos : 0 < c := by
      have : 0 < 2 * j * k := by
        have h1 : 0 < 2 * j := by omega
        exact Nat.mul_pos h1 hk
      omega
    have hak : oddCount x k ≤ k := AffineExact.oddCount_le_self x k
    have hrange : 2 * oddCount x k ≤ 5 * c := by
      have : 2 * k ≤ c := by
        have h2 : 2 * k ≤ 2 * j * k := Nat.mul_le_mul_right k (by omega)
        omega
      omega
    have hmain := (pin_explicit hcpos hc hrange).2
    -- `c ≥ 2jk ≥ 2j·a`, so `c + 2a ≤ c·(j+1)/j`
    have hja : 2 * j * oddCount x k ≤ c := by
      have : 2 * j * oddCount x k ≤ 2 * j * k := Nat.mul_le_mul_left _ hak
      omega
    have hstep : j * (c * (2 ^ k * acceleratedOrbit k x))
        ≤ j * ((c + 2 * oddCount x k) * (3 ^ oddCount x k * x)) :=
      Nat.mul_le_mul_left _ hmain
    have hcoef : j * (c + 2 * oddCount x k) ≤ (j + 1) * c := by
      have e1 : j * (c + 2 * oddCount x k) = j * c + j * (2 * oddCount x k) :=
        Nat.mul_add _ _ _
      have e2 : j * (2 * oddCount x k) = 2 * j * oddCount x k := by
        simp [Nat.mul_comm, Nat.mul_left_comm]
      have e3 : (j + 1) * c = j * c + c := by rw [Nat.add_mul, Nat.one_mul]
      omega
    have hcmp : j * ((c + 2 * oddCount x k) * (3 ^ oddCount x k * x))
        ≤ ((j + 1) * c) * (3 ^ oddCount x k * x) := by
      have e : j * ((c + 2 * oddCount x k) * (3 ^ oddCount x k * x))
          = (j * (c + 2 * oddCount x k)) * (3 ^ oddCount x k * x) := by
        rw [Nat.mul_assoc]
      rw [e]
      exact Nat.mul_le_mul_right _ hcoef
    have hfin : c * (j * (2 ^ k * acceleratedOrbit k x))
        ≤ c * ((j + 1) * (3 ^ oddCount x k * x)) := by
      have eL : c * (j * (2 ^ k * acceleratedOrbit k x))
          = j * (c * (2 ^ k * acceleratedOrbit k x)) := by
        simp [Nat.mul_comm, Nat.mul_left_comm]
      have eR : c * ((j + 1) * (3 ^ oddCount x k * x))
          = ((j + 1) * c) * (3 ^ oddCount x k * x) := by
        simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      rw [eL, eR]
      exact Nat.le_trans hstep hcmp
    exact Nat.le_of_mul_le_mul_left hfin hcpos
  · subst hk
    have h0 : oddCount x 0 = 0 := by simp [oddCount, parityVector]
    rw [h0]
    simp [acceleratedOrbit]
    have : j * x ≤ (j + 1) * x := Nat.mul_le_mul_right _ (by omega)
    omega

/-- **The factor-two pin.**  A floor above twice the window length gives error `2`. -/
theorem pin_two {x c k : Nat} (hfloor : 2 * k ≤ c)
    (hc : ∀ i : Nat, c ≤ acceleratedOrbit i x) :
    2 ^ k * acceleratedOrbit k x ≤ 2 * (3 ^ oddCount x k * x) := by
  have h := pin_ratio (j := 1) (by omega) (by omega) hc
  omega

/-- **The pin constant tends to `1` along a divergent orbit.**  Hypothesis: the
orbit is eventually above every bound — the exact content of divergence, and
available on the divergence half only.  Conclusion: for every window length `k`
and every accuracy `j`, some tail start `N` has

`j · (2 ^ k · T^k(y)) ≤ (j+1) · (3 ^ (a k) · y)`,   `y = T^N(x)`,

i.e. the archimedean coordinate and the word datum agree to within `1 + 1/j`.
Together with `FloorSchedule.pin_lower` (which needs no hypothesis) this is a
two-sided pin with error `→ 1`.  Round IX's "one open bit" is therefore *zero*
bits asymptotically on the divergence half: `log₂ x_{N+k} − log₂ x_N` is the word
statistic `a·log₂3 − k` in the limit, and no quantity coupling the two data can
be a function of neither. -/
theorem pin_tends_to_one {x : Nat}
    (hdiv : ∀ B : Nat, ∃ N : Nat, ∀ i : Nat, N ≤ i → B ≤ acceleratedOrbit i x)
    (k j : Nat) (hj : 0 < j) :
    ∃ N : Nat, j * (2 ^ k * acceleratedOrbit k (acceleratedOrbit N x))
      ≤ (j + 1) * (3 ^ oddCount (acceleratedOrbit N x) k * acceleratedOrbit N x) := by
  obtain ⟨N, hN⟩ := hdiv (2 * j * k)
  refine ⟨N, ?_⟩
  refine pin_ratio (c := 2 * j * k) hj (Nat.le_refl _) ?_
  intro i
  have e : acceleratedOrbit i (acceleratedOrbit N x) = acceleratedOrbit (i + N) x :=
    acceleratedOrbit_add i N x
  rw [e]
  exact hN (i + N) (by omega)

/-! ## What it sees, and what it forbids -/

/-- **The deficit lower bound.**  Under a floor above `2k`, the 2-adic deficit
`3 ^ (a k) / 2 ^ k` is at least `T^k(x) / (2x)`: the deficit a divergent orbit
must run is *proportional to its archimedean gain*.  On a bounded orbit the
right-hand side is bounded; on a divergent one it is not. -/
theorem deficit_of_growth {x c k : Nat} (hfloor : 2 * k ≤ c)
    (hc : ∀ i : Nat, c ≤ acceleratedOrbit i x) :
    2 ^ k * acceleratedOrbit k x ≤ 2 * 3 ^ oddCount x k * x := by
  have h := pin_two hfloor hc
  have e : 2 * (3 ^ oddCount x k * x) = 2 * 3 ^ oddCount x k * x := by
    rw [Nat.mul_assoc]
  omega

/-- **The filter, in its final log-free form.**  If in addition the window does
not drop below its start (`x ≤ T^k(x)`), then

`2 ^ k ≤ 2 · 3 ^ (a k)`.

Every high never-dropping window of length `k` has at least
`k·log₃2 − log₃2` odd steps: heavy, with a *bounded* additive slack, uniformly in
`k`.  A divergent orbit must satisfy this for **every** `k`. -/
theorem heavy_of_never_drop {x c k : Nat} (hx : 0 < x) (hfloor : 2 * k ≤ c)
    (hc : ∀ i : Nat, c ≤ acceleratedOrbit i x)
    (hnd : x ≤ acceleratedOrbit k x) :
    2 ^ k ≤ 2 * 3 ^ oddCount x k := by
  have h := deficit_of_growth hfloor hc
  have hmono : 2 ^ k * x ≤ 2 ^ k * acceleratedOrbit k x := Nat.mul_le_mul_left _ hnd
  have hfin : 2 ^ k * x ≤ 2 * 3 ^ oddCount x k * x := Nat.le_trans hmono h
  have e : x * 2 ^ k ≤ x * (2 * 3 ^ oddCount x k) := by
    have e1 : x * 2 ^ k = 2 ^ k * x := Nat.mul_comm _ _
    have e2 : x * (2 * 3 ^ oddCount x k) = 2 * 3 ^ oddCount x k * x := Nat.mul_comm _ _
    omega
  exact Nat.le_of_mul_le_mul_left e hx

/-! ## The polarity check: vacuous on bounded orbits -/

/-- **Not a cycle detector.**  The trivial cycle has every orbit value `≤ 2`
(`BackwardRun.accOrbit_small`), so no floor `c` with `2k ≤ c` exists once
`k ≥ 2`: the hypothesis of every theorem above is *unsatisfiable* on a bounded
orbit.  This is the opposite polarity to every other filter in this
development, each of which is refuted by a genuine cycle of some `3x + d`. -/
theorem cycle_hypothesis_fails {c k : Nat} (hk : 2 ≤ k) (hfloor : 2 * k ≤ c)
    (hc : ∀ i : Nat, c ≤ acceleratedOrbit i 1) : False := by
  have h := hc 0
  have hsmall : acceleratedOrbit 0 1 ≤ 2 := BackwardRun.accOrbit_small 0 1 (by omega) (by omega)
  omega

/-- The same statement for the whole trivial cycle rather than its start: any
`x` with `0 < x ≤ 2` has a bounded orbit, so it admits no admissible floor. -/
theorem bounded_orbit_hypothesis_fails {x c k : Nat} (hx : 0 < x) (hx2 : x ≤ 2)
    (hk : 2 ≤ k) (hfloor : 2 * k ≤ c) (hc : ∀ i : Nat, c ≤ acceleratedOrbit i x) :
    False := by
  have h := hc 0
  have hsmall : acceleratedOrbit 0 x ≤ 2 := BackwardRun.accOrbit_small 0 x hx hx2
  omega

end GlobalHeight
end Collatz
