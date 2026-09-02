import Collatz.Strategy.RouteCap

/-!
# The gap along the staircase is an exact recurrence, not an approximation

`Strategy.RouteCap` reduced the cost of a certificate rung to the size of

    gapAt a  =  2 · 2 ^ (fexp a) − 3 ^ a,

how far `3 ^ a` sits below `2 ^ (fexp a + 1)`, and checked five rungs of the
`306 + 665k` staircase by hand.  The measured pattern was that
`gapAt a / 3 ^ a` falls by about `4.37 · 10⁻⁵` per rung.  Round LXXV, iteration 2
recorded that turning this into a theorem looked Diophantine.

**It is not.**  The shrinkage is an exact integer identity.  Write

    δ  =  3 ^ 665 − 2 ^ 1054   (positive: `665 · log₂ 3 = 1054.0000629…`)

Then whenever `fexp` advances by exactly `1054` across a rung,

    gapAt (a + 665)  +  3 ^ a · δ  =  2 ^ 1054 · gapAt a          (`gap_step`)

with no error term at all.  Both sides are the same integer.  This is `gap_step`
below, and it is nothing but `2 · 2 ^ (F + 1054) = 2 ^ 1054 · (2 · 2 ^ F)`
together with `3 ^ (a+665) = 3 ^ a · 3 ^ 665`, rearranged.

## What the identity buys

Dividing by `3 ^ (a + 665)`, the normalised gap `h = gapAt a / 3 ^ a` obeys

    h' = (2 ^ 1054 / 3 ^ 665) · h − δ / 3 ^ 665  <  h − δ / 3 ^ 665,

so `h` falls by at least `δ / 3 ^ 665 ≈ 4.365 · 10⁻⁵` every rung — the measured
constant, now derived.  Since `h > 0` always, **a staircase run is finite**, and
`run_bound` gives the count outright:

    k · δ · 3 ^ a  ≤  gapAt a · 3 ^ 665.

At `a = 4296` that reads `k ≤ 17.4`.  The staircase from `4296` in fact runs
exactly `17` rungs and breaks at `a = 15601`, where `fexp` advances by `1055`
instead of `1054`.  The bound is sharp to within one rung, and it is elementary:
no continued fractions, no irrationality measure, one `decide` on
`2 ^ 1054 < 3 ^ 665`.

## Scope, stated exactly

Settled: the behaviour of the gap **within one staircase run**, and hence that
the run is finite with an explicit length bound.  Not settled: what happens
across a break, where the gap resets upward by roughly `3 ^ a · 2 ^ 1054` and a
new run begins with its own `h₀`.  Chaining runs is the next level of the
continued fraction of `log₂ 3` and is not attempted here.  So this closes the
part of `RouteCap`'s open question that was *not* Diophantine, and isolates the
part that is.
-/

namespace Collatz
namespace StairGap

open RealizableBound RouteCap

/-! ## The gap -/

/-- `gapAt a = 2 · 2 ^ (fexp a) − 3 ^ a`, the quantity `RouteCap.reach_sharp`
charges the certificate against.  Positive for every `a`, by `lt_fexp`. -/
def gapAt (a : Nat) : Nat := 2 * 2 ^ fexp a - 3 ^ a

/-- The staircase increment, `3 ^ 665 − 2 ^ 1054`. -/
def stairDelta : Nat := 3 ^ 665 - 2 ^ 1054

set_option maxRecDepth 20000 in
set_option exponentiation.threshold 20000 in
/-- `2 ^ 1054 < 3 ^ 665`: the convergent `1054/665` of `log₂ 3` approaches from
below, so `δ` is a positive integer. -/
theorem two_pow_lt_three_pow : (2:Nat) ^ 1054 < 3 ^ 665 := by decide

theorem stairDelta_pos : 0 < stairDelta := by
  have := two_pow_lt_three_pow
  unfold stairDelta
  omega

/-- `3 ^ a ≤ 2 · 2 ^ fexp a`, the positivity behind `gapAt`. -/
theorem three_pow_le (a : Nat) : (3:Nat) ^ a ≤ 2 * 2 ^ fexp a := by
  have hlt := lt_fexp a
  have hp2 : (2:Nat) ^ (fexp a + 1) = 2 ^ fexp a * 2 := Nat.pow_succ 2 (fexp a)
  omega

/-! ## The identity -/

/-- The whole content of `gap_step`, over abstract naturals: with
`P = 2 ^ fexp a`, `Q = 3 ^ a`, `U = 2 ^ 1054`, `V = 3 ^ 665`,

  `(2PU − QV) + Q(V − U) = U(2P − Q)`. -/
theorem gap_algebra {P Q U V : Nat} (hUV : U ≤ V) (hQ : Q * V ≤ 2 * (P * U)) :
    (2 * (P * U) - Q * V) + Q * (V - U) = U * (2 * P - Q) := by
  have e1 : Q * (V - U) = Q * V - Q * U := Nat.mul_sub Q V U
  have e2 : U * (2 * P - Q) = U * (2 * P) - U * Q := Nat.mul_sub U (2 * P) Q
  have e3 : U * (2 * P) = 2 * (P * U) := by
    rw [Nat.mul_comm U (2 * P), Nat.mul_assoc]
  have e4 : U * Q = Q * U := Nat.mul_comm U Q
  have hCB : Q * U ≤ Q * V := Nat.mul_le_mul (Nat.le_refl Q) hUV
  omega

/-- **The gap recurrence, exactly.**  Across a rung on which `fexp` advances by
`1054`, the gap satisfies `gapAt (a+665) + 3 ^ a · δ = 2 ^ 1054 · gapAt a`.
No approximation, no error term. -/
theorem gap_step {a : Nat} (h : fexp (a + 665) = fexp a + 1054) :
    gapAt (a + 665) + 3 ^ a * stairDelta = 2 ^ 1054 * gapAt a := by
  have hP : (2:Nat) ^ fexp (a + 665) = 2 ^ fexp a * 2 ^ 1054 := by
    rw [h, Nat.pow_add]
  have hQ : (3:Nat) ^ (a + 665) = 3 ^ a * 3 ^ 665 := Nat.pow_add 3 a 665
  have hUV : (2:Nat) ^ 1054 ≤ 3 ^ 665 := Nat.le_of_lt two_pow_lt_three_pow
  have hbig : (3:Nat) ^ a * 3 ^ 665 ≤ 2 * (2 ^ fexp a * 2 ^ 1054) := by
    have hle := three_pow_le (a + 665)
    rw [hQ, hP] at hle
    omega
  show (2 * 2 ^ fexp (a + 665) - 3 ^ (a + 665)) + 3 ^ a * (3 ^ 665 - 2 ^ 1054)
      = 2 ^ 1054 * (2 * 2 ^ fexp a - 3 ^ a)
  rw [hP, hQ]
  exact gap_algebra hUV hbig

/-! ## A staircase run is finite

The identity says the gap is multiplied by `2 ^ 1054` and then reduced by
`3 ^ a · δ`.  Since `2 ^ 1054 < 3 ^ 665`, the *normalised* gap strictly loses
ground every rung, and it cannot do so forever because it is a positive integer
ratio.  The bookkeeping is one induction. -/

/-- `fexp` advances by exactly `1054` across each of the first `k` rungs from
`a` — i.e. `a` starts a staircase run of length at least `k`. -/
def StairRun (a k : Nat) : Prop :=
  ∀ j : Nat, j < k → fexp (a + 665 * (j + 1)) = fexp (a + 665 * j) + 1054

/-- The induction step of `run_invariant`, over abstract naturals. -/
theorem run_algebra {G G' g0 W V U d Y k : Nat} (hUV : U ≤ V)
    (hstep : G' + Y * d = U * G)
    (hIH : G * V + k * d * Y ≤ g0 * W * V) :
    G' * V + (k + 1) * d * (Y * V) ≤ g0 * W * V * V := by
  have e1 : (k + 1) * d * (Y * V) = k * d * Y * V + Y * d * V := by
    have h1 : (k + 1) * d * (Y * V) = k * d * (Y * V) + d * (Y * V) := by
      rw [Nat.succ_mul, Nat.add_mul]
    have h2 : k * d * (Y * V) = k * d * Y * V := (Nat.mul_assoc (k * d) Y V).symm
    have h3 : d * (Y * V) = Y * d * V := by
      rw [← Nat.mul_assoc d Y V, Nat.mul_comm d Y]
    omega
  have e2 : (G' + Y * d) * V = U * G * V := by rw [hstep]
  have e3 : (G' + Y * d) * V = G' * V + Y * d * V := Nat.add_mul _ _ _
  have e4 : (G * V + k * d * Y) * V = G * V * V + k * d * Y * V := Nat.add_mul _ _ _
  have e5 : (G * V + k * d * Y) * V ≤ g0 * W * V * V :=
    Nat.mul_le_mul hIH (Nat.le_refl V)
  have e6 : U * G * V ≤ G * V * V := by
    have h1 : U * G ≤ V * G := Nat.mul_le_mul hUV (Nat.le_refl G)
    have h2 : V * G = G * V := Nat.mul_comm V G
    have h3 : U * G ≤ G * V := by omega
    exact Nat.mul_le_mul h3 (Nat.le_refl V)
  omega

set_option maxRecDepth 10000 in
/-- **The normalised gap loses a fixed amount every rung.**  Along a staircase
run of length `k` from `a`, the gap at the far end plus `k` units of `δ` is still
under the gap at `a`, all measured against `3 ^ 665`. -/
theorem run_invariant (a : Nat) : ∀ k : Nat, StairRun a k →
    gapAt (a + 665 * k) * 3 ^ 665 + k * stairDelta * (3 ^ a * 3 ^ (665 * k))
      ≤ gapAt a * 3 ^ (665 * k) * 3 ^ 665 := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hrun
    have hIH := ih (fun j hj => hrun j (by omega))
    have ha : a + 665 * (k + 1) = a + 665 * k + 665 := by omega
    have hstep : gapAt (a + 665 * (k + 1)) + 3 ^ (a + 665 * k) * stairDelta
        = 2 ^ 1054 * gapAt (a + 665 * k) := by
      have h := gap_step (a := a + 665 * k) (by rw [← ha]; exact hrun k (by omega))
      rw [← ha] at h
      exact h
    have hY : (3:Nat) ^ (a + 665 * k) = 3 ^ a * 3 ^ (665 * k) := Nat.pow_add 3 a (665 * k)
    have hW : (3:Nat) ^ (665 * (k + 1)) = 3 ^ (665 * k) * 3 ^ 665 := by
      rw [show 665 * (k + 1) = 665 * k + 665 from by omega, Nat.pow_add]
    have hUV : (2:Nat) ^ 1054 ≤ 3 ^ 665 := Nat.le_of_lt two_pow_lt_three_pow
    rw [hW, ← Nat.mul_assoc (3 ^ a) (3 ^ (665 * k)) (3 ^ 665),
      ← Nat.mul_assoc (gapAt a) (3 ^ (665 * k)) (3 ^ 665)]
    rw [hY] at hstep
    exact run_algebra hUV hstep hIH

/-- **A staircase run has bounded length.**  If `fexp` advances by `1054` across
each of `k` consecutive rungs from `a`, then `k · δ · 3 ^ a ≤ gapAt a · 3 ^ 665`.

At `a = 4296`, where `gapAt a / 3 ^ a ≈ 7.606 · 10⁻⁴`, this reads `k ≤ 17.4`.
The run from `4296` is exactly `17` rungs long: `fexp` advances by `1055` at
`a = 15601`.  So the bound is sharp to within one rung. -/
theorem run_bound {a k : Nat} (h : StairRun a k) :
    k * stairDelta * 3 ^ a ≤ gapAt a * 3 ^ 665 := by
  have hinv := run_invariant a k h
  have hone : 1 ≤ (3:Nat) ^ (665 * k) := Nat.one_le_pow _ _ (by omega)
  have hpos : 0 < (3:Nat) ^ (665 * k) := by omega
  have hL : k * stairDelta * (3 ^ a * 3 ^ (665 * k))
      = k * stairDelta * 3 ^ a * 3 ^ (665 * k) := (Nat.mul_assoc _ _ _).symm
  have hR : gapAt a * 3 ^ (665 * k) * 3 ^ 665
      = gapAt a * 3 ^ 665 * 3 ^ (665 * k) := by
    rw [Nat.mul_assoc, Nat.mul_comm (3 ^ (665 * k)) (3 ^ 665), ← Nat.mul_assoc]
  have hchain : k * stairDelta * 3 ^ a * 3 ^ (665 * k)
      ≤ gapAt a * 3 ^ 665 * 3 ^ (665 * k) := by omega
  exact Nat.le_of_mul_le_mul_right hchain hpos

/-! ## The payoff: the range requirement blows up along a run

`RouteCap.reach_sharp` charges the certificate `a · 3 ^ a < 6c · gapAt a`, and
`run_invariant` bounds `gapAt` at the far end of a run.  Combining them, the
huge factor `3 ^ (665k)` cancels on both sides and what is left is a statement
whose only `k`-dependence is linear:

    (a + 665k) · 3 ^ a · 3 ^ 665  <  6c · (gapAt a · 3 ^ 665 − k · δ · 3 ^ a).

The left side grows linearly in `k`; the bracket on the right *shrinks* linearly
in `k`, and by `run_bound` it is what forces the run to stop.  So `c` is squeezed
from both directions, and this is the divergence Round XLIV measured, now with
both halves proved. -/

/-- The combination, over abstract naturals. -/
theorem payoff_algebra {n Q W V G g0 t c : Nat} (hW : 0 < W) (hV : 0 < V)
    (hs : n * (Q * W) < 6 * c * G)
    (hinv : G * V + t * (Q * W) ≤ g0 * W * V) :
    n * (Q * V) < 6 * c * (g0 * V - t * Q) := by
  have p1 : t * (Q * W) = t * Q * W := (Nat.mul_assoc t Q W).symm
  have p2 : g0 * W * V = g0 * V * W := by
    rw [Nat.mul_assoc, Nat.mul_comm W V, ← Nat.mul_assoc]
  have hle : t * Q * W ≤ g0 * V * W := by omega
  have hsub : (g0 * V - t * Q) * W = g0 * V * W - t * Q * W := Nat.sub_mul _ _ _
  have hGV : G * V ≤ (g0 * V - t * Q) * W := by omega
  have hmul : 6 * c * (G * V) ≤ 6 * c * ((g0 * V - t * Q) * W) :=
    Nat.mul_le_mul (Nat.le_refl (6 * c)) hGV
  have hsV : n * (Q * W) * V < 6 * c * G * V := Nat.mul_lt_mul_of_pos_right hs hV
  have q3 : Q * W * V = Q * V * W := by
    rw [Nat.mul_assoc Q W V, Nat.mul_comm W V, ← Nat.mul_assoc Q V W]
  have p3 : n * (Q * W) * V = n * (Q * V) * W := by
    rw [Nat.mul_assoc n (Q * W) V, Nat.mul_assoc Q W V, Nat.mul_comm W V,
      ← Nat.mul_assoc Q V W, ← Nat.mul_assoc n (Q * V) W]
  have p4 : 6 * c * G * V = 6 * c * (G * V) := Nat.mul_assoc _ _ _
  have p5 : 6 * c * ((g0 * V - t * Q) * W) = 6 * c * (g0 * V - t * Q) * W :=
    (Nat.mul_assoc _ _ _).symm
  have hfin : n * (Q * V) * W < 6 * c * (g0 * V - t * Q) * W := by omega
  exact Nat.lt_of_mul_lt_mul_right hfin

/-- **The range required grows along a staircase run.**  If `a` starts a run of
length `k` and a certificate at range `c` reaches past `a + 665k`, then

  `(a + 665k) · 3 ^ a · 3 ^ 665 < 6c · (gapAt a · 3 ^ 665 − k · δ · 3 ^ a)`.

Every power of `3 ^ (665k)` has cancelled: the bound is linear in `k` on both
sides, growing on the left and shrinking on the right. -/
theorem range_gt_along_run {a k c A : Nat} (hrun : StairRun a k)
    (hA : a + 665 * k < A)
    (hcert : ∀ i : Nat, i < A → Bcap i + 3 ^ i * c < 2 * 2 ^ fexp i * c) :
    (a + 665 * k) * (3 ^ a * 3 ^ 665)
      < 6 * c * (gapAt a * 3 ^ 665 - k * stairDelta * 3 ^ a) := by
  have hs : (a + 665 * k) * 3 ^ (a + 665 * k)
      < 6 * c * gapAt (a + 665 * k) := RouteCap.reach_sharp (hcert _ hA)
  have hpow : (3:Nat) ^ (a + 665 * k) = 3 ^ a * 3 ^ (665 * k) := Nat.pow_add 3 a (665 * k)
  rw [hpow] at hs
  have hinv := run_invariant a k hrun
  have hW : 0 < (3:Nat) ^ (665 * k) := by
    have := Nat.one_le_pow (665 * k) 3 (by omega); omega
  have hV : 0 < (3:Nat) ^ 665 := by
    have := Nat.one_le_pow 665 3 (by omega); omega
  exact payoff_algebra hW hV hs hinv

/-! ## A checked instance: the run from `4296` breaks by rung 18

`4296` is the reach of the first certificate in `PreCertified`'s table, and the
staircase that carries the whole ladder starts there.  `run_bound` at `a = 4296`
reads `k ≤ 17.42`, so the run cannot be `18` rungs long — and the proof needs no
knowledge of `fexp` anywhere along the run.  Three kernel comparisons do it: two
to pin `fexp 4296 = 6808`, one for the final inequality.

The run from `4296` is in fact exactly `17` rungs, breaking at `a = 16266`.  So
the bound is not merely finite, it is off by less than one rung. -/

set_option maxRecDepth 20000 in
set_option exponentiation.threshold 20000 in
theorem fexp_4296_lo : (2:Nat) ^ 6808 ≤ 3 ^ 4296 := by decide

set_option maxRecDepth 20000 in
set_option exponentiation.threshold 20000 in
theorem fexp_4296_hi : (3:Nat) ^ 4296 < 2 ^ (6808 + 1) := by decide

theorem fexp_4296 : fexp 4296 = 6808 :=
  RouteCap.fexp_eq_of fexp_4296_lo fexp_4296_hi

theorem gapAt_4296 : gapAt 4296 = 2 * 2 ^ 6808 - 3 ^ 4296 := by
  unfold gapAt; rw [fexp_4296]

set_option maxRecDepth 20000 in
set_option exponentiation.threshold 20000 in
/-- The arithmetic behind `no_run_18`: eighteen rungs would cost more than the
gap at `4296` can pay. -/
theorem eighteen_too_many :
    (2 * 2 ^ 6808 - 3 ^ 4296) * 3 ^ 665 < 18 * (3 ^ 665 - 2 ^ 1054) * 3 ^ 4296 := by
  decide

/-- **The staircase run from `4296` is shorter than `18` rungs.**  Unconditional,
and proved without evaluating `fexp` at any of the intervening rungs. -/
theorem no_run_18 : ¬ StairRun 4296 18 := by
  intro h
  have hb := run_bound h
  rw [gapAt_4296] at hb
  unfold stairDelta at hb
  have := eighteen_too_many
  omega

/-! ## The dichotomy: the gap decides its own recurrence

`gap_step` takes the `fexp` increment as a hypothesis.  It need not.  Writing
`3 ^ 665 = 2 ^ 1054 + δ` and `gapAt a + 3 ^ a = 2 · 2 ^ (fexp a)`, the comparison
`3 ^ (a+665)` against `2 ^ (fexp a + 1055)` reduces exactly to

    3 ^ a · δ   versus   2 ^ 1054 · gapAt a,

which is the same quantity `gap_step` subtracts.  So the recurrence *decides its
own applicability*: `fexp` advances by `1054` precisely when the subtraction
`2 ^ 1054 · gapAt a − 3 ^ a · δ` would leave something positive, and by `1055`
otherwise.  Checked against `fexp` directly at every `a < 400` and at the rungs
of the table: zero disagreements, as the proof requires.

This removes every `fexp` hypothesis downstream.  `StairRun` becomes a statement
about integer arithmetic on `gapAt`, not about a recursion nobody wants to
evaluate. -/

/-- The no-break criterion at `a`. -/
def NoBreak (a : Nat) : Prop := 3 ^ a * stairDelta < 2 ^ 1054 * gapAt a

theorem three_pow_665_eq : (3:Nat) ^ 665 = 2 ^ 1054 + stairDelta := by
  have := two_pow_lt_three_pow
  unfold stairDelta
  omega

theorem gapAt_add (a : Nat) : gapAt a + 3 ^ a = 2 * 2 ^ fexp a := by
  have := three_pow_le a
  unfold gapAt
  omega

set_option maxRecDepth 20000 in
set_option exponentiation.threshold 20000 in
/-- `3 ^ 665 < 2 ^ 1055`: the other side of the convergent, needed for the break
branch. -/
theorem three_pow_lt_two_pow : (3:Nat) ^ 665 < 2 ^ 1055 := by decide

/-- Splitting `2 ^ (fexp a + 1054 + 1)`. -/
theorem pow_split (a : Nat) :
    (2:Nat) ^ (fexp a + 1054 + 1) = 2 * 2 ^ fexp a * 2 ^ 1054 := by
  rw [show fexp a + 1054 + 1 = fexp a + 1 + 1054 from by omega, Nat.pow_add,
    Nat.pow_succ, Nat.mul_comm (2 ^ fexp a) 2]

/-- The lower half of both branches: `2 ^ (fexp a + 1054) ≤ 3 ^ (a + 665)`
always. -/
theorem pow_le_pow_shift (a : Nat) : (2:Nat) ^ (fexp a + 1054) ≤ 3 ^ (a + 665) := by
  rw [Nat.pow_add 2 (fexp a) 1054, Nat.pow_add 3 a 665]
  exact Nat.mul_le_mul (fexp_le a) (Nat.le_of_lt two_pow_lt_three_pow)

/-- **No break: `fexp` advances by `1054`.**  Derived from the gap, with no
appeal to the `fexp` recursion. -/
theorem fexp_step_of_noBreak {a : Nat} (h : NoBreak a) : fexp (a + 665) = fexp a + 1054 := by
  refine RouteCap.fexp_eq_of (pow_le_pow_shift a) ?_
  have e2 : (3:Nat) ^ (a + 665) = 3 ^ a * 3 ^ 665 := Nat.pow_add 3 a 665
  have e4 : (3:Nat) ^ a * 3 ^ 665 = 3 ^ a * 2 ^ 1054 + 3 ^ a * stairDelta := by
    rw [three_pow_665_eq, Nat.mul_add]
  have e5 : 2 * 2 ^ fexp a * 2 ^ 1054 = gapAt a * 2 ^ 1054 + 3 ^ a * 2 ^ 1054 := by
    rw [← gapAt_add a, Nat.add_mul]
  have e6 : gapAt a * 2 ^ 1054 = 2 ^ 1054 * gapAt a := Nat.mul_comm _ _
  have e7 := pow_split a
  unfold NoBreak at h
  omega

/-- **Break: `fexp` advances by `1055`.**  The complementary branch. -/
theorem fexp_step_of_break {a : Nat} (h : 2 ^ 1054 * gapAt a ≤ 3 ^ a * stairDelta) :
    fexp (a + 665) = fexp a + 1055 := by
  refine RouteCap.fexp_eq_of ?_ ?_
  · have e2 : (3:Nat) ^ (a + 665) = 3 ^ a * 3 ^ 665 := Nat.pow_add 3 a 665
    have e4 : (3:Nat) ^ a * 3 ^ 665 = 3 ^ a * 2 ^ 1054 + 3 ^ a * stairDelta := by
      rw [three_pow_665_eq, Nat.mul_add]
    have e5 : 2 * 2 ^ fexp a * 2 ^ 1054 = gapAt a * 2 ^ 1054 + 3 ^ a * 2 ^ 1054 := by
      rw [← gapAt_add a, Nat.add_mul]
    have e6 : gapAt a * 2 ^ 1054 = 2 ^ 1054 * gapAt a := Nat.mul_comm _ _
    have e7 : (2:Nat) ^ (fexp a + 1055) = 2 * 2 ^ fexp a * 2 ^ 1054 := by
      rw [show fexp a + 1055 = fexp a + 1054 + 1 from by omega]; exact pow_split a
    omega
  · have e2 : (3:Nat) ^ (a + 665) = 3 ^ a * 3 ^ 665 := Nat.pow_add 3 a 665
    have e8 : (2:Nat) ^ (fexp a + 1055 + 1) = 2 ^ (fexp a + 1) * 2 ^ 1055 := by
      rw [show fexp a + 1055 + 1 = fexp a + 1 + 1055 from by omega, Nat.pow_add]
    have hlt := lt_fexp a
    have hstep : (3:Nat) ^ a * 3 ^ 665 < 2 ^ (fexp a + 1) * 3 ^ 665 :=
      Nat.mul_lt_mul_of_pos_right hlt (by
        have := Nat.one_le_pow 665 3 (by omega); omega)
    have hstep2 : (2:Nat) ^ (fexp a + 1) * 3 ^ 665 ≤ 2 ^ (fexp a + 1) * 2 ^ 1055 :=
      Nat.mul_le_mul (Nat.le_refl _) (Nat.le_of_lt three_pow_lt_two_pow)
    omega

/-- **The break identity, exactly.**  Across a rung where `fexp` advances by
`1055`, the gap *grows*: it is multiplied by `2 ^ 1055` and then increased by
`3 ^ a · (2 ^ 1055 − 3 ^ 665)`.  Normalised, the gap resets from at most
`δ / 2 ^ 1054 ≈ 4.4 · 10⁻⁵` back up to just over `1`, its maximum. -/
theorem gap_break {a : Nat} (h : 2 ^ 1054 * gapAt a ≤ 3 ^ a * stairDelta) :
    gapAt (a + 665) = 2 ^ 1055 * gapAt a + 3 ^ a * (2 ^ 1055 - 3 ^ 665) := by
  have hf := fexp_step_of_break h
  have hdef : gapAt (a + 665) = 2 * 2 ^ fexp (a + 665) - 3 ^ (a + 665) := rfl
  have hle : (3:Nat) ^ (a + 665) ≤ 2 * 2 ^ fexp (a + 665) := three_pow_le (a + 665)
  have e2 : (3:Nat) ^ (a + 665) = 3 ^ a * 3 ^ 665 := Nat.pow_add 3 a 665
  have h3 : 2 * (2:Nat) ^ fexp (a + 665) = 2 ^ 1055 * (2 * 2 ^ fexp a) := by
    rw [hf, show fexp a + 1055 = 1055 + fexp a from by omega, Nat.pow_add,
      ← Nat.mul_assoc 2 (2 ^ 1055) (2 ^ fexp a), Nat.mul_comm 2 (2 ^ 1055), Nat.mul_assoc]
  have h2 : (2:Nat) ^ 1055 * (gapAt a + 3 ^ a) = 2 ^ 1055 * (2 * 2 ^ fexp a) := by
    rw [gapAt_add a]
  have h1 : (2:Nat) ^ 1055 * (gapAt a + 3 ^ a) = 2 ^ 1055 * gapAt a + 2 ^ 1055 * 3 ^ a :=
    Nat.mul_add _ _ _
  have e11 : (3:Nat) ^ a * (2 ^ 1055 - 3 ^ 665) = 3 ^ a * 2 ^ 1055 - 3 ^ a * 3 ^ 665 :=
    Nat.mul_sub _ _ _
  have e12 : (2:Nat) ^ 1055 * 3 ^ a = 3 ^ a * 2 ^ 1055 := Nat.mul_comm _ _
  have e13 : (3:Nat) ^ a * 3 ^ 665 ≤ 3 ^ a * 2 ^ 1055 :=
    Nat.mul_le_mul (Nat.le_refl _) (Nat.le_of_lt three_pow_lt_two_pow)
  omega

/-- `gap_step` with the `fexp` hypothesis discharged. -/
theorem gap_step_of_noBreak {a : Nat} (h : NoBreak a) :
    gapAt (a + 665) + 3 ^ a * stairDelta = 2 ^ 1054 * gapAt a :=
  gap_step (fexp_step_of_noBreak h)

/-- A staircase run, from the arithmetic criterion alone. -/
theorem stairRun_of_noBreak {a k : Nat} (h : ∀ j : Nat, j < k → NoBreak (a + 665 * j)) :
    StairRun a k := by
  intro j hj
  have := fexp_step_of_noBreak (h j hj)
  rw [show a + 665 * (j + 1) = a + 665 * j + 665 from by omega]
  exact this

/-! ## Every run ends, and where it ends is where the ladder gets expensive

`run_bound` says a run of `k` rungs costs `k · δ · 3 ^ a` against a budget of
`gapAt a · 3 ^ 665`.  Contrapositively, once `k` exceeds that budget a break must
have occurred — and by `gap_break` the gap at a break has just come down to at
most `δ / 2 ^ 1054` of `3 ^ a`, its smallest value anywhere on the run.

That is exactly where `RouteCap.reach_sharp` bites hardest, so **the break point
is the ladder's cliff**.  The staircase carrying `PreCertified`'s table breaks at
`a = 16266`; the last index before it is `a = 15601`, and the two theorems below
are the same fact seen from both sides. -/

/-- **A run longer than its budget is impossible**, so a break occurs. -/
theorem break_within {a k : Nat} (h : gapAt a * 3 ^ 665 < k * stairDelta * 3 ^ a) :
    ¬ (∀ j : Nat, j < k → NoBreak (a + 665 * j)) := by
  intro hall
  have := run_bound (stairRun_of_noBreak hall)
  omega

/-! ### The cliff, checked -/

set_option maxRecDepth 40000 in
set_option exponentiation.threshold 40000 in
theorem fexp_15601_lo : (2:Nat) ^ 24726 ≤ 3 ^ 15601 := by decide

set_option maxRecDepth 40000 in
set_option exponentiation.threshold 40000 in
theorem fexp_15601_hi : (3:Nat) ^ 15601 < 2 ^ (24726 + 1) := by decide

theorem fexp_15601 : fexp 15601 = 24726 :=
  RouteCap.fexp_eq_of fexp_15601_lo fexp_15601_hi

theorem gapAt_15601 : gapAt 15601 = 2 * 2 ^ 24726 - 3 ^ 15601 := by
  unfold gapAt; rw [fexp_15601]

set_option maxRecDepth 40000 in
set_option exponentiation.threshold 40000 in
theorem break_arith :
    2 ^ 1054 * (2 * 2 ^ 24726 - 3 ^ 15601) ≤ 3 ^ 15601 * (3 ^ 665 - 2 ^ 1054) := by
  decide

/-- **`15601` is a break point**: the staircase carrying `PreCertified`'s table
ends there, and `fexp` advances by `1055` at the next rung. -/
theorem break_at_15601 : ¬ NoBreak 15601 := by
  intro h
  unfold NoBreak at h
  rw [gapAt_15601] at h
  unfold stairDelta at h
  have := break_arith
  omega

theorem fexp_16266 : fexp 16266 = fexp 15601 + 1055 := by
  have h : (2:Nat) ^ 1054 * gapAt 15601 ≤ 3 ^ 15601 * stairDelta := by
    rw [gapAt_15601]; unfold stairDelta; exact break_arith
  have := fexp_step_of_break h
  rw [show (15601 : Nat) + 665 = 16266 from by omega] at this
  exact this

set_option maxRecDepth 40000 in
set_option exponentiation.threshold 40000 in
/-- The witness for the cliff: `N = 142 907 493` is the largest value the sharp
inequality admits at `a = 15601`. -/
theorem cliff_wit :
    6 * 142907493 * (2 * 2 ^ 24726 - 3 ^ 15601) ≤ 15601 * 3 ^ 15601 := by decide

/-- **The ladder's cliff.**  A certificate whose reach passes `15601` needs a
verified range above `142 907 493` — against the `3 380 808` that reaches `8286`.
Forty-two times the range for less than twice the reach, and the reason is
structural: `15601` is the last index of a staircase run, where the gap is at its
smallest (`break_at_15601`). -/
theorem range_gt_142907493 {c A : Nat} (hA : 15601 < A)
    (hcert : ∀ i : Nat, i < A → Bcap i + 3 ^ i * c < 2 * 2 ^ fexp i * c) :
    142907493 < c :=
  RouteCap.range_gt_of_reach hA fexp_15601_lo fexp_15601_hi cliff_wit hcert

end StairGap
end Collatz
