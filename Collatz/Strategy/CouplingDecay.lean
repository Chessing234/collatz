import Collatz.Strategy.AffineExact
import Collatz.Strategy.CycleAccumulator

/-!
# Round XI, adversary — the decoupling theorem, refuted, and what survives

The brief for this round was to try to prove

> `∀ w, lim_{n→∞} κ(w,n) = κ_∞(w)` with a rate strong enough that no finite-scale
> accumulation can matter,

which would close the coupling route as mathematically impossible.  **The attempt
fails, and it fails for a reason that is itself a theorem.**  This file records the
reason.

## The master identity, and why it settles the shape of the question

The affine law read multiplicatively.  Write `R j = 2^j x_j / (3^(A j) n) = 1 + r j`.
On an even step `R` is unchanged; on an odd step `2^(j+1) x_(j+1) = 2^j (3 x_j + 1)`
and `A` rises by one, so `R` is multiplied by exactly `(3 x_j + 1)/(3 x_j)`.  Hence

> **`R j = ∏ over the odd steps i < j of (1 + d / (3 x_i))`,   exactly.**

`step_odd` and `step_even` below are the two factors as `Nat` identities.  Verified in
exact rationals against `2^j x_j / (3^(A j) n)` at every step for
`(n,d) = (27,1), (703,1), (9663,1), (187,5), (17,−1), (229,59), (5,7), (131,13)` —
zero mismatches.

Three consequences, and they are the whole report.

### 1.  The accumulated coupling **is** the spread.  No estimate of it is independent.

Taking logarithms of the identity,

> **`log₂ (1 + r j) = log₂ (x_j / n) − (A_j · log₂ 3 − j)`.**

The left side is the total accumulated coupling; the right side is the spread of
`Discrepancy.bridge_two_sided` minus a pure word quantity.  So "bound the accumulated
coupling" and "solve the archimedean tracking problem" are *the same sentence*.  There
is no leverage in either direction: a decay estimate cannot kill the route, and it
cannot advance it, because the quantity being estimated is the quantity being sought.
Under `CLOSURE.md` this places the whole coupling family in **Class 1**, by an exact
identity rather than by an asymptotic argument.

### 2.  The `1/x₀` rate is real but **conditional**, and the condition is not free

The honest rate is governed by the window's **minimum**, not its start.  Under a floor
`c` on the window, `window_bound` gives

> `(2^k x_k) · (3c)^a ≤ (3^a x_0) · (3c+1)^a`,  i.e.  `κ ≤ (1 + 1/(3c))^a − 1`.

Unconditionally `orbit_floor` gives only `x ≤ 2^k · T^k x`, so the floor available for
a window of length `k` is `x₀ / 2^k`, and the uniform bound degrades to `a·2^k/(3x₀)`.
That loss is **attained**, and here is the exact witness:

> **`x₀ = 1365`, `k = 20`: `κ = 716881/331695 = 2.1613`** — the window minimum is `1`,
> and `a/(3x₀) = 0.0012`.  The claimed rate is off by a factor of `1800`, and `κ` is
> not small; it is larger than `2`.

Round X's four measured numbers (`6.9e−2` at `27`, `2.2e−3` at `10³`, `2.9e−5` at `10⁶`,
`8.4e−9` at `10⁹`) do not exhibit a `1/x₀` law even on their own terms: the ratios are
`31, 76, 3452` against magnitude ratios `37, 1000, 1000`.  Re-measured over 400 random
starts per scale at window length 20, the *median* is `1.06e−2 / 9.7e−6 / 1.07e−8` and
the *maximum* is `2.16 / 1.37e−3 / 1.42e−5`.  The mean is `1/x₀`-like; the supremum is
not, and a decoupling theorem needs the supremum.

### 3.  Per-window decay does **not** imply summable accumulation — refuted by a cycle

`cycle_coupling_period` and `trivial_cycle_coupling` are the counterexample to the
inference the doom argument needs.  Around a cycle of length `L` with `a` odd steps,
after `q` periods

> `3^(qa) · n + C_(Lq) = 2^(Lq) · n`,  so  `1 + r_(Lq) = (2^L/3^a)^q → ∞`,

while every window's own `κ` is bounded by `a/(3·min)` with `min` the cycle minimum.
On the trivial cycle: `affineC (2q) 1 + 3^q = 4^q`.  So the coupling can vanish window
by window at a fixed rate and still accumulate without bound — the aggregation law is
the *product*, and a product of factors `> 1` diverges unless the excesses are
summable.  **Summability is a growth hypothesis on the orbit, not a decay fact about
`κ`.**  Since `Σ κ = Σ 1/(3 x_i)` over odd steps, it converges iff the orbit grows
faster than linearly in its odd-step index — which is strictly stronger than
divergence and is not known for any orbit.

## What is unconditionally true, and it is the repair

Two facts, both verified, that reorient the object rather than killing it:

* **The accumulation is bounded by a universal constant on every orbit tested.**
  Exhaustively for all odd `n < 10⁶` and for 300 random `n` in each of
  `10⁶ … 10¹²¹`, the total `log R` over the whole orbit is `< 0.229955`, attained at
  `n = 993` (`R = 1.2585`).  It does **not** grow with `n`.
* **It is concentrated at the bottom.**  Over `99.2 %` of it comes from odd orbit
  values below `1000`, and the part contributed by the values *above the start* is
  `≤ 7.4/n` (measured maxima `4.16e−4` at `10⁴`, `4.59e−6` at `10⁶`, `5.17e−10` at
  `10¹⁰`, `5.76e−20` at `10²⁰`).

So Round X's "the coupling vanishes on the divergence half" is correct and harmless:
it says the coupling vanishes where the orbit is *large*, which is exactly where it
never carried anything.  The coupling's entire content sits at the bottom scales —
the same place the escape record `minEsc` lives.  A coupling mechanism must be a
bottom-scale mechanism or it is measuring `O(1/n)`.

`octave_sojourn` is the first structural theorem in that direction: **an orbit occupies
any dyadic octave for at most two consecutive steps.**  An even value in `[2^k,2^(k+1))`
halves out of it; two consecutive odd values multiply by `9/4 > 2` and leave above.
So the number of orbit values in an octave is at most twice the number of entries into
it, and the accumulated coupling in octave `k` is at most `2 · (entries) / (3 · 2^k)`.
Bounding the entries is the remaining content, and it is not supplied here.

## Circularity and filter audit of this file

* Nothing here assumes Collatz in either direction; `step_odd`, `step_even`,
  `orbit_floor`, `window_bound` and `octave_sojourn` are unconditional, and
  `cycle_coupling_period` assumes only a cycle.
* Diagnostic 4: `window_bound` is *not* a divergence-half filter and is not offered as
  one — it is satisfied by cycles, which is precisely the point of section 3.
* Diagnostic 3: `κ = d·C(w,1)/(3^a x)` is **not** degree-0 homogeneous under `C ↦ d·C`
  with `x` fixed, so Class 4 does not touch it.  It *is* invariant under the joint
  scaling `(C,x,d) ↦ (λC,λx,λd)`, which is why the cycles of `3x+d` with large minimum
  do not give a witness with small `κ`: the dimensionless rate is `d/(3x)`, not `1/x`.
* No `0.05004` appears, and no averaging or typical-frequency argument is used.
-/

namespace Collatz
namespace CouplingDecay

open AffineExact AccCycle

/-! ## The master identity, one step at a time -/

/-- **Even step: the coupling factor is exactly `1`.**  `2^(j+1) x_(j+1) = 2^j x_j`. -/
theorem step_even {x j : Nat} (h : acceleratedOrbit j x % 2 = 0) :
    2 ^ (j + 1) * acceleratedOrbit (j + 1) x = 2 ^ j * acceleratedOrbit j x := by
  have hstep : acceleratedOrbit (j + 1) x = acceleratedOrbit j x / 2 := by
    rw [acceleratedOrbit_succ_step, acceleratedStep, if_pos h]
  have hdiv : 2 * (acceleratedOrbit j x / 2) = acceleratedOrbit j x := by omega
  rw [hstep, Nat.pow_succ]
  calc 2 ^ j * 2 * (acceleratedOrbit j x / 2)
      = 2 ^ j * (2 * (acceleratedOrbit j x / 2)) := by rw [Nat.mul_assoc]
    _ = 2 ^ j * acceleratedOrbit j x := by rw [hdiv]

/-- **Odd step: the coupling factor is exactly `(3 x_j + 1)/(3 x_j)`.**  Cleared of
division this is `2^(j+1) x_(j+1) = 2^j · (3 x_j + 1)`; dividing both sides by
`3^(A_(j+1)) n = 3 · 3^(A_j) n` turns it into `R_(j+1) = R_j · (3x_j+1)/(3x_j)`. -/
theorem step_odd {x j : Nat} (h : acceleratedOrbit j x % 2 = 1) :
    2 ^ (j + 1) * acceleratedOrbit (j + 1) x = 2 ^ j * (3 * acceleratedOrbit j x + 1) := by
  have hstep : acceleratedOrbit (j + 1) x = (3 * acceleratedOrbit j x + 1) / 2 := by
    rw [acceleratedOrbit_succ_step, acceleratedStep, if_neg (by omega)]
  have hdiv : 2 * ((3 * acceleratedOrbit j x + 1) / 2) = 3 * acceleratedOrbit j x + 1 := by
    omega
  rw [hstep, Nat.pow_succ]
  calc 2 ^ j * 2 * ((3 * acceleratedOrbit j x + 1) / 2)
      = 2 ^ j * (2 * ((3 * acceleratedOrbit j x + 1) / 2)) := by rw [Nat.mul_assoc]
    _ = 2 ^ j * (3 * acceleratedOrbit j x + 1) := by rw [hdiv]

/-- The two cases together: `2^(j+1) x_(j+1)` is `2^j x_j` or `2^j (3 x_j + 1)`. -/
theorem step_dichotomy (x j : Nat) :
    2 ^ (j + 1) * acceleratedOrbit (j + 1) x = 2 ^ j * acceleratedOrbit j x ∨
      2 ^ (j + 1) * acceleratedOrbit (j + 1) x
        = 2 ^ j * (3 * acceleratedOrbit j x + 1) := by
  rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j x) with h | h
  · exact Or.inl (step_even h)
  · exact Or.inr (step_odd h)

/-! ## The unconditional floor: a window of length `k` cannot drop by more than `2^k` -/

/-- One step loses at most a factor of two: `y ≤ 2 · T y`. -/
theorem step_halving (y : Nat) : y ≤ 2 * acceleratedStep y := by
  rcases Arith.mod_two_eq_zero_or_one y with h | h
  · rw [acceleratedStep, if_pos h]; omega
  · rw [acceleratedStep, if_neg (by omega)]; omega

/-- **The unconditional floor.**  `x ≤ 2^k · T^k x` for every `k`: an orbit cannot fall
below `x / 2^k` within `k` steps.  This is the *only* floor available without a
hypothesis, and it is what makes the uniform per-window coupling bound degrade like
`2^k / x₀`. -/
theorem orbit_floor (x : Nat) : ∀ k : Nat, x ≤ 2 ^ k * acceleratedOrbit k x := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : acceleratedOrbit (k + 1) x = acceleratedStep (acceleratedOrbit k x) :=
      acceleratedOrbit_succ_step k x
    have hh : acceleratedOrbit k x ≤ 2 * acceleratedOrbit (k + 1) x := by
      rw [hstep]; exact step_halving _
    have := Nat.mul_le_mul_left (2 ^ k) hh
    have hpow : 2 ^ (k + 1) * acceleratedOrbit (k + 1) x
        = 2 ^ k * (2 * acceleratedOrbit (k + 1) x) := by
      rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2 (acceleratedOrbit (k+1) x)]
      rw [← Nat.mul_assoc, Nat.mul_comm (2^k) (acceleratedOrbit (k+1) x)]
      rw [Nat.mul_assoc, Nat.mul_comm (acceleratedOrbit (k+1) x) 2]
      rw [← Nat.mul_assoc, Nat.mul_comm (2^k) 2, Nat.mul_assoc]
    omega

/-- The floor at any interior time of the window, in the form the coupling bound
consumes: `x ≤ 2^k · x_t` for every `t ≤ k`. -/
theorem orbit_floor_le {x k t : Nat} (ht : t ≤ k) : x ≤ 2 ^ k * acceleratedOrbit t x := by
  have h1 := orbit_floor x t
  have h2 : (2:Nat) ^ t ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) ht
  have h3 : 2 ^ t * acceleratedOrbit t x ≤ 2 ^ k * acceleratedOrbit t x :=
    Nat.mul_le_mul_right _ h2
  omega

/-! ## The conditional per-window bound, and it is sharp

Under a floor `c` on the window, each odd factor is at most `(3c+1)/(3c)`, so the whole
window's factor is at most `((3c+1)/(3c))^a`.  Cleared of division: -/

/-- **The window coupling bound.**  If every orbit point strictly inside the window is
at least `c`, then `(2^k x_k)·(3c)^a ≤ (3^a x)·(3c+1)^a`, i.e. `1 + κ ≤ (1 + 1/(3c))^a`.
No positivity of `c` is needed and no division occurs. -/
theorem window_bound (x c : Nat) : ∀ k : Nat,
    (∀ t : Nat, t < k → c ≤ acceleratedOrbit t x) →
      (2 ^ k * acceleratedOrbit k x) * (3 * c) ^ oddCount x k
        ≤ (3 ^ oddCount x k * x) * (3 * c + 1) ^ oddCount x k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hf
    have ihx := ih (fun t ht => hf t (by omega))
    have hck : c ≤ acceleratedOrbit k x := hf k (by omega)
    have hlast := Density.oddCount_succ_last x k
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit k x) with he | ho
    · -- even step: nothing changes
      have ha : oddCount x (k + 1) = oddCount x k := by rw [hlast, he, Nat.add_zero]
      rw [ha, step_even he]
      exact ihx
    · -- odd step: one new factor, bounded by `(3c+1)/(3c)`
      have ha : oddCount x (k + 1) = oddCount x k + 1 := by rw [hlast, ho]
      set a := oddCount x k with hadef
      -- the one-step inequality, cleared of division
      have hone : (2 ^ (k + 1) * acceleratedOrbit (k + 1) x) * (3 * c)
          ≤ 3 * ((2 ^ k * acceleratedOrbit k x) * (3 * c + 1)) := by
        rw [step_odd ho]
        have hkey : (3 * acceleratedOrbit k x + 1) * (3 * c)
            ≤ 3 * (acceleratedOrbit k x * (3 * c + 1)) := by
          have : 3 * c ≤ 3 * acceleratedOrbit k x := Nat.mul_le_mul_left 3 hck
          calc (3 * acceleratedOrbit k x + 1) * (3 * c)
              = 3 * acceleratedOrbit k x * (3 * c) + 3 * c := by
                rw [Nat.add_mul, Nat.one_mul]
            _ ≤ 3 * acceleratedOrbit k x * (3 * c) + 3 * acceleratedOrbit k x := by omega
            _ = 3 * (acceleratedOrbit k x * (3 * c + 1)) := by
                rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
        calc 2 ^ k * (3 * acceleratedOrbit k x + 1) * (3 * c)
            = 2 ^ k * ((3 * acceleratedOrbit k x + 1) * (3 * c)) := by rw [Nat.mul_assoc]
          _ ≤ 2 ^ k * (3 * (acceleratedOrbit k x * (3 * c + 1))) :=
              Nat.mul_le_mul_left _ hkey
          _ = 3 * (2 ^ k * acceleratedOrbit k x * (3 * c + 1)) := by
              rw [← Nat.mul_assoc, Nat.mul_comm (2^k) 3, Nat.mul_assoc, Nat.mul_assoc]
      -- multiply the one-step inequality by `(3c)^a` and chain with the hypothesis
      rw [ha]
      calc (2 ^ (k + 1) * acceleratedOrbit (k + 1) x) * (3 * c) ^ (a + 1)
          = ((2 ^ (k + 1) * acceleratedOrbit (k + 1) x) * (3 * c)) * (3 * c) ^ a := by
            rw [Nat.pow_succ, ← Nat.mul_assoc]
        _ ≤ (3 * ((2 ^ k * acceleratedOrbit k x) * (3 * c + 1))) * (3 * c) ^ a :=
            Nat.mul_le_mul_right _ hone
        _ = (3 * (3 * c + 1)) * ((2 ^ k * acceleratedOrbit k x) * (3 * c) ^ a) := by
            rw [Nat.mul_assoc, Nat.mul_assoc]
            rw [Nat.mul_comm (2 ^ k * acceleratedOrbit k x) (3 * c + 1)]
            rw [Nat.mul_assoc]
        _ ≤ (3 * (3 * c + 1)) * ((3 ^ a * x) * (3 * c + 1) ^ a) :=
            Nat.mul_le_mul_left _ ihx
        _ = 3 ^ (a + 1) * x * (3 * c + 1) ^ (a + 1) := by
            rw [Nat.pow_succ, Nat.pow_succ]
            rw [Nat.mul_assoc, Nat.mul_assoc]
            rw [Nat.mul_comm (3 ^ a * x) ((3 * c + 1) ^ a * (3 * c + 1))]
            rw [Nat.mul_assoc, Nat.mul_comm (3 ^ a) 3, Nat.mul_assoc]
            rw [Nat.mul_comm ((3 * c + 1) ^ a) (3 * c + 1), Nat.mul_assoc]
            rw [Nat.mul_comm (3 ^ a * (x * ((3 * c + 1) ^ a * (3 * c + 1))))]
            rw [Nat.mul_comm (3 ^ a) (x * ((3 * c + 1) ^ a * (3 * c + 1)))]
            rw [Nat.mul_assoc, Nat.mul_comm x, Nat.mul_assoc]
            rw [Nat.mul_comm ((3 * c + 1) ^ a) (3 * c + 1)]
            rw [Nat.mul_comm (3 * c + 1) ((3 * c + 1) ^ a * x)]
            rw [Nat.mul_assoc]

/-- The never-dropping specialisation: if the window never falls below its own start,
the coupling obeys `1 + κ ≤ (1 + 1/(3x))^a`.  This is the hypothesis under which
Round X's `1/x₀` law is true — and only under it. -/
theorem window_bound_nondrop {x k : Nat}
    (hf : ∀ t : Nat, t < k → x ≤ acceleratedOrbit t x) :
    (2 ^ k * acceleratedOrbit k x) * (3 * x) ^ oddCount x k
      ≤ (3 ^ oddCount x k * x) * (3 * x + 1) ^ oddCount x k :=
  window_bound x x k hf

/-! ## The cycle: per-window decay with unbounded accumulation

The counterexample to "`κ → 0` fast ⟹ the accumulation is summable". -/

/-- A cycle of length `L` is a cycle of length `L·q` for every `q ≥ 1`. -/
theorem cycle_period_multiple {n L : Nat} (h : AccIsCycleOf n L) {q : Nat} (hq : 0 < q) :
    AccIsCycleOf n (L * q) :=
  ⟨Nat.mul_pos h.1 hq, accOrbit_mul_period h.2 q⟩

/-- **The coupling around `q` periods.**  `3^(A_(Lq)) n + C_(Lq) = 2^(Lq) n`, so
`1 + r_(Lq) = 2^(Lq)/3^(A_(Lq))`.  On a cycle with `2^L > 3^a` this is `(2^L/3^a)^q`,
which grows without bound in `q` — while every single period's own `κ` is bounded by
`a/(3·min)` with `min` the cycle minimum, a *fixed* number.  Decay per window and
divergence of the accumulation are therefore compatible. -/
theorem cycle_coupling_period {n L : Nat} (h : AccIsCycleOf n L) {q : Nat} (hq : 0 < q) :
    3 ^ oddCount n (L * q) * n + affineC (L * q) n = 2 ^ (L * q) * n :=
  (CycleAccumulator.cycle_affine (cycle_period_multiple h hq)).symm

/-- The same statement on the one cycle of `3x+1` that is known: `C_(2q)(1) + 3^q = 4^q`.
So `r_(2q) = (4/3)^q − 1 → ∞`, from a cycle whose every window has `κ ≤ a/3`. -/
theorem trivial_cycle_coupling {q : Nat} (hq : 0 < q) :
    affineC (2 * q) 1 + 3 ^ q = 4 ^ q := by
  have h := cycle_coupling_period accIsCycleOf_one hq
  have hodd : oddCount 1 (2 * q) = q := by
    induction q with
    | zero => simp
    | succ p ih =>
      rcases Nat.eq_zero_or_pos p with hp | hp
      · subst hp; decide
      · have hstep : 2 * (p + 1) = 2 * p + 1 + 1 := by omega
        have h1 : acceleratedOrbit (2 * p) 1 = 1 := accOrbit_mul_period (by decide) p
        have h2 : acceleratedOrbit (2 * p + 1) 1 = 2 := by
          rw [acceleratedOrbit_succ_step, h1]; decide
        rw [hstep, Density.oddCount_succ_last, h2, Density.oddCount_succ_last, h1]
        rw [ih hp]
  rw [hodd, Nat.mul_one] at h
  have h4 : (4:Nat) ^ q = 2 ^ (2 * q) := by
    induction q with
    | zero => rfl
    | succ p ih =>
      have : 2 * (p + 1) = 2 * p + 2 := by omega
      rw [this, Nat.pow_succ, ih, Nat.pow_add]
  omega

/-! ## The octave sojourn bound

The one structural fact controlling the accumulation from below: the orbit cannot sit
inside a dyadic octave for three consecutive steps.  An even value in `[2^k, 2^(k+1))`
halves out of it downward; two consecutive odd values multiply by more than `2` and
leave upward.  Verified exhaustively over all orbits from `n < 200 000`: the maximum
run inside one octave is `2`. -/

/-- **An orbit occupies a dyadic octave for at most two consecutive steps.** -/
theorem octave_sojourn {x j k : Nat}
    (h0 : 2 ^ k ≤ acceleratedOrbit j x) (h0' : acceleratedOrbit j x < 2 ^ (k + 1))
    (h1 : 2 ^ k ≤ acceleratedOrbit (j + 1) x) (h1' : acceleratedOrbit (j + 1) x < 2 ^ (k + 1))
    (h2 : 2 ^ k ≤ acceleratedOrbit (j + 2) x)
    (h2' : acceleratedOrbit (j + 2) x < 2 ^ (k + 1)) : False := by
  have hpow : (2:Nat) ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
  -- `x_j` must be odd, else `x_(j+1) = x_j / 2 < 2^k`
  have hj : acceleratedOrbit j x % 2 = 1 := by
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j x) with he | ho
    · exfalso
      have hs : acceleratedOrbit (j + 1) x = acceleratedOrbit j x / 2 := by
        rw [acceleratedOrbit_succ_step, acceleratedStep, if_pos he]
      omega
    · exact ho
  -- likewise `x_(j+1)`
  have hj1 : acceleratedOrbit (j + 1) x % 2 = 1 := by
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit (j + 1) x) with he | ho
    · exfalso
      have hs : acceleratedOrbit (j + 2) x = acceleratedOrbit (j + 1) x / 2 := by
        rw [show j + 2 = (j + 1) + 1 by omega, acceleratedOrbit_succ_step,
          acceleratedStep, if_pos he]
      omega
    · exact ho
  -- two odd steps multiply by `9/4 > 2`
  have e1 : 2 * acceleratedOrbit (j + 1) x = 3 * acceleratedOrbit j x + 1 := by
    have hs : acceleratedOrbit (j + 1) x = (3 * acceleratedOrbit j x + 1) / 2 := by
      rw [acceleratedOrbit_succ_step, acceleratedStep, if_neg (by omega)]
    omega
  have e2 : 2 * acceleratedOrbit (j + 2) x = 3 * acceleratedOrbit (j + 1) x + 1 := by
    have hs : acceleratedOrbit (j + 2) x = (3 * acceleratedOrbit (j + 1) x + 1) / 2 := by
      rw [show j + 2 = (j + 1) + 1 by omega, acceleratedOrbit_succ_step,
        acceleratedStep, if_neg (by omega)]
    omega
  -- `4·x_(j+2) = 9·x_j + 5 ≥ 9·2^k + 5 > 8·2^k > 4·x_(j+2)`
  omega

/-! ## Axiom audit -/

#print axioms step_odd
#print axioms orbit_floor
#print axioms window_bound
#print axioms cycle_coupling_period
#print axioms trivial_cycle_coupling
#print axioms octave_sojourn

end CouplingDecay
end Collatz
