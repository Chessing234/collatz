import Collatz.Strategy.RealizableFrontier6809
import Collatz.Strategy.PrimeLedge
import Collatz.Strategy.GapVector

/-!
# The convergents of `log₂ 3` acting on valuation blocks

Round XV, brief section 14 (with section 13 folded in as a negative).

## What was open

`scripts/index.py` reports **`2-adic valuation ↔ Beatty/Sturmian` as an empty
concept pair**, and the reason is structural, not accidental: `GapVector` builds
the whole run-length calculus (`gapT`, `gapC`, `beattyGap`, `gapC_le_Bcap`) over a
*free* function `g : Nat → Nat` and never instantiates it at an actual orbit.  So
every Beatty statement in the repository is about `(L, a)` shapes or about abstract
gap vectors; none of them is about the 2-adic run lengths of a real trajectory.

Round XII's finding — the frontier ladder marches in steps of `665` in `a` and
`1054` in `L`, literally the continued fraction of `log₂ 3` — was likewise stated
on the `(L, a)` side, which the brief declares exhausted.  This file moves both to
the valuation side and reports what happens there.

## 1. The convergents, as shift laws for the Beatty ceiling

`fexp i = ⌊i log₂ 3⌋` is the Beatty ceiling.  The two convergents that flank
`log₂ 3` give **unconditional shift laws** for it, each a one-line consequence of a
kernel-checked inequality already in `PrimeLedge`:

| convergent | sign | inequality | shift law |
|---|---|---|---|
| `485/306` | `485 > 306 log₂3` | `3^306 ≤ 2^485` | `fexp (i+306) ≤ fexp i + 485` |
| `1054/665` | `1054 < 665 log₂3` | `2^1054 ≤ 3^665` | `fexp i + 1054 ≤ fexp (i+665)` |

(`fexp_shift_306`, `fexp_shift_665`.)  Iterated (`fexp_block_306`,
`fexp_block_665`) they read

`fexp (306 q) ≤ 485 q`   and   `1054 q ≤ fexp (665 q)`.

These are **valuation-block statements**, not `(L,a)` statements: `fexp a − a` is
exactly the number of *even* steps the Beatty box permits alongside `a` odd steps,
so the two laws constrain the permitted even-step count per odd step by

`389/665 = 0.5849624…`  (from below, at `a = 665q`)  and  `179/306 = 0.5849673…`
(from above, at `a = 306q`).

**Correction (Round XV adversary).  These are *not* a bracket, and an earlier draft
called them one.**  The two bounds hold at *different index progressions*, so no single
`a` is caught between them except where the progressions meet: over `a = 1 … 3000` the
ratio `(fexp a − a)/a` lies in `[0.5849624, 0.5849673]` for exactly **four** values —
`665, 1330, 1995, 2660`, the multiples of `665`.  What is proved is two one-sided
statements on two arithmetic progressions, which is weaker and must be cited that way.

The interval is also **not centred on `log₂3 − 1`**: its centre is `0.5849648631`
against `log₂3 − 1 = 0.5849625007`, which sits at `1.9%` across it, near the low end.
`0.5849625007` is *contained*, not central.

## 2. The block law for a real orbit

`RealizableFrontier6809.no_light_window` already contains, as an intermediate step,
`j ≤ fexp (oddCount m j)` for a never-dropping `m ≥ 1086464` with
`oddCount m j < 4296`.  It is extracted here as `orbit_time_le_fexp` and combined
with the shift law to give the theorem this file exists for:

**`even_steps_per_306` :** a never-dropping `m ≥ 1086464` takes **at most `179 q`
even steps** in any prefix containing exactly `306 q` odd steps (`306 q < 4296`,
i.e. `q ≤ 14`).

That is a continued-fraction constraint on 2-adic run lengths of an actual
trajectory, and it is the first statement in the repository that bridges the empty
pair.

## 3. The gap vector, instantiated at a real orbit

`gapT_gapC_of_orbit` closes the abstraction gap in `GapVector` directly: if
`g i` is the number of even steps between the `i`-th and `(i+1)`-st odd step of the
orbit of `x` — that is, `g i = v₂`-run length — then

`affineC (gapT g a) x = gapC g a`   and   `oddCount x (gapT g a) = a`.

So the free gap vector of `GapVector` *is* the orbit's valuation profile, and
`gapC_le_Bcap` / `gapC_eq_Bcap` now apply to real trajectories.  `orbit_run_box`
records the consequence: for a never-dropping `m ≥ 1086464` the orbit's cumulative
valuation times obey the Beatty box `gapT g i ≤ fexp i` outright.

## 4. Verdict — honest

**The convergents do constrain valuations, and they constrain them to exactly the
same number they constrain `(L, a)` to.**  The two shift laws pin the even-step
density to `[0.5849624, 0.5849673]`, an interval of width `4.9e−6`, and its centre
is `log₂ 3 − 1`.  Nothing else is available: a Sturmian word of slope `log₂ 3 − 1`
*is* `beattyGap` (`GapVector.gapT_beatty`), and `BeattyStability.corner_is_a_real_cycle`
shows that word is a genuine cycle of `x ↦ (3x+47)/2^v`, so no consequence of the
valuation profile alone can see `d = 1`.  The move to the valuation side is
therefore **Class 1 by identity**, exactly as the `(L,a)` side is — but the identity
is now proved rather than assumed, and the empty concept pair is filled.

## 5. The `expStep` test

`expStep x = 3x/2` (even), `(3x+1)/2` (odd).

* §1 (`fexp_shift_306`, `fexp_shift_665`, `fexp_block_*`) is pure arithmetic on
  `log₂ 3`; it has no dynamical content, so `expStep` **satisfies** it vacuously.
* §3 (`gapT_gapC_of_orbit`) uses only the two branch formulas at odd steps and
  `affineC_even` at even steps.  For `expStep` the even branch is `3x/2`, not
  `x/2`, so `affineC` is not its accumulator: the bridge **fails to apply**, but
  not for a reason that discriminates — the analogous bridge for `expStep`'s own
  accumulator is true.
* §2 (`orbit_time_le_fexp`, `even_steps_per_306`) **fails for `expStep`**, and this
  is the discriminating item.  It rests on `neverDrops_iff_affine` plus
  `affineC_le_Bcap`, both of which consume `2 · T(x) ≤ x` on the even branch.
  Take `n = 2^k`: every `expStep` step is even, `oddCount = 0`, `fexp 0 = 0`, and
  the claim `j ≤ 0` is false for every `j ≥ 1`.  As Round X predicted, the only
  live content is the even branch's exact contraction.

## 6. Section 13, reported as a negative

The brief asked whether the exact logarithmic cocycle plus **integrality** gives
anything the spread does not.  The natural candidate is: the correction factor at
an odd step is `(3x+1)/(3x)` with `x` a positive integer, so an integer floor `B`
below the whole window caps every factor at `(3B+1)/(3B)`, giving the
denominator-free

`2^L · B^a · T^L(n) ≤ n · (3B + 1)^a`.

**This is already `CycleProduct.product_invariant`** (and, in the `3B`-scaled form
with the window hypothesis `∀ t < k`, `CouplingDecay.window_bound`).  It was
re-derived independently here from the cocycle and then withdrawn as a duplicate.
Its `B = n` specialisation is `CycleProduct.neverDrops_product_bound`; feeding it
the affine identity gives the accumulator sandwich that `AffineExact`'s own header
already records as carrying **no new information**; and its sharp `a = 2` shadow is
`Structure.Minimal.mod_four_of_minimal` / `OrbitMinSieve.residue_mod_four`.  So the
answer to section 13 is **no**: integrality's only purchase on the cocycle is the
integer floor, and that purchase was spent in Round VIII.
-/

namespace Collatz
namespace ValuationBeatty

open Reach Congruence AffineExact RealizableBound GapVector

/-! ## 1. The convergents as shift laws for `fexp` -/

/-- **A convergent from above gives an upper shift law.**  If `3 ^ q ≤ 2 ^ p`
— that is, `p/q ≥ log₂ 3` — then `⌊(i+q) log₂3⌋ ≤ ⌊i log₂3⌋ + p` for every `i`. -/
theorem fexp_shift_le {p q : Nat} (h : (3:Nat) ^ q ≤ 2 ^ p) (i : Nat) :
    fexp (i + q) ≤ fexp i + p := by
  have hup : (3:Nat) ^ i < 2 ^ (fexp i + 1) := lt_fexp i
  have hlow : (2:Nat) ^ fexp (i + q) ≤ 3 ^ (i + q) := fexp_le (i + q)
  have hpos : 0 < (2:Nat) ^ p := Nat.pow_pos (by omega)
  have hsplit : (3:Nat) ^ (i + q) = 3 ^ i * 3 ^ q := Nat.pow_add 3 i q
  have hA : (3:Nat) ^ i * 3 ^ q ≤ 3 ^ i * 2 ^ p := Nat.mul_le_mul_left _ h
  have hsucc : (3:Nat) ^ i + 1 ≤ 2 ^ (fexp i + 1) := Nat.succ_le_of_lt hup
  have hB : ((3:Nat) ^ i + 1) * 2 ^ p ≤ 2 ^ (fexp i + 1) * 2 ^ p :=
    Nat.mul_le_mul_right _ hsucc
  have hE : ((3:Nat) ^ i + 1) * 2 ^ p = 3 ^ i * 2 ^ p + 2 ^ p := by
    rw [Nat.add_mul, Nat.one_mul]
  have hjoin : (2:Nat) ^ (fexp i + 1) * 2 ^ p = 2 ^ (fexp i + 1 + p) := by
    rw [← Nat.pow_add]
  rcases Nat.lt_or_ge (fexp i + p) (fexp (i + q)) with hcon | hok
  · exfalso
    have hmono : (2:Nat) ^ (fexp i + 1 + p) ≤ 2 ^ fexp (i + q) :=
      Arith.two_pow_le_two_pow (by omega)
    omega
  · exact hok

/-- **A convergent from below gives a lower shift law.**  If `2 ^ p ≤ 3 ^ q`
— that is, `p/q ≤ log₂ 3` — then `⌊i log₂3⌋ + p ≤ ⌊(i+q) log₂3⌋` for every `i`. -/
theorem fexp_shift_ge {p q : Nat} (h : (2:Nat) ^ p ≤ 3 ^ q) (i : Nat) :
    fexp i + p ≤ fexp (i + q) := by
  have hlow : (2:Nat) ^ fexp i ≤ 3 ^ i := fexp_le i
  have hsplit2 : (2:Nat) ^ (fexp i + p) = 2 ^ fexp i * 2 ^ p := Nat.pow_add 2 _ _
  have hsplit3 : (3:Nat) ^ (i + q) = 3 ^ i * 3 ^ q := Nat.pow_add 3 i q
  have hle : (2:Nat) ^ (fexp i + p) ≤ 3 ^ (i + q) := by
    rw [hsplit2, hsplit3]
    exact Nat.mul_le_mul hlow h
  exact le_fexp_of_pow_le hle

/-- **The `485/306` convergent, from above** (`3 ^ 306 ≤ 2 ^ 485`). -/
theorem fexp_shift_306 (i : Nat) : fexp (i + 306) ≤ fexp i + 485 :=
  fexp_shift_le PrimeLedge.three_pow_306_le i

/-- **The `1054/665` convergent, from below** (`2 ^ 1054 ≤ 3 ^ 665`). -/
theorem fexp_shift_665 (i : Nat) : fexp i + 1054 ≤ fexp (i + 665) :=
  fexp_shift_ge PrimeLedge.two_pow_1054_le i

/-- The `485/306` law iterated: `⌊306q · log₂3⌋ ≤ 485q`. -/
theorem fexp_block_306 : ∀ q : Nat, fexp (306 * q) ≤ 485 * q := by
  intro q
  induction q with
  | zero => exact Nat.le_refl 0
  | succ q ih =>
    have hidx : 306 * (q + 1) = 306 * q + 306 := by omega
    have h := fexp_shift_306 (306 * q)
    rw [hidx]
    omega

/-- The `1054/665` law iterated: `1054q ≤ ⌊665q · log₂3⌋`. -/
theorem fexp_block_665 : ∀ q : Nat, 1054 * q ≤ fexp (665 * q) := by
  intro q
  induction q with
  | zero => exact Nat.le_refl 0
  | succ q ih =>
    have hidx : 665 * (q + 1) = 665 * q + 665 := by omega
    have h := fexp_shift_665 (665 * q)
    rw [hidx]
    omega

/-- **The two convergents bracket the permitted even-step density.**  The Beatty
box allows at least `389` and at most `179 · 665/306` even steps per `665` odd
steps; cleared of division, `389 · q` from below at index `665q` and `179 · q` from
above at index `306q`.  `0.5849624 ≤ (fexp a − a)/a ≤ 0.5849673`. -/
theorem beatty_density_bracket (q : Nat) :
    389 * q + 665 * q ≤ fexp (665 * q) ∧ fexp (306 * q) ≤ 179 * q + 306 * q := by
  have h1 := fexp_block_665 q
  have h2 := fexp_block_306 q
  omega

/-! ## 2. The block law at a real orbit -/

/-- **A never-dropping orbit's odd-step times obey the Beatty ceiling.**  Extracted
from the interior of `RealizableFrontier6809.no_light_window`, where it is proved
but not named.

`expStep` fails this: with `n = 2^k` every `expStep` step is even, `oddCount = 0`,
`fexp 0 = 0`, and `j ≤ 0` is false for `j ≥ 1`. -/
theorem orbit_time_le_fexp {m j : Nat} (hc : 1086464 ≤ m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m) (hA : oddCount m j < 4296) :
    j ≤ fexp (oddCount m j) := by
  have hB : affineC j m ≤ Bcap (oddCount m j) :=
    affineC_le_Bcap (by omega) hc hnd RealizableFrontier6809.cert_1086464 j (by omega)
  exact le_fexp_of_affineC_le (by omega) hc hnd
    (RealizableFrontier6809.cert_1086464 _ hA) rfl hB

/-- **The continued fraction constrains the valuation blocks of a real orbit.**
A never-dropping `m ≥ 1086464` whose first `j` steps contain exactly `306 q` odd
steps has `j ≤ 485 q`, hence **at most `179 q` even steps**.

This is `485/306`, the convergent of `log₂ 3` that approximates from above,
acting directly on 2-adic run lengths — the bridge the index reports as missing
between the `2-adic valuation` and `Beatty/Sturmian` clusters. -/
theorem even_steps_per_306 {m j q : Nat} (hc : 1086464 ≤ m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m)
    (hcount : oddCount m j = 306 * q) (hA : 306 * q < 4296) :
    j ≤ 485 * q ∧ j - oddCount m j ≤ 179 * q := by
  have htime : j ≤ fexp (oddCount m j) := orbit_time_le_fexp hc hnd (by omega)
  rw [hcount] at htime
  have hblock := fexp_block_306 q
  exact ⟨by omega, by omega⟩

/-! ## 3. The gap vector, instantiated at a real orbit -/

/-- **One odd step followed by `r` even steps.**  The accumulator takes exactly one
Horner step and the odd count rises by exactly one, whatever `r` is. -/
theorem affineC_run {x j : Nat} (hodd : acceleratedOrbit j x % 2 = 1) :
    ∀ r : Nat, (∀ s : Nat, s < r → acceleratedOrbit (j + 1 + s) x % 2 = 0) →
      affineC (j + 1 + r) x = 3 * affineC j x + 2 ^ j
        ∧ oddCount x (j + 1 + r) = oddCount x j + 1 := by
  intro r
  induction r with
  | zero =>
    intro _
    have hc := Density.oddCount_succ_last x j
    have hidx : j + 1 + 0 = j + 1 := by omega
    rw [hidx]
    exact ⟨affineC_odd hodd, by omega⟩
  | succ r ih =>
    intro hev
    obtain ⟨hC, hO⟩ := ih (fun s hs => hev s (by omega))
    have heven : acceleratedOrbit (j + 1 + r) x % 2 = 0 := hev r (by omega)
    have hidx : j + 1 + (r + 1) = (j + 1 + r) + 1 := by omega
    have hc := Density.oddCount_succ_last x (j + 1 + r)
    rw [hidx]
    exact ⟨by rw [affineC_even heven]; exact hC, by omega⟩

/-- **The free gap vector of `GapVector` is the orbit's valuation profile.**
If `g i` is the number of even steps between the `i`-th and `(i+1)`-st odd step of
the orbit of `x` — the `i`-th 2-adic run length — then the abstract `gapT`/`gapC`
recursion computes the orbit's own odd-step times and accumulator:

`affineC (gapT g a) x = gapC g a`  and  `oddCount x (gapT g a) = a`.

`GapVector`'s box and extremality theorems (`gapC_le_Bcap`, `gapC_eq_Bcap`,
`gapT_beatty`, `gapC_beatty`) therefore now apply to actual trajectories. -/
theorem gapT_gapC_of_orbit {x : Nat} (g : Nat → Nat) :
    ∀ a : Nat,
      (∀ i : Nat, i < a → acceleratedOrbit (gapT g i) x % 2 = 1) →
      (∀ i : Nat, i < a → ∀ s : Nat, s < g i →
        acceleratedOrbit (gapT g i + 1 + s) x % 2 = 0) →
      affineC (gapT g a) x = gapC g a ∧ oddCount x (gapT g a) = a := by
  intro a
  induction a with
  | zero => intro _ _; exact ⟨rfl, rfl⟩
  | succ a ih =>
    intro hodd hev
    obtain ⟨hC, hO⟩ := ih (fun i hi => hodd i (by omega)) (fun i hi => hev i (by omega))
    have hstep := affineC_run (hodd a (Nat.lt_succ_self a)) (g a)
      (fun s hs => hev a (Nat.lt_succ_self a) s hs)
    rw [gapT_succ, gapC_succ]
    exact ⟨by rw [hstep.1, hC], by rw [hstep.2, hO]⟩

/-- **A never-dropping orbit's valuation profile sits inside the Beatty box.**
The hypothesis `gapT g i ≤ fexp i` that `GapVector.gapC_le_Bcap` assumes is
*derived* here for real trajectories above the verified range. -/
theorem orbit_run_box {m : Nat} (g : Nat → Nat) (hc : 1086464 ≤ m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m) {a : Nat} (ha : a < 4296)
    (hodd : ∀ i : Nat, i < a → acceleratedOrbit (gapT g i) m % 2 = 1)
    (hev : ∀ i : Nat, i < a → ∀ s : Nat, s < g i →
      acceleratedOrbit (gapT g i + 1 + s) m % 2 = 0) :
    ∀ i : Nat, i ≤ a → gapT g i ≤ fexp i := by
  intro i hi
  obtain ⟨_, hO⟩ := gapT_gapC_of_orbit (x := m) g i
    (fun k hk => hodd k (by omega)) (fun k hk => hev k (by omega))
  have h := orbit_time_le_fexp (j := gapT g i) hc hnd (by rw [hO]; omega)
  rw [hO] at h
  exact h

/-- **The accumulator of a real never-dropping orbit is capped by the Beatty
ceiling, read through its valuation profile.**  This is `gapC_le_Bcap` with its
hypothesis discharged dynamically. -/
theorem orbit_gapC_le_Bcap {m : Nat} (g : Nat → Nat) (hc : 1086464 ≤ m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m) {a : Nat} (ha : a < 4296)
    (hodd : ∀ i : Nat, i < a → acceleratedOrbit (gapT g i) m % 2 = 1)
    (hev : ∀ i : Nat, i < a → ∀ s : Nat, s < g i →
      acceleratedOrbit (gapT g i + 1 + s) m % 2 = 0) :
    gapC g a ≤ Bcap a :=
  gapC_le_Bcap g a (fun i hi => orbit_run_box g hc hnd ha hodd hev i (by omega))

end ValuationBeatty
end Collatz
