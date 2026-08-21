import Collatz.Strategy.RealizableBound

/-!
# The gap sandwich: a cycle's length is determined by its odd-step count

`RealizableBound` bounds the accumulator of a never-dropper by the Beatty ceiling
`Bcap a = Σ_{i<a} 3 ^ (a−1−i) · 2 ^ (⌊i log₂ 3⌋)`, but only as far as its finite
certificate reaches — the induction that produces it *stops dead* at the first
index where the certificate fails (`a = 2966` at the verified range `768 000`),
because there the never-drop hypothesis no longer forces the odd-step time down
to `⌊a log₂ 3⌋`.

This file removes that cliff.  Instead of demanding that the odd-step time be
`≤ fexp a` and giving up when the arithmetic will not supply it, the ceiling
here *degrades*: at each index it takes the smallest exponent the never-drop
hypothesis can actually certify, and carries on.

`Bstar c 0 = 0`,
`Bstar c (a+1) = 3 · Bstar c a + 2 ^ (Ecap c a)`,
`Ecap c a = fexp a` if `Bstar c a + 3 ^ a · c < 2 · 2 ^ (fexp a) · c`, else `fexp a + 1`.

`Ecap c a` is the largest odd-step time the hypothesis leaves open at index `a`,
and `affineC j m ≤ Bstar c (oddCount m j)` holds **at every `a`**, with no
certificate at all.

## Why one extra bit of slack always suffices

Widening by one is enough because the ceiling is quantitatively small: the crude
induction

`3 · Bstar c a ≤ 2 · a · 3 ^ a`   (`Bstar_le`)

— whose step needs only `2 ^ (Ecap c a) ≤ 2 · 3 ^ a`, i.e. `fexp_le` — gives
`Bstar c a < 3 ^ a · c` as soon as `2 · a < 3 · c`, and then
`Bstar c a + 3 ^ a · c < 2 · 3 ^ a · c < 4 · 2 ^ (fexp a) · c`, which is exactly
the statement that `Ecap c a ≤ fexp a + 1`.  At `c = 768 000` that covers every
`a < 1 152 000`.  **No `decide`, no certificate, no kernel arithmetic.**

## The consequence: `L = ⌊a log₂ 3⌋ + 1`

For a cycle the accumulator is pinned, so Lemma A applies at `j = L` itself and
yields `L ≤ Ecap c a ≤ fexp a + 1`.  In the other direction `3 ^ a < 2 ^ L`
forces `fexp a < L`.  Hence

**`L = fexp a + 1`**   (`cycle_length_eq`),

for every nontrivial accelerated cycle whose odd-step count satisfies
`2 · a < 3 · c`.  The development previously knew only the one-sided
`fexp a < L`.  Two-sidedness collapses the cycle problem from two parameters to
one: the length is a *function* of the odd-step count, the gap
`G = 2 ^ (fexp a + 1) − 3 ^ a` is the least gap available at that `a`, and the
whole question becomes a statement about how well `a · log₂ 3` approximates an
integer from below.

## The sandwich, and the window on the cycle minimum

Feeding `L = fexp a + 1` back into `(2 ^ L − 3 ^ a) · m = affineC L m ≤ Bstar c a`
gives the two-sided pin (`cycle_sandwich`, `cycle_min_window`)

`c ≤ m`   and   `3 · m · (2 ^ (fexp a + 1) − 3 ^ a) ≤ 2 · a · 3 ^ a`.

Numerically, with the exact `Bstar` recursion at `c = 768 000`, the first `a`
for which this is satisfiable at all is `a = 2966`, `L = 4701` — reproducing
`RealizableBound.length_ge_4701` — and there the window on the cycle minimum is

`768 000 ≤ m ≤ 841 477`,

a range of `73 478` integers.  The next surviving pairs and their windows:

| `a` | `L` | `m ≤` |
|---|---|---|
| 2966 | 4701 | 841 477 |
| 3631 | 5755 | 1 086 262 |
| 4296 | 6809 | 1 359 156 |
| 4961 | 7863 | 1 665 296 |
| 5626 | 8917 | 2 011 150 |
| 5932 | 9402 | 841 477 |

so the frontier as a function of the verified range `c` continues
`768 000 → 4701`, `841 478 → 5755`, `1 086 263 → 6809`, `1 359 157 → 7863`,
`2 011 151 → 9971`, `2 405 251 → 11 025`.  Every step of that staircase costs a
genuine extension of the verified range; the ratio `m_max / c` is only about
`1.1`, so the bootstrap does not run by itself.

## Where `d = 1` enters

In exactly one place, and it is named: `c ≤ m`, the verified range.  Asset (a)
of the soundness filter.  `Bstar`, `Ecap`, `fexp` and `Bstar_le` are all
`d`-free — for `T_d(x) = (3x+d)/2` the accumulator scales as `C(w,d) = d·C(w,1)`
and every inequality here scales with it — so the *only* thing that makes the
sandwich non-vacuous is the archimedean input `768 000 ≤ m`.  For `d = −1` the
cycle equation reads `(2^L − 3^a)·n = −C`, the sign is wrong, and the argument
never starts; for `d = 5` the cycle `5 → 5` has `m = 5`, far below any verified
range, and the sandwich `3·5·(2^{fexp a+1} − 3^a) ≤ 2·a·3^a·5` is satisfied at
`a = 1`, `L = 2` — the correct answer, not a contradiction.

## What it does *not* give: there is no gap lower bound

`Chains/CycleTargets.H36_cycleSmall` needs a bound on cycle points valid for all
`(L, a)`, and `AccumulatorCap` records that what is missing is a lower bound on
the gap.  The sandwich shows that no such bound exists in the required strength.
Writing `δ_a = ⌈a log₂ 3⌉ − a log₂ 3 ∈ (0,1)`, the gap at the forced length is
`G = 3 ^ a (2 ^ (δ_a) − 1) ≥ 3 ^ a · δ_a · ln 2`, and the sandwich survives
exactly when

`δ_a ≲ 2 · a / (3 · c · ln 2)`.

The right-hand side *grows* linearly in `a`, while `δ_a` is as small as
`1 / q_{k+1}` infinitely often (`q_k` the convergent denominators of `log₂ 3`:
`1, 2, 5, 12, 41, 53, 306, 665, 15 601, 31 867, 79 335, 111 202, 190 537, …`).
So the number of surviving `a` below `A` is asymptotically `A² / (3 c ln 2)` —
counted exactly: `2216` survivors below `60 000` at `c = 768 000`, against the
prediction `2254`.  It diverges for every fixed `c`.  **The sandwich, and every
sharpening of its constant, can only ever prove a frontier, never `H36`.**

The surviving `a` are not arbitrary.  With `δ₃₀₆ = 1.474779·10⁻³` and
`ε = 1 − δ₆₆₅ = 6.298·10⁻⁵`, the good indices are `a = 306 k + 665 j` with
`δ_a = k·δ₃₀₆ − j·ε`; the survivor list begins
`2966 = 306 + 4·665`, `3631 = 306 + 5·665`, `4296`, `4961`, `5626`,
`5932 = 2·306 + 8·665`, … and the *gaps between consecutive survivors* are
exactly the continued-fraction denominators `5, 12, 17, 29, 41, 53, 94, 147,
200, 253, 306, 359, 665` (5547 gaps of `12`, 853 of `41`, 843 of `29`, 826 of
`17`, 600 of `53`, … over the first 9032 survivors).  This is the same
staircase `RealizableBound` names: the quality of the rational approximations to
`log 3 / log 2`, and nothing else.
-/

namespace Collatz
namespace GapSandwich

open Reach Congruence AffineExact AccumulatorArith RealizableBound

/-! ## The degrading ceiling -/

/-- `Bstar c a` — the accumulator ceiling that never gives up.  At index `a` it
adds `2 ^ (fexp a)` if the never-drop hypothesis at range `c` forces the odd-step
time down that far, and `2 ^ (fexp a + 1)` otherwise. -/
def Bstar (c : Nat) : Nat → Nat
  | 0 => 0
  | a + 1 =>
      3 * Bstar c a +
        (if Bstar c a + 3 ^ a * c < 2 * 2 ^ fexp a * c then 2 ^ fexp a else 2 * 2 ^ fexp a)

/-- `Ecap c a` — the largest odd-step time left open at index `a`. -/
def Ecap (c a : Nat) : Nat :=
  if Bstar c a + 3 ^ a * c < 2 * 2 ^ fexp a * c then fexp a else fexp a + 1

@[simp] theorem Bstar_zero (c : Nat) : Bstar c 0 = 0 := rfl

theorem Bstar_succ (c a : Nat) :
    Bstar c (a + 1) = 3 * Bstar c a + 2 ^ Ecap c a := by
  rw [Bstar, Ecap]
  by_cases h : Bstar c a + 3 ^ a * c < 2 * 2 ^ fexp a * c
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, Arith.two_pow_succ]

/-- `2 ^ (Ecap c a) ≤ 2 · 3 ^ a`: the widened exponent is still subcritical up to
a factor two, because `2 ^ (fexp a) ≤ 3 ^ a`. -/
theorem two_pow_Ecap_le (c a : Nat) : 2 ^ Ecap c a ≤ 2 * 3 ^ a := by
  have hf := fexp_le a
  rw [Ecap]
  by_cases h : Bstar c a + 3 ^ a * c < 2 * 2 ^ fexp a * c
  · rw [if_pos h]; omega
  · rw [if_neg h, Arith.two_pow_succ]; omega

/-- **The crude majorant, by pure induction.**  `3 · Bstar c a ≤ 2 · a · 3 ^ a`.

The step is exactly `2 ^ (Ecap c a) ≤ 2 · 3 ^ a`: the ceiling's increment at
index `a`, divided by `3 ^ (a+1)`, is at most `2/3`, so `Bstar c a / 3 ^ a` grows
by at most `2/3` per index.  (The true growth rate is `1/(2 ln 2 · 3) = 0.2404`;
this bound is loose by a factor `2.77`, which is precisely the difference between
the frontier `1636` this yields and the frontier `2966` the exact certificate of
`RealizableBound` yields.) -/
theorem Bstar_le (c : Nat) : ∀ a : Nat, 3 * Bstar c a ≤ 2 * a * 3 ^ a := by
  intro a
  induction a with
  | zero => simp
  | succ a ih =>
    have hstep := two_pow_Ecap_le c a
    have h3 : (3:Nat) ^ (a + 1) = 3 * 3 ^ a := Arith.three_pow_succ a
    have hexpand : 2 * (a + 1) * 3 ^ (a + 1) = 3 * (2 * a * 3 ^ a) + 6 * 3 ^ a := by
      rw [h3]
      simp [Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      omega
    rw [Bstar_succ, hexpand]
    omega

/-- `Bstar c a < 3 ^ a · c` as soon as `2 · a < 3 · c`. -/
theorem Bstar_lt (c a : Nat) (h : 2 * a < 3 * c) : Bstar c a < 3 ^ a * c := by
  have hle := Bstar_le c a
  have hpos : 0 < (3:Nat) ^ a := Arith.three_pow_pos a
  have hmul : 2 * a * 3 ^ a < 3 * c * 3 ^ a := by
    exact Nat.mul_lt_mul_of_lt_of_le h (Nat.le_refl _) hpos
  have he : 3 * c * 3 ^ a = 3 * (3 ^ a * c) := by
    rw [Nat.mul_comm (3 ^ a) c, Nat.mul_assoc]
  omega

/-- **The widening bound, certificate-free.**  When `2 · a < 3 · c` the
never-drop hypothesis really does force the odd-step time to be at most
`fexp a + 1`; equivalently `Ecap c a ≤ fexp a + 1`, which is how `Ecap` is
defined, *and* the inequality that makes that definition sound. -/
theorem widen_cert (c a : Nat) (h : 2 * a < 3 * c) :
    Bstar c a + 3 ^ a * c < 4 * 2 ^ fexp a * c := by
  have hB := Bstar_lt c a h
  have hgap := lt_fexp a
  have hbase : 2 * 3 ^ a ≤ 4 * 2 ^ fexp a := by
    have h2 : (2:Nat) ^ (fexp a + 1) = 2 * 2 ^ fexp a := Arith.two_pow_succ _
    omega
  have hmul : (2 * 3 ^ a) * c ≤ (4 * 2 ^ fexp a) * c := Nat.mul_le_mul_right _ hbase
  have hassoc : (2 * 3 ^ a) * c = 2 * (3 ^ a * c) := by rw [Nat.mul_assoc]
  have hassoc2 : (4 * 2 ^ fexp a) * c = 4 * 2 ^ fexp a * c := rfl
  omega

/-! ## Lemma A, degrading -/

/-- The arithmetic core shared by both branches: a positive linear-form gap that
the verified range beats cannot also be beaten by the actual size. -/
theorem gap_contra {P B3 Bv m c : Nat} (hc : c ≤ m)
    (hkey : P * m ≤ B3 * m + Bv) (hcert : Bv + B3 * c < P * c) : False := by
  obtain ⟨d, hd⟩ : ∃ d : Nat, P = B3 + d := ⟨P - B3, by
    rcases Nat.lt_or_ge P B3 with hlt | hge
    · exfalso
      have h1 : P * c ≤ B3 * c := Nat.mul_le_mul_right _ (Nat.le_of_lt hlt)
      omega
    · omega⟩
  rw [hd, Nat.add_mul] at hkey hcert
  have hmono : d * c ≤ d * m := Nat.mul_le_mul_left _ hc
  omega

/-- **Lemma A, degrading form.**  For a never-dropper `m ≥ c`, at every time `j`
whose odd-step count is `a`, the time is at most `Ecap c a` — provided only
`2 · a < 3 · c`.  No certificate. -/
theorem le_Ecap {m c a j : Nat} (hcpos : 0 < c) (hc : c ≤ m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m)
    (hac : 2 * a < 3 * c)
    (ha : oddCount m j = a) (hB : affineC j m ≤ Bstar c a) : j ≤ Ecap c a := by
  rcases Nat.lt_or_ge (Ecap c a) j with hcon | hok
  case inr => exact hok
  exfalso
  have hmpos : 0 < m := by omega
  have harith := (neverDrops_iff_affine hmpos).mp hnd j
  rw [ha] at harith
  by_cases hbr : Bstar c a + 3 ^ a * c < 2 * 2 ^ fexp a * c
  · -- tight branch: `Ecap c a = fexp a`, so `j ≥ fexp a + 1`
    have hE : Ecap c a = fexp a := by rw [Ecap, if_pos hbr]
    have hstep : 2 * 2 ^ fexp a ≤ 2 ^ j := by
      have h1 : fexp a + 1 ≤ j := by omega
      have h2 : (2:Nat) ^ (fexp a + 1) ≤ 2 ^ j := Arith.two_pow_le_two_pow h1
      rw [Arith.two_pow_succ] at h2
      exact h2
    have hkey : 2 * 2 ^ fexp a * m ≤ 3 ^ a * m + Bstar c a := by
      have h1 : 2 * 2 ^ fexp a * m ≤ 2 ^ j * m := Nat.mul_le_mul_right _ hstep
      omega
    exact gap_contra hc hkey hbr
  · -- widened branch: `Ecap c a = fexp a + 1`, so `j ≥ fexp a + 2`
    have hE : Ecap c a = fexp a + 1 := by rw [Ecap, if_neg hbr]
    have hstep : 4 * 2 ^ fexp a ≤ 2 ^ j := by
      have h1 : fexp a + 2 ≤ j := by omega
      have h2 : (2:Nat) ^ (fexp a + 2) ≤ 2 ^ j := Arith.two_pow_le_two_pow h1
      have h3 : (2:Nat) ^ (fexp a + 2) = 4 * 2 ^ fexp a := by
        rw [Nat.pow_succ, Nat.pow_succ]; omega
      omega
    have hkey : 4 * 2 ^ fexp a * m ≤ 3 ^ a * m + Bstar c a := by
      have h1 : 4 * 2 ^ fexp a * m ≤ 2 ^ j * m := Nat.mul_le_mul_right _ hstep
      omega
    exact gap_contra hc hkey (widen_cert c a hac)

/-- **Lemma B, degrading form.**  `affineC j m ≤ Bstar c (oddCount m j)` for a
never-dropper above the verified range, at every window whose odd-step count
stays below `3 c / 2`.  Compare `RealizableBound.affineC_le_Bcap`, which needs a
`2966`-index kernel certificate and stops there. -/
theorem affineC_le_Bstar {m c A : Nat} (hcpos : 0 < c) (hc : c ≤ m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m) (hA : 2 * A < 3 * c) :
    ∀ j : Nat, oddCount m j ≤ A → affineC j m ≤ Bstar c (oddCount m j) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hle
    have hlast := Density.oddCount_succ_last m j
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j m) with he | ho
    · have hcount : oddCount m (j + 1) = oddCount m j := by omega
      rw [hcount, affineC_even he]
      exact ih (by omega)
    · have hcount : oddCount m (j + 1) = oddCount m j + 1 := by omega
      have hIH := ih (by omega)
      have hac : 2 * oddCount m j < 3 * c := by omega
      have htime : j ≤ Ecap c (oddCount m j) :=
        le_Ecap hcpos hc hnd hac rfl hIH
      have hpow : (2:Nat) ^ j ≤ 2 ^ Ecap c (oddCount m j) :=
        Arith.two_pow_le_two_pow htime
      rw [hcount, affineC_odd ho, Bstar_succ]
      omega

/-! ## The cycle: length is a function of odd-step count -/

/-- The one-sided half already available: `3 ^ a < 2 ^ L` gives `fexp a < L`. -/
theorem fexp_lt_of_light {a L : Nat} (h : 3 ^ a < 2 ^ L) : fexp a < L := by
  rcases Nat.lt_or_ge (fexp a) L with hok | hcon
  · exact hok
  · exfalso
    have h1 : (2:Nat) ^ L ≤ 2 ^ fexp a := Arith.two_pow_le_two_pow hcon
    have h2 := fexp_le a
    omega

/-- **The length is determined by the odd-step count.**  For a cycle whose
minimum `m` is at least the verified range `c`, and whose odd-step count `a`
satisfies `2 · a < 3 · c`,

`L = fexp a + 1 = ⌊a · log₂ 3⌋ + 1`.

The development previously had only `fexp a < L`.  The reverse inequality is the
degrading Lemma A applied at `j = L`, where the cycle equation makes the
accumulator bound tight. -/
theorem cycle_length_eq {m c L : Nat} (hcpos : 0 < c) (hc : c ≤ m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m)
    (hlight : 3 ^ oddCount m L < 2 ^ L)
    (hac : 2 * oddCount m L < 3 * c) :
    L = fexp (oddCount m L) + 1 := by
  have hB : affineC L m ≤ Bstar c (oddCount m L) :=
    affineC_le_Bstar hcpos hc hnd hac L (Nat.le_refl _)
  have hup : L ≤ Ecap c (oddCount m L) := le_Ecap hcpos hc hnd hac rfl hB
  have hEle : Ecap c (oddCount m L) ≤ fexp (oddCount m L) + 1 := by
    rw [Ecap]
    by_cases hbr : Bstar c (oddCount m L) + 3 ^ oddCount m L * c
        < 2 * 2 ^ fexp (oddCount m L) * c
    · rw [if_pos hbr]; omega
    · rw [if_neg hbr]; omega
  have hlow := fexp_lt_of_light hlight
  omega

/-- **The sandwich.**  Both sides of `(2 ^ L − 3 ^ a) · m = affineC L m` at once,
stated without subtraction: the verified range from below, the degrading ceiling
from above. -/
theorem cycle_sandwich {m c L : Nat} (hcpos : 0 < c) (hc : c ≤ m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m)
    (hlight : 3 ^ oddCount m L < 2 ^ L)
    (hac : 2 * oddCount m L < 3 * c)
    (hcyc : (2 ^ L - 3 ^ oddCount m L) * m = affineC L m) :
    2 ^ L * c ≤ 3 ^ oddCount m L * c + Bstar c (oddCount m L) := by
  have hB : affineC L m ≤ Bstar c (oddCount m L) :=
    affineC_le_Bstar hcpos hc hnd hac L (Nat.le_refl _)
  have hsplit : (2 ^ L - 3 ^ oddCount m L) * m + 3 ^ oddCount m L * m = 2 ^ L * m := by
    rw [← Nat.add_mul]
    congr 1
    omega
  have hmc : (2 ^ L - 3 ^ oddCount m L) * c ≤ (2 ^ L - 3 ^ oddCount m L) * m :=
    Nat.mul_le_mul_left _ hc
  have hsc : (2 ^ L - 3 ^ oddCount m L) * c + 3 ^ oddCount m L * c = 2 ^ L * c := by
    rw [← Nat.add_mul]
    congr 1
    omega
  omega

/-- **The window on the cycle minimum**, in fully elementary form:

`3 · m · (2 ^ (fexp a + 1) − 3 ^ a) ≤ 2 · a · 3 ^ a`,

written without subtraction.  Together with `c ≤ m` this is a two-sided pin on
`m` depending on `a` alone.  At `c = 768 000` the least `a` for which it is
satisfiable is `2966`, where it reads `768 000 ≤ m ≤ 841 477`. -/
theorem cycle_min_window {m c L : Nat} (hcpos : 0 < c) (hc : c ≤ m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m)
    (hlight : 3 ^ oddCount m L < 2 ^ L)
    (hac : 2 * oddCount m L < 3 * c)
    (hcyc : (2 ^ L - 3 ^ oddCount m L) * m = affineC L m) :
    3 * (2 ^ L * m) ≤ 3 * (3 ^ oddCount m L * m) + 2 * oddCount m L * 3 ^ oddCount m L := by
  have hB : affineC L m ≤ Bstar c (oddCount m L) :=
    affineC_le_Bstar hcpos hc hnd hac L (Nat.le_refl _)
  have hcrude := Bstar_le c (oddCount m L)
  have hsplit : (2 ^ L - 3 ^ oddCount m L) * m + 3 ^ oddCount m L * m = 2 ^ L * m := by
    rw [← Nat.add_mul]
    congr 1
    omega
  omega

/-! ## At the verified range -/

/-- The instance the repository can use: at `c = 768 000` the length of a
nontrivial cycle is `⌊a log₂ 3⌋ + 1` for every odd-step count below
`1 152 000`. -/
theorem cycle_length_eq_768000 {m L : Nat} (hc : 768000 ≤ m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m)
    (hlight : 3 ^ oddCount m L < 2 ^ L)
    (hac : oddCount m L < 1152000) :
    L = fexp (oddCount m L) + 1 :=
  cycle_length_eq (by omega) hc hnd hlight (by omega)

/-- The window at the verified range. -/
theorem cycle_min_window_768000 {m L : Nat} (hc : 768000 ≤ m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m)
    (hlight : 3 ^ oddCount m L < 2 ^ L)
    (hac : oddCount m L < 1152000)
    (hcyc : (2 ^ L - 3 ^ oddCount m L) * m = affineC L m) :
    3 * (2 ^ L * m) ≤ 3 * (3 ^ oddCount m L * m) + 2 * oddCount m L * 3 ^ oddCount m L :=
  cycle_min_window (by omega) hc hnd hlight (by omega) hcyc

/-! ## Assembled for a genuine cycle

The same plumbing `RealizableBound.length_ge_4701` uses: pass to the cycle's
minimum, which is a never-dropper above the verified range. -/

set_option exponentiation.threshold 6000 in
open AccCycle in
/-- **Every nontrivial accelerated cycle has `L = ⌊a · log₂ 3⌋ + 1`.**

Combined with `RealizableBound.length_ge_4701` (which gives `a ≥ 2966`) this
says: the cycle problem has *one* free parameter, the odd-step count `a`, and
`a` is constrained to those indices at which `a · log₂ 3` lies within
`≈ 2a / (3 · 768000 · ln 2)` below an integer. -/
theorem cycle_length_determined {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hnr : ¬ ReachesOne n) {m : Nat}
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hmin : ∀ j : Nat, m ≤ acceleratedOrbit j n)
    (hac : oddCount m L < 1152000) :
    L = fexp (oddCount m L) + 1 := by
  obtain ⟨i, hi⟩ := hm
  have hmpos : 0 < m := by rw [← hi]; exact acceleratedOrbit_positive hn i
  have htrans : ∀ k : Nat, acceleratedOrbit k m = acceleratedOrbit (k + i) n := by
    intro k; rw [← hi, acceleratedOrbit_add k i n]
  have hnd : ∀ k : Nat, m ≤ acceleratedOrbit k m := by
    intro k; rw [htrans k]; exact hmin _
  have hc : 768000 ≤ m := CycleLength2593.ge_verified_768000 hn hnr ⟨i, hi⟩
  have hcyc : acceleratedOrbit L m = m := by
    rw [htrans L, Nat.add_comm L i, ← acceleratedOrbit_add i L n, h.2, hi]
  have hlight : 3 ^ oddCount m L < 2 ^ L :=
    Cycle.two_pow_gt_three_pow_of_accCycle hmpos h.1 hcyc
  exact cycle_length_eq_768000 hc hnd hlight hac

end GapSandwich
end Collatz
