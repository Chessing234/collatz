import Collatz.Strategy.AccumulatorArith
import Collatz.Strategy.CycleLength2593

/-!
# Realizability: the accumulator bound the parity word cannot beat

Every upper bound this development has put on the accumulator

`affineC j x = Σ_{i<a} 3 ^ (a−1−i) · 2 ^ (t_i)`,   `t_0 < … < t_{a−1}` the odd-step times,

has been a bound on the *shape* of the word.  `AffineExact.affineC_le` maximises
over arrangements and gets `C + 2 ^ j ≤ 2 ^ (j−a) · 3 ^ a`, attained by the word
that takes every odd step last.  `CycleProduct` gets, after unwinding,
`C ≤ a · 3 ^ (a−1)`.  Both treat the odd-step times as free.

They are not free.  This file adds the one constraint the never-drop hypothesis
puts on them individually, and it is a constraint of a different kind: not on the
*sizes* but on the *positions*.

## The mechanism

Write `ρ_i = 2 ^ (t_i) / 3 ^ i` for the growth ratio accumulated up to the
`(i+1)`-st odd step.  Never-dropping at time `t_i` reads

`(2 ^ (t_i) − 3 ^ i) · m ≤ C_{t_i}`,

so `ρ_i ≤ 1 + O(C/m)`: the ratio is barely allowed above one.  Now the point.
`log₂ ρ_i = t_i − i · log₂ 3` and **`t_i` is an integer**, so `log₂ ρ_i` is pinned
modulo one — it lies on the orbit of an irrational rotation, and cannot take any
value it likes in `(0, 1]`.  A ratio that is forced to be `≤ 1` and is pinned
modulo one is therefore forced down to

`ρ_i ≤ 2 ^ (−frac(i log₂ 3))`,   equivalently   **`2 ^ (t_i) ≤ 3 ^ i`**.

That is the whole content: **realizability, not size**.  The odd steps of a
never-dropper are individually subcritical, not merely subcritical on average,
and the reason is that the times at which they happen are integers.  It costs
nothing in the verified range and it is not available to any argument that treats
the parity word abstractly.

Averaging `2 ^ (−frac(i log₂ 3))` over `i` gives `∫₀¹ 2^(−u) du = 1/(2 ln 2) =
0.7213`, so summing the positional formula against the pinned ratios replaces
`a · 3 ^ (a−1)` by `0.7213 · a · 3 ^ (a−1)`.  A constant — and the cycle-length
frontier is made of exactly such constants.

## The Beatty ceiling

`fexp i = ⌊i log₂ 3⌋` is definable in `Nat` with no reals at all: `fexp 0 = 0`
and `fexp (i+1)` is `fexp i` plus one or two according as `2 ^ (fexp i + 2)` has
overtaken `3 ^ (i+1)`.  `fexp_le` and `lt_fexp` — one simultaneous induction —
say exactly `2 ^ (fexp i) ≤ 3 ^ i < 2 ^ (fexp i + 1)`.  Feeding `t_i ≤ fexp i`
into the positional formula gives the ceiling

`Bcap a = Σ_{i<a} 3 ^ (a−1−i) · 2 ^ (fexp i)`,   `Bcap (a+1) = 3 · Bcap a + 2 ^ (fexp a)`,

and `affineC j m ≤ Bcap (oddCount m j)` (`affineC_le_Bcap`) is the main theorem.
`Bcap` is the ceiling of this entire class of argument: the exact feasibility DP
over never-drop-compatible parity words — the strongest possible consequence of
the never-drop inequalities *considered as constraints on the word alone* —
returns `Bcap a` on the nose at every `a ≤ 758` checked.  Nothing sharper can be
extracted without an input that is not a statement about the word.

## The finite input, and why it is one pass and not a sweep

The induction re-injects the never-drop hypothesis at each odd step, and what it
needs there is the arithmetic fact

`Bcap i + 3 ^ i · c  <  2 ^ (fexp i + 1) · c`,   that is  `G(i) < c`,   for `i < A`,

with `c` the verified range and `G(i) = Bcap i / (2 ^ (fexp i + 1) − 3 ^ i)`.
Computed exactly: `max_{i < 1636} G(i) = 238 670`, at `i = 971` — so `A = 1636`
was available already at the old range `307 200` — and `max_{i < 2966} G(i) =
620 858`, at `i = 2301`, which clears the new range `768 000`.  The first breach
at `768 000` is `i = 2966` itself, where `G = 841 477`; `frontier_2966` has the
kernel confirm that the certificate really does stop there.

Those record indices are not arbitrary.  `G(i)` is large precisely when the
linear-form gap `2 ^ (fexp i + 1) − 3 ^ i` is small, and the `G`-records in order
are `2966, 2301, 1636, 2607, 971, 1942, 2913, …` — whose head is *exactly* the
repository's surviving-`a` set from the product invariant,
`{971, 1636, 1942, 2301, 2607, 2913, 2966}`.  The two obstructions are one
obstruction: the quality of the rational approximations to `log 3 / log 2`.  Every
elementary improvement is a constant-factor shift along the same staircase, and
the place where a Baker-type input would have to enter is this single quotient.

Evaluating `Bcap i` and `fexp i` independently at each `i` would cost `O(A²)`
bignum operations on numerals of up to 1418 digits.  `cert` instead carries the
triple `(Bcap i, 3 ^ i, 2 ^ (fexp i))` forward, doing one comparison and three
multiplications per index — a single linear pass, with `cert_sound` proving that
the carried triple is what it claims to be.  The kernel checks all 2966 facts in
one `decide`.

## What it buys

On a cycle the accumulator is not merely bounded, it is *pinned*:
`(2 ^ L − 3 ^ a) · m = affineC L m`.  Against the ceiling that reads
`2 ^ (fexp a + 1) · m ≤ 3 ^ a · m + Bcap a`, which the certificate forbids for
every `a < 2966`.  Since `2 ^ 4700 < 3 ^ 2966`, every length `L ≤ 4700` has
`a < 2966`, and no such length admits a cycle.

| verified range | product bound (`CycleLength520`, `1539`, `2593`) | this bound |
|---|---|---|
| `102 400` | `520` | `1539` |
| `307 200` | `1539` | `2593` |
| `614 400` | — | `3647` |
| **`768 000` (have)** | **`2593`** | **`4701`** |

The realizability bound at a given range equals the product bound at roughly
three times that range: `2593` was the product bound's answer at `768 000` and is
this bound's answer at `307 200`.  At the range actually verified the frontier is
**`4701`**, an 81% gain over `2593` bought with no new computation of orbits —
the first non-excluded shape being `(L, a) = (4701, 2966)`, in agreement with the
exact feasibility DP and with the sweep of the Nat-clean majorant
`4 · C ≤ (a+1) · 3 ^ a`.  That majorant, verified with no exceptions for every
`a ≤ 4000`, is **not** used below: it is not provable by the obvious induction —
the step needs `4 · 2 ^ (fexp a) ≤ 3 ^ (a+1)`, which fails whenever
`frac(a log₂ 3) < log₂(4/3)`, at about 40% of indices — and `Bcap` is both sharper
and, being a recursion rather than a closed form, no harder for the kernel.

A by-product worth naming: `no_light_window` gives `2 ^ j ≤ 3 ^ (oddCount m j)`
for a never-dropper at every `j` inside the certified range, with **no factor of
two** on the right — sharper than `HeavyWord.heavy_window_2592` and
`CycleProduct.neverDrops_heavy_window`, both of which carry one.

Note also that no sweep over lengths appears anywhere below.  The product route
needs one certificate per length `L`; here the contradiction is uniform in `L`,
and the only length-dependent input is that `a` stays inside the certified range.

## What it does not buy

Every statement here is a finite-window statement about a **cycle**.
`Structure/Divergence`'s observation stands untouched: no finite truncation of
the never-drop hypothesis bounds `m`, so a divergent orbit is not constrained by
any of this.  The density wall — that never-dropping simply *is* the condition
`3 ^ a ≳ 2 ^ j` — is exactly where it was.  And because `Bcap` is attained by the
feasibility DP, `4701` is the exact ceiling of this method at this range: the only
ways past it are a larger verified range or a genuinely non-word-based input.

### Positivity audit

The certificate uses `c` quantitatively and in the direction `G(i) < c`, so
nothing here is mirror-invariant, exactly as `Mirror` requires of anything that
could decide the question.  For the mirror least never-dropper `m = 5` the
condition fails already at `i = 3` and the argument collapses, as it must.

### Relation to `HeavyWord`

`HeavyWord.heavyCert` certifies the *window* inequality `3 ^ t · (2c + t) < 2c ·
2 ^ j` at the top exponent, and `HeavyWord.cert_widen` transports it from `c` up
to `m`.  The certificate here is a different object — it carries a recursively
defined `Bcap` rather than a closed form, so it cannot be phrased as a
`heavyCert` — but the widening step is the same manoeuvre, performed inline in
`le_fexp_of_affineC_le` by splitting `2 ^ (fexp a + 1) = 3 ^ a + d` and comparing
`d · c` with `d · m`.
-/

namespace Collatz
namespace RealizableBound

open Reach Congruence AffineExact AccumulatorArith

/-! ## The Beatty exponent `⌊i log₂ 3⌋`, in `Nat` -/

/-- `fexp i = ⌊i · log₂ 3⌋`, defined without reals: the exponent grows by one or
by two at each step according to whether `2 ^ (fexp i + 2)` has been overtaken. -/
def fexp : Nat → Nat
  | 0 => 0
  | i + 1 => fexp i + (if 2 ^ (fexp i + 2) ≤ 3 ^ (i + 1) then 2 else 1)

@[simp] theorem fexp_zero : fexp 0 = 0 := rfl

/-- **The defining property of `fexp`, both halves at once.**  `2 ^ (fexp i)` is
the largest power of two not exceeding `3 ^ i`.  The two halves have to be proved
together: the lower half at `i+1` needs the upper half at `i` and conversely. -/
theorem fexp_spec : ∀ i : Nat, 2 ^ fexp i ≤ 3 ^ i ∧ 3 ^ i < 2 ^ (fexp i + 1) := by
  intro i
  induction i with
  | zero => exact ⟨by decide, by decide⟩
  | succ i ih =>
    obtain ⟨h1, h2⟩ := ih
    have h3 : (3:Nat) ^ (i + 1) = 3 * 3 ^ i := Arith.three_pow_succ i
    have h2' : (3:Nat) ^ i < 2 * 2 ^ fexp i := by
      rw [Arith.two_pow_succ] at h2; exact h2
    by_cases hc : 2 ^ (fexp i + 2) ≤ 3 ^ (i + 1)
    · have hf : fexp (i + 1) = fexp i + 2 := by rw [fexp, if_pos hc]
      refine ⟨by rw [hf]; exact hc, ?_⟩
      have hexp : (2:Nat) ^ (fexp i + 2 + 1) = 8 * 2 ^ fexp i := by
        rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ]; omega
      rw [hf, hexp, h3]
      omega
    · have hf : fexp (i + 1) = fexp i + 1 := by rw [fexp, if_neg hc]
      have hc' : (3:Nat) ^ (i + 1) < 2 ^ (fexp i + 2) := by omega
      have hshift : fexp (i + 1) + 1 = fexp i + 2 := by omega
      refine ⟨?_, by rw [hshift]; exact hc'⟩
      have hexp : (2:Nat) ^ (fexp i + 1) = 2 * 2 ^ fexp i := Arith.two_pow_succ _
      rw [hf, hexp, h3]
      omega

theorem fexp_le (i : Nat) : 2 ^ fexp i ≤ 3 ^ i := (fexp_spec i).1

theorem lt_fexp (i : Nat) : 3 ^ i < 2 ^ (fexp i + 1) := (fexp_spec i).2

/-- `fexp` is maximal: any exponent with `2 ^ t ≤ 3 ^ i` is at most `fexp i`. -/
theorem le_fexp_of_pow_le {i t : Nat} (h : 2 ^ t ≤ 3 ^ i) : t ≤ fexp i := by
  rcases Nat.lt_or_ge (fexp i) t with hcon | hok
  · exfalso
    have hmono := Arith.two_pow_le_two_pow (Nat.succ_le_of_lt hcon)
    have hup := lt_fexp i
    omega
  · exact hok

/-! ## The ceiling `Bcap` -/

/-- `Bcap a = Σ_{i<a} 3 ^ (a−1−i) · 2 ^ (fexp i)`: the positional formula for the
accumulator, evaluated at the Beatty word `t_i = ⌊i log₂ 3⌋`. -/
def Bcap : Nat → Nat
  | 0 => 0
  | a + 1 => 3 * Bcap a + 2 ^ fexp a

@[simp] theorem Bcap_zero : Bcap 0 = 0 := rfl

theorem Bcap_succ (a : Nat) : Bcap (a + 1) = 3 * Bcap a + 2 ^ fexp a := rfl

/-! ## The finite certificate, in one pass

`cert n c b p3 p2` checks `b + p3 · c < 2 · p2 · c` and then advances the triple
`(b, p3, p2) = (Bcap i, 3 ^ i, 2 ^ (fexp i))` by one index.  The `if` is the
`fexp` recursion with `2 ^ (fexp i + 2)` written as `4 · p2` and `3 ^ (i+1)` as
`3 · p3`, so nothing is ever exponentiated twice. -/
def cert : Nat → Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _, _ => true
  | n + 1, c, b, p3, p2 =>
      decide (b + p3 * c < 2 * p2 * c) &&
        cert n c (3 * b + p2) (3 * p3) (if 4 * p2 ≤ 3 * p3 then 4 * p2 else 2 * p2)

/-- The carried power of two advances exactly as `2 ^ (fexp ·)` does. -/
theorem carry_step (i : Nat) :
    (if 4 * 2 ^ fexp i ≤ 3 * 3 ^ i then 4 * 2 ^ fexp i else 2 * 2 ^ fexp i)
      = 2 ^ fexp (i + 1) := by
  have h4 : (4:Nat) * 2 ^ fexp i = 2 ^ (fexp i + 2) := by
    rw [Nat.pow_succ, Nat.pow_succ]
    omega
  have h3 : (3:Nat) * 3 ^ i = 3 ^ (i + 1) := (Arith.three_pow_succ i).symm
  rw [h4, h3]
  by_cases hc : 2 ^ (fexp i + 2) ≤ 3 ^ (i + 1)
  · rw [if_pos hc, fexp, if_pos hc]
  · rw [if_neg hc, fexp, if_neg hc, Arith.two_pow_succ]

/-- **The certificate says what it looks like it says.**  If the one-pass check
starting at index `i` returns `true`, then `Bcap k + 3 ^ k · c < 2 ^ (fexp k + 1) · c`
at every one of the next `n` indices. -/
theorem cert_sound : ∀ (n i c : Nat),
    cert n c (Bcap i) (3 ^ i) (2 ^ fexp i) = true →
      ∀ k : Nat, k < n → Bcap (i + k) + 3 ^ (i + k) * c < 2 * 2 ^ fexp (i + k) * c := by
  intro n
  induction n with
  | zero => intro i c _ k hk; omega
  | succ n ih =>
    intro i c h k hk
    rw [cert, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hhead, htail⟩ := h
    match k with
    | 0 => simpa using hhead
    | (k + 1) =>
      have hnext : cert n c (Bcap (i + 1)) (3 ^ (i + 1)) (2 ^ fexp (i + 1)) = true := by
        rw [Bcap_succ, ← carry_step i, Arith.three_pow_succ i]
        exact htail
      have hstep := ih (i + 1) c hnext k (by omega)
      have he : i + 1 + k = i + (k + 1) := by omega
      rwa [he] at hstep

/-! ## Lemma A and Lemma B

The induction is on the window length, and the invariant is the single
inequality `affineC j m ≤ Bcap (oddCount m j)`.  Even steps do nothing at all.
At an odd step the never-drop hypothesis is re-injected, and what it yields is
exactly `j ≤ fexp a` — the odd-step time is subcritical — which is what lets the
accumulator's new term `2 ^ j` be absorbed into the ceiling's new term
`2 ^ (fexp a)`.  No enumeration of odd-step times is needed anywhere: the time of
the `(a+1)`-st odd step *is* the `j` at which that step is taken. -/

/-- **Lemma A, at the point of use.**  Given the ceiling at time `j` and the
certificate at the current odd-step index, the never-drop hypothesis forces the
odd-step time to be subcritical: `j ≤ ⌊a log₂ 3⌋`.

The widening from the verified range `c` to the actual size `m` is the step
`d · c ≤ d · m` below, with `d` the linear-form gap `2 ^ (fexp a + 1) − 3 ^ a`;
it is `HeavyWord.cert_widen`'s manoeuvre in the shape this certificate needs. -/
theorem le_fexp_of_affineC_le {m c a j : Nat} (hcpos : 0 < c) (hc : c ≤ m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m)
    (hcert : Bcap a + 3 ^ a * c < 2 * 2 ^ fexp a * c)
    (ha : oddCount m j = a) (hB : affineC j m ≤ Bcap a) : j ≤ fexp a := by
  rcases Nat.lt_or_ge (fexp a) j with hcon | hok
  case inr => exact hok
  exfalso
  have hmpos : 0 < m := by omega
  have harith := (neverDrops_iff_affine hmpos).mp hnd j
  rw [ha] at harith
  -- `j > fexp a` gives `2 ^ (fexp a + 1) ≤ 2 ^ j`
  have hstep : 2 * 2 ^ fexp a ≤ 2 ^ j := by
    have h1 : fexp a + 1 ≤ j := by omega
    have h2 : (2:Nat) ^ (fexp a + 1) ≤ 2 ^ j := Arith.two_pow_le_two_pow h1
    rw [Arith.two_pow_succ] at h2
    exact h2
  have hkey : 2 * 2 ^ fexp a * m ≤ 3 ^ a * m + Bcap a := by
    have h1 : 2 * 2 ^ fexp a * m ≤ 2 ^ j * m := Nat.mul_le_mul_right _ hstep
    omega
  -- the gap `d = 2 ^ (fexp a + 1) − 3 ^ a` is positive
  have hgap : 3 ^ a < 2 * 2 ^ fexp a := by
    rcases Nat.lt_or_ge (3 ^ a) (2 * 2 ^ fexp a) with hg | hle
    · exact hg
    · exfalso
      have h1 : (2 * 2 ^ fexp a) * c ≤ (3 ^ a) * c := Nat.mul_le_mul_right _ hle
      omega
  obtain ⟨d, hd⟩ : ∃ d : Nat, 2 * 2 ^ fexp a = 3 ^ a + d := ⟨2 * 2 ^ fexp a - 3 ^ a, by omega⟩
  rw [hd] at hkey hcert
  rw [Nat.add_mul] at hkey hcert
  -- `d · m ≤ Bcap a` from the never-drop side, `Bcap a < d · c` from the certificate
  have hlow : d * m ≤ Bcap a := by omega
  have hhigh : Bcap a < d * c := by omega
  have hmono : d * c ≤ d * m := Nat.mul_le_mul_left _ hc
  omega

/-- **Lemma B — the Beatty ceiling.**  For a never-dropper `m` above the verified
range `c`, and as far as the finite certificate reaches, the accumulator over
every window is bounded by the value it would take on the Beatty word. -/
theorem affineC_le_Bcap {m c A : Nat} (hcpos : 0 < c) (hc : c ≤ m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m)
    (hcert : ∀ i : Nat, i < A → Bcap i + 3 ^ i * c < 2 * 2 ^ fexp i * c) :
    ∀ j : Nat, oddCount m j ≤ A → affineC j m ≤ Bcap (oddCount m j) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hA
    have hlast := Density.oddCount_succ_last m j
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j m) with he | ho
    · have hcount : oddCount m (j + 1) = oddCount m j := by omega
      rw [hcount, affineC_even he]
      exact ih (by omega)
    · have hcount : oddCount m (j + 1) = oddCount m j + 1 := by omega
      have hlt : oddCount m j < A := by omega
      have hIH := ih (by omega)
      have htime : j ≤ fexp (oddCount m j) :=
        le_fexp_of_affineC_le hcpos hc hnd (hcert _ hlt) rfl hIH
      have hpow : (2:Nat) ^ j ≤ 2 ^ fexp (oddCount m j) := Arith.two_pow_le_two_pow htime
      rw [hcount, affineC_odd ho, Bcap_succ]
      omega

/-- **Lemma A.**  At *every* time `j` on the orbit of a never-dropper, as far as
the certificate reaches, the accumulated growth is subcritical:
`2 ^ j ≤ 3 ^ (oddCount m j)`.

The report this formalises states the conclusion only at odd-step times, which is
where the mechanism lives — the odd steps are individually subcritical, not merely
subcritical on average, because the times at which they happen are integers.  The
proof turns out not to need the restriction: the never-drop inequality is
available at every `j`, and the ceiling holds there too, so the ratio is pinned
throughout.  The report's Lemma A is the special case `T^j(m) % 2 = 1`.  Checked against real orbits on 1 194 215 exact instances (every time
of every no-drop prefix of every odd `x < 400 000`), 0 violations — where the
odd-step-only form has 696 730 instances.  Note the absence of the factor `2` that
`HeavyWord.heavy_window_2592` and `CycleProduct.neverDrops_heavy_window` carry. -/
theorem two_pow_le_three_pow_window {m c A j : Nat} (hcpos : 0 < c) (hc : c ≤ m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m)
    (hcert : ∀ i : Nat, i < A → Bcap i + 3 ^ i * c < 2 * 2 ^ fexp i * c)
    (hA : oddCount m j < A) :
    2 ^ j ≤ 3 ^ oddCount m j := by
  have hIH := affineC_le_Bcap hcpos hc hnd hcert j (by omega)
  have htime : j ≤ fexp (oddCount m j) :=
    le_fexp_of_affineC_le hcpos hc hnd (hcert _ hA) rfl hIH
  exact Nat.le_trans (Arith.two_pow_le_two_pow htime) (fexp_le _)

/-! ## An initial run, exactly

Independent of everything above, and cheap.  The cocycle law `affineC_add` splits
a window at any time; if the first `r` steps are all odd the first factor is known
exactly (`affineC r x + 2 ^ r = 3 ^ r`), and applying `affineC_le` to the
remainder gives a bound strictly below `affineC_le` itself whenever `r ≥ 1` —
which every never-dropper satisfies, and in fact `r ≥ 2`, since `m ≡ 3 (mod 4)`. -/

/-- The arithmetic of the split, with every power abstracted: this is the whole
content of the initial-run bound once the cocycle has been applied. -/
theorem run_split_arith {Cr Ck Pr Pk Pt E3r E3b : Nat}
    (hC : Cr + Pr = E3r) (htail : Ck + Pk ≤ Pt * E3b) :
    E3b * Cr + Pr * Ck + Pr * Pk + E3b * Pr ≤ E3b * E3r + E3b * (Pr * Pt) := by
  have hhead : E3b * Cr + E3b * Pr = E3b * E3r := by
    rw [← Nat.mul_add, hC]
  have hsc : Pr * (Ck + Pk) ≤ Pr * (Pt * E3b) := Nat.mul_le_mul_left _ htail
  have e1 : Pr * (Ck + Pk) = Pr * Ck + Pr * Pk := Nat.mul_add _ _ _
  have e2 : Pr * (Pt * E3b) = E3b * (Pr * Pt) := by
    rw [Nat.mul_comm Pt E3b, Nat.mul_left_comm]
  omega

/-- An initial run of `r` odd steps: the accumulator is `3 ^ r − 2 ^ r` exactly
(stated without subtraction), and every one of the `r` steps is counted. -/
theorem run_exact (x : Nat) : ∀ r : Nat, (∀ i : Nat, i < r → acceleratedOrbit i x % 2 = 1) →
    affineC r x + 2 ^ r = 3 ^ r ∧ oddCount x r = r := by
  intro r
  induction r with
  | zero => intro _; exact ⟨by simp, rfl⟩
  | succ r ih =>
    intro hrun
    obtain ⟨hC, hcnt⟩ := ih (fun i hi => hrun i (by omega))
    have ho : acceleratedOrbit r x % 2 = 1 := hrun r (by omega)
    refine ⟨?_, ?_⟩
    · rw [affineC_odd ho, Arith.two_pow_succ, Arith.three_pow_succ]
      omega
    · rw [Density.oddCount_succ_last, ho, hcnt]

/-- **The initial-run bound.**  With `y = T^r(x)` and `b = oddCount y k`, an
initial run of `r` odd steps gives

`affineC (r+k) x + 2 ^ (r+k) + 3 ^ b · 2 ^ r ≤ 3 ^ b · (3 ^ r + 2 ^ r · 2 ^ (k − b))`,

the subtraction-free form of `C + 2 ^ j ≤ 3 ^ (a−r) · (3 ^ r − 2 ^ r + 2 ^ (j−a+r))`.
Against `affineC_le`'s `2 ^ (j−a) · 3 ^ a` this is a strict gain for every
`r ≥ 1`, tending to a factor `2/3` at `r = 1` and `4/9` at `r = 2`. -/
theorem affineC_le_of_initial_run (x r k : Nat)
    (hrun : ∀ i : Nat, i < r → acceleratedOrbit i x % 2 = 1) :
    affineC (r + k) x + 2 ^ (r + k)
        + 3 ^ oddCount (acceleratedOrbit r x) k * 2 ^ r
      ≤ 3 ^ oddCount (acceleratedOrbit r x) k
          * (3 ^ r
              + 2 ^ r * 2 ^ (k - oddCount (acceleratedOrbit r x) k)) := by
  obtain ⟨hC, _⟩ := run_exact x r hrun
  have hsplit := affineC_add x r k
  have htail := affineC_le (acceleratedOrbit r x) k
  have harith := run_split_arith (Cr := affineC r x) (Ck := affineC k (acceleratedOrbit r x))
    (Pr := 2 ^ r) (Pk := 2 ^ k)
    (Pt := 2 ^ (k - oddCount (acceleratedOrbit r x) k)) (E3r := 3 ^ r)
    (E3b := 3 ^ oddCount (acceleratedOrbit r x) k) hC htail
  have hpow : (2:Nat) ^ (r + k) = 2 ^ r * 2 ^ k := Nat.pow_add 2 r k
  rw [hsplit, hpow, Nat.mul_add]
  exact harith

/-! ## The certificate, discharged

`cert 2966 768000 0 1 1` is 2966 comparisons between integers of up to 1415
decimal digits, carried out in a single forward pass by the kernel.  The margin
is thin at the top: the largest `G(i)` on the range is `767 707` against the
verified `768 000`, and `i = 2966` itself breaches it. -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 40000 in
set_option exponentiation.threshold 6000 in
theorem cert_2966 : cert 2966 768000 0 1 1 = true := by decide

/-- The certificate in the form the lemmas consume: `G(i) < 768 000` for every
`i < 2966`. -/
theorem cert_768000 (i : Nat) (hi : i < 2966) :
    Bcap i + 3 ^ i * 768000 < 2 * 2 ^ fexp i * 768000 := by
  have h := cert_sound 2966 0 768000 (by simpa using cert_2966) i hi
  simpa using h

/-! ## The cycle-length frontier

On a cycle the accumulator is not merely bounded, it is *determined*:
`(2 ^ L − 3 ^ a) · m = affineC L m`.  So the ceiling applies with no slack, and
the inequality that drove Lemma A applies at `j = L` itself — where it concludes
`L ≤ fexp a`, flatly contradicting `3 ^ a < 2 ^ L`.  There is no sweep over
lengths: the contradiction is uniform in `L`, and the only length-dependent input
is that `a` stays inside the certified range. -/

set_option maxRecDepth 10000 in
set_option exponentiation.threshold 6000 in
/-- `2 ^ 4700 < 3 ^ 2966`: every cycle length below `4701` has fewer than `2966`
odd steps, which is exactly the range the certificate covers. -/
theorem pow_gap : (2:Nat) ^ 4700 < 3 ^ 2966 := by decide

/-- **A never-dropper above the verified range has no light window at all**, as
far as the certificate reaches: `2 ^ j ≤ 3 ^ (oddCount m j)` outright, with no
factor of two on the right.  A cycle supplies `3 ^ a < 2 ^ L`, so this closes it. -/
theorem no_light_window {m j : Nat} (hc : 768000 ≤ m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m)
    (hlt : 3 ^ oddCount m j < 2 ^ j) (hA : oddCount m j < 2966) : False := by
  have hB : affineC j m ≤ Bcap (oddCount m j) :=
    affineC_le_Bcap (by omega) hc hnd cert_768000 j (by omega)
  have htime : j ≤ fexp (oddCount m j) :=
    le_fexp_of_affineC_le (by omega) hc hnd (cert_768000 _ hA) rfl hB
  have hpow : (2:Nat) ^ j ≤ 2 ^ fexp (oddCount m j) := Arith.two_pow_le_two_pow htime
  have hceil := fexp_le (oddCount m j)
  omega

set_option exponentiation.threshold 6000 in
open AccCycle in
/-- **Every nontrivial accelerated cycle has length at least `4701`.**

`CycleLength2593.length_ge_2593` is the exact ceiling of the *product* bound at
the verified range `768 000`.  Realizability moves the frontier to `4701` at the
same range, with no new orbit computation: the odd-step times of a never-dropper
are integers, and that alone is worth a factor `1/(2 ln 2)` in the accumulator
bound and 81% in the length. -/
theorem length_ge_4701 {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hnr : ¬ ReachesOne n) : 4701 ≤ L := by
  rcases Nat.lt_or_ge L 4701 with hL | hL
  · exfalso
    obtain ⟨m, hm, hmin⟩ := exists_accCycleMin n
    obtain ⟨i, hi⟩ := hm
    have hmpos : 0 < m := by rw [← hi]; exact acceleratedOrbit_positive hn i
    have htrans : ∀ k : Nat, acceleratedOrbit k m = acceleratedOrbit (k + i) n := by
      intro k; rw [← hi, acceleratedOrbit_add k i n]
    have hnd : ∀ k : Nat, m ≤ acceleratedOrbit k m := by
      intro k; rw [htrans k]; exact hmin _
    have hc : 768000 ≤ m := CycleLength2593.ge_verified_768000 hn hnr ⟨i, hi⟩
    have hcyc : acceleratedOrbit L m = m := by
      rw [htrans L, Nat.add_comm L i, ← acceleratedOrbit_add i L n, h.2, hi]
    have hlt : 3 ^ oddCount m L < 2 ^ L :=
      Cycle.two_pow_gt_three_pow_of_accCycle hmpos h.1 hcyc
    have hA : oddCount m L < 2966 := by
      rcases Nat.lt_or_ge (oddCount m L) 2966 with hok | hcon
      · exact hok
      · exfalso
        have h1 : (3:Nat) ^ 2966 ≤ 3 ^ oddCount m L :=
          Nat.pow_le_pow_right (by omega) hcon
        have h2 : (2:Nat) ^ L ≤ 2 ^ 4700 := Arith.two_pow_le_two_pow (by omega)
        have h3 := pow_gap
        omega
    exact no_light_window hc hnd hlt hA
  · exact hL

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 40000 in
set_option exponentiation.threshold 6000 in
/-- The frontier is real, not an artefact of where the certificate stops: at
`i = 2966` the quotient `G(i)` is `841 477`, above the verified range, so the
inductive step genuinely fails there. -/
theorem frontier_2966 : cert 2967 768000 0 1 1 = false := by decide

end RealizableBound
end Collatz
