import Collatz.Strategy.ExtremalWord

/-!
# Round XIII: the Beatty corner is stable, and stability is the whole game

`ExtremalWord` shows the accumulator ceiling `Bcap a` is attained exactly at the
Beatty corner `t i = fexp i`.  This file measures *how much* a word loses by
leaving that corner, and records the two constraints that were tested against
the corner and found to be vacuous.

## The stability gap (`Cw_gap`, `stability_quarter`)

If a word lies in the box and is strictly below the ceiling at one index `i`,
then

`2 · C(w) + 3 ^ (a−1−i) · 2 ^ (fexp i)  ≤  2 · Bcap a`      (`Cw_gap`)

— the loss is at least half the `i`-th positional weight.  Every positional
weight is bigger than `3 ^ (a−1) / 2` (because `3 ^ i < 2 ^ (fexp i + 1)`), and
`Bcap a ≤ a · 3 ^ (a−1)` (`Bcap_upper`), so one strict coordinate already costs a
`1 / (4a)` fraction of the ceiling:

`4 · a · C(w) + Bcap a  ≤  4 · a · Bcap a`                   (`stability_quarter`)

i.e. `C(w) ≤ Bcap a · (1 − 1/(4a))`.  The exponent in `a` is **−1**, and it is
the true exponent, not an artifact: the measured runner-up law is
`1 − second/Bcap = 0.46226/a` at `a = 4296`, against the closed form
`2 ln 2 / 3 = 0.4620981…`, which is what `(1/2)·min_i weight / Bcap` gives when
`Bcap ≈ 3^(a−1)·a/(2 ln 2)` and `min_i weight ≈ 3^(a−1)/3`.  So the constant in
front of `1/a` is between `1/4` (proved here) and `2 ln 2 / 3` (measured), and no
choice of constant changes the exponent.

**Consequence, and it is the honest headline.**  Iterating over `D` strict
coordinates gives `C ≤ Bcap · (1 − D/(4a))` at worst, and with the exact weight
distribution `C ≤ Bcap · (1 − (2^(D/a) − 1)/2)`.  At the surviving frontier pair
`(L, a) = (6809, 4296)` the exclusion of `n ≥ 1086464` needs `C/Bcap ≤ 0.799624`,
which needs `D ≥ 2089 = 0.4863 · a` (computed exactly, integer arithmetic, from
the sorted weight list).  A single perturbation delivers `D = 1`.  So the corner
is *stable*, and stability is not a defect of the bound — it is the statement
that the frontier is a `Ω(a)`-perturbation away, not an `O(1)` one.

## What `D` means dynamically

`δ i = fexp i − t i`, and on a cycle with minimum `n` the value at the `i`-th odd
step is `x_i = (3^i · n + c_i) / 2^(t i) ≥ 3^i n / 2^(t i)`.  If `δ i ≥ 1` then
`2 ^ (t i) ≤ 3 ^ i / 2`, hence `x_i ≥ 2n` (`delta_pos_high`).  Conversely `δ i = 0`
forces `x_i < 2n + 2a/3`.  So

**`D(w)` is, to within a boundary band of width `2a/3`, the number of odd cycle
elements that exceed twice the minimum**, and the frontier reduces to:

> *prove that in a `3x+1` cycle at least `48.7%` of the odd elements are `≥ 2·min`.*

The Beatty corner is exactly the word with `D = 0`: its idealised orbit is
`x_i = n · 3^i / 2^(fexp i) ∈ [n, 2n)`, the pure `3/2` orbit, every element inside
one octave-and-a-bit of the minimum.  Measured `D/a` on genuine cycles of
`3x + d`: `0.714` (`3x−1`, `n = 17`, `a = 7`), `0.882` and `0.529` (`3x+5`,
`n = 187, 347`, `a = 17`), `0.733` (`3x+13`, `n = 131`, `a = 15`), `0.667`
(`3x+59`, `n = 133`, `a = 6`).  The needed `0.4863` sits below all but one.

## The two vacuous constraints

* **The leaf condition** ("every odd multiple of 3 has no odd predecessor", so no
  cycle element is divisible by 3) is *vacuous as a word condition*:
  `C(w) ≡ 2 ^ (t (a−1)) (mod 3)`, so `3 ∤ C(w)` for **every** word
  (`leaf_vacuous`), Beatty corner included.  It removes nothing, ever.
* **The `O0 E^m O0` ban** (`OctaveWord.no_O0_after_O0`) is also vacuous on the
  corner.  The octave letters are the rotation coding `θ_(i+1) = θ_i + α mod 1`
  with `α = log₂3 − 1 = 0.58496…`, and `O0` is `θ_i < 1 − α = 0.41504…`; since
  `α > 1 − α`, `θ_i < 1 − α` forces `θ_(i+1) ≥ α > 1 − α`, so **no rotation coding
  ever has two consecutive `O0`** — the ban is a restatement of `α > 1/2`.  At the
  counting level it says `#O0 ≤ #O1`, i.e. `2a − L ≤ L − a`, i.e. `L ≥ 3a/2`,
  strictly weaker than the heaviness bound `L ≥ a·log₂3 = 1.58496a` already in
  hand.  Verified computationally: the Beatty corner's octave word has zero
  consecutive `O0` at `a = 7, 10, 17, 25, 60, 200, 4296`, and so do all six
  genuine `3x+d` cycles above.

## Why *no* word-level constraint can remove the corner (`corner_is_a_real_cycle`)

The reason the leaf condition and the ban are vacuous on the corner is structural,
not accidental.  Put `G = 2 ^ (fexp a + 1) − 3 ^ a`, `g = gcd(G, Bcap a)`,
`d = G / g`, `n = Bcap a / g`.  Then `n · G = d · Bcap a`, so the Beatty word is
**an exact cycle of the map `x ↦ (3x + d) / 2^v`** with minimum `n`.  Verified by
running the orbit, exact integers, at `a = 4, 5, 6, 7, 10, 17, 25, 40, 100, 4296`:
the orbit closes, every element is odd, `n` is the minimum, and the odd-step times
are `fexp i` on the nose.  At `a = 4296` this is a genuine `4296`-element cycle of
`3x + d` with `d` a `6799`-bit number and `n` a `6820`-bit number, and `max/min =
1.999677` — the whole cycle inside `[n, 2n)`.  The smallest instance is `a = 4`,
`d = 47`, `n = 85`: `85 → 151 → 125 → 211 → 85` (`corner_is_a_real_cycle`).

Consequently **every constraint that is a consequence of "is a cycle of some
`3x + d`" is satisfied by the Beatty corner**: minimum-phase, cyclic rotation,
the heavy window, the leaf condition, and the `O0 E^m O0` ban all hold on it,
because they hold on an actual cycle.  The only constraint left is the one that
sees `d = 1`, namely `G | C`.  Of the six candidates in the Round XIII brief, it
is the only one that removes the corner, and (`ExtremalWord`, recomputed here) it
buys `1358717 → 1358571` against a target of `1086464` — `0.0536%` of the distance.

## Corrected constants at the frontier pair

Recomputed with exact integers (`fexp 4295 = 6807`, `fexp 4296 = 6808`, so
`L = 6809`, `G = 2^6809 − 3^4296`):

| quantity | value |
|---|---|
| `Bcap 4296 / G` | `1358717.7527` |
| `⌊Bcap 4296 / G⌋` (`G ∣ C` alone) | `1358717` |
| second-largest feasible `C / G` | `1358571.5524` (drop at `i = 3632`) |
| current `n`-bound | `1086464` |
| fraction of `Bcap` that must be cut | `0.2003755` |
| runner-up law `1 − second/Bcap` | `1.076017e−4 = 0.462257/a` |
| `D` needed | `2089 = 0.486266 · a` |
| shortfall in `n` after removing the corner | factor `1.2505` |

The closed form for the runner-up constant is `2 ln 2 / 3 = 0.4620981…`
(`min weight ≈ 3^(a−1)/3`, `Bcap ≈ 3^(a−1) a / (2 ln 2)`), and the closed form for
the required `D` is `κ = log₂(1 + 2 · 0.2003755) = 0.486202`, against the exactly
computed `0.486266`.  Note these differ from the Round XIII brief's `1.296e6`,
`16.17%` and `1503×`; the brief's `0.4623/a` runner-up law is confirmed.
-/

namespace Collatz
namespace BeattyStability

open ExtremalWord RealizableBound

/-! ## The corner is a genuine cycle of `3x + 47` -/

/-- **The Beatty corner, realised.**  `Bcap 4 = 85`, `2 ^ 7 − 3 ^ 4 = 47`, and
`85 → 151 → 125 → 211 → 85` is a closed cycle of `x ↦ (3x + 47) / 2^v` with
minimum `85`, halving counts `1, 2, 1, 3` summing to `L = 7`, and odd-step times
`0, 1, 3, 4 = fexp 0, fexp 1, fexp 2, fexp 3`.  So the accumulator ceiling is
attained by an *actual* cycle, and every `d`-independent cycle constraint holds
on it. -/
theorem corner_is_a_real_cycle :
    Bcap 4 = 85 ∧ 2 ^ 7 - 3 ^ 4 = 47 ∧
      3 * 85 + 47 = 2 * 151 ∧ 3 * 151 + 47 = 4 * 125 ∧
      3 * 125 + 47 = 2 * 211 ∧ 3 * 211 + 47 = 8 * 85 ∧
      85 * (2 ^ 7 - 3 ^ 4) = 47 * Bcap 4 ∧
      fexp 0 = 0 ∧ fexp 1 = 1 ∧ fexp 2 = 3 ∧ fexp 3 = 4 := by
  decide

/-! ## Small arithmetic helpers (no Mathlib) -/

theorem three_pow_pos : ∀ k : Nat, 0 < 3 ^ k := by
  intro k
  induction k with
  | zero => decide
  | succ k ih => rw [Arith.three_pow_succ]; omega

theorem two_pow_pos : ∀ k : Nat, 0 < 2 ^ k := by
  intro k
  induction k with
  | zero => decide
  | succ k ih => rw [Arith.two_pow_succ]; omega

theorem two_mul_swap (a c : Nat) : a * (2 * c) = 2 * (a * c) := by
  rw [← Nat.mul_assoc, Nat.mul_comm a 2, Nat.mul_assoc]

/-- `2 ^ k` is never `0 mod 3`. -/
theorem two_pow_mod_three : ∀ k : Nat, 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
  intro k
  induction k with
  | zero => left; rfl
  | succ k ih => rw [Arith.two_pow_succ]; omega

/-! ## An upper bound on the ceiling -/

/-- Every positional weight is at most `3 ^ (a−1)`, so `3 · Bcap a ≤ a · 3 ^ a`. -/
theorem Bcap_upper : ∀ a : Nat, 3 * Bcap a ≤ a * 3 ^ a := by
  intro a
  induction a with
  | zero => exact Nat.le_refl 0
  | succ a ih =>
    have hw : (2:Nat) ^ fexp a ≤ 3 ^ a := fexp_le a
    have h3 : (3:Nat) ^ (a + 1) = 3 * 3 ^ a := Arith.three_pow_succ a
    have hgoal : (a + 1) * 3 ^ (a + 1) = 3 * (a * 3 ^ a) + 3 * 3 ^ a := by
      rw [h3, Nat.succ_mul, Nat.mul_left_comm]
    rw [Bcap_succ, hgoal]
    omega

/-! ## The stability gap at one coordinate -/

/-- **The stability gap.**  A word in the box that is strictly below the Beatty
ceiling at index `i` loses at least half of the `i`-th positional weight.
Subtraction-free: `2·C + weight ≤ 2·Bcap`. -/
theorem Cw_gap {t : Nat → Nat} :
    ∀ a : Nat, (∀ j : Nat, j < a → t j ≤ fexp j) →
      ∀ i : Nat, i < a → t i < fexp i →
        2 * Cw t a + 3 ^ (a - 1 - i) * 2 ^ fexp i ≤ 2 * Bcap a := by
  intro a
  induction a with
  | zero => intro _ i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ a ih =>
    intro hbox i hi hlt
    have hbox' : ∀ j : Nat, j < a → t j ≤ fexp j := fun j hj =>
      hbox j (Nat.lt_succ_of_lt hj)
    rcases Nat.lt_or_ge i a with hia | hia
    · have hIH := ih hbox' i hia hlt
      have hlast : (2:Nat) ^ t a ≤ 2 ^ fexp a :=
        Arith.two_pow_le_two_pow (hbox a (Nat.lt_succ_self a))
      have hidx : a + 1 - 1 - i = (a - 1 - i) + 1 := by omega
      have hp : (3:Nat) ^ (a + 1 - 1 - i) = 3 * 3 ^ (a - 1 - i) := by
        rw [hidx]; exact Arith.three_pow_succ _
      have hkey : 3 * (2 * Cw t a + 3 ^ (a - 1 - i) * 2 ^ fexp i)
          ≤ 3 * (2 * Bcap a) := Nat.mul_le_mul_left 3 hIH
      have hexp : 3 * (3 ^ (a - 1 - i) * 2 ^ fexp i)
          = 3 * 3 ^ (a - 1 - i) * 2 ^ fexp i := (Nat.mul_assoc 3 _ _).symm
      rw [Cw_succ, Bcap_succ, hp]
      omega
    · have hia' : i = a := by omega
      subst hia'
      have hhalf : (2:Nat) ^ t i ≤ 2 ^ (fexp i - 1) :=
        Arith.two_pow_le_two_pow (by omega)
      have hdbl : 2 * 2 ^ (fexp i - 1) = 2 ^ fexp i := by
        have he : fexp i - 1 + 1 = fexp i := by omega
        rw [← Arith.two_pow_succ, he]
      have hbase : Cw t i ≤ Bcap i := by
        have := Cw_le t fexp i hbox'
        rw [Cw_fexp] at this; exact this
      have hidx : i + 1 - 1 - i = 0 := by omega
      rw [Cw_succ, Bcap_succ, hidx, Nat.pow_zero, Nat.one_mul]
      omega

/-- Pure arithmetic core of the `1/(4a)` law. -/
theorem quarter_helper {C B W P a : Nat}
    (hgap : 2 * C + W ≤ 2 * B) (hW : P < 2 * W) (hB : B ≤ a * P) :
    4 * a * C + B ≤ 4 * a * B := by
  have h1 : a * (2 * C + W) ≤ a * (2 * B) := Nat.mul_le_mul_left a hgap
  have h2 : a * P ≤ a * (2 * W) := Nat.mul_le_mul_left a (Nat.le_of_lt hW)
  have e1 : a * (2 * C + W) = 2 * (a * C) + a * W := by
    rw [Nat.mul_add, two_mul_swap]
  have e2 : a * (2 * B) = 2 * (a * B) := two_mul_swap a B
  have e3 : a * (2 * W) = 2 * (a * W) := two_mul_swap a W
  have e4 : 4 * a * C = 4 * (a * C) := Nat.mul_assoc 4 a C
  have e5 : 4 * a * B = 4 * (a * B) := Nat.mul_assoc 4 a B
  omega

/-- **One strict coordinate costs a `1/(4a)` fraction of the ceiling.**
`4·a·C(w) + Bcap a ≤ 4·a·Bcap a`, i.e. `C(w) ≤ Bcap a · (1 − 1/(4a))`. -/
theorem stability_quarter {t : Nat → Nat} {a i : Nat}
    (hbox : ∀ j : Nat, j < a → t j ≤ fexp j) (hi : i < a) (hlt : t i < fexp i) :
    4 * a * Cw t a + Bcap a ≤ 4 * a * Bcap a := by
  have hgap := Cw_gap a hbox i hi hlt
  have hsplit : (3:Nat) ^ (a - 1 - i) * 3 ^ i = 3 ^ (a - 1) := by
    rw [← Nat.pow_add]
    have he : a - 1 - i + i = a - 1 := by omega
    rw [he]
  have hup : (3:Nat) ^ i < 2 * 2 ^ fexp i := by
    have h := lt_fexp i
    rw [Arith.two_pow_succ] at h
    exact h
  have hstep : (3:Nat) ^ (a - 1 - i) * (3 ^ i + 1)
      ≤ 3 ^ (a - 1 - i) * (2 * 2 ^ fexp i) :=
    Nat.mul_le_mul_left _ (by omega)
  have e1 : (3:Nat) ^ (a - 1 - i) * (3 ^ i + 1) = 3 ^ (a - 1) + 3 ^ (a - 1 - i) := by
    rw [Nat.mul_add, Nat.mul_one, hsplit]
  have e2 : (3:Nat) ^ (a - 1 - i) * (2 * 2 ^ fexp i)
      = 2 * (3 ^ (a - 1 - i) * 2 ^ fexp i) := two_mul_swap _ _
  have hp : 0 < (3:Nat) ^ (a - 1 - i) := three_pow_pos _
  have hweight : (3:Nat) ^ (a - 1) < 2 * (3 ^ (a - 1 - i) * 2 ^ fexp i) := by omega
  have hcap : 3 * Bcap a ≤ a * 3 ^ a := Bcap_upper a
  have hapos : 0 < a := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
  have ha1 : (3:Nat) ^ a = 3 * 3 ^ (a - 1) := by
    have he : a - 1 + 1 = a := by omega
    rw [← he, Arith.three_pow_succ]
    have he2 : a - 1 + 1 - 1 = a - 1 := by omega
    rw [he2]
  have hswap : a * (3 * 3 ^ (a - 1)) = 3 * (a * 3 ^ (a - 1)) :=
    Nat.mul_left_comm a 3 (3 ^ (a - 1))
  have hcap' : Bcap a ≤ a * 3 ^ (a - 1) := by
    rw [ha1] at hcap; omega
  exact quarter_helper hgap hweight hcap'

/-! ## The leaf condition is vacuous -/

/-- **`3` never divides an accumulator.**  `C(w) ≡ 2 ^ (t (a−1)) (mod 3)`.  So
"no cycle element is divisible by `3`" is automatic for every word and removes
nothing — the Beatty corner least of all. -/
theorem leaf_vacuous (t : Nat → Nat) (a : Nat) : Cw t (a + 1) % 3 ≠ 0 := by
  rw [Cw_succ]
  have h := two_pow_mod_three (t a)
  omega

/-- **`Bcap` itself is never divisible by `3`**, the corner's instance. -/
theorem Bcap_not_dvd_three (a : Nat) : Bcap (a + 1) % 3 ≠ 0 := by
  rw [← Cw_fexp]
  exact leaf_vacuous fexp a

/-! ## `δ i ≥ 1` means the orbit is at least twice the minimum -/

/-- **The dynamical reading of `D`.**  If the `i`-th odd-step time is strictly
below the Beatty ceiling then `2 ^ (t i + 1) ≤ 3 ^ i`. -/
theorem delta_pos_high {t : Nat → Nat} {i : Nat} (h : t i < fexp i) :
    2 * 2 ^ t i ≤ 3 ^ i := by
  have h1 : (2:Nat) ^ (t i + 1) ≤ 2 ^ fexp i := Arith.two_pow_le_two_pow (by omega)
  have h2 : (2:Nat) ^ fexp i ≤ 3 ^ i := fexp_le i
  rw [Arith.two_pow_succ] at h1
  omega

/-- **`D` counts the odd steps at height `≥ 2n`.**  If `x · 2 ^ (t i) = 3 ^ i · n + c`
— the cycle identity at the `i`-th odd step — and `t i < fexp i`, then `x ≥ 2 n`. -/
theorem high_of_delta_pos {t : Nat → Nat} {i n x c : Nat}
    (h : t i < fexp i) (hx : x * 2 ^ t i = 3 ^ i * n + c) : 2 * n ≤ x := by
  have hd := delta_pos_high (t := t) (i := i) h
  have hpos : 0 < (2:Nat) ^ t i := two_pow_pos _
  have hmul : (2 * 2 ^ t i) * n ≤ 3 ^ i * n := Nat.mul_le_mul_right n hd
  have he : (2 * 2 ^ t i) * n = 2 ^ t i * (2 * n) := by
    rw [Nat.mul_comm 2 (2 ^ t i), Nat.mul_assoc]
  have hx' : 2 ^ t i * x = 3 ^ i * n + c := by
    rw [Nat.mul_comm]; exact hx
  have hle : 2 ^ t i * (2 * n) ≤ 2 ^ t i * x := by omega
  exact Nat.le_of_mul_le_mul_left hle hpos

end BeattyStability
end Collatz
