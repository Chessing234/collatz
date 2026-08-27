import Collatz.Strategy.AffineExact

/-!
# The deficit: the exact demand the accumulator has to meet

`AffineExact` turns never-dropping into `∀ j, 2 ^ j · m ≤ 3 ^ a · m + affineC j m`.
This file names the quantity on the *other* side of that inequality and studies
it as an object in its own right.

## The deficit

`deficit m j = 2 ^ j · m − 3 ^ a · m`  (as an integer, so it may be negative).

It is exactly the amount of additive compensation a window of length `j` demands
of the accumulator: never-dropping is `∀ j, deficit m j ≤ affineC j m`
(`neverDrops_iff_deficit`).

## The dual pair

The two objects obey mirror-image recurrences, and each is fed by the letters the
other ignores:

| step | `affineC` | `deficit` |
|---|---|---|
| odd  | `C ↦ 3 C + 2 ^ j` | `R ↦ 2 R − 3 ^ a · m` |
| even | `C ↦ C`           | `R ↦ 2 R + 3 ^ a · m` |

(`affineC_odd`/`affineC_even`, `deficit_succ_odd`/`deficit_succ_even`.)  **The
accumulator is fed only by odd steps and the demand only by even steps.**  That
is the whole tension of the problem in two lines.

## What the comparison is worth — the decisive identity

The natural next question is how `affineC j m` and `deficit m j` compare in size.
It has an exact answer, and the answer is that the question is the original one:

`affineC j m − deficit m j = 2 ^ j · (T^j(m) − m)`   (`displacement_identity`).

So the surplus of accumulator over demand is *precisely* `2 ^ j` times how far
above its start the orbit is sitting.  Consequences, all immediate:

* `C ≥ R` at `j` ⟺ the orbit is at or above `m` at time `j`;
* `C = R` at `j` ⟺ the orbit has returned to `m` at time `j` (a cycle of length
  `j`, `cycle_iff_deficit_eq_affineC`);
* the extremal ratio `C / R` over admissible patterns is not an auxiliary
  statistic to be estimated — it *is* the orbit's position, re-encoded.

**Honest reading.** "Compare the growth rates of `C_j` and `R_j`" is therefore not
a route into the problem; it is a change of variables on the problem.  Any bound
on the comparison that is not already a bound on the orbit is impossible.  What
*can* pay is a bound on one side alone, obtained from structure the other side
does not see — which is what the rest of this file does with even runs.

## The even-run freeze, and what it buys

The accumulator is frozen across an even run while the demand doubles each step.
That asymmetry gives a strictly sharper window condition than
`neverDrops_window_condition` gives at the same endpoint: the cap available at
time `j + r` is the one from time `j`, a factor `2 ^ r` smaller
(`neverDrops_even_run`).  Two consequences:

* `heavy_after_even_run` — the conclusion `2 ^ (j+r) ≤ 2 · 3 ^ a` of
  `AffineExact.heavy_while_few_even` at the endpoint, from its hypothesis at the
  *start* of the run.  A weaker hypothesis by the factor `2 ^ r`.
* `even_run_le_one_of_balanced` — a never-dropper takes no two consecutive even
  steps at a time when its window is balanced-or-light (`3 ^ a ≤ 2 ^ j`) and its
  even count is at most `log₂ m`.

**Honest reach.**  The second is sharp as an inequality and empty as a tool.  Its
balance hypothesis was measured on every no-drop prefix of every odd start below
`200 000`: it holds at `j = 0` and at no later window, for all 99 999 starts.  A
never-dropper is *strictly* heavy at every few-even window past the origin
(143 876 strictly heavy against 29 999 balanced, the latter being exactly the
`j = 0` window of each start), so the corollary reproduces "the first step is
odd" and nothing beyond it.  The first result is non-vacuous but narrow: 1 387
windows below `120 000` where it applies and `heavy_while_few_even` does not.

**Mirror audit** (`3n − 1`, same accumulator with the opposite sign).  The mirror
identity is `2 ^ j · T^j(x) = 3 ^ a · x − C`, so mirror-never-dropping is
`C ≤ −deficit` — an *upper* bound on `C` where the `3n+1` world has a lower one.
The asymmetric line is therefore the *direction of the cap*: the `3n+1`
derivations here consume `affineC_le` (odd steps last, the maximum), and their
mirrors consume `three_pow_le_affineC` (odd steps first, the minimum).  The
even-run statement itself survives the mirror, and survives it in a *stronger*
form — a mirror even run forces heaviness at its end outright, with no cap
needed (57 455 checks, zero failures), and the mirror satisfies the balanced
corollary too (50 000 checks, zero failures).  So the freeze is **not a
sign-sensitive mechanism**: the `+1` does not supply it, the `+1` only degrades
it by the slack `2 ^ (j−a) / m`.  It cannot separate `3n+1` from `3n−1`, whose
cycle `5 → 7 → 5` it leaves untouched.

Measured before formalising, on exact integer arithmetic and genuine no-drop
prefixes only: displacement identity 163 959 checks, deficit recurrence 89 970
checks, first-crossing parity 19 966 checks, even-run condition 58 112 checks,
the balanced corollary 50 001 checks, `heavy_after_even_run` 111 790 checks —
zero failures throughout.
-/

namespace Collatz
namespace AffineDeficit

open Reach Congruence AffineExact

/-! ## The object -/

/-- The additive compensation a window of length `j` demands: `2 ^ j · m − 3 ^ a · m`.
Negative exactly when the window is strictly heavy. -/
def deficit (m j : Nat) : Int :=
  ((2 ^ j * m : Nat) : Int) - ((3 ^ oddCount m j * m : Nat) : Int)

@[simp] theorem deficit_zero (m : Nat) : deficit m 0 = 0 := by
  simp [deficit]

/-! ## The recurrence — fed only by even steps -/

/-- An even step doubles the demand and adds `3 ^ a · m`. -/
theorem deficit_succ_even {m j : Nat} (h : acceleratedOrbit j m % 2 = 0) :
    deficit m (j + 1) = 2 * deficit m j + ((3 ^ oddCount m j * m : Nat) : Int) := by
  have hlast := Density.oddCount_succ_last m j
  have hcount : oddCount m (j + 1) = oddCount m j := by omega
  have hpow : (2:Nat) ^ (j + 1) * m = 2 * (2 ^ j * m) := by
    rw [Arith.two_pow_succ, Nat.mul_assoc]
  unfold deficit
  rw [hcount, hpow]
  omega

/-- An odd step doubles the demand and subtracts `3 ^ a · m`. -/
theorem deficit_succ_odd {m j : Nat} (h : acceleratedOrbit j m % 2 = 1) :
    deficit m (j + 1) = 2 * deficit m j - ((3 ^ oddCount m j * m : Nat) : Int) := by
  have hlast := Density.oddCount_succ_last m j
  have hcount : oddCount m (j + 1) = oddCount m j + 1 := by omega
  have hpow : (2:Nat) ^ (j + 1) * m = 2 * (2 ^ j * m) := by
    rw [Arith.two_pow_succ, Nat.mul_assoc]
  have h3 : (3:Nat) ^ (oddCount m j + 1) * m = 3 * (3 ^ oddCount m j * m) := by
    rw [Nat.pow_succ, Nat.mul_comm (3 ^ oddCount m j) 3, Nat.mul_assoc]
  unfold deficit
  rw [hcount, hpow, h3]
  omega

/-! ## Sign -/

/-- A heavy window demands nothing. -/
theorem deficit_nonpos_of_heavy {m j : Nat} (h : (2:Nat) ^ j ≤ 3 ^ oddCount m j) :
    deficit m j ≤ 0 := by
  have hmul : (2:Nat) ^ j * m ≤ 3 ^ oddCount m j * m := Nat.mul_le_mul_right _ h
  unfold deficit
  omega

/-- Conversely, a positive demand certifies a light window. -/
theorem light_of_deficit_pos {m j : Nat} (h : 0 < deficit m j) :
    3 ^ oddCount m j < 2 ^ j := by
  unfold deficit at h
  have hlt : (3:Nat) ^ oddCount m j * m < 2 ^ j * m := by omega
  rcases Nat.eq_zero_or_pos m with hm | hm
  · exact absurd hlt (by simp [hm])
  · exact Nat.lt_of_mul_lt_mul_right hlt

/-- The demand is positive exactly when the window is light, for a positive start. -/
theorem deficit_pos_iff {m j : Nat} (hm : 0 < m) :
    0 < deficit m j ↔ 3 ^ oddCount m j < 2 ^ j := by
  constructor
  · exact light_of_deficit_pos
  · intro h
    have hmul : (3:Nat) ^ oddCount m j * m < 2 ^ j * m := Nat.mul_lt_mul_of_lt_of_le h (Nat.le_refl m) hm
    unfold deficit
    omega

/-! ## The decisive identity

The accumulator's surplus over the demand is exactly `2 ^ j` times the orbit's
displacement above its start. -/

/-- **The displacement identity.**  `affineC j m − deficit m j = 2 ^ j · (T^j(m) − m)`.
So the comparison of accumulator against demand is a re-encoding of the orbit's
position, not an independent statistic. -/
theorem displacement_identity (m j : Nat) :
    ((affineC j m : Nat) : Int) - deficit m j
      = ((2 ^ j * acceleratedOrbit j m : Nat) : Int) - ((2 ^ j * m : Nat) : Int) := by
  have hexact := affine_exact m j
  unfold deficit
  omega

/-- **Never-dropping, in the two named objects.**  The demand is met at every
window. -/
theorem neverDrops_iff_deficit {m : Nat} (hm : 0 < m) :
    (∀ j : Nat, m ≤ acceleratedOrbit j m)
      ↔ (∀ j : Nat, deficit m j ≤ ((affineC j m : Nat) : Int)) := by
  rw [neverDrops_iff_affine hm]
  constructor
  · intro h j
    have := h j
    unfold deficit
    omega
  · intro h j
    have := h j
    unfold deficit at this
    omega

/-- Meeting the demand at a single window is exactly not dropping at it. -/
theorem deficit_le_iff_no_drop {m : Nat} (hm : 0 < m) (j : Nat) :
    deficit m j ≤ ((affineC j m : Nat) : Int) ↔ m ≤ acceleratedOrbit j m := by
  have hexact := affine_exact m j
  have hpos : 0 < (2:Nat) ^ j := Arith.two_pow_pos j
  constructor
  · intro h
    have hmul : 2 ^ j * m ≤ 2 ^ j * acceleratedOrbit j m := by
      unfold deficit at h; omega
    exact Nat.le_of_mul_le_mul_left hmul hpos
  · intro h
    have hmul : 2 ^ j * m ≤ 2 ^ j * acceleratedOrbit j m := Nat.mul_le_mul_left _ h
    unfold deficit
    omega

/-- **Exact demand is exact return.**  A cycle of length `j` is precisely the case
where the accumulator meets the demand with nothing to spare. -/
theorem cycle_iff_deficit_eq_affineC {m : Nat} (hm : 0 < m) (j : Nat) :
    acceleratedOrbit j m = m ↔ deficit m j = ((affineC j m : Nat) : Int) := by
  have hexact := affine_exact m j
  have hpos : 0 < (2:Nat) ^ j := Arith.two_pow_pos j
  constructor
  · intro h
    rw [h] at hexact
    unfold deficit
    omega
  · intro h
    have hmul : 2 ^ j * acceleratedOrbit j m = 2 ^ j * m := by
      unfold deficit at h; omega
    exact Nat.eq_of_mul_eq_mul_left hpos hmul

/-! ## The forced drop — cycle-free, one window at a time

The positional cap `affineC_le` bounds the accumulator by `2 ^ (j−a) · 3 ^ a`.
Any window whose demand exceeds that cap forces a drop, with no never-drop
hypothesis anywhere: this is a statement about an arbitrary positive orbit. -/

/-- **Insufficient compensation forces a drop.**  If the multiplicative deficit of a
single window exceeds what the accumulator can possibly supply, the orbit is
already below its start at the end of that window. -/
theorem drop_of_insufficient {m j : Nat}
    (h : 3 ^ oddCount m j * m + 2 ^ (j - oddCount m j) * 3 ^ oddCount m j < 2 ^ j * m) :
    acceleratedOrbit j m < m := by
  have hexact := affine_exact m j
  have hcap := affineC_le m j
  have hpos : 0 < (2:Nat) ^ j := Arith.two_pow_pos j
  have hmul : 2 ^ j * acceleratedOrbit j m < 2 ^ j * m := by omega
  exact Nat.lt_of_mul_lt_mul_left hmul

/-- The same statement in the deficit language: a demand above the cap is a drop. -/
theorem drop_of_deficit_gt_cap {m j : Nat}
    (h : ((2 ^ (j - oddCount m j) * 3 ^ oddCount m j : Nat) : Int) < deficit m j) :
    acceleratedOrbit j m < m := by
  refine drop_of_insufficient ?_
  unfold deficit at h
  omega

/-- Contrapositive: a never-dropper's demand never exceeds the positional cap. -/
theorem neverDrops_deficit_le_cap {m : Nat}
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m) (j : Nat) :
    deficit m j ≤ ((2 ^ (j - oddCount m j) * 3 ^ oddCount m j : Nat) : Int) := by
  have hexact := affine_exact m j
  have hcap := affineC_le m j
  have hmul : 2 ^ j * m ≤ 2 ^ j * acceleratedOrbit j m := Nat.mul_le_mul_left _ (hnd j)
  have hpos : 0 < (2:Nat) ^ j := Arith.two_pow_pos j
  unfold deficit
  omega

/-! ## The first crossing

The demand starts at zero and can only become positive on an even step: an odd
step multiplies `2 ^ j` by two and `3 ^ a` by three, so it cannot turn a
non-positive demand positive. -/

/-- **The first positive demand arrives on an even step.**  If the demand is
non-positive at `j` and positive at `j + 1`, the step taken was even. -/
theorem crossing_step_even {m j : Nat} (hm : 0 < m)
    (hle : deficit m j ≤ 0) (hpos : 0 < deficit m (j + 1)) :
    acceleratedOrbit j m % 2 = 0 := by
  rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j m) with he | ho
  · exact he
  · exfalso
    have hlast := Density.oddCount_succ_last m j
    have hcount : oddCount m (j + 1) = oddCount m j + 1 := by omega
    -- light at `j + 1`: `3 ^ (a+1) < 2 ^ (j+1)`
    have hlight : 3 ^ oddCount m (j + 1) < 2 ^ (j + 1) := light_of_deficit_pos hpos
    rw [hcount] at hlight
    -- heavy-or-balanced at `j`: `2 ^ j ≤ 3 ^ a`, read off the sign of the demand
    have hmulle : (2:Nat) ^ j * m ≤ 3 ^ oddCount m j * m := by
      unfold deficit at hle; omega
    have hheavy : (2:Nat) ^ j ≤ 3 ^ oddCount m j :=
      Nat.le_of_mul_le_mul_right hmulle hm
    have h3 : (3:Nat) ^ (oddCount m j + 1) = 3 * 3 ^ oddCount m j := by
      rw [Nat.pow_succ, Nat.mul_comm]
    have h2 : (2:Nat) ^ (j + 1) = 2 * 2 ^ j := Arith.two_pow_succ j
    have h3pos : 0 < (3:Nat) ^ oddCount m j := Arith.three_pow_pos _
    omega

/-- At the first crossing the demand is still small: it is at most `3 ^ a · m`,
because the window was heavy-or-balanced one step earlier. -/
theorem crossing_demand_small {m j : Nat}
    (he : acceleratedOrbit j m % 2 = 0) (hle : deficit m j ≤ 0) :
    deficit m (j + 1) ≤ ((3 ^ oddCount m j * m : Nat) : Int) := by
  rw [deficit_succ_even he]
  omega

/-! ## The even-run freeze

Across an even run the accumulator does not move while the demand doubles at
every step.  That is the one place where the two objects can be compared without
the displacement identity collapsing the comparison. -/

/-- The accumulator is constant across a run of even steps. -/
theorem affineC_even_run {m : Nat} : ∀ r j : Nat,
    (∀ i : Nat, i < r → acceleratedOrbit (j + i) m % 2 = 0) →
    affineC (j + r) m = affineC j m := by
  intro r
  induction r with
  | zero => intro j _; rfl
  | succ r ih =>
    intro j h
    have hstep : acceleratedOrbit (j + r) m % 2 = 0 := h r (by omega)
    have hsucc : j + (r + 1) = (j + r) + 1 := by omega
    rw [hsucc, affineC_even hstep]
    exact ih j (fun i hi => h i (by omega))

/-- The odd-step count is constant across a run of even steps. -/
theorem oddCount_even_run {m : Nat} : ∀ r j : Nat,
    (∀ i : Nat, i < r → acceleratedOrbit (j + i) m % 2 = 0) →
    oddCount m (j + r) = oddCount m j := by
  intro r
  induction r with
  | zero => intro j _; rfl
  | succ r ih =>
    intro j h
    have hstep : acceleratedOrbit (j + r) m % 2 = 0 := h r (by omega)
    have hlast := Density.oddCount_succ_last m (j + r)
    have hsucc : j + (r + 1) = (j + r) + 1 := by omega
    rw [hsucc]
    have := ih j (fun i hi => h i (by omega))
    omega

/-- **The even-run window condition.**  A never-dropper that takes `r` consecutive
even steps from time `j` must satisfy the window condition of time `j + r` with
the *cap of time `j`* — a factor `2 ^ r` sharper than
`neverDrops_window_condition` at the same endpoint, because the accumulator is
frozen while the demand doubles. -/
theorem neverDrops_even_run {m j r : Nat} (hm : 0 < m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m)
    (heven : ∀ i : Nat, i < r → acceleratedOrbit (j + i) m % 2 = 0) :
    2 ^ (j + r) * m
      ≤ 3 ^ oddCount m j * m + 2 ^ (j - oddCount m j) * 3 ^ oddCount m j := by
  have hend := (neverDrops_iff_affine hm).mp hnd (j + r)
  have hfreeze := affineC_even_run r j heven
  have hcount := oddCount_even_run r j heven
  have hcap := affineC_le m j
  rw [hcount, hfreeze] at hend
  have hpos : 0 < (2:Nat) ^ j := Arith.two_pow_pos j
  omega

/-- **Heaviness survives an even run for free.**  `AffineExact.heavy_while_few_even`
concludes `2 ^ i ≤ 2 · 3 ^ a` at a window `i` from the hypothesis `2 ^ (i−a) ≤ m`.
Across an even run the accumulator is frozen, so the *endpoint* conclusion follows
from the hypothesis at the *start* of the run — a hypothesis weaker by the whole
factor `2 ^ r`.

Measured on genuine no-drop prefixes below `120 000`: 1 387 windows where this
hypothesis holds and `heavy_while_few_even`'s does not, and no failures. -/
theorem heavy_after_even_run {m j r : Nat} (hm : 0 < m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m)
    (hfew : (2:Nat) ^ (j - oddCount m j) ≤ m)
    (heven : ∀ i : Nat, i < r → acceleratedOrbit (j + i) m % 2 = 0) :
    2 ^ (j + r) ≤ 2 * 3 ^ oddCount m j := by
  have hrun := neverDrops_even_run hm hnd heven
  have hcap : 3 ^ oddCount m j * m + 2 ^ (j - oddCount m j) * 3 ^ oddCount m j
      ≤ 3 ^ oddCount m j * m + m * 3 ^ oddCount m j :=
    Nat.add_le_add_left (Nat.mul_le_mul_right _ hfew) _
  have hcomm : m * 3 ^ oddCount m j = 3 ^ oddCount m j * m := Nat.mul_comm _ _
  have htwo : 3 ^ oddCount m j * m + 3 ^ oddCount m j * m
      = (2 * 3 ^ oddCount m j) * m := by
    rw [Nat.mul_assoc]; omega
  have hmul : 2 ^ (j + r) * m ≤ (2 * 3 ^ oddCount m j) * m := by omega
  exact Nat.le_of_mul_le_mul_right hmul hm

/-- **Even runs are trivial in the balanced regime.**  If a never-dropper's window
at time `j` is balanced-or-light (`3 ^ a ≤ 2 ^ j`) and its even count is at most
`log₂ m` (`2 ^ (j−a) ≤ m`), then it cannot take two consecutive even steps from
`j`: every all-even run starting there has length at most one.

The strength comes from the freeze.  `neverDrops_window_condition` at the same
endpoint `j + r` supplies the cap `2 ^ (j+r−a) · 3 ^ a`, which under these
hypotheses is `≥ 2 ^ r · 2 ^ j · m` and so excludes nothing; the frozen cap
`2 ^ (j−a) · 3 ^ a` is smaller by the whole factor `2 ^ r`, and excludes `r ≥ 2`. -/
theorem even_run_le_one_of_balanced {m j r : Nat} (hm : 0 < m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m)
    (hbal : (3:Nat) ^ oddCount m j ≤ 2 ^ j)
    (hfew : (2:Nat) ^ (j - oddCount m j) ≤ m)
    (heven : ∀ i : Nat, i < r → acceleratedOrbit (j + i) m % 2 = 0) :
    r ≤ 1 := by
  have hrun := neverDrops_even_run hm hnd heven
  -- the cap collapses: `3 ^ a (m + 2 ^ (j−a)) ≤ 2 · 2 ^ j · m`
  have hcap : 3 ^ oddCount m j * m + 2 ^ (j - oddCount m j) * 3 ^ oddCount m j
      ≤ 3 ^ oddCount m j * m + m * 3 ^ oddCount m j :=
    Nat.add_le_add_left (Nat.mul_le_mul_right _ hfew) _
  have hcomm : m * 3 ^ oddCount m j = 3 ^ oddCount m j * m := Nat.mul_comm _ _
  have hbal' : 3 ^ oddCount m j * m ≤ 2 ^ j * m := Nat.mul_le_mul_right _ hbal
  have hsplit : 2 ^ (j + r) * m = 2 ^ r * (2 ^ j * m) := by
    rw [Nat.pow_add, Nat.mul_comm ((2:Nat) ^ j) (2 ^ r), Nat.mul_assoc]
  have hmpos : 0 < 2 ^ j * m := Nat.mul_pos (Arith.two_pow_pos j) hm
  have hle2 : 2 ^ r * (2 ^ j * m) ≤ 2 * (2 ^ j * m) := by omega
  have hr : (2:Nat) ^ r ≤ 2 := Nat.le_of_mul_le_mul_right hle2 hmpos
  match r, hr with
  | 0, _ => omega
  | 1, _ => omega
  | (k + 2), hk =>
    exfalso
    have h4 : (2:Nat) ^ 2 ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by omega) (by omega)
    have h44 : (2:Nat) ^ 2 = 4 := rfl
    omega

/-- **No two consecutive even steps while balanced.**  A never-dropper whose window
at time `j` is balanced-or-light (`3 ^ a ≤ 2 ^ j`) and whose even count is at most
`log₂ m` (`2 ^ (j−a) ≤ m`) cannot take two even steps in a row from `j`. -/
theorem not_two_even_of_balanced {m j : Nat} (hm : 0 < m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m)
    (hbal : (3:Nat) ^ oddCount m j ≤ 2 ^ j)
    (hfew : (2:Nat) ^ (j - oddCount m j) ≤ m) :
    ¬ (acceleratedOrbit j m % 2 = 0 ∧ acceleratedOrbit (j + 1) m % 2 = 0) := by
  rintro ⟨h0, h1⟩
  have heven : ∀ i : Nat, i < 2 → acceleratedOrbit (j + i) m % 2 = 0 := by
    intro i hi
    match i, hi with
    | 0, _ => simpa using h0
    | 1, _ => simpa using h1
  have := even_run_le_one_of_balanced (r := 2) hm hnd hbal hfew heven
  omega

/-- The same exclusion at the start of the orbit: `j = 0` is balanced with even
count zero, so a never-dropper's first two steps are never both even.  (Its first
step is not even at all — `oddCount_pos_of_neverDrops` — so this is the weaker
statement, recorded as the base case of the family.) -/
theorem not_two_even_at_start {m : Nat} (hm : 0 < m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m) :
    ¬ (acceleratedOrbit 0 m % 2 = 0 ∧ acceleratedOrbit 1 m % 2 = 0) := by
  have h0 : oddCount m 0 = 0 := rfl
  refine not_two_even_of_balanced (j := 0) hm hnd ?_ ?_
  · rw [h0]; simp
  · rw [h0]; exact hm

end AffineDeficit
end Collatz
