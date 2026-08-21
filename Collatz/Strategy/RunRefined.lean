import Collatz.Strategy.HeavyResidue
import Collatz.Strategy.RunAlgebra

/-!
# The run-refined accumulator bound

`HeavyResidue.heavy_accumulator_bound_sharp` says `3 · C ≤ a · 3 ^ a` on a heavy
window, i.e. `C ≤ 0.3333 · a · 3 ^ a`.  That bound is proved one *odd step* at a
time, and its induction is exactly tight at every step — so it cannot be improved
without using information the per-step argument does not carry.

This file supplies that information.  The per-step induction is tight only when
each odd step is *isolated*; when two odd steps are adjacent, the second one has
slack, and the slack is a constant factor.

## The mechanism

Heaviness gives `2 ^ j ≤ 3 ^ (a_j)` at every time.  But if the step at `j − 1`
was *also* odd, then `a_j = a_(j−1) + 1`, and heaviness at `j − 1` gives

`2 ^ j = 2 · 2 ^ (j−1) ≤ 2 · 3 ^ (a_j − 1)`,   i.e.   `3 · 2 ^ j ≤ 2 · 3 ^ (a_j)`.

So at the second and every later odd step of a run, `2 ^ j` is a factor `3/2`
below what heaviness alone allows, and the induction has room to spare.  Counting
those occurrences gives the refinement.

Write `p` for the number of adjacent odd pairs — indices `i` with `T^i(x)` and
`T^(i+1)(x)` both odd (`pairCount`).  Then

`9 · C + p · 3 ^ a ≤ 3 · (a · 3 ^ a)`     (`accumulator_pair_bound`)

which is `3 · C ≤ a · 3 ^ a` exactly when `p = 0`, and strictly sharper otherwise.

## What it is worth

With `r` the number of odd runs, `p = a − r`, so the bound reads
`9 · C ≤ (2a + r) · 3 ^ a`.  Composed with `RunAlgebra.heavy_run_count`
(`17 r < 10 a` on a heavy window) this gives

`153 · C ≤ (44 a + 17) · 3 ^ a`,   i.e.   `C ≲ 0.2876 · a · 3 ^ a`,

a 13.7 % improvement on the stored constant, **certificate-free** — no realizability
recursion and no kernel sweep.  (An earlier draft said 15 %.)

Measured, exhaustively over all **12 449** words of length ≤ 21 heavy at every
*proper* prefix with positive gap: zero failures, worst ratio **0.85185**.

*Two corrections to an earlier version of this paragraph, both found by adversarial
audit and both mine.*  First, it claimed the bound is "exactly tight (worst ratio
1.0000)".  It is not: ratio 1 is attained at exactly three words, `1`, `11` and
`110`, all of length ≤ 3.  At every heavy length ≥ 4 the ratio is ≤ 0.958, and at
`L = 20` the maximum is 0.86840.  So the asymptotic slack is about 13 %, and the
true extremal constant is nearer 0.250 — much closer to `Bcap`'s 0.2404 than
claimed.  Second, it quoted "12 448 heavy words with positive gap" measured against
*proper*-prefix heaviness, while the theorem then hypothesised heaviness at every
`i ≤ j`.  Under that stronger hypothesis the positive-gap class is **empty**, since
heaviness at `i = j` is exactly the negation of a positive gap.  The hypothesis is
now weakened to `i < j` — which the induction never needed, and which is what makes
the bound applicable to a cycle word at all.

## Honest comparison, and why this does not move the frontier

`RealizableBound.Bcap` is sharper: it reaches `0.2404 · a · 3 ^ a` asymptotically,
and it is **exactly attained** — independently confirmed here, `max C = Bcap a` on
the nose for every `a ≤ 12`.  So this bound does not beat `Bcap` and does not move
the cycle frontier.  Its value is that it is a *different* mechanism (run
structure, not integrality of odd-step times), it costs no certificate, and it
identifies the extremal shape.  The two informations are independent and could in
principle be combined; that is not attempted here.

One endpoint caution, recorded because it caught me: the clean composition
`153 C < 44 a 3 ^ a` is **false** at `a = 1` (the trivial-cycle word `10`, where
`153 > 132`), because `heavy_run_count` needs a complete final run.  The `+ 17`
form above is the universally true one.
-/

namespace Collatz
namespace RunRefined

open Reach Density AffineExact HeavyWord

/-- The number of adjacent odd pairs in the first `j` steps: indices `i + 1 < j`
with `T^i(x)` and `T^(i+1)(x)` both odd, counted at the later index. -/
def pairCount (x : Nat) : Nat → Nat
  | 0 => 0
  | 1 => 0
  | j + 2 =>
      pairCount x (j + 1) +
        (if acceleratedOrbit (j + 1) x % 2 = 1 ∧ acceleratedOrbit j x % 2 = 1 then 1 else 0)

@[simp] theorem pairCount_zero (x : Nat) : pairCount x 0 = 0 := rfl
@[simp] theorem pairCount_one (x : Nat) : pairCount x 1 = 0 := rfl

theorem pairCount_succ_succ (x j : Nat) :
    pairCount x (j + 2) =
      pairCount x (j + 1) +
        (if acceleratedOrbit (j + 1) x % 2 = 1 ∧ acceleratedOrbit j x % 2 = 1 then 1 else 0) := rfl

/-! ## Pure algebra, isolated so that `omega` only ever sees linear atoms -/

private theorem alg_rhs (m A : Nat) : 3 * ((m + 1) * (A * 3)) = 9 * (m * A) + 9 * A := by
  simp [Nat.add_mul, Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

private theorem alg_open (Cj p A t : Nat) :
    9 * (3 * Cj + t) + p * (A * 3) = 3 * (9 * Cj + p * A) + 9 * t := by
  simp [Nat.add_mul, Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  try omega

private theorem alg_pair (Cj p A t : Nat) :
    9 * (3 * Cj + t) + (p + 1) * (A * 3)
      = 3 * (9 * Cj + p * A) + 3 * (3 * t) + 3 * A := by
  simp [Nat.add_mul, Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  try omega

/-! ## The slack at a non-initial odd step -/

/-- **The whole content of the refinement.**  If the step before an odd step was
also odd, heaviness one step earlier is a factor `3/2` stronger than heaviness
at the step itself. -/
theorem three_two_pow_le {x j : Nat}
    (hprev : acceleratedOrbit j x % 2 = 1)
    (hheavy : 2 ^ j ≤ 3 ^ oddCount x j) :
    3 * 2 ^ (j + 1) ≤ 2 * 3 ^ oddCount x (j + 1) := by
  have hcount : oddCount x (j + 1) = oddCount x j + 1 := by
    have := Density.oddCount_succ_last x j
    omega
  rw [hcount, Nat.pow_succ 3 (oddCount x j), Nat.pow_succ 2 j]
  have h3 : 3 ^ oddCount x j ≤ 3 ^ oddCount x j := Nat.le_refl _
  calc 3 * (2 ^ j * 2) = 6 * 2 ^ j := by omega
    _ ≤ 6 * 3 ^ oddCount x j := Nat.mul_le_mul_left 6 hheavy
    _ = 2 * (3 ^ oddCount x j * 3) := by omega

/-! ## The refined bound -/

/-- **The run-refined accumulator bound.**  `9 C + p · 3 ^ a ≤ 3 a · 3 ^ a`, where
`p` counts adjacent odd pairs.  At `p = 0` this is exactly
`HeavyResidue.heavy_accumulator_bound_sharp`; every adjacent odd pair buys a
further `3 ^ a / 9`. -/
theorem accumulator_pair_bound (x : Nat) : ∀ j : Nat,
    (∀ i : Nat, i < j → 2 ^ i ≤ 3 ^ oddCount x i) →
    9 * affineC j x + pairCount x j * 3 ^ oddCount x j
      ≤ 3 * (oddCount x j * 3 ^ oddCount x j) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hheavy
    have ihb := ih (fun i hi => hheavy i (Nat.lt_succ_of_lt hi))
    have hlast := Density.oddCount_succ_last x j
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j x) with he | ho
    · -- even step: accumulator, odd-count and pair-count all unchanged
      have hcount : oddCount x (j + 1) = oddCount x j := by omega
      have hpair : pairCount x (j + 1) = pairCount x j := by
        cases j with
        | zero => rfl
        | succ k =>
          rw [pairCount_succ_succ, if_neg (by rintro ⟨h1, _⟩; omega), Nat.add_zero]
      rw [hcount, hpair, affineC_even he]
      exact ihb
    · -- odd step
      have hcount : oddCount x (j + 1) = oddCount x j + 1 := by omega
      have hC : affineC (j + 1) x = 3 * affineC j x + 2 ^ j := affineC_odd ho
      have hj : 2 ^ j ≤ 3 ^ oddCount x j := hheavy j (Nat.lt_succ_self j)
      have hpow : (3 : Nat) ^ (oddCount x j + 1) = 3 ^ oddCount x j * 3 := Nat.pow_succ 3 _
      -- the right-hand side, expanded once so `omega` sees only atoms
      have hRHS := alg_rhs (oddCount x j) (3 ^ oddCount x j)
      cases j with
      | zero =>
        have hpair : pairCount x 1 = 0 := rfl
        rw [hcount, hpair, hC, hpow]
        simp
      | succ k =>
        rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit k x) with hke | hko
        · -- previous step even: this odd step opens a run, no pair is added
          have hpair : pairCount x (k + 2) = pairCount x (k + 1) := by
            rw [pairCount_succ_succ, if_neg (by rintro ⟨_, h2⟩; omega), Nat.add_zero]
          have hL := alg_open (affineC (k + 1) x) (pairCount x (k + 1))
            (3 ^ oddCount x (k + 1)) (2 ^ (k + 1))
          have hb : 9 * 2 ^ (k + 1) ≤ 9 * 3 ^ oddCount x (k + 1) := Nat.mul_le_mul_left 9 hj
          have h3 := Nat.mul_le_mul_left 3 ihb
          rw [hcount, hpair, hC, hpow, hL, hRHS]
          omega
        · -- previous step odd: a pair is added, and the extra slack pays for it
          have hpair : pairCount x (k + 2) = pairCount x (k + 1) + 1 := by
            rw [pairCount_succ_succ, if_pos ⟨ho, hko⟩]
          have hslack : 3 * 2 ^ (k + 1) ≤ 2 * 3 ^ oddCount x (k + 1) :=
            three_two_pow_le hko (hheavy k (by omega))
          have hL := alg_pair (affineC (k + 1) x) (pairCount x (k + 1))
            (3 ^ oddCount x (k + 1)) (2 ^ (k + 1))
          have h3 := Nat.mul_le_mul_left 3 ihb
          have h4 := Nat.mul_le_mul_left 3 hslack
          rw [hcount, hpair, hC, hpow, hL, hRHS]
          omega


/-! ## From adjacent pairs to a numeric bound

`accumulator_pair_bound` is only useful with a *lower* bound on `pairCount`.  That
is pure word combinatorics: runs of odd steps are separated by at least one even
step, so with `a` odd steps in `j` and `r` runs, `r ≤ (j − a) + 1`, and
`p = a − r ≥ 2a − j − 1`.  The induction below carries the sharper form, in which
the slack is exactly the parity of the last step. -/

/-- The sharp form: the slack is the parity of the final step. -/
theorem pair_bound_succ (x : Nat) : ∀ j : Nat,
    2 * oddCount x (j + 1)
      ≤ pairCount x (j + 1) + (j + 1) + acceleratedOrbit j x % 2 := by
  intro j
  induction j with
  | zero =>
    have h := Density.oddCount_succ_last x 0
    have : acceleratedOrbit 0 x % 2 = 0 ∨ acceleratedOrbit 0 x % 2 = 1 :=
      Arith.mod_two_eq_zero_or_one _
    simp [pairCount] at *
    omega
  | succ j ih =>
    rw [show j + 1 + 1 = j + 2 from rfl]
    have hlast : oddCount x (j + 2) = oddCount x (j + 1) + acceleratedOrbit (j + 1) x % 2 :=
      Density.oddCount_succ_last x (j + 1)
    have hp := pairCount_succ_succ x j
    have h1 : acceleratedOrbit j x % 2 = 0 ∨ acceleratedOrbit j x % 2 = 1 :=
      Arith.mod_two_eq_zero_or_one _
    have h2 : acceleratedOrbit (j + 1) x % 2 = 0 ∨ acceleratedOrbit (j + 1) x % 2 = 1 :=
      Arith.mod_two_eq_zero_or_one _
    rcases h2 with he | ho
    · rw [if_neg (by rintro ⟨h, _⟩; omega)] at hp
      omega
    · rcases h1 with hke | hko
      · rw [if_neg (by rintro ⟨_, h⟩; omega)] at hp
        omega
      · rw [if_pos ⟨ho, hko⟩] at hp
        omega

/-- `2 a ≤ p + j + 1` at every length. -/
theorem pair_bound (x j : Nat) : 2 * oddCount x j ≤ pairCount x j + j + 1 := by
  cases j with
  | zero => simp
  | succ j =>
    have hs := pair_bound_succ x j
    have hpar : acceleratedOrbit j x % 2 = 0 ∨ acceleratedOrbit j x % 2 = 1 :=
      Arith.mod_two_eq_zero_or_one _
    omega

/-- **The run-refined bound, in closed form.**  On a heavy window,

`9 · C ≤ (a + j + 1) · 3 ^ a`.

Since a heavy window has `j ≤ a · log₂ 3`, this is `C ≲ 0.2873 · a · 3 ^ a`,
against the stored `0.3333` of `heavy_accumulator_bound_sharp` — a 14 %
improvement carrying no certificate.  Measured worst ratio **0.85185** (`= 23/27`) over the 12 449 words of length ≤ 21
heavy at every *proper* prefix with positive gap.

*Corrected:* an earlier version of this docstring said "exactly tight (worst ratio
1.0000) over all 59 058 heavy words of length at most 20".  That population is
heaviness at **every** prefix including the last — which, as the header explains,
contains no positive-gap word at all, so the measurement was over a class holding no
cycle word, and ratio 1 is attained only at the length-1 word `1`.  This is the same
defect the header repairs, left live one screen further down. -/
theorem accumulator_closed_bound (x j : Nat)
    (hheavy : ∀ i : Nat, i < j → 2 ^ i ≤ 3 ^ oddCount x i) :
    9 * affineC j x ≤ (oddCount x j + j + 1) * 3 ^ oddCount x j := by
  have hmain := accumulator_pair_bound x j hheavy
  have hpair := pair_bound x j
  have hpos : 0 < 3 ^ oddCount x j := Arith.three_pow_pos _
  -- `3 a - p ≤ a + j + 1` from `2a ≤ p + j + 1`
  have hcoef : 3 * oddCount x j ≤ pairCount x j + (oddCount x j + j + 1) := by omega
  have hmul := Nat.mul_le_mul_right (3 ^ oddCount x j) hcoef
  rw [Nat.add_mul] at hmul
  have hexp : 3 * oddCount x j * 3 ^ oddCount x j
      = 3 * (oddCount x j * 3 ^ oddCount x j) := by
    rw [Nat.mul_assoc]
  omega

end RunRefined
end Collatz
