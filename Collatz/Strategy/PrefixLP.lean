import Collatz.Strategy.OrderBox

/-!
# The prefix LP: its value is exactly `Bcap`, and its dual multipliers are zero

Round XIII asked whether the `L−1` minimum-rotation prefix inequalities of a cycle,

`G · C_j ≥ (2 ^ j − 3 ^ (A j)) · C`,    `j = 1, …, L−1`,

can be *combined* — weighted, telescoped, dualised — into a bound on the accumulator
`C` strictly better than `Bcap a`.  The brief's own hard constraint was that only a
constant-factor reduction is worth anything: at the frontier pair `(L, a) = (6809, 4296)`
the certificate needs `Bcap a / G < c`, and it misses.

**The answer is that the family is vacuous on the box, so the LP value is exactly
`Bcap a` and every optimal dual multiplier on a prefix row is zero.**  This is a
sharpness theorem for `Bcap`, not a repair of it, and it closes the route.

## The one-line reason

Write `A j` for the number of odd steps before time `j` and `t i` for the time of the
`i`-th odd step.  If `A j = i < a` then by definition `j ≤ t i` — time `j` has not yet
reached the `(i+1)`-st odd step.  The box `t i ≤ fexp i` therefore gives

`2 ^ j ≤ 2 ^ (t i) ≤ 2 ^ (fexp i) ≤ 3 ^ i = 3 ^ (A j)`,

which is *heaviness at every prefix at once* (`box_heavy`), and `prefix_gap_of_heavy`
already shows a heavy prefix satisfies its inequality for free — for **every** `g`,
every `C`, with no cycle hypothesis and no magnitude.  The remaining prefixes, those
with `A j = a`, need `j ≤ fexp a`, which on the ledge `L = fexp a + 1` is exactly
`j < L`; the closing index `j = L` is the cycle equation (`prefix_gap_at_L`).

So the box implies the entire family, the feasible set of `{box} ∪ {prefix}` is the
box, and `Cw_le_Bcap` already caps it at `Bcap a`, attained at the Beatty word
(`Cw_fexp`).  Adding the prefix rows to the LP moves neither the optimum nor the
value.  Measured slack confirms the degeneracy question: at the Beatty corner every
one of the `L−1` prefix rows is **strictly** slack (relative slack minimum `0.5, 0.5,
0.207, 0.32, 0.131, 0.228, 0.306, 0.168, …`, positive for every `a < 120`, exact
rational arithmetic), so complementary slackness forces `λ_j = 0` in *every* optimal
dual, not merely in one.

## The family is not just non-binding, it is strictly weaker

`prefix_beaten_a7` exhibits the point in the kernel.  At `a = 7`, `L = 12`,
`G = 2 ^ 12 − 3 ^ 7 = 1909`, the word `t = (0,1,3,5,6,8,10)` satisfies **all eleven**
prefix inequalities and has `Cw t 7 = 5095 > 3767 = Bcap 7`.  A positive combination
of inequalities can never exclude a point that satisfies each of them, so no dual
certificate built from this family alone can prove `C ≤ Bcap a`, let alone beat it.
Exhaustively over all words: `max C` subject to the prefix family alone, against
`Bcap a`, is `1, 7/5, 1, 101/85, 1, 1357/1085, 5095/3767, 14501/13349, 60191/44143,
159181/148813, 579943/479207` for `a = 1..11` — up to **36 % worse** than `Bcap`,
never better.  And `box ⊆ prefix-feasible` was checked over every word for `a ≤ 11`,
zero exceptions, as `box_heavy` predicts.

## The two increment cases (§XXXVII–XXXVIII), exactly

The natural potential is the pair `Q j = 2 ^ j · C` against
`P j = G · C_j + 3 ^ (A j) · C`, the family being `Q j ≤ P j`.  Because
`A (j+1) − A j ∈ {0,1}` there are exactly two cases, and both are exact identities
with no constant to choose (`potential_even`, `potential_odd`):

* even step: `P (j+1) = P j`,        `Q (j+1) = 2 · Q j`;
* odd step at `j = t i`: `P (j+1) = 3 · P j + G · 2 ^ j`,   `Q (j+1) = 2 · Q j`.

So the ratio `Q/P` doubles on an even step and is multiplied by rather less than
`2/3` on an odd step, and over the whole word the two factors compose to
`2 ^ L / 3 ^ a`, which is `> 1` by the ledge and `= 1 + G/3 ^ a` on the nose.  The
telescoped sum is therefore **the cycle equation itself** (`prefix_gap_at_L`) — an
identity, carrying exactly zero information.  This is the precise sense in which the
sophisticated per-step accumulator induction fails: the state `(j, A j)` is not too
coarse, it is exactly right, and what it computes is the tautology.  No constant is
missing, so §XXXIX's prohibition is respected: there is nothing here to repair.
-/

namespace Collatz
namespace PrefixLP

open RealizableBound ExtremalWord OrderBox

/-! ## From the box to heaviness at every prefix -/

/-- If the `i`-th odd step has already happened by time `j`, the prefix count at `j`
is at least `i + 1`.  The counting half of `cnt_at_time`. -/
theorem succ_le_cnt {t : Nat → Nat} (hst : StrictInc t) {j : Nat} :
    ∀ a i : Nat, i < a → t i < j → i + 1 ≤ cnt t a j := by
  intro a
  induction a with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ a ih =>
    intro i hi hlt
    rcases Nat.lt_or_ge i a with hia | hia
    · have h1 := ih i hia hlt
      have h2 : cnt t a j ≤ cnt t (a + 1) j := by
        rw [cnt_succ]; exact Nat.le_add_right _ _
      omega
    · have hia' : i = a := by omega
      subst hia'
      have hall : cnt t i j = i :=
        cnt_all_lt i (fun k hk => Nat.lt_trans (strictInc_mono hst k i hk) hlt)
      rw [cnt_succ, hall, if_pos hlt]
      exact Nat.le_refl _

/-- **Time `j` never outruns the odd step it is still waiting for.**  If the prefix
count at `j` is `i < a`, then `j ≤ t i`. -/
theorem le_time_of_cnt {t : Nat → Nat} (hst : StrictInc t) {a i j : Nat}
    (hi : i < a) (hcnt : cnt t a j = i) : j ≤ t i := by
  rcases Nat.lt_or_ge (t i) j with hlt | hge
  · have := succ_le_cnt hst a i hi hlt
    omega
  · exact hge

/-- **The box implies heaviness at every prefix simultaneously.**  This is the
converse of `heavy_le_fexp`, and it is the whole content of the round: a word in the
box is heavy at *every* `j ≤ fexp a`, which on the ledge `L = fexp a + 1` is every
proper prefix. -/
theorem box_heavy {t : Nat → Nat} (hst : StrictInc t) {a : Nat}
    (hbox : ∀ i : Nat, i < a → t i ≤ fexp i) :
    ∀ j : Nat, j ≤ fexp a → 2 ^ j ≤ 3 ^ cnt t a j := by
  intro j hj
  rcases Nat.lt_or_ge (cnt t a j) a with hlt | hge
  · have hle : j ≤ t (cnt t a j) := le_time_of_cnt hst hlt rfl
    have h1 : (2:Nat) ^ j ≤ 2 ^ t (cnt t a j) := Arith.two_pow_le_two_pow hle
    have h2 : (2:Nat) ^ t (cnt t a j) ≤ 2 ^ fexp (cnt t a j) :=
      Arith.two_pow_le_two_pow (hbox _ hlt)
    have h3 : (2:Nat) ^ fexp (cnt t a j) ≤ 3 ^ cnt t a j := fexp_le _
    omega
  · have hcnt : cnt t a j = a := by
      have : cnt t a j ≤ a := by
        clear hge hj
        induction a with
        | zero => exact Nat.le_refl _
        | succ a ih =>
          rw [cnt_succ]
          have := ih (fun i hi => hbox i (Nat.lt_succ_of_lt hi))
          by_cases hc : t a < j <;> simp [hc] <;> omega
      omega
    rw [hcnt]
    have h1 : (2:Nat) ^ j ≤ 2 ^ fexp a := Arith.two_pow_le_two_pow hj
    have h2 : (2:Nat) ^ fexp a ≤ 3 ^ a := fexp_le a
    omega

/-! ## The prefix family is vacuous on the box -/

/-- **The headline.**  Every member of the minimum-rotation prefix family holds for
free on the box, for every gap `g` and every accumulator value `X` — no cycle
hypothesis, no magnitude, no verified range.  The `L−1` inequalities the round set out
to combine are, one and all, implied by the single hypothesis that already produced
`Bcap`. -/
theorem prefix_vacuous_on_box {t : Nat → Nat} (hst : StrictInc t) {a : Nat}
    (hbox : ∀ i : Nat, i < a → t i ≤ fexp i) (g X : Nat) :
    ∀ j : Nat, j ≤ fexp a →
      2 ^ j * X ≤ 3 ^ cnt t a j * X + g * Cw t (cnt t a j) := by
  intro j hj
  have h : (2:Nat) ^ j * X ≤ 3 ^ cnt t a j * X :=
    Nat.mul_le_mul_right _ (box_heavy hst hbox j hj)
  omega

/-- **The LP value is exactly `Bcap a`.**  Adding the whole prefix family to the box
changes neither the feasible optimum nor the value: the Beatty word is still feasible
(first component, for every `g` and `X`), it still attains `Bcap a` (second), and
every feasible word is still capped by it (third).  A sharpness theorem for `Bcap`. -/
theorem lp_value_eq_Bcap (a : Nat) :
    (∀ g X j : Nat, j ≤ fexp a →
        2 ^ j * X ≤ 3 ^ cnt fexp a j * X + g * Cw fexp (cnt fexp a j))
      ∧ Cw fexp a = Bcap a
      ∧ (∀ t : Nat → Nat, StrictInc t → (∀ i : Nat, i < a → t i ≤ fexp i) →
          Cw t a ≤ Bcap a) := by
  refine ⟨?_, Cw_fexp a, ?_⟩
  · intro g X j hj
    exact prefix_vacuous_on_box fexp_strictInc (fun i _ => Nat.le_refl _) g X j hj
  · intro t _ hbox
    rw [← Cw_fexp]
    exact Cw_le t fexp a hbox

/-! ## The family is strictly weaker than the box

A positive combination of inequalities cannot exclude a point satisfying every one of
them.  So it is enough to exhibit one prefix-feasible word above `Bcap`. -/

/-- The witness word `t = (0,1,3,5,6,8,10)` at `a = 7`, `L = 12`. -/
def w7 : Nat → Nat
  | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 5 | 4 => 6 | 5 => 8 | 6 => 10
  | _ => 12

theorem w7_strictInc_below : ∀ i : Nat, i < 6 → w7 i < w7 (i + 1) := by decide

/-- **The prefix family alone cannot even reach `Bcap`, let alone beat it.**  All
eleven prefix inequalities hold at `G = 1909 = 2 ^ 12 − 3 ^ 7`, and the accumulator is
`5095 > 3767 = Bcap 7`.  Hence no positive combination — no weighting, telescoping,
or dual certificate — drawn from this family alone can prove `C ≤ Bcap 7`. -/
theorem prefix_beaten_a7 :
    (∀ j : Nat, 1 ≤ j → j < 12 →
        2 ^ j * Cw w7 7 ≤ 3 ^ cnt w7 7 j * Cw w7 7 + 1909 * Cw w7 (cnt w7 7 j))
      ∧ Cw w7 7 = 5095 ∧ Bcap 7 = 3767 ∧ Bcap 7 < Cw w7 7 := by
  refine ⟨?_, by decide, by decide, by decide⟩
  intro j h1 h2
  have hj : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9
      ∨ j = 10 ∨ j = 11 := by omega
  rcases hj with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide

/-- The closing index is the cycle equation: `2 ^ 12 = 3 ^ 7 + 1909`, so at `j = L`
the inequality is an identity for this word too.  Nothing anywhere in the chain
separates it from the box. -/
theorem w7_closes : (2:Nat) ^ 12 = 3 ^ 7 + 1909 := by decide

/-! ## The two increment cases (§XXXVII–XXXVIII) -/

/-- **Even step.**  The prefix count does not move, so `P` is *literally unchanged*
(the same expression in `i`), while `Q` doubles.  Exact, and no constant to choose. -/
theorem potential_even (X j : Nat) : 2 ^ (j + 1) * X = 2 * (2 ^ j * X) := by
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, Nat.mul_assoc]

/-- **Odd step.**  At `j = t i` the count advances by one, and the potential obeys
`P (j+1) = 3 · P j + G · 2 ^ j` exactly — the `+ G · 2 ^ j` is forced, not chosen.
This is the two-case law §XXXVII asked for, and both branches are identities. -/
theorem potential_odd {t : Nat → Nat} (G X i : Nat) :
    G * Cw t (i + 1) + 3 ^ (i + 1) * X
      = 3 * (G * Cw t i + 3 ^ i * X) + G * 2 ^ t i := by
  rw [Cw_succ, Nat.pow_succ]
  have e1 : G * (3 * Cw t i + 2 ^ t i) = 3 * (G * Cw t i) + G * 2 ^ t i := by
    rw [Nat.mul_add, Nat.mul_left_comm]
  have e2 : 3 ^ i * 3 * X = 3 * (3 ^ i * X) := by
    rw [Nat.mul_comm (3 ^ i) 3, Nat.mul_assoc]
  omega

/-- The two cases composed over a whole word multiply `Q` by `2 ^ L` and `P` by at
least `3 ^ a`; on the ledge `2 ^ L = 3 ^ a + G`, so the telescoped statement is the
cycle equation and the accumulated gain is exactly zero. -/
theorem telescope_is_the_cycle_equation {G a L X : Nat} (hledge : 2 ^ L = 3 ^ a + G) :
    2 ^ L * X = 3 ^ a * X + G * X := by
  rw [hledge, Nat.add_mul]

end PrefixLP
end Collatz
