import Collatz.Strategy.NeverDrops

/-!
# The denominator test: the whole theory is uniform in `d`, and `d = 5` has cycles

`Mirror` shows that every theorem derived from the shift identity and
congruences is blind to the *sign* of the `+1`, because `3x − 1` on `ℕ` is
`3x + 1` on the negative integers and that world has nontrivial cycles.  This
file sharpens that from the sign of the `1` to **the value of the `d`**, and it
is a strictly stronger filter.

## The family

For any odd `d`, put

`T_d(x) = x / 2` for even `x`,  `(3x + d) / 2` for odd `x`.

`T_1` is exactly `acceleratedStep` (`genStep_one`).  The point is that the
*entire* elementary apparatus of this development is uniform in `d`:

* the run identity.  For odd `d`, whenever `2 ^ L ∣ (x + d)` the next `L` steps
  are all odd and
  `2 ^ L · (T_d^L(x) + d) = 3 ^ L · (x + d)`   (`gen_run_value`),
  which is `RunValue.oddRun_value` with `x + 1` replaced by `x + d` throughout.
  The proof is the same three lines and never touches the value of `d` beyond
  its parity;
* the branch structure modulo `2 ^ k`: `x + d` odd or even decides the branch,
  and `2 ^ L ∣ (x + d)` decides the run length, so the parity vectors, the
  heavy/light classification `3 ^ a` versus `2 ^ L`, the oddCount bookkeeping and
  the density theory all transfer verbatim under `x + 1 ↦ x + d`;
* the cycle inequality.  A cycle of length `L` with `a` odd steps satisfies the
  same `2 ^ L` against `3 ^ a` comparison, with the same average-contraction
  constant `(3/4)^(1/2)`;
* the finite-quotient obstruction.  The returning family of `NoFiniteRanking`
  becomes `x + d = 2 ^ (k+L) · 3 ^ l · s`, and returns to the class of `−d` at
  both moduli.

Nothing in `Collatz/Chains`, `Collatz/Structure` or the congruence half of
`Collatz/Strategy` distinguishes `d = 1` from any other odd `d`.

## And yet

**`3x + 5` has nontrivial cycles.**  Verified by machine and re-verified in Lean
by `decide` below, under this file's accelerated convention:

| cycle | length |
|---|---|
| `1 → 4 → 2 → 1` | 3 |
| `5 → 10 → 5` | 2 |
| `19 → 31 → 49 → 76 → 38 → 19` | 5 |
| `23 → 37 → 58 → 29 → 46 → 23` | 5 |

(there are more further out, e.g. one of length 27 through `187` and another
through `347`).  So for `d = 5` the number `5` never drops, never reaches `1`,
and is not `1`.  Equivalently, the accelerated `3x + 1` map on rationals with odd
denominator has nontrivial cycles: `d = 7`'s cycle `5 → 10 → 11 → 20 → 5`
becomes the `3x + 1` cycle `5/7 → 10/7 → 11/7 → 20/7 → 5/7`.

## The payoff

`no_uniform_d_argument` states it: the sentence

> for every odd `d`, the only `x` that never drops under `T_d` is `1`

is **false**, with witness `d = 5`, `x = 5`.  Its `d = 1` instance is exactly the
Collatz conjecture (`collatz_iff_genNeverDrops_one`).  Therefore:

**any chain of reasoning whose every step remains valid when `d` is left as a
free odd parameter cannot prove Collatz.**  Not "is unlikely to"; cannot — a
model exists in which every such step holds and the conclusion fails.

This is a mechanical soundness filter, cheap to apply.  Given a candidate
argument, ask: does any step use a numerical fact about `1` that is false for
`5`?  If not, discard the argument without spending Lean effort on it.

## Which repo results survive the filter, and which shapes it kills

**Survive**, because they consume something specific to `d = 1`:

* everything downstream of `Search.reachesOne_of_lt_307200` /
  `reachesOne_of_lt_102400` — the verified initial segment.  Its `d = 5` analogue
  is false at `x = 5` (`gen_verified_range_fails`), which is exactly why those
  results are not uniform.  `NeverDrops.exists_neverDrops`, `OneRunCycle`,
  `CycleLength520`, `Descent`'s numerical corollaries and everything using
  `102400 ≤ m` are in this class;
* `CycleProduct`'s explicit floor and any statement of the shape "a
  counterexample exceeds an explicit bound `B`", since a large positive lower
  bound has no analogue when the least never-dropper is `5`;
* `HeavyState.full_density_size` and `Frontier.targetB`, whose hypotheses are
  about the *size* of `x` (`2 ^ k ≤ x`), not about residues.  Size hypotheses are
  not uniform in `d` in any useful way: for `d = 5` the obstruction sits at
  `x = 5`, below every scale.

**Killed**, because they are uniform in `d`:

* any argument built from the run identity, congruences modulo `2 ^ k` and
  `3 ^ l`, parity vectors, oddCount inequalities and heavy/light density alone;
* any purely 2-adic or 3-adic argument — `ThreeAdic`, `ThreeResidue`,
  `ThreeObstruction`, `AccumulatorArith` are all `d`-uniform, which is precisely
  why each of them is stated as an obstruction rather than as progress;
* any "average contraction" argument, since `log₂ 3 < 2` holds for every `d`;
* any sieve or congruence-quotient argument, by the same reasoning as
  `TransitionInvariant` — the returning family exists for every odd `d`.

The filter is strictly stronger than `Mirror`'s.  `Mirror` rules out arguments
blind to the sign of the shift; this rules out arguments blind to its
*magnitude*, and the sign test is the special case that reads `d = 1` over `ℤ`.
It is also sharper as a diagnosis: for `d = 5` the verified initial segment does
essentially no work (the counterexample is `5`), while for `d = 1` it must do
unbounded work.  That is a precise statement of why "verify further" is not a
strategy — the verified range is the *only* non-uniform ingredient, and it is
being asked to carry the entire argument.

Finally, the honest caveat.  This file does not prove that the repo's theorems
are uniform in `d`; it proves the run identity is uniform, exhibits the `d = 5`
cycles, and states the pruning rule.  The uniformity of any *particular*
downstream theorem is a claim about its proof, to be checked by reading it — the
docstring above records that reading, not a formal result.
-/

namespace Collatz
namespace Denominator

open Reach NeverDrops

/-! ## The generalized map -/

/-- The accelerated `3x + d` map: `x / 2` for even `x`, `(3x + d) / 2` for odd
`x`.  For odd `d` the second branch is exact, since `3x + d` is then even. -/
def genStep (d n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else (3 * n + d) / 2

/-- Its orbit. -/
def genOrbit (d : Nat) : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => genOrbit d k (genStep d n)

@[simp] theorem genOrbit_zero (d n : Nat) : genOrbit d 0 n = n := rfl

@[simp] theorem genOrbit_succ (d k n : Nat) :
    genOrbit d (k + 1) n = genOrbit d k (genStep d n) := rfl

theorem genOrbit_succ_step (d k n : Nat) :
    genOrbit d (k + 1) n = genStep d (genOrbit d k n) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => rw [genOrbit_succ, ih, genOrbit_succ]

/-- **`d = 1` is the Collatz map.**  Definitionally, not up to anything. -/
theorem genStep_one (n : Nat) : genStep 1 n = acceleratedStep n := rfl

theorem genOrbit_one (k n : Nat) : genOrbit 1 k n = acceleratedOrbit k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => rw [genOrbit_succ, acceleratedOrbit_succ, genStep_one, ih]

/-! ## The shared run identity

This is the theorem that makes the whole development uniform in `d`.  Compare
`RunValue.oddRun_value`: same statement, same proof, `x + 1` replaced by
`x + d`. -/

/-- **The run identity, for every odd `d`.**  If `2 ^ L ∣ (x + d)` then the next
`L` steps of `T_d` are all odd and

`2 ^ L · (T_d^L(x) + d) = 3 ^ L · (x + d)`.

The proof uses only `d % 2 = 1`, and only to know that `3x + d` is even when `x`
is odd.  Nothing else about `d` enters — which is the point of the file. -/
theorem gen_run_value {d : Nat} (hd : d % 2 = 1) :
    ∀ L x : Nat, 2 ^ L ∣ (x + d) →
      2 ^ L * (genOrbit d L x + d) = 3 ^ L * (x + d) := by
  intro L
  induction L with
  | zero => intro x _; rw [genOrbit_zero, Nat.pow_zero, Nat.one_mul]
  | succ L ih =>
    intro x hdvd
    obtain ⟨c, hc⟩ := hdvd
    have hL1 : (2:Nat) ^ (L + 1) = 2 * 2 ^ L := by
      rw [Nat.pow_succ, Nat.mul_comm]
    have h3L1 : (3:Nat) ^ (L + 1) = 3 ^ L * 3 := Nat.pow_succ 3 L
    obtain ⟨m, hm⟩ : ∃ m : Nat, m = 2 ^ L * c := ⟨_, rfl⟩
    have hxd : x + d = 2 * m := by rw [hm, hc, hL1, Nat.mul_assoc]
    have hxodd : x % 2 = 1 := by omega
    have hstep : genStep d x = (3 * x + d) / 2 := by
      rw [genStep, if_neg (by omega)]
    have hy2 : 2 * (genStep d x + d) = 3 * (x + d) := by rw [hstep]; omega
    have hyd : genStep d x + d = 3 * m := by omega
    have hdvd' : 2 ^ L ∣ (genStep d x + d) :=
      ⟨3 * c, by rw [hyd, hm, ← Nat.mul_assoc, Nat.mul_comm 3 ((2:Nat) ^ L),
        Nat.mul_assoc]⟩
    have ihapp := ih (genStep d x) hdvd'
    calc 2 ^ (L + 1) * (genOrbit d (L + 1) x + d)
        = 2 * (2 ^ L * (genOrbit d L (genStep d x) + d)) := by
          rw [genOrbit_succ, hL1, Nat.mul_assoc]
      _ = 2 * (3 ^ L * (genStep d x + d)) := by rw [ihapp]
      _ = 3 ^ L * (2 * (genStep d x + d)) := by
          rw [← Nat.mul_assoc, Nat.mul_comm 2 ((3:Nat) ^ L), Nat.mul_assoc]
      _ = 3 ^ L * (3 * (x + d)) := by rw [hy2]
      _ = 3 ^ (L + 1) * (x + d) := by rw [h3L1, Nat.mul_assoc]

/-- The identity for `d = 1`, to make the comparison explicit: this is the same
statement as `RunValue.oddRun_value`, obtained by substituting `d := 1`. -/
theorem run_value_one (L x : Nat) (h : 2 ^ L ∣ (x + 1)) :
    2 ^ L * (acceleratedOrbit L x + 1) = 3 ^ L * (x + 1) := by
  have := gen_run_value (d := 1) (by decide) L x h
  rw [genOrbit_one] at this
  exact this

/-- The identity for `d = 5`, on the nose.  Same theorem, same proof, different
constant — and this one has cycles. -/
theorem run_value_five (L x : Nat) (h : 2 ^ L ∣ (x + 5)) :
    2 ^ L * (genOrbit 5 L x + 5) = 3 ^ L * (x + 5) :=
  gen_run_value (d := 5) (by decide) L x h

/-! ## Never dropping, uniformly in `d` -/

/-- The `d`-analogue of `NeverDrops`. -/
def GenNeverDrops (d x : Nat) : Prop := ∀ j : Nat, x ≤ genOrbit d j x

/-- At `d = 1` this is the repo's `NeverDrops`. -/
theorem genNeverDrops_one (x : Nat) : GenNeverDrops 1 x ↔ NeverDrops x := by
  constructor
  · intro h j; have := h j; rw [genOrbit_one] at this; exact this
  · intro h j; rw [genOrbit_one]; exact h j

/-- **The `d = 1` instance is exactly the conjecture.**  So a statement proved
uniformly in odd `d` would, at `d = 1`, be a proof of Collatz.

This is the one theorem in the file that is not choice-free: it is routed
through `NeverDrops.collatz_iff_neverDrops`, whose backward direction uses
`by_cases` on `ReachesOne`.  Everything else here, including
`no_uniform_d_argument` itself, depends only on `propext` and `Quot.sound`. -/
theorem collatz_iff_genNeverDrops_one :
    CollatzConjecture ↔ ∀ x : Nat, GenNeverDrops 1 x → x ≤ 1 := by
  rw [collatz_iff_neverDrops]
  constructor
  · intro h x hx; exact h x ((genNeverDrops_one x).mp hx)
  · intro h x hx; exact h x ((genNeverDrops_one x).mpr hx)

/-! ## The cycles of `3x + 5`

Four of them, checked by the kernel.  The convention is the accelerated one, so
`1 → 4 → 2 → 1` is a three-cycle and not a two-cycle. -/

/-- `1 → 4 → 2 → 1`: the analogue of the trivial cycle. -/
theorem five_cycle_one : genOrbit 5 3 1 = 1 := by decide

/-- `5 → 10 → 5`: the smallest **nontrivial** cycle of `3x + 5`. -/
theorem five_cycle_five : genOrbit 5 2 5 = 5 := by decide

/-- `19 → 31 → 49 → 76 → 38 → 19`. -/
theorem five_cycle_nineteen : genOrbit 5 5 19 = 19 := by decide

/-- `23 → 37 → 58 → 29 → 46 → 23`. -/
theorem five_cycle_twentythree : genOrbit 5 5 23 = 23 := by decide

/-- The three explicit steps of the `19`-cycle, so that the shape is on the
record and not hidden inside a `decide`. -/
theorem five_cycle_nineteen_steps :
    genStep 5 19 = 31 ∧ genStep 5 31 = 49 ∧ genStep 5 49 = 76 ∧
      genStep 5 76 = 38 ∧ genStep 5 38 = 19 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-! ## `5` never drops under `3x + 5` -/

/-- The orbit of `5` under `T_5` is confined to `{5, 10}`. -/
theorem orbit_five : ∀ k : Nat, genOrbit 5 k 5 = 5 ∨ genOrbit 5 k 5 = 10 := by
  intro k
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih =>
    rw [genOrbit_succ_step]
    rcases ih with h | h <;> rw [h] <;> decide

/-- **`5` never drops in the `3x + 5` world**, and it is not `1`. -/
theorem five_genNeverDrops : GenNeverDrops 5 5 := by
  intro j
  rcases orbit_five j with h | h <;> rw [h] <;> omega

/-- **`5` never reaches `1`** under `3x + 5`. -/
theorem five_never_reaches_one (k : Nat) : genOrbit 5 k 5 ≠ 1 := by
  rcases orbit_five k with h | h <;> rw [h] <;> omega

/-- The orbit of `19` is confined to its five-cycle. -/
theorem orbit_nineteen : ∀ k : Nat,
    genOrbit 5 k 19 = 19 ∨ genOrbit 5 k 19 = 31 ∨ genOrbit 5 k 19 = 49 ∨
      genOrbit 5 k 19 = 76 ∨ genOrbit 5 k 19 = 38 := by
  intro k
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih =>
    rw [genOrbit_succ_step]
    rcases ih with h | h | h | h | h <;> rw [h] <;> decide

/-- A second, independent never-dropper for `d = 5`, so that the obstruction is
visibly not an artefact of one small number. -/
theorem nineteen_genNeverDrops : GenNeverDrops 5 19 := by
  intro j
  rcases orbit_nineteen j with h | h | h | h | h <;> rw [h] <;> omega

/-! ## The pruning rule -/

/-- **The denominator test.**  The sentence "for every odd `d`, the only number
that never drops under `T_d` is `1`" is false.

Its `d = 1` instance is the Collatz conjecture
(`collatz_iff_genNeverDrops_one`).  So any argument that establishes that
sentence uniformly in `d` — that is, any argument each of whose steps remains
valid with `d` a free odd parameter — is unsound.  Since the run identity, the
branch structure, the parity/oddCount combinatorics and the heavy–light density
theory of this development are all `d`-uniform, an argument assembled from those
ingredients alone provably cannot reach the conclusion. -/
theorem no_uniform_d_argument :
    ¬ (∀ d : Nat, d % 2 = 1 → ∀ x : Nat, GenNeverDrops d x → x ≤ 1) := by
  intro h
  have := h 5 (by decide) 5 five_genNeverDrops
  omega

/-- The same, in the form an argument-checker actually uses: a `d`-uniform proof
of Collatz would prove a false statement.  The hypothesis is the shape of the
proof, the conclusion is that no such proof exists. -/
theorem collatz_needs_specific_d
    (huniform : ∀ d : Nat, d % 2 = 1 → ∀ x : Nat, GenNeverDrops d x → x ≤ 1) :
    False :=
  no_uniform_d_argument huniform

/-- **The verified initial segment is the ingredient that is not uniform.**  The
`d = 5` analogue of `Search.reachesOne_of_lt_307200` is false, and it fails at
`x = 5` — the very bottom of the range.  So for `d = 5` the verified segment
contributes nothing, while for `d = 1` it is the sole non-uniform input to every
result in this development.  That is the precise sense in which the conjecture
rests entirely on it, and the precise sense in which extending the verified range
is not a strategy: the range is already the only asymmetric ingredient, and more
of it is still only finitely much. -/
theorem gen_verified_range_fails :
    ¬ (∀ n : Nat, 0 < n → n < 307200 → ∃ k : Nat, genOrbit 5 k n = 1) := by
  intro h
  obtain ⟨k, hk⟩ := h 5 (by omega) (by omega)
  exact five_never_reaches_one k hk

/-- **The filter, stated as a model.**  There is an odd `d` and an `x > 1` that
never drops, satisfies the same run identity as `d = 1` at every window, and
never reaches `1`.  Every `d`-uniform hypothesis of this development holds of it;
the conclusion does not. -/
theorem denominator_model_of_the_theory :
    ∃ d x : Nat, d % 2 = 1 ∧ 1 < x ∧ GenNeverDrops d x ∧
      (∀ k : Nat, genOrbit d k x ≠ 1) ∧
      (∀ L y : Nat, 2 ^ L ∣ (y + d) →
        2 ^ L * (genOrbit d L y + d) = 3 ^ L * (y + d)) :=
  ⟨5, 5, by decide, by omega, five_genNeverDrops, five_never_reaches_one,
   gen_run_value (by decide)⟩

end Denominator
end Collatz
