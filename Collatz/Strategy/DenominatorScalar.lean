import Collatz.Strategy.Denominator
import Collatz.Strategy.CycleAccumulator

/-!
# The constant enters only as a scalar

`Denominator` shows that the run identity, and with it the whole
congruence/density/word theory, is uniform in the constant `d` of `3x + d`, and
that `3x + 5` has genuine cycles.  That leaves a question it does not answer:
*where exactly* does `d` enter, if the theory cannot see it?

The answer is that it enters in exactly one place, as an overall scalar on the
accumulator.  Running the same recursion with `d` in place of `1`,

`U_{j+1} = 3 U_j + 2 ^ j` at an odd step, `U_j` at an even one,

the correction for the `3x + d` map is `d · U_j` (`genC_eq_scalar`), with `U`
the *same* function of the word for every `d`.  So the exact affine law reads

`2 ^ j · T_d^j(x) = 3 ^ a · x + d · U_j`,

and for a cycle, `(2 ^ L − 3 ^ a) · x = d · U_L`.

The consequence is the sharp form of the obstruction.  At the level of the
parity word, the problem for `3x + d` differs from the problem for `3x + 1` only
through `gcd(d, 2 ^ L − 3 ^ a)`: the word contributes `U`, which knows nothing
about `d`, and `d` contributes nothing but a factor which the gap may or may not
absorb.  `3x + 5` has its cycle at `(L, a) = (5, 3)` precisely because the gap
there is `5`, and `5` divides `d`.

So there are exactly two levers on the cycle side that are not `d`-uniform:

* `gcd(d, gap)` — arithmetic, and for `d = 1` it is trivially `1`, which is why
  `d = 1` is the hardest case rather than an easier one;
* positivity, which is archimedean and is where the verified range lives.

Any proposed mechanism that touches neither is refuted before it is written
down, by `Denominator.no_uniform_d_argument`.
-/

namespace Collatz
namespace DenominatorScalar

open Reach Denominator

/-! ## The unit accumulator -/

/-- The accumulator of the word, with the constant divided out: the same
recursion `affineC` satisfies, run along the `3x + d` orbit. -/
def genU (d : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | j + 1, x => if genOrbit d j x % 2 = 1 then 3 * genU d j x + 2 ^ j else genU d j x

@[simp] theorem genU_zero (d x : Nat) : genU d 0 x = 0 := rfl

theorem genU_odd {d j x : Nat} (h : genOrbit d j x % 2 = 1) :
    genU d (j + 1) x = 3 * genU d j x + 2 ^ j := by
  rw [genU, if_pos h]

theorem genU_even {d j x : Nat} (h : genOrbit d j x % 2 = 0) :
    genU d (j + 1) x = genU d j x := by
  rw [genU, if_neg (by omega)]

/-- At `d = 1` the unit accumulator is the development's `affineC`. -/
theorem genU_one (j x : Nat) : genU 1 j x = AffineExact.affineC j x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have horb : genOrbit 1 j x = acceleratedOrbit j x := genOrbit_one j x
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j x) with he | ho
    · rw [genU_even (by rw [horb]; exact he), AffineExact.affineC_even he, ih]
    · rw [genU_odd (by rw [horb]; exact ho), AffineExact.affineC_odd ho, ih]

/-! ## The constant is a scalar -/

/-- The odd-step count along the `3x + d` orbit. -/
def genOddCount (d : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | j + 1, x => genOddCount d j x + (if genOrbit d j x % 2 = 1 then 1 else 0)

@[simp] theorem genOddCount_zero (d x : Nat) : genOddCount d 0 x = 0 := rfl

/-- **The exact affine law for `3x + d`.**  The word supplies `3 ^ a` and `U`;
the constant supplies nothing but a factor of `d`. -/
theorem gen_affine_exact {d : Nat} (hd : d % 2 = 1) (x : Nat) : ∀ j : Nat,
    2 ^ j * genOrbit d j x = 3 ^ genOddCount d j x * x + d * genU d j x := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have hstep : genOrbit d (j + 1) x = genStep d (genOrbit d j x) :=
      genOrbit_succ_step d j x
    rcases Arith.mod_two_eq_zero_or_one (genOrbit d j x) with he | ho
    · have hcount : genOddCount d (j + 1) x = genOddCount d j x := by
        rw [genOddCount, if_neg (by omega), Nat.add_zero]
      have hval : genStep d (genOrbit d j x) = genOrbit d j x / 2 := by
        rw [genStep, if_pos he]
      have hhalf : 2 * (genOrbit d j x / 2) = genOrbit d j x := by omega
      rw [hcount, genU_even he, hstep, hval, Arith.two_pow_succ]
      have hexp : 2 * 2 ^ j * (genOrbit d j x / 2)
          = 2 ^ j * (2 * (genOrbit d j x / 2)) := by
        rw [Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm 2 (2 ^ j), Nat.mul_assoc]
      rw [hexp, hhalf]
      exact ih
    · have hcount : genOddCount d (j + 1) x = genOddCount d j x + 1 := by
        rw [genOddCount, if_pos ho]
      have hval : genStep d (genOrbit d j x) = (3 * genOrbit d j x + d) / 2 := by
        rw [genStep, if_neg (by omega)]
      have hdouble : 2 * ((3 * genOrbit d j x + d) / 2) = 3 * genOrbit d j x + d := by
        omega
      rw [hcount, genU_odd ho, hstep, hval, Arith.two_pow_succ, Arith.three_pow_succ]
      have hexp : 2 * 2 ^ j * ((3 * genOrbit d j x + d) / 2)
          = 2 ^ j * (2 * ((3 * genOrbit d j x + d) / 2)) := by
        rw [Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm 2 (2 ^ j), Nat.mul_assoc]
      rw [hexp, hdouble, Nat.mul_add]
      have hleft : 2 ^ j * (3 * genOrbit d j x) = 3 * (2 ^ j * genOrbit d j x) := by
        rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm (2 ^ j) 3]
      have hright : d * (3 * genU d j x + 2 ^ j) = 3 * (d * genU d j x) + 2 ^ j * d := by
        rw [Nat.mul_add, ← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm d 3,
          Nat.mul_comm d (2 ^ j)]
      have hmul : 3 * 3 ^ genOddCount d j x * x = 3 * (3 ^ genOddCount d j x * x) :=
        Nat.mul_assoc _ _ _
      rw [hleft, hright, hmul, ih]
      omega

/-! ## What the constant can and cannot do -/

/-- **The cycle equation for `3x + d`.**  The gap must divide `d` times the
word's own accumulator — and the word's accumulator does not depend on `d`. -/
theorem gen_cycle_gap {d : Nat} (hd : d % 2 = 1) {x L : Nat}
    (hcyc : genOrbit d L x = x) (hlt : 3 ^ genOddCount d L x ≤ 2 ^ L) :
    (2 ^ L - 3 ^ genOddCount d L x) * x = d * genU d L x := by
  have hex := gen_affine_exact hd x L
  rw [hcyc] at hex
  have hsub : (2 ^ L - 3 ^ genOddCount d L x) * x = 2 ^ L * x - 3 ^ genOddCount d L x * x :=
    Nat.sub_mul _ _ _
  have hmono : 3 ^ genOddCount d L x * x ≤ 2 ^ L * x := Nat.mul_le_mul_right x hlt
  omega

/-- At `d = 1` the scalar is invisible and the equation is the development's
own: `(2 ^ L − 3 ^ a) · x = affineC L x`. -/
theorem gen_cycle_gap_one {x L : Nat} (hx : 0 < x) (hcyc : AccCycle.AccIsCycleOf x L) :
    (2 ^ L - 3 ^ oddCount x L) * x = AffineExact.affineC L x :=
  CycleAccumulator.cycle_gap_mul hx hcyc

end DenominatorScalar
end Collatz
