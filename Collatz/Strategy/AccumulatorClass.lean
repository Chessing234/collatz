import Collatz.Strategy.AccumulatorArith

/-!
# The accumulator is a function of the residue class

`AffineExact` computes the additive correction `C_j(x)` from the orbit, and
`AccumulatorArith` computes its valuations.  Both treat `C_j` as attached to a
*number*.  It is not: it is attached to the *parity word*, and the parity word
of the first `j` steps is a function of `x mod 2 ^ j` alone
(`Congruence.accOrbit_pow_two_mul_add` is the dynamical half of this).

This file proves the arithmetic half:

* `oddCount_class` — `a(2 ^ j · m + r, j) = a(r, j)`;
* `affineC_class` — `C_j(2 ^ j · m + r) = C_j(r)`.

So the pair `(a, C)` — the entire affine map carrying the class forward — is
constant on residue classes modulo `2 ^ j`.  This is the bridge that lets
word-level facts (Terras: every word of length `j` is exactly one class mod
`2 ^ j`) be transported to accumulator arithmetic and back: a statement about
`C` for one representative is a statement about `C` for the whole class, and a
statement about all words of length `j` is a statement about all `2 ^ j`
possible accumulators, with no orbit quantifier anywhere.

The immediate payoff is `affineC_congr_of_mod`: two starting points congruent
modulo `2 ^ j` have *equal* accumulators, not merely congruent ones.  Combined
with `affine_exact` this pins the difference of their `j`-step orbits exactly:
`2 ^ j · (T^j(y) − T^j(x)) = 3 ^ a · (y − x)` (`orbit_diff_of_mod`), which is
`accOrbit_class_step` in a form that does not name a class representative.
-/

namespace Collatz
namespace AccumulatorClass

open Congruence AffineExact

/-! ## Class invariance -/

/-- **The odd-step count sees only the residue.**  Adding a multiple of `2 ^ j`
does not change which of the first `j` steps are odd. -/
theorem oddCount_class : ∀ (j m r : Nat), oddCount (2 ^ j * m + r) j = oddCount r j := by
  intro j
  induction j with
  | zero => intro m r; simp
  | succ j ih =>
    intro m r
    rcases Arith.mod_two_eq_zero_or_one r with hr | hr
    · have hsplit : 2 ^ (j + 1) * m = 2 * (2 ^ j * m) := by
        rw [Arith.two_pow_succ, Nat.mul_assoc]
      have heven : (2 ^ (j + 1) * m + r) % 2 = 0 := by rw [hsplit]; omega
      rw [oddCount_succ_of_even heven, oddCount_succ_of_even hr,
        accStep_pow_two_mul_add_even hr, ih]
    · have hsplit : 2 ^ (j + 1) * m = 2 * (2 ^ j * m) := by
        rw [Arith.two_pow_succ, Nat.mul_assoc]
      have hodd : (2 ^ (j + 1) * m + r) % 2 = 1 := by rw [hsplit]; omega
      rw [oddCount_succ_of_odd hodd, oddCount_succ_of_odd hr,
        accStep_pow_two_mul_add_odd hr, ih]

/-- **The accumulator sees only the residue.**  `C_j` is constant on residue
classes modulo `2 ^ j`: the additive correction is carried by the parity word,
and the parity word is carried by the class. -/
theorem affineC_class (j m r : Nat) : affineC j (2 ^ j * m + r) = affineC j r := by
  have hx := affine_exact (2 ^ j * m + r) j
  have hr := affine_exact r j
  have horb := accOrbit_pow_two_mul_add j m r
  have hcount := oddCount_class j m r
  rw [horb, hcount, Nat.mul_add, Nat.mul_add] at hx
  have hcomm : 2 ^ j * (3 ^ oddCount r j * m) = 3 ^ oddCount r j * (2 ^ j * m) := by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm (2 ^ j) (3 ^ oddCount r j)]
  rw [hcomm] at hx
  omega

/-- The class-invariance of the accumulator, stated for congruent starting
points rather than for a chosen representative. -/
theorem affineC_congr_of_mod {x y j : Nat} (h : x % 2 ^ j = y % 2 ^ j) :
    affineC j x = affineC j y := by
  have hx : affineC j x = affineC j (x % 2 ^ j) := by
    have hdec : 2 ^ j * (x / 2 ^ j) + x % 2 ^ j = x := by
      have := Nat.div_add_mod x (2 ^ j); omega
    have := affineC_class j (x / 2 ^ j) (x % 2 ^ j)
    rw [hdec] at this
    exact this
  have hy : affineC j y = affineC j (y % 2 ^ j) := by
    have hdec : 2 ^ j * (y / 2 ^ j) + y % 2 ^ j = y := by
      have := Nat.div_add_mod y (2 ^ j); omega
    have := affineC_class j (y / 2 ^ j) (y % 2 ^ j)
    rw [hdec] at this
    exact this
  rw [hx, hy, h]

/-- Likewise for the multiplier. -/
theorem oddCount_congr_of_mod {x y j : Nat} (h : x % 2 ^ j = y % 2 ^ j) :
    oddCount x j = oddCount y j := by
  have hx : oddCount x j = oddCount (x % 2 ^ j) j := by
    have hdec : 2 ^ j * (x / 2 ^ j) + x % 2 ^ j = x := by
      have := Nat.div_add_mod x (2 ^ j); omega
    have := oddCount_class j (x / 2 ^ j) (x % 2 ^ j)
    rw [hdec] at this
    exact this
  have hy : oddCount y j = oddCount (y % 2 ^ j) j := by
    have hdec : 2 ^ j * (y / 2 ^ j) + y % 2 ^ j = y := by
      have := Nat.div_add_mod y (2 ^ j); omega
    have := oddCount_class j (y / 2 ^ j) (y % 2 ^ j)
    rw [hdec] at this
    exact this
  rw [hx, hy, h]

/-! ## What the invariance pins down -/

/-- **Congruent starts, parallel orbits.**  If `x ≡ y (mod 2 ^ j)` then the two
`j`-step orbits differ by exactly the multiplier applied to the difference:
`2 ^ j · T^j(y) = 2 ^ j · T^j(x) + 3 ^ a · (y − x)`, stated additively to stay
inside `Nat`. -/
theorem orbit_diff_of_mod {x y j : Nat} (h : x % 2 ^ j = y % 2 ^ j) (hle : x ≤ y) :
    2 ^ j * acceleratedOrbit j y
      = 2 ^ j * acceleratedOrbit j x + 3 ^ oddCount x j * (y - x) := by
  have hx := affine_exact x j
  have hy := affine_exact y j
  rw [← oddCount_congr_of_mod h, ← affineC_congr_of_mod h] at hy
  have hmul : 3 ^ oddCount x j * (y - x) + 3 ^ oddCount x j * x = 3 ^ oddCount x j * y := by
    rw [← Nat.mul_add]
    congr 1
    omega
  omega

/-- The accumulator of a residue is the accumulator of every member of its
class, so there are at most `2 ^ j` accumulators at window length `j` — one per
parity word.  Stated as: `C_j` factors through `· % 2 ^ j`. -/
theorem affineC_eq_of_mod_eq (j : Nat) (x : Nat) :
    affineC j x = affineC j (x % 2 ^ j) :=
  affineC_congr_of_mod (by simp)

end AccumulatorClass
end Collatz
