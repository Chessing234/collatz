import Collatz.Strategy.RealizableBound
import Collatz.Strategy.HeavyResidue

/-!
# The self-strengthening loop, and the exact factor by which it loses

Every frontier bound in this development has the same shape: a verified range `c`
is fed in, a finite certificate is checked, and a cycle-length bound comes out.
Nothing converts the output back into a larger `c`.  This file asks whether it
*could*, closes the loop honestly, and measures the gain.

## The loop

Let a nontrivial cycle have minimum `m`, length `L`, odd-step count `a`, and gap
`G = 2 ^ L − 3 ^ a`.  `CycleAccumulator.cycle_gap_mul` gives `G · m = C` exactly,
where `C = affineC L m`.  So a floor `c ≤ m` and a ceiling on `C` bound `G`:

* **Step out** (`bootstrap_step`): `3 · G · c ≤ a · 3 ^ a`, from `G · c ≤ G · m = C`
  and `HeavyResidue.heavy_accumulator_bound_sharp` (`3 C ≤ a · 3 ^ a`).
* **Step back** (`affineC_ge_pow`, `bootstrap_floor`): `3 ^ a ≤ C + 2 ^ a`, so
  `G · m = C ≥ 3 ^ a − 2 ^ a`, hence `m ≥ (3 ^ a − 2 ^ a) / G`.

Composing, the new floor the loop delivers is

  `m ≥ 3 · c · (3 ^ a − 2 ^ a) / (a · 3 ^ a)`,

so the gain factor is exactly `3 (1 − (2/3) ^ a) / a`.

## The verdict

`bootstrap_loses`: the gain factor is `< 1` for every `a ≥ 4`.  The loop is a
genuine implication `P(c) ⇒ P(f(c))`, and `f(c) < c`.  The whole loss is the
spread of the accumulator over heavy windows of a fixed odd-count: the ceiling
`Bcap a` and the floor `3 ^ a − 2 ^ a` differ by a factor of order `a`
(`bcap_ge_pow`, `bcap_gt_pow`), and both ends are attained — the floor by the
one-run word (`RealizableBound.run_exact`: `affineC r x + 2 ^ r = 3 ^ r`), the
ceiling by the Beatty word.  At the current frontier `a = 2966` the factor is
`3 (1 − (2/3) ^ 2966) / 2966 ≈ 0.00101`: one turn of the loop divides the
verified range by about a thousand.

## Soundness filter

Every step above is free of `d`.  `cycle_gap_mul` becomes `G · m = |d| · C`,
`C(w, d) = d · C(w, 1)` (`DenominatorScalar`), and heaviness does not see `d` at
all.  The genuine `3x − 1` cycle `5 → 7 → 10 → 5` has `a = 2`, `m = 5`,
`C = 5`, `G = 3 ^ 2 − 2 ^ 3 = 1`, and satisfies `bootstrap_step` and
`bootstrap_floor` verbatim — including the extremal case `C = 3 ^ a − 2 ^ a = 5`.
That the loop refuses to produce a contradiction there is not an accident: a
`d`-free mechanism cannot, and this one does not.  The only `d = 1` input
anywhere in the loop is the base case `c = 768000`.
-/

namespace Collatz
namespace Bootstrap

open Congruence AffineExact AccCycle RealizableBound

/-! ## The floor on the accumulator

The dual of `AccumulatorCap.affineC_cap`.  No hypotheses at all: the `i`-th odd
step happens at time `t i ≥ i − 1`, so the positional sum is at least the
geometric one, `Σ 3 ^ (a−i) 2 ^ (i−1) = 3 ^ a − 2 ^ a`. -/

/-- **`3 ^ a ≤ C + 2 ^ a`** — the accumulator never falls below `3 ^ a − 2 ^ a`. -/
theorem affineC_ge_pow (x : Nat) :
    ∀ j : Nat, 3 ^ oddCount x j ≤ affineC j x + 2 ^ oddCount x j := by
  intro j
  induction j with
  | zero => simp [affineC, oddCount, parityVector]
  | succ j ih =>
    have hlast := Density.oddCount_succ_last x j
    have hle : oddCount x j ≤ j := oddCount_le_self x j
    have hpow : (2:Nat) ^ oddCount x j ≤ 2 ^ j := Arith.two_pow_le_two_pow hle
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j x) with ho | ho
    · have hc : affineC (j + 1) x = affineC j x := affineC_even ho
      have hcount : oddCount x (j + 1) = oddCount x j := by omega
      rw [hc, hcount]; exact ih
    · have hc : affineC (j + 1) x = 3 * affineC j x + 2 ^ j := affineC_odd ho
      have hcount : oddCount x (j + 1) = oddCount x j + 1 := by omega
      rw [hc, hcount, Arith.three_pow_succ, Arith.two_pow_succ]
      omega

/-! ## The step out: a floor on the cycle point caps the gap -/

/-- **Step out.**  If every point of the cycle is at least `c`, the gap obeys
`3 · G · c ≤ a · 3 ^ a`.  This is the only way a verified range constrains the
gap, and it is exactly the inequality the frontier certificates check. -/
theorem bootstrap_step {m L c : Nat} (hm : 0 < m) (hc : c ≤ m)
    (h : AccIsCycleOf m L)
    (hheavy : ∀ i : Nat, i ≤ L → 2 ^ i ≤ 3 ^ oddCount m i) :
    3 * ((2 ^ L - 3 ^ oddCount m L) * c) ≤ oddCount m L * 3 ^ oddCount m L := by
  have hgap : (2 ^ L - 3 ^ oddCount m L) * m = affineC L m :=
    CycleAccumulator.cycle_gap_mul hm h
  have hmono : (2 ^ L - 3 ^ oddCount m L) * c ≤ (2 ^ L - 3 ^ oddCount m L) * m :=
    Nat.mul_le_mul_left _ hc
  have hsharp : 3 * affineC L m ≤ oddCount m L * 3 ^ oddCount m L :=
    HeavyResidue.heavy_accumulator_bound_sharp m L hheavy
  omega

/-! ## The step back: a cap on the gap floors the cycle point -/

/-- **Step back.**  `G · m ≥ 3 ^ a − 2 ^ a`, so a cap on the gap is a floor on
the minimum.  Stated additively to stay inside `Nat`. -/
theorem bootstrap_floor {m L : Nat} (hm : 0 < m) (h : AccIsCycleOf m L) :
    3 ^ oddCount m L ≤ (2 ^ L - 3 ^ oddCount m L) * m + 2 ^ oddCount m L := by
  have hgap : (2 ^ L - 3 ^ oddCount m L) * m = affineC L m :=
    CycleAccumulator.cycle_gap_mul hm h
  have hge := affineC_ge_pow m L
  omega

/-- **The loop, closed.**  From a floor `c` on every cycle point, the loop
returns the floor `3 · c · (3 ^ a − 2 ^ a) ≤ a · 3 ^ a · m` on that same point.
This is a real implication `P(c) ⇒ P(f(c))`; `bootstrap_loses` measures `f`. -/
theorem bootstrap_loop {m L c : Nat} (hm : 0 < m) (hc : c ≤ m)
    (h : AccIsCycleOf m L)
    (hheavy : ∀ i : Nat, i ≤ L → 2 ^ i ≤ 3 ^ oddCount m i) :
    3 * (c * (3 ^ oddCount m L - 2 ^ oddCount m L))
      ≤ oddCount m L * 3 ^ oddCount m L * m := by
  have hstep := bootstrap_step hm hc h hheavy
  have hfloor := bootstrap_floor hm h
  -- `3 c (3^a − 2^a) ≤ 3 c (G m) = (3 G c) m ≤ (a 3^a) m`
  have hsub : 3 ^ oddCount m L - 2 ^ oddCount m L ≤ (2 ^ L - 3 ^ oddCount m L) * m := by
    omega
  have h1 : 3 * (c * (3 ^ oddCount m L - 2 ^ oddCount m L))
      ≤ 3 * (c * ((2 ^ L - 3 ^ oddCount m L) * m)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hsub)
  have hy : 3 * (c * ((2 ^ L - 3 ^ oddCount m L) * m))
      = 3 * ((2 ^ L - 3 ^ oddCount m L) * c) * m := by
    simp [Nat.mul_comm, Nat.mul_left_comm]
  have hx : 3 * ((2 ^ L - 3 ^ oddCount m L) * c) * m
      ≤ oddCount m L * 3 ^ oddCount m L * m := Nat.mul_le_mul_right _ hstep
  omega

/-! ## The verdict: the gain factor is `3 (1 − (2/3) ^ a) / a`

The loop returns `f(c) = 3 c (3 ^ a − 2 ^ a) / (a · 3 ^ a)`.  Comparing with `c`
is a comparison of `3 · (3 ^ a − 2 ^ a)` with `a · 3 ^ a`, and the latter wins
from `a = 4` on. -/

/-- **The bootstrap strictly loses for every `a ≥ 4`.**  The new floor the loop
returns is smaller than the floor it was given, by the factor `3/a` up to the
`(2/3) ^ a` correction. -/
theorem bootstrap_loses {a c : Nat} (hc : 0 < c) (ha : 4 ≤ a) :
    3 * (c * (3 ^ a - 2 ^ a)) < a * 3 ^ a * c := by
  have h2 : (0:Nat) < 2 ^ a := Arith.two_pow_pos a
  have hle : (2:Nat) ^ a ≤ 3 ^ a := Nat.pow_le_pow_left (by omega) a
  have h3 : (0:Nat) < 3 ^ a := by omega
  -- `3 (3^a − 2^a) < 3 · 3^a ≤ a · 3^a`
  have hA : 3 * (3 ^ a - 2 ^ a) < 3 * 3 ^ a := by omega
  have hB : 3 * 3 ^ a ≤ a * 3 ^ a := Nat.mul_le_mul_right _ (by omega)
  have hlt : 3 * (3 ^ a - 2 ^ a) < a * 3 ^ a := by omega
  have heq : 3 * (c * (3 ^ a - 2 ^ a)) = (3 * (3 ^ a - 2 ^ a)) * c := by
    simp [Nat.mul_comm, Nat.mul_left_comm]
  have hmul : (3 * (3 ^ a - 2 ^ a)) * c < (a * 3 ^ a) * c :=
    (Nat.mul_lt_mul_right hc).mpr hlt
  omega

/-! ## Where the loss comes from: the accumulator window spans a factor `a`

`Bcap` is the exact ceiling of the accumulator on a heavy window of odd-count
`a` (`RealizableBound.affineC_le_Bcap`), and `3 ^ a − 2 ^ a` is its exact floor,
attained by the one-run word.  The two differ by a factor of order `a`, and that
factor is the whole of the loss. -/

/-- **`a · 3 ^ a ≤ 6 · Bcap a`.**  The ceiling grows a factor `a/6` faster than
`3 ^ a`; each step of the `Bcap` recursion adds `2 ^ fexp a > 3 ^ a / 2`. -/
theorem bcap_ge_pow : ∀ a : Nat, a * 3 ^ a ≤ 6 * Bcap a := by
  intro a
  induction a with
  | zero => simp
  | succ a ih =>
    have hlt : (3:Nat) ^ a < 2 ^ (fexp a + 1) := lt_fexp a
    have he : (2:Nat) ^ (fexp a + 1) = 2 * 2 ^ fexp a := Arith.two_pow_succ _
    have hB : Bcap (a + 1) = 3 * Bcap a + 2 ^ fexp a := Bcap_succ a
    have h3 : (3:Nat) ^ (a + 1) = 3 * 3 ^ a := Arith.three_pow_succ a
    -- `6 Bcap(a+1) = 18 Bcap a + 6 · 2^(fexp a) ≥ 3 a 3^a + 3 · 3^a = (a+1) 3^(a+1)`
    have hkey : 3 * 3 ^ a ≤ 6 * 2 ^ fexp a := by omega
    have h18 : 3 * (a * 3 ^ a) ≤ 3 * (6 * Bcap a) := Nat.mul_le_mul_left _ ih
    have hexp : (a + 1) * (3 * 3 ^ a) = 3 * (a * 3 ^ a) + 3 * 3 ^ a := by
      rw [Nat.succ_mul]
      simp [Nat.mul_left_comm]
    rw [hB, h3]
    omega

/-- **`3 ^ a < Bcap a` for `a ≥ 7`** — the accumulator ceiling on a heavy window
overtakes its floor, so the loop's return value is below its input. -/
theorem bcap_gt_pow {a : Nat} (ha : 7 ≤ a) : 3 ^ a < Bcap a := by
  have h := bcap_ge_pow a
  have h3 : (0:Nat) < 3 ^ a := Nat.pow_pos (by omega)
  have h7 : 7 * 3 ^ a ≤ a * 3 ^ a := Nat.mul_le_mul_right _ ha
  omega

/-! ## The mod-`2 ^ m` bootstrap dies at `m = 3`, and exactly why

`HeavyResidue.affineC_mod_four` is a genuine bootstrap: heaviness at `i = 1, 2`
forces the first two steps odd, every later odd step contributes `2 ^ j` with
`j ≥ 2` — invisible mod four — and multiplies `C` and `3 ^ a` alike.  The natural
generalisation `C ≡ 3 ^ a (mod 2 ^ m)` would need heaviness to force the first
`m` steps odd.  It forces exactly two, because

  `2 ^ 1 > 3 ^ 0`,   `2 ^ 2 > 3 ^ 1`,   but   `2 ^ 3 = 8 ≤ 9 = 3 ^ 2`.

The third step is free, and the two branches split `C` mod eight: `C ≡ 3 ^ a` if
it is odd, `C ≡ 3 ^ a + 4` if it is even.  The witness below is the second
branch — the smallest one. -/

/-- `x = 11` has parity word `1101` over four steps and is heavy throughout. -/
theorem heavy_eleven :
    2 ^ 1 ≤ 3 ^ oddCount 11 1 ∧ 2 ^ 2 ≤ 3 ^ oddCount 11 2 ∧
      2 ^ 3 ≤ 3 ^ oddCount 11 3 ∧ 2 ^ 4 ≤ 3 ^ oddCount 11 4 := by decide

/-- **Mod four holds on it** — `affineC 4 11 = 23 ≡ 3 ≡ 27 = 3 ^ 3`. -/
theorem eleven_mod_four : affineC 4 11 % 4 = 3 ^ oddCount 11 4 % 4 := by decide

/-- **Mod eight fails on it**: `23 % 8 = 7` while `27 % 8 = 3`.  So no bootstrap
of the form `C ≡ 3 ^ a (mod 2 ^ m)` on heavy windows survives past `m = 2`. -/
theorem eleven_mod_eight : affineC 4 11 % 8 ≠ 3 ^ oddCount 11 4 % 8 := by decide

/-- The exact obstruction: heaviness cannot force a third odd step, because
`2 ^ 3 ≤ 3 ^ 2`.  (Contrast `2 ^ 2 > 3 ^ 1`, which is why mod four works.) -/
theorem third_step_free : (2:Nat) ^ 3 ≤ 3 ^ 2 ∧ (3:Nat) ^ 1 < 2 ^ 2 := by decide

end Bootstrap
end Collatz
