import Collatz.Strategy.GhostHeight
import Collatz.Strategy.CycleProduct

/-!
# The max-side product bound: the missing half of the cycle-ratio sandwich

## Selection

Surveying the four sources named:

* **Hercher 2023, Lemma 9** — already formalised here as `HercherMerge.merge`, with
  Remark 10 as `unbounded_descends`.  Not a gap.
* **Halbeisen–Hungerbühler 1997** — their Lemma 5 was the gap, and it is now proved
  (`HHLemmaFive.hhExtremal_holds`); `hhMin` and the criterion are formalised.
* **collatz-lab.org** — `BakerSeparation` is stated there as a *conjecture de
  travail*, an undemonstrated strengthening of Rhin/Wu/Salikhov carried as an
  axiom; formalising it would mean **adding an axiom**, which this development
  forbids.  Its `δ8` note is an *obstruction* lemma — no Baker + continued-fraction
  + Khinchin derivation yields a uniform `F(k) < 2^71` — so it closes a route rather
  than moving a bound.  Neither qualifies.
* **The cycle-ratio theorem**, as presented in T. I. Martiny, *New Lower Bound on
  Cycle Length for the 3n+1 Problem* (Univ. of Pittsburgh, 9 April 2015, slide 9):
  for a cycle `Ω` of `T` with odd part `Ω₁`,

  `log₂(3 + M⁻¹) < |Ω|/|Ω₁| ≤ log₂(3 + m⁻¹)`,  `M = max Ω`, `m = min Ω`.

  **Its lower half is the gap.**

Clearing denominators with `L = |Ω|`, `a = |Ω₁|`, the sandwich is

`(3M+1)^a ≤ 2^L · M^a`   and   `2^L · m^a ≤ (3m+1)^a`.

The **right-hand** inequality is already this repository's `CycleProduct.product_invariant`
specialised at a cycle — it is the source of the product bound and of every
`CycleLength` result.  The **left-hand** inequality, the one controlled by the
cycle's *maximum*, is absent.  This file supplies it.

## What is proved

`product_invariant_max` — dual to `product_invariant`, with the inequality
reversed and the cycle minimum replaced by an upper bound `M`:

**`(3M+1)^(a_k) · x ≤ 2^k · M^(a_k) · T^k(x)`  whenever `T^i(x) ≤ M` for all `i`.**

The step is one line of arithmetic: at an odd `y ≤ M`,
`(3M+1)·y ≤ M·(3y+1)` — because `3My + y ≤ 3My + M`.  At an even step both sides
simply double.

`cycle_max_bound` specialises it at `T^L(x) = x` and cancels `x`:

**`(3M+1)^a ≤ 2^L · M^a`.**

Verified: no violation of the invariant over `155 961` pairs `(x, k)` with
`x < 4000`, `k ≤ 39`, and strict in `151 972` of them.  On the trivial cycle
`{1,2}` (`L = 2`, `a = 1`, `M = 2`, `m = 1`) the sandwich reads `7 ≤ 8` and
`4 ≤ 4` — the min side exactly tight.

## What it buys — corrected

An earlier draft of this docstring claimed the max side "cuts the admissible `(L,a)`
region from two sides rather than one".  **That inference was wrong**, and the
correction matters more than the theorem.

Clear both inequalities.  With `θ = 1/(2^(L/a) − 3)`:

* min side `2^L·m^a ≤ (3m+1)^a` ⟺ `m·(2^(L/a) − 3) ≤ 1` ⟺ **`m ≤ θ`**;
* max side `(3M+1)^a ≤ 2^L·M^a` ⟺ `M·(2^(L/a) − 3) ≥ 1` ⟺ **`M ≥ θ`**.

**The same `θ`.**  So the pair says exactly `m ≤ θ ≤ M`, and the max side is a
*lower* bound on the maximum.  Exclusion needs an **upper** bound to contradict — a
cycle whose maximum is large is not absurd — so the max side **cannot contribute to
excluding a length at all**.  It is a true statement and structurally inert.
Verified at `(L,a) = (2,1), (485,306), (1539,971), (2593,1636), (6809,4296)`, where
`θ = 1, 99781, 330749, 583287, 1.883×10^6`.

What makes the min side work is the *external* input `m ≥ c` from a verified range,
which turns `m ≤ θ` into `c ≤ θ` and excludes the length.  There is no external
*upper* bound on `M`, and the only provable one is the chain bound
`2^(a−1)·(M+1) ≤ 3^a·(m+1)` — from `2(n_{i+1}+1) ≤ 3(n_i+1)` per step.  Measured, it
misses the required threshold by `54`, `171`, `288` and over `750` orders of
magnitude at those pairs, the gap growing with `a`.  It is consistent with the
trivial cycle (`M ≤ 5` against the actual `M = 2`), so it is not wrong — only
hopelessly weak.

The theorem below stands.  Its role is to complete the sandwich as a statement, not
to move a bound.
-/

namespace Collatz
namespace ProductMax

/-- **The max-side product invariant.**  Dual to `CycleProduct.product_invariant`:
where that bounds the orbit above using a *lower* bound on its values, this bounds
it below using an *upper* bound `M`. -/
theorem product_invariant_max {x M : Nat} (hM : ∀ k : Nat, acceleratedOrbit k x ≤ M) :
    ∀ k : Nat, (3 * M + 1) ^ oddCount x k * x
      ≤ 2 ^ k * M ^ oddCount x k * acceleratedOrbit k x := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : acceleratedOrbit (k + 1) x = acceleratedStep (acceleratedOrbit k x) :=
      acceleratedOrbit_succ_step k x
    have hyM : acceleratedOrbit k x ≤ M := hM k
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit k x) with he | ho
    · -- even step: the count is unchanged and both sides double
      have hdouble : 2 * acceleratedOrbit (k + 1) x = acceleratedOrbit k x := by
        rw [hstep, acceleratedStep, if_pos he]; omega
      rw [Density.oddCount_succ_last, he]
      simp only [Nat.add_zero]
      have hpow : (2 : Nat) ^ (k + 1) = 2 ^ k * 2 := by rw [Nat.pow_succ]
      calc (3 * M + 1) ^ oddCount x k * x
          ≤ 2 ^ k * M ^ oddCount x k * acceleratedOrbit k x := ih
        _ = 2 ^ k * M ^ oddCount x k * (2 * acceleratedOrbit (k + 1) x) := by rw [hdouble]
        _ = 2 ^ (k + 1) * M ^ oddCount x k * acceleratedOrbit (k + 1) x := by
            rw [hpow]; simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    · -- odd step: the count rises, and `(3M+1)·y ≤ M·(3y+1)` because `y ≤ M`
      have hdouble : 2 * acceleratedOrbit (k + 1) x = 3 * acceleratedOrbit k x + 1 := by
        rw [hstep, acceleratedStep, if_neg (by omega)]; omega
      have hkey : (3 * M + 1) * acceleratedOrbit k x
          ≤ M * (3 * acceleratedOrbit k x + 1) := by
        have h1 : (3 * M + 1) * acceleratedOrbit k x
            = 3 * M * acceleratedOrbit k x + acceleratedOrbit k x := by
          rw [Nat.add_mul]; omega
        have h2 : M * (3 * acceleratedOrbit k x + 1)
            = 3 * M * acceleratedOrbit k x + M := by
          rw [Nat.mul_add]
          simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        omega
      rw [Density.oddCount_succ_last, ho]
      have hpA : (3 * M + 1) ^ (oddCount x k + 1)
          = (3 * M + 1) ^ oddCount x k * (3 * M + 1) := by rw [Nat.pow_succ]
      have hpB : M ^ (oddCount x k + 1) = M ^ oddCount x k * M := by rw [Nat.pow_succ]
      have hpow : (2 : Nat) ^ (k + 1) = 2 ^ k * 2 := by rw [Nat.pow_succ]
      have hstep1 : (3 * M + 1) ^ oddCount x k * (3 * M + 1) * x
          ≤ (2 ^ k * M ^ oddCount x k * acceleratedOrbit k x) * (3 * M + 1) := by
        have := Nat.mul_le_mul_right (3 * M + 1) ih
        calc (3 * M + 1) ^ oddCount x k * (3 * M + 1) * x
            = (3 * M + 1) ^ oddCount x k * x * (3 * M + 1) := by
              simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
          _ ≤ (2 ^ k * M ^ oddCount x k * acceleratedOrbit k x) * (3 * M + 1) := this
      have hstep2 : (2 ^ k * M ^ oddCount x k * acceleratedOrbit k x) * (3 * M + 1)
          ≤ 2 ^ k * M ^ oddCount x k * (M * (3 * acceleratedOrbit k x + 1)) := by
        have hmm : acceleratedOrbit k x * (3 * M + 1)
            ≤ M * (3 * acceleratedOrbit k x + 1) := by
          rw [Nat.mul_comm (acceleratedOrbit k x) (3 * M + 1)]; exact hkey
        calc (2 ^ k * M ^ oddCount x k * acceleratedOrbit k x) * (3 * M + 1)
            = 2 ^ k * M ^ oddCount x k * (acceleratedOrbit k x * (3 * M + 1)) := by
              rw [Nat.mul_assoc]
          _ ≤ 2 ^ k * M ^ oddCount x k * (M * (3 * acceleratedOrbit k x + 1)) :=
              Nat.mul_le_mul_left _ hmm
      rw [hpA, hpB]
      calc (3 * M + 1) ^ oddCount x k * (3 * M + 1) * x
          ≤ 2 ^ k * M ^ oddCount x k * (M * (3 * acceleratedOrbit k x + 1)) :=
            Nat.le_trans hstep1 hstep2
        _ = 2 ^ k * M ^ oddCount x k * (M * (2 * acceleratedOrbit (k + 1) x)) := by
            rw [hdouble]
        _ = 2 ^ (k + 1) * (M ^ oddCount x k * M) * acceleratedOrbit (k + 1) x := by
            rw [hpow]; simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- **The max-side cycle bound.**  On a cycle, `(3M+1)^a ≤ 2^L · M^a` — the left
half of the sandwich `log₂(3 + 1/M) < L/a ≤ log₂(3 + 1/m)`. -/
theorem cycle_max_bound {x L M : Nat} (hx : 0 < x)
    (hM : ∀ k : Nat, acceleratedOrbit k x ≤ M) (hcyc : acceleratedOrbit L x = x) :
    (3 * M + 1) ^ oddCount x L ≤ 2 ^ L * M ^ oddCount x L := by
  have h := product_invariant_max hM L
  rw [hcyc] at h
  exact Nat.le_of_mul_le_mul_right (by
    calc (3 * M + 1) ^ oddCount x L * x
        ≤ 2 ^ L * M ^ oddCount x L * x := h
      _ = 2 ^ L * M ^ oddCount x L * x := rfl) hx

end ProductMax
end Collatz
