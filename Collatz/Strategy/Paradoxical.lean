import Collatz.Basic
import Collatz.Accelerated
import Collatz.Core.Arith
import Collatz.Structure.Density
import Collatz.Structure.AccCycle
import Collatz.Strategy.AffineExact

/-!
# Paradoxical pairs (Rozier–Terracol)

O. Rozier and C. Terracol, *Paradoxical behavior in Collatz sequences*,
Discrete Mathematics **349** (2026); arXiv:2502.00948.

Throughout, `T` is the Terras map

  `T(n) = n / 2` for even `n`,  `T(n) = (3n+1) / 2` for odd `n`,

which in this repository is `Collatz.acceleratedStep`, iterated by
`Collatz.acceleratedOrbit`.  Nothing on the odd-step ("accelerated") clock of
`Collatz.Strategy.CoefficientStopping` is used here: Rozier–Terracol count
*total* `T`-steps, and so does every statement below.

**Definition 1.1 of the paper.**  For positive `j` and `n > 2` the sequence
`n, T(n), …, T^j(n)` is *paradoxical* when

  (i)  `C_j(n) = 3^q / 2^j < 1`, where `q` is the number of odd terms among
       `n, T(n), …, T^(j-1)(n)`;  and
  (ii) `T^j(n) ≥ n`.

Condition (i) is `3^q < 2^j` over `Nat`, and `q` is `Collatz.oddCount n j`.
The paper's remark that sequences merely repeating the trivial cycle `(1,2)`
are excluded is carried by the constraint `n > 2` alone.

## What is proved here and what is cited

Proved (elementary, off the exact affine identity `AffineExact.affine_exact`):

* `orbit_ge_of_two_pow_le` — `E_j(n) ≥ 0` in integer form: `2^j ≤ 3^q` forces
  `T^j(n) ≥ n`.  Hence paradoxicality is exactly "no descent although the
  coefficient already dropped below 1".
* `paradoxical_of_cycle` — a cycle through `n > 2` of period `j ≥ 1` is
  paradoxical, and (`paradoxical_of_leastTerm_cycle`) in particular the least
  term of a nontrivial cycle is, at `j = ` the period.
* `coeffStoppingTime_le_stoppingTime` — `τ(n) ≤ t(n)`, the easy half of Terras'
  Conjecture 2.9.
* `paradoxical_of_cst_failure` — a failure of CST at `n` yields a paradoxical
  pair, **at `j = τ(n)`, not at `j = t(n)`**; and
  `not_paradoxical_at_stoppingTime` — `(n, t(n))` is *never* paradoxical, for
  any `n`.  See the section "Which clock reading is the witness" below.
* `trace_eq` — a fused checker agreeing with `acceleratedOrbit`/`oddCount`,
  used to certify the published examples by kernel evaluation.

Cited, never proved (Section 5 and Theorem 1.3 of the paper): the census of 593
paradoxical sequences with first term `≤ 4614`, their absence in
`(4614, 2.8·10^19]`, and the implication "no others ⇒ Collatz".  These appear
below only as `Prop`-valued definitions, gathered in `RozierTerracolThm13`.

## Roadmap

| section | content | headline |
|---|---|---|
| The definition | Definition 1.1 verbatim | `Paradoxical` |
| The remainder is nonnegative | `E_j ≥ 0` in integer form | `orbit_ge_of_two_pow_le` |
| Cycles are paradoxical | a cycle above `2` is paradoxical at its period | `paradoxical_of_cycle` |
| Stopping times; which clock reading is the witness | `τ ≤ t`; the witness sits at `τ`, never at `t` | `paradoxical_of_cst_failure`, `not_paradoxical_at_stoppingTime` |
| Formulations C1–C3 | the paper's three equivalent forms, closed pointwise | `length_gt_stoppingTime_of_cst`, `cst_of_exists_earlier_drop` |
| Lemma A.1 | no paradoxical sequence has a unique local maximum (acyclic case) | `not_paradoxical_unimodal` |
| A standalone checker | one-pass `trace`, proved to compute the definition | `trace_eq`, `paradoxicalB_iff` |
| The published examples | Section 1 and Appendix C, checked | `paradoxical_seven`, `oddCounts_of_table_one` |
| A small exhaustive census | completeness on `n ≤ 200` | `census_two_hundred` |
| Section 3 | the elementary case of Theorem 3.2 | `paradoxical_of_no_descent` |
| Theorem 1.3 | cited only | `RozierTerracolThm13` |

**Cited, never proved:** `RozierTerracolThm13`, `RT_Cor54`, `RT_Lemma31`,
`RT_Thm32`.  Everything else in the file is proved.  Lemma A.1 is proved only in
the acyclic case; the cyclic case is the non-existence of circuits, which the
paper takes from transcendence theory.

Lean 4.33.0-rc1.  No Mathlib, no `sorry`, no `axiom`, no `native_decide`.
-/

namespace Collatz
namespace Paradoxical

open Arith AffineExact

set_option maxRecDepth 100000

/-! ## The definition -/

/-- The coefficient condition (i): `C_j(n) < 1`, cleared of denominators. -/
def CoeffBelowOne (n j : Nat) : Prop := 3 ^ oddCount n j < 2 ^ j

theorem coeffBelowOne_iff {n j : Nat} :
    CoeffBelowOne n j ↔ 3 ^ oddCount n j < 2 ^ j := Iff.rfl

/-- **Definition 1.1 (Rozier–Terracol).**  The pair `(n, j)` is paradoxical
when `n > 2`, `j ≥ 1`, the coefficient `3^q / 2^j` is below `1`, and the `j`-th
iterate still fails to drop below `n`. -/
def Paradoxical (n j : Nat) : Prop :=
  2 < n ∧ 1 ≤ j ∧ 3 ^ oddCount n j < 2 ^ j ∧ n ≤ acceleratedOrbit j n

theorem paradoxical_def {n j : Nat} :
    Paradoxical n j ↔
      2 < n ∧ 1 ≤ j ∧ 3 ^ oddCount n j < 2 ^ j ∧ n ≤ acceleratedOrbit j n := Iff.rfl

/-- A paradoxical pair is cyclic (`T^j(n) = n`) or acyclic (`T^j(n) > n`); the
paper's two disjoint subsets. -/
theorem cyclic_or_acyclic {n j : Nat} (h : Paradoxical n j) :
    acceleratedOrbit j n = n ∨ n < acceleratedOrbit j n := by
  have := h.2.2.2
  omega

/-! ## The remainder is nonnegative

The paper writes `T^j(n) = C_j(n)·n + E_j(n)` with `E_j(n) ≥ 0`, and observes
that therefore `C_j(n) ≥ 1` already forces `T^j(n) ≥ n`.  Over `Nat` the exact
identity is `2^j · T^j(n) = 3^q · n + affineC j n`, and `E_j(n) ≥ 0` is the
statement that `affineC` is a natural number at all. -/

/-- **`E_j ≥ 0`, integer form.**  If the coefficient has not yet fallen below
`1`, the orbit cannot have descended. -/
theorem orbit_ge_of_two_pow_le {n j : Nat} (h : 2 ^ j ≤ 3 ^ oddCount n j) :
    n ≤ acceleratedOrbit j n := by
  have hexact := affine_exact n j
  have hpos : 0 < 2 ^ j := two_pow_pos j
  have hmul : 2 ^ j * n ≤ 2 ^ j * acceleratedOrbit j n := by
    have h1 : 2 ^ j * n ≤ 3 ^ oddCount n j * n := Nat.mul_le_mul_right n h
    omega
  exact Nat.le_of_mul_le_mul_left hmul hpos

/-- Contrapositive: any actual descent certifies that the coefficient has
already dropped below `1`.  This is the inequality `t(n) ≥ τ(n)`, pointwise. -/
theorem coeffBelowOne_of_descent {n j : Nat} (h : acceleratedOrbit j n < n) :
    CoeffBelowOne n j := by
  show 3 ^ oddCount n j < 2 ^ j
  rcases Nat.lt_or_ge (3 ^ oddCount n j) (2 ^ j) with hlt | hge
  · exact hlt
  · have := orbit_ge_of_two_pow_le (n := n) (j := j) hge
    omega

/-- Paradoxicality, restated: the pair `(n, j)` is paradoxical exactly when the
orbit fails to descend *and* that failure is not explained by the coefficient. -/
theorem paradoxical_iff_unexplained {n j : Nat} (hn : 2 < n) (hj : 1 ≤ j) :
    Paradoxical n j ↔ (n ≤ acceleratedOrbit j n ∧ ¬ (2 ^ j ≤ 3 ^ oddCount n j)) := by
  constructor
  · intro h
    exact ⟨h.2.2.2, by have := h.2.2.1; omega⟩
  · intro h
    exact ⟨hn, hj, by omega, h.1⟩

/-! ## Cycles are paradoxical

"Any Collatz sequence that starts and ends at the same integer (greater than 2)
and has at least one iteration of `T` is necessarily paradoxical."  The only
input is that `2^j` is even while `3^q` is odd. -/

private theorem three_pow_odd (q : Nat) : 3 ^ q % 2 = 1 := by
  induction q with
  | zero => rfl
  | succ q ih => rw [Nat.pow_succ]; omega

private theorem two_pow_even {j : Nat} (hj : 1 ≤ j) : 2 ^ j % 2 = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [Nat.pow_succ]
  omega

/-- No power of two with positive exponent is a power of three. -/
theorem three_pow_ne_two_pow {j q : Nat} (hj : 1 ≤ j) : 3 ^ q ≠ 2 ^ j := by
  intro h
  have h1 := three_pow_odd q
  have h2 := two_pow_even hj
  omega

/-- **A cycle through `n > 2` is paradoxical at its period.**  Condition (ii)
holds with equality; condition (i) is forced, because equality in the affine
identity with a vanishing remainder would make `2^j` a power of three. -/
theorem paradoxical_of_cycle {n j : Nat} (hn : 2 < n) (hj : 1 ≤ j)
    (hcyc : acceleratedOrbit j n = n) : Paradoxical n j := by
  refine ⟨hn, hj, ?_, by omega⟩
  have hexact := affine_exact n j
  rw [hcyc] at hexact
  -- `2 ^ j * n = 3 ^ q * n + affineC j n`
  rcases Nat.lt_or_ge (3 ^ oddCount n j) (2 ^ j) with hlt | hle
  · exact hlt
  · exfalso
    have hmul : 2 ^ j * n ≤ 3 ^ oddCount n j * n := Nat.mul_le_mul_right n hle
    have heq : 2 ^ j * n = 3 ^ oddCount n j * n := by omega
    have hnpos : 0 < n := by omega
    have hpow : 2 ^ j = 3 ^ oddCount n j := Nat.eq_of_mul_eq_mul_right hnpos heq
    exact three_pow_ne_two_pow (j := j) (q := oddCount n j) hj hpow.symm

/-- The repository's cycle predicate, transported. -/
theorem paradoxical_of_accIsCycleOf {n L : Nat} (hn : 2 < n)
    (h : AccCycle.AccIsCycleOf n L) : Paradoxical n L :=
  paradoxical_of_cycle hn h.1 h.2

/-- **The least term of a nontrivial cycle is paradoxical at `j = ` the period.**
`hmin` is the minimality hypothesis; it is not needed for the conclusion, and is
carried only to record that this is the statement about the least term.  What
excludes the trivial cycle `(1,2)` is `2 < n`. -/
theorem paradoxical_of_leastTerm_cycle {n L : Nat} (hn : 2 < n) (hL : 1 ≤ L)
    (hcyc : acceleratedOrbit L n = n)
    (_hmin : ∀ i : Nat, n ≤ acceleratedOrbit i n) : Paradoxical n L :=
  paradoxical_of_cycle hn hL hcyc

/-! ## Stopping time and coefficient stopping time

Definition 1.2 of the paper, on the Terras clock.  `Collatz.stoppingTime n t`
already says that `t` is the least positive index with `T^t(n) < n`, so it is
reused verbatim. -/

/-- `τ` is the coefficient stopping time of `n`: the least positive `j` with
`C_j(n) < 1`. -/
def IsCoeffStoppingTime (n τ : Nat) : Prop :=
  1 ≤ τ ∧ CoeffBelowOne n τ ∧ ∀ i : Nat, 1 ≤ i → i < τ → ¬ CoeffBelowOne n i

/-- **`τ(n) ≤ t(n)`**, the easy half of Terras' Conjecture 2.9 (the CST
conjecture), for the two times where both exist. -/
theorem coeffStoppingTime_le_stoppingTime {n t τ : Nat}
    (ht : stoppingTime n t) (hτ : IsCoeffStoppingTime n τ) : τ ≤ t := by
  rcases Nat.lt_or_ge t τ with hlt | hge
  · exact absurd (coeffBelowOne_of_descent ht.2.1) (hτ.2.2 t ht.1 hlt)
  · exact hge

/-! ### Which clock reading is the witness

A CST failure at `n` is `t(n) ≠ τ(n)`, hence `τ(n) < t(n)`.  The paradoxical
pair it produces is `(n, τ(n))`, at the **coefficient** stopping time.  The pair
`(n, t(n))` is never paradoxical, for any `n` whatsoever: at `j = t(n)` the
orbit has by definition already descended, so condition (ii) fails.  So a
witness read at `j = σ = t(n)` does not exist — not because of any mismatch
between the Terras clock and the accelerated clock, but because the stopping
time is precisely the first index at which condition (ii) is *false*.  The two
indices coincide exactly when CST holds at `n`, and then neither is a
paradoxical length. -/

/-- **`(n, t(n))` is never paradoxical.**  Condition (ii) fails at the stopping
time by definition of the stopping time. -/
theorem not_paradoxical_at_stoppingTime {n t : Nat} (ht : stoppingTime n t) :
    ¬ Paradoxical n t := by
  intro h
  have h1 := h.2.2.2
  have h2 := ht.2.1
  omega

/-- **A CST failure produces a paradoxical pair, at `j = τ(n)`.** -/
theorem paradoxical_of_cst_failure {n t τ : Nat} (hn : 2 < n)
    (ht : stoppingTime n t) (hτ : IsCoeffStoppingTime n τ) (hne : τ ≠ t) :
    Paradoxical n τ := by
  have hle := coeffStoppingTime_le_stoppingTime ht hτ
  have hlt : τ < t := by omega
  have hnodrop : ¬ (acceleratedOrbit τ n < n) := ht.2.2 τ hτ.1 hlt
  exact ⟨hn, hτ.1, hτ.2.1, by omega⟩

/-- The same conclusion without naming `τ`: whenever the coefficient has dropped
below `1` at some positive `j` and the orbit has not, `(n, j)` is paradoxical.
This is the form used in the cycle and divergence arguments. -/
theorem paradoxical_of_coeff_drop_without_descent {n j : Nat} (hn : 2 < n)
    (hj : 1 ≤ j) (hc : CoeffBelowOne n j) (hd : ¬ acceleratedOrbit j n < n) :
    Paradoxical n j :=
  ⟨hn, hj, hc, Nat.not_lt.mp hd⟩

/-- A paradoxical length is at least the coefficient stopping time: condition
(i) is exactly the condition defining `τ`, so `τ(n) ≤ j`.  Unconditional. -/
theorem coeffStoppingTime_le_of_paradoxical {n j τ : Nat}
    (h : Paradoxical n j) (hτ : IsCoeffStoppingTime n τ) : τ ≤ j := by
  rcases Nat.lt_or_ge j τ with hlt | hge
  · exact absurd h.2.2.1 (hτ.2.2 j h.2.1 hlt)
  · exact hge

/-- **Formulation C2, derived from C1.**  Granting the CST conjecture at `n`
(`t(n) = τ(n)`), every paradoxical length for `n` strictly exceeds the stopping
time.  The hypothesis is essential: unconditionally only `τ(n) ≤ j` and
`j ≠ t(n)` are available, and `t(n) < j` is one of the paper's three equivalent
forms of the conjecture, not a theorem. -/
theorem length_gt_stoppingTime_of_cst {n j t τ : Nat}
    (h : Paradoxical n j) (ht : stoppingTime n t) (hτ : IsCoeffStoppingTime n τ)
    (hcst : t = τ) : t < j := by
  have h1 : τ ≤ j := coeffStoppingTime_le_of_paradoxical h hτ
  have h2 : j ≠ t := by
    intro heq
    exact not_paradoxical_at_stoppingTime ht (heq ▸ h)
  omega

/-- **Formulation C3**, derived from C1.  "The first term of a paradoxical
sequence is never the smallest": granting the CST conjecture at `n`, every
paradoxical sequence from `n` has already dropped below `n` strictly earlier. -/
theorem exists_earlier_drop_of_cst {n j t τ : Nat}
    (h : Paradoxical n j) (ht : stoppingTime n t) (hτ : IsCoeffStoppingTime n τ)
    (hcst : t = τ) : ∃ i : Nat, i < j ∧ acceleratedOrbit i n < n :=
  ⟨t, length_gt_stoppingTime_of_cst h ht hτ hcst, ht.2.1⟩

/-- **C3 ⇒ C1**, at a single `n`.  If every paradoxical sequence starting at `n`
already dropped below `n` strictly earlier, the two stopping times agree.  With
`exists_earlier_drop_of_cst` this closes the loop `C1 ⇒ C2 ⇒ C3 ⇒ C1` of the
paper's Section 1, pointwise in `n`. -/
theorem cst_of_exists_earlier_drop {n t τ : Nat} (hn : 2 < n)
    (ht : stoppingTime n t) (hτ : IsCoeffStoppingTime n τ)
    (hC3 : ∀ j : Nat, Paradoxical n j → ∃ i : Nat, i < j ∧ acceleratedOrbit i n < n) :
    t = τ := by
  have hle := coeffStoppingTime_le_stoppingTime ht hτ
  rcases Nat.eq_or_lt_of_le hle with heq | hlt
  · exact heq.symm
  · exfalso
    have hpar := paradoxical_of_cst_failure hn ht hτ (by omega)
    obtain ⟨i, hij, hdrop⟩ := hC3 τ hpar
    rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · rw [hi0, acceleratedOrbit_zero] at hdrop
      omega
    · exact absurd hdrop (ht.2.2 i hi0 (by omega))

/-! ## Sequences with a unique local maximum (Rozier–Terracol, Lemma A.1)

A parity vector of the form `1^q 0^{j-q}` means the orbit rises `q` times and
then falls: a unique local maximum.  The paper rules these out; the cyclic case
`T^j(n) = n` needs transcendence theory (it is the non-existence of circuits),
but the acyclic case `T^j(n) > n` is elementary, and that is what is proved here.

Two identities do the work.  Along the rising prefix `T^i(n) + 1` scales by
exactly `3/2`; along the falling tail `T` just halves.  Together they give

  `2^j · T^j(n) + 2^q = 3^q · (n + 1)`,

and `T^j(n) > n` then forces `2^j < 3^q` — the opposite of condition (i). -/

/-- Along an all-odd prefix, `T^i(n) + 1` scales by `3/2` each step. -/
theorem terras_ones_identity {n : Nat} : ∀ q : Nat,
    (∀ i : Nat, i < q → acceleratedOrbit i n % 2 = 1) →
    2 ^ q * (acceleratedOrbit q n + 1) = 3 ^ q * (n + 1) := by
  intro q
  induction q with
  | zero => intro _; simp
  | succ q ih =>
    intro hodd
    have hIH := ih (fun i hi => hodd i (by omega))
    have hq : acceleratedOrbit q n % 2 = 1 := hodd q (by omega)
    have hstep : acceleratedOrbit (q + 1) n = (3 * acceleratedOrbit q n + 1) / 2 := by
      rw [acceleratedOrbit_succ_step, acceleratedStep, if_neg (by omega)]
    have hdouble : 2 * (acceleratedOrbit (q + 1) n + 1) = 3 * (acceleratedOrbit q n + 1) := by
      rw [hstep]; omega
    calc 2 ^ (q + 1) * (acceleratedOrbit (q + 1) n + 1)
        = 2 ^ q * (2 * (acceleratedOrbit (q + 1) n + 1)) := by
          rw [Arith.two_pow_succ, Nat.mul_assoc, Nat.mul_left_comm]
      _ = 2 ^ q * (3 * (acceleratedOrbit q n + 1)) := by rw [hdouble]
      _ = 3 * (2 ^ q * (acceleratedOrbit q n + 1)) := by rw [Nat.mul_left_comm]
      _ = 3 * (3 ^ q * (n + 1)) := by rw [hIH]
      _ = 3 ^ (q + 1) * (n + 1) := by
          rw [Nat.pow_succ, Nat.mul_comm (3 ^ q) 3, Nat.mul_assoc]

/-- Along an all-even stretch, `T` is exactly halving. -/
theorem terras_halving_identity {n q : Nat} : ∀ r : Nat,
    (∀ i : Nat, q ≤ i → i < q + r → acceleratedOrbit i n % 2 = 0) →
    2 ^ r * acceleratedOrbit (q + r) n = acceleratedOrbit q n := by
  intro r
  induction r with
  | zero => intro _; simp
  | succ r ih =>
    intro heven
    have hIH := ih (fun i h1 h2 => heven i h1 (by omega))
    have hqr : acceleratedOrbit (q + r) n % 2 = 0 := heven (q + r) (by omega) (by omega)
    have hstep : acceleratedOrbit (q + r + 1) n = acceleratedOrbit (q + r) n / 2 := by
      rw [acceleratedOrbit_succ_step, acceleratedStep, if_pos hqr]
    have hdouble : 2 * acceleratedOrbit (q + r + 1) n = acceleratedOrbit (q + r) n := by
      rw [hstep]; omega
    calc 2 ^ (r + 1) * acceleratedOrbit (q + (r + 1)) n
        = 2 ^ r * (2 * acceleratedOrbit (q + r + 1) n) := by
          rw [Arith.two_pow_succ, Nat.mul_assoc, Nat.mul_left_comm,
            show q + (r + 1) = q + r + 1 by omega]
      _ = 2 ^ r * acceleratedOrbit (q + r) n := by rw [hdouble]
      _ = acceleratedOrbit q n := hIH

/-- The tripling count of a unimodal parity vector is the length of its rise. -/
theorem oddCount_of_ones {n : Nat} : ∀ q : Nat,
    (∀ i : Nat, i < q → acceleratedOrbit i n % 2 = 1) → oddCount n q = q := by
  intro q
  induction q with
  | zero => intro _; simp [oddCount, parityVector]
  | succ q ih =>
    intro hodd
    have hIH := ih (fun i hi => hodd i (by omega))
    have hlast := Density.oddCount_succ_last n q
    rw [hodd q (by omega)] at hlast
    omega

theorem oddCount_const_of_evens {n q : Nat} : ∀ r : Nat,
    (∀ i : Nat, q ≤ i → i < q + r → acceleratedOrbit i n % 2 = 0) →
    oddCount n (q + r) = oddCount n q := by
  intro r
  induction r with
  | zero => intro _; simp
  | succ r ih =>
    intro heven
    have hIH := ih (fun i h1 h2 => heven i h1 (by omega))
    have hlast := Density.oddCount_succ_last n (q + r)
    rw [heven (q + r) (by omega) (by omega)] at hlast
    rw [show q + (r + 1) = q + r + 1 by omega]
    omega

/-- **Lemma A.1, acyclic case.**  No paradoxical sequence has a unique local
maximum.  Precisely: if the parity vector of `n` over `j` steps is `1^q 0^{j-q}`
with `q ≥ 1` and the sequence ends strictly above where it started, then the
coefficient condition fails — `2^j < 3^q`, so `C_j(n) > 1`.

The cyclic case `T^j(n) = n` is *not* covered; it is the non-existence of
circuits, which the paper obtains from transcendence theory and which is not
formalized here. -/
theorem no_paradoxical_unimodal {n j q : Nat} (hq : 1 ≤ q) (hqj : q ≤ j)
    (hodd : ∀ i : Nat, i < q → acceleratedOrbit i n % 2 = 1)
    (heven : ∀ i : Nat, q ≤ i → i < j → acceleratedOrbit i n % 2 = 0)
    (hgrow : n < acceleratedOrbit j n) : 2 ^ j < 3 ^ q := by
  have hrise := terras_ones_identity q hodd
  have hfall := terras_halving_identity (n := n) (q := q) (j - q)
    (fun i h1 h2 => heven i h1 (by omega))
  rw [show q + (j - q) = j by omega] at hfall
  -- `2^j · T^j(n) + 2^q = 3^q · (n+1)`
  have hkey : 2 ^ j * acceleratedOrbit j n + 2 ^ q = 3 ^ q * (n + 1) := by
    have hsplit : (2 : Nat) ^ j = 2 ^ q * 2 ^ (j - q) := by
      rw [← Nat.pow_add, show q + (j - q) = j by omega]
    rw [hsplit, Nat.mul_assoc, hfall]
    omega
  have hqpos : 0 < 2 ^ q := Arith.two_pow_pos q
  have hle : 2 ^ j * (n + 1) ≤ 2 ^ j * acceleratedOrbit j n :=
    Nat.mul_le_mul_left _ (by omega)
  have hlt : 2 ^ j * (n + 1) < 3 ^ q * (n + 1) := by omega
  exact Nat.lt_of_mul_lt_mul_right hlt

/-- A worked instance: `n = 7`, `j = 4`, `q = 3` has parity vector `1,1,1,0` and
`T^4(7) = 13 > 7`, and indeed `2^4 = 16 < 27 = 3^3`, so the coefficient is above
`1` and the pair is not paradoxical. -/
theorem unimodal_seven :
    (List.range 4).map (fun i => acceleratedOrbit i 7 % 2) = [1, 1, 1, 0] ∧
      acceleratedOrbit 4 7 = 13 ∧ (2 : Nat) ^ 4 < 3 ^ 3 := by decide

/-- Restated against `Paradoxical`: such a pair is never paradoxical. -/
theorem not_paradoxical_unimodal {n j q : Nat} (hq : 1 ≤ q) (hqj : q ≤ j)
    (hodd : ∀ i : Nat, i < q → acceleratedOrbit i n % 2 = 1)
    (heven : ∀ i : Nat, q ≤ i → i < j → acceleratedOrbit i n % 2 = 0)
    (hgrow : n < acceleratedOrbit j n) : ¬ Paradoxical n j := by
  intro hpar
  have hcount : oddCount n j = q := by
    have h1 := oddCount_const_of_evens (n := n) (q := q) (j - q)
      (fun i ha hb => heven i ha (by omega))
    rw [show q + (j - q) = j by omega] at h1
    rw [h1]
    exact oddCount_of_ones q hodd
  have h := no_paradoxical_unimodal hq hqj hodd heven hgrow
  have := hpar.2.2.1
  rw [hcount] at this
  omega

/-! ## A standalone checker

`oddCount` recomputes the orbit for every prefix, which is quadratic in `j` and
too slow for kernel evaluation.  `trace n j` carries the state and the odd count
together in one pass; `trace_eq` proves it computes exactly the pair
`(T^j(n), q_j(n))`, so certificates obtained by `decide` are certificates about
the definitions above. -/

/-- One pass over `j` Terras steps, carrying `(T^i(n), q_i(n))`. -/
def trace (n : Nat) : Nat → Nat × Nat
  | 0 => (n, 0)
  | j + 1 =>
      let p := trace n j
      if p.1 % 2 = 1 then ((3 * p.1 + 1) / 2, p.2 + 1) else (p.1 / 2, p.2)

/-- The checker computes the iterate and the odd count. -/
theorem trace_eq (n j : Nat) : trace n j = (acceleratedOrbit j n, oddCount n j) := by
  induction j with
  | zero => simp [trace, oddCount, parityVector]
  | succ j ih =>
    have hstep : acceleratedOrbit (j + 1) n = acceleratedStep (acceleratedOrbit j n) :=
      acceleratedOrbit_succ_step j n
    have hlast := Density.oddCount_succ_last n j
    rw [trace, ih]
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j n) with he | ho
    · rw [if_neg (by omega)]
      rw [hstep, acceleratedStep, if_pos he, hlast, he]
      simp
    · rw [if_pos ho]
      rw [hstep, acceleratedStep, if_neg (by omega), hlast, ho]

/-- Decidable form of `Paradoxical`, computed in one pass. -/
def paradoxicalB (n j : Nat) : Bool :=
  2 < n && 1 ≤ j && 3 ^ (trace n j).2 < 2 ^ j && n ≤ (trace n j).1

/-- The checker decides the definition. -/
theorem paradoxicalB_iff {n j : Nat} : paradoxicalB n j = true ↔ Paradoxical n j := by
  simp [paradoxicalB, Paradoxical, trace_eq, and_assoc]

theorem paradoxical_of_check {n j : Nat} (h : paradoxicalB n j = true) :
    Paradoxical n j := paradoxicalB_iff.mp h

theorem not_paradoxical_of_check {n j : Nat} (h : paradoxicalB n j = false) :
    ¬ Paradoxical n j := by
  intro hp
  have := paradoxicalB_iff.mpr hp
  rw [h] at this
  exact Bool.noConfusion this

/-! ## The published examples

The paper's leading example (Section 1) is the sequence of eight iterations

  `7, 11, 17, 26, 13, 20, 10, 5, 8`

with `q = 5`, coefficient `3^5/2^8 = 243/256 < 1` and `T^8(7) = 8 > 7`.  The
further starting values are from Table 1 and Appendix C of the paper. -/

/-- The eight iterates listed in the paper, verbatim. -/
theorem orbit_seven : (List.range 9).map (fun i => acceleratedOrbit i 7)
    = [7, 11, 17, 26, 13, 20, 10, 5, 8] := by decide

/-- `T^8(7) = 8` and `q_8(7) = 5`. -/
theorem trace_seven : trace 7 8 = (8, 5) := by decide

/-- `3^5 = 243 < 256 = 2^8`: the coefficient of the example is below `1`. -/
theorem coeff_seven : (3 : Nat) ^ 5 < 2 ^ 8 := by decide

/-- **The example of Section 1**: `(7, 8)` is paradoxical, with `q = 5`. -/
theorem paradoxical_seven : Paradoxical 7 8 := paradoxical_of_check (by decide)

/-- The remaining `(j, q) = (8, 5)` starting values of Appendix C. -/
theorem paradoxical_nine : Paradoxical 9 8 := paradoxical_of_check (by decide)
theorem paradoxical_eighteen : Paradoxical 18 8 := paradoxical_of_check (by decide)
theorem paradoxical_nineteen : Paradoxical 19 8 := paradoxical_of_check (by decide)
theorem paradoxical_twentyfive : Paradoxical 25 8 := paradoxical_of_check (by decide)

/-- Appendix C, `(j, q) = (27, 17)`: the least starting value is `164`. -/
theorem paradoxical_164 : Paradoxical 164 27 := paradoxical_of_check (by decide)

/-- Appendix C, `(j, q) = (46, 29)`: the least starting value is `91`. -/
theorem paradoxical_91 : Paradoxical 91 46 := paradoxical_of_check (by decide)

/-- Appendix C, `(j, q) = (54, 34)`: only `432` and `864` occur. -/
theorem paradoxical_432 : Paradoxical 432 54 := paradoxical_of_check (by decide)
theorem paradoxical_864 : Paradoxical 864 54 := paradoxical_of_check (by decide)

/-- Appendix C, `(j, q) = (65, 41)`: the least starting value is `73`. -/
theorem paradoxical_73 : Paradoxical 73 65 := paradoxical_of_check (by decide)

/-- Appendix C, `(j, q) = (73, 46)`: the least starting value is `487`. -/
theorem paradoxical_487 : Paradoxical 487 73 := paradoxical_of_check (by decide)

/-- Appendix C, `(j, q) = (92, 58)`: the least starting value is `3567`. -/
theorem paradoxical_3567 : Paradoxical 3567 92 := paradoxical_of_check (by decide)

/-- Further Appendix C entries, checked individually: the next `(46,29)` value
after `91`, and the first four of the `(27,17)` row. -/
theorem paradoxical_121 : Paradoxical 121 46 := paradoxical_of_check (by decide)
theorem paradoxical_165 : Paradoxical 165 27 := paradoxical_of_check (by decide)
theorem paradoxical_166 : Paradoxical 166 27 := paradoxical_of_check (by decide)
theorem paradoxical_171 : Paradoxical 171 27 := paradoxical_of_check (by decide)
theorem paradoxical_231 : Paradoxical 231 65 := paradoxical_of_check (by decide)
theorem paradoxical_242 : Paradoxical 242 46 := paradoxical_of_check (by decide)

/-- Appendix C is a list of *starting values*; the paper notes that `Ωj(n)` and
`Ωj(n/2)` both occur when `n` is even.  Here `18` and `9`, and `242` and `121`. -/
theorem paradoxical_halving_pairs :
    Paradoxical 18 8 ∧ Paradoxical 9 8 ∧ Paradoxical 242 46 ∧ Paradoxical 121 46 :=
  ⟨paradoxical_eighteen, paradoxical_nine, paradoxical_242, paradoxical_121⟩

/-- Section 5: `859` initiates three distinct paradoxical sequences, of lengths
`46`, `65` and `73`, reaching `890`, `911` and `866` in that order. -/
theorem paradoxical_859_46 : Paradoxical 859 46 := paradoxical_of_check (by decide)
theorem paradoxical_859_65 : Paradoxical 859 65 := paradoxical_of_check (by decide)
theorem paradoxical_859_73 : Paradoxical 859 73 := paradoxical_of_check (by decide)

theorem endpoints_859 :
    (acceleratedOrbit 46 859, acceleratedOrbit 65 859, acceleratedOrbit 73 859)
      = (890, 911, 866) := by decide

/-- The recorded odd counts match Table 1: `q_j(n) = ⌊j·log2/log3⌋` for each of
the seven admissible pairs `(j, q)`. -/
theorem oddCounts_of_table_one :
    ((trace 7 8).2, (trace 164 27).2, (trace 91 46).2, (trace 432 54).2,
     (trace 73 65).2, (trace 487 73).2, (trace 3567 92).2)
      = (5, 17, 29, 34, 41, 46, 58) := by decide

/-- **Every `(j, q)` in Table 1 has `j` minimal for its `q`.**  For each of the
seven admissible pairs, `3^q < 2^j` but `2^{j-1} ≤ 3^q`: the length is the
smallest at which the coefficient drops below `1`, so `j = ⌈q·log₂3⌉`.

This is what the paper observes when it says the ratios `q/j` are convergents or
semiconvergents of `log 2 / log 3` and the coefficients `C` are close to `1`.
It also matches the window of `OddClock.paradoxical_window`, whose lower endpoint
is exactly this minimal `j`. -/
theorem table_one_minimal_length :
    ((3:Nat) ^ 5 < 2 ^ 8 ∧ 2 ^ 7 ≤ 3 ^ 5) ∧
    ((3:Nat) ^ 17 < 2 ^ 27 ∧ 2 ^ 26 ≤ 3 ^ 17) ∧
    ((3:Nat) ^ 29 < 2 ^ 46 ∧ 2 ^ 45 ≤ 3 ^ 29) ∧
    ((3:Nat) ^ 34 < 2 ^ 54 ∧ 2 ^ 53 ≤ 3 ^ 34) ∧
    ((3:Nat) ^ 41 < 2 ^ 65 ∧ 2 ^ 64 ≤ 3 ^ 41) ∧
    ((3:Nat) ^ 46 < 2 ^ 73 ∧ 2 ^ 72 ≤ 3 ^ 46) ∧
    ((3:Nat) ^ 58 < 2 ^ 92 ∧ 2 ^ 91 ≤ 3 ^ 58) := by decide

/-! ### Non-examples

`n ≤ 2` is excluded by Definition 1.1 precisely to remove finite repetitions of
the trivial cycle; the checker confirms that the exclusion is what does the
work, since `(2, 2)` would otherwise qualify. -/

theorem trivial_cycle_would_qualify :
    (trace 2 2 = (2, 1) ∧ (3 : Nat) ^ 1 < 2 ^ 2) := by decide

theorem not_paradoxical_two : ¬ Paradoxical 2 2 := not_paradoxical_of_check (by decide)

/-! ## A small exhaustive census

Enumerating all pairs with `n ≤ N` and `1 ≤ j ≤ J`. -/

/-- All paradoxical pairs with first term at most `N` and length at most `J`. -/
def census (N J : Nat) : List (Nat × Nat) :=
  (List.range (N + 1)).flatMap fun n =>
    (List.range (J + 1)).filterMap fun j => if paradoxicalB n j then some (n, j) else none

/-- Membership in the census is exactly paradoxicality, in range. -/
theorem mem_census {N J n j : Nat} (hn : n ≤ N) (hj : j ≤ J) :
    (n, j) ∈ census N J ↔ Paradoxical n j := by
  simp only [census, List.mem_flatMap, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨m, _, k, _, hk⟩
    by_cases hb : paradoxicalB m k
    · rw [if_pos hb] at hk
      have h1 : m = n := congrArg Prod.fst (Option.some.inj hk)
      have h2 : k = j := congrArg Prod.snd (Option.some.inj hk)
      subst h1; subst h2
      exact paradoxicalB_iff.mp hb
    · rw [if_neg hb] at hk; simp at hk
  · intro hp
    exact ⟨n, by omega, j, by omega, by rw [if_pos (paradoxicalB_iff.mpr hp)]⟩

/-- **Exhaustive check below `40`.**  Table 1 records that the only paradoxical
sequences with first term `< 40` are the five of length `8`, starting at
`7, 9, 18, 19, 25`.  This reproduces that, over every length up to `92` (the
largest length occurring anywhere in Table 1). -/
theorem census_forty : census 40 92 = [(7, 8), (9, 8), (18, 8), (19, 8), (25, 8)] := by
  decide

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 1000000 in
/-- **Exhaustive check below `200`.**  A sharper test of Appendix C: over every
first term `≤ 200` and every length `≤ 92`, the paradoxical pairs are exactly

  `(7,8) (9,8) (18,8) (19,8) (25,8) (73,65) (91,46) (121,46)
   (164,27) (165,27) (166,27) (171,27)`,

which is precisely the initial segment of the paper's Appendix C lists for four
different `(j,q)` rows — `(8,5)`, `(65,41)`, `(46,29)` and `(27,17)`.  In
particular the paper's `(27,17)` row really does begin `164, 165, 166, 171`, and
nothing outside those lists appears.

This is a completeness check, not a spot check: it also certifies that no
paradoxical pair with `n ≤ 200` was omitted from Appendix C. -/
theorem census_two_hundred :
    census 200 92 = [(7, 8), (9, 8), (18, 8), (19, 8), (25, 8), (73, 65), (91, 46),
      (121, 46), (164, 27), (165, 27), (166, 27), (171, 27)] := by decide

/-! ### Counting, in one pass

`census` recomputes `trace n j` from scratch for every `j`, so it costs
`O(N·J²)` — fine for `N = 200`, hopeless for the paper's `N = 4614`.  Counting
instead of listing allows a single forward pass per `n`, carrying the state, at
`O(N·J)`.

`countAt` is that pass and `countRefFrom` is the obvious reference that adds one
exactly when `paradoxicalB` holds; `countAt_eq` identifies them.  Since
`paradoxicalB_iff` already identifies `paradoxicalB` with `Paradoxical`, the
count is by construction the number of paradoxical pairs. -/

/-- One Terras step on the carried state. -/
def stepX (x : Nat) : Nat := if x % 2 = 1 then (3 * x + 1) / 2 else x / 2

/-- The tripling count after one step. -/
def stepC (x c : Nat) : Nat := if x % 2 = 1 then c + 1 else c

/-- Paradoxical pairs `(n, j')` for `j' ∈ [j, j+s)`, counted in one pass.  The
state carries `x = (trace n j).1` and the *powers* `p3 = 3^{q_j}`, `p2 = 2^j`
rather than the exponents, so each step is a multiplication instead of an
exponentiation — the difference between a four-minute kernel evaluation and a
ten-second one at `N = 4614`. -/
def countAt (n : Nat) : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _, _ => 0
  | s + 1, j, x, p3, p2 =>
      (if 2 < n && 1 ≤ j && p3 < p2 && n ≤ x then 1 else 0)
        + countAt n s (j + 1) (stepX x) (if x % 2 = 1 then 3 * p3 else p3) (2 * p2)

/-- The reference count: add one exactly when `paradoxicalB` holds. -/
def countRefFrom (n : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | s + 1, j => (if paradoxicalB n j then 1 else 0) + countRefFrom n s (j + 1)

theorem trace_step (n j : Nat) :
    trace n (j + 1) = (stepX (trace n j).1, stepC (trace n j).1 (trace n j).2) := by
  rw [trace]
  by_cases h : (trace n j).1 % 2 = 1
  · rw [if_pos h, stepX, if_pos h, stepC, if_pos h]
  · rw [if_neg h, stepX, if_neg h, stepC, if_neg h]

/-- **The one-pass count agrees with the reference.** -/
theorem countAt_eq (n : Nat) : ∀ s j : Nat,
    countAt n s j (trace n j).1 (3 ^ (trace n j).2) (2 ^ j) = countRefFrom n s j := by
  intro s
  induction s with
  | zero => intro _; rfl
  | succ s ih =>
    intro j
    rw [countAt, countRefFrom]
    have h1 : (trace n (j + 1)).1 = stepX (trace n j).1 := by rw [trace_step n j]
    have h3 : (3 : Nat) ^ (trace n (j + 1)).2
        = if (trace n j).1 % 2 = 1 then 3 * 3 ^ (trace n j).2 else 3 ^ (trace n j).2 := by
      rw [trace_step n j]
      by_cases h : (trace n j).1 % 2 = 1
      · rw [if_pos h, stepC, if_pos h, Nat.pow_succ, Nat.mul_comm]
      · rw [if_neg h, stepC, if_neg h]
    have h2 : (2 : Nat) ^ (j + 1) = 2 * 2 ^ j := Arith.two_pow_succ j
    rw [← h1, ← h3, ← h2, ih (j + 1)]
    congr 1

/-- The total over `n ≤ N` and `j ≤ J`. -/
def paradoxTotal (N J : Nat) : Nat :=
  ((List.range (N + 1)).map fun n => countAt n (J + 1) 0 n 1 1).sum

/-- Each summand really is the count of paradoxical lengths for that `n`. -/
theorem paradoxTotal_summand (n J : Nat) :
    countAt n (J + 1) 0 n 1 1 = countRefFrom n (J + 1) 0 :=
  countAt_eq n (J + 1) 0

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 10000000 in
/-- **42 paradoxical pairs with `n ≤ 400` and `j ≤ 92`**, kernel-checked. -/
theorem paradoxTotal_400 : paradoxTotal 400 92 = 42 := by decide

/-! #### On Theorem 1.3's count

Run with the *compiler* rather than the kernel, `paradoxTotal` reproduces the
paper's headline number exactly:

```
#eval paradoxTotal 4614 92   -- 593
```

and the breakdown by length is `(8):5, (27):50, (46):231, (54):2, (65):244,
(73):56, (92):5`, matching Table 1 row for row.

That is **evidence, not proof**.  `#eval` uses compiled evaluation, which is not
part of the trusted kernel; only a `decide` (or `rfl`) is.  Kernel-checking the
full range costs about four minutes — the cost is per-step interpreter overhead,
not arithmetic, so carrying the powers `3^{q_j}` and `2^j` in the state instead
of recomputing them (which `countAt` does) did not change it.  The checked
points, at increasing cost, are:

| `N` | 200 | 400 | 600 | 1000 | 4614 |
|---|---|---|---|---|---|
| pairs | 12 | 42 | 89 | 170 | 593 |
| kernel | ~3 s | ~12 s | ~25 s | ~54 s | ~4 min |

`paradoxTotal_400` is the point included in the build; `census_two_hundred`
additionally pins the *identity* of every pair below `200`, not just the count.

So Theorem 1.3's first clause remains **cited** rather than proved here — but its
count is reproduced by an independent implementation whose correctness against
`Paradoxical` is itself proved (`countAt_eq`, `paradoxicalB_iff`). -/

/-! #### Section 5's other statistics

The same one-pass scan, with an extra predicate on `(n, j, T^j(n))`, reproduces
the rest of the paper's Section 5 counts.  `countWhen` generalizes `countAt`;
`countWhen_eq` is the same correctness statement. -/

/-- Paradoxical pairs in `[j, j+s)` additionally satisfying `P n j' (T^{j'}(n))`. -/
def countWhen (P : Nat → Nat → Nat → Bool) (n : Nat) :
    Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _, _ => 0
  | s + 1, j, x, p3, p2 =>
      (if 2 < n && 1 ≤ j && p3 < p2 && n ≤ x && P n j x then 1 else 0)
        + countWhen P n s (j + 1) (stepX x) (if x % 2 = 1 then 3 * p3 else p3) (2 * p2)

/-- The reference: add one exactly when the pair is paradoxical and `P` holds. -/
def countWhenRef (P : Nat → Nat → Nat → Bool) (n : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | s + 1, j =>
      (if paradoxicalB n j && P n j (trace n j).1 then 1 else 0)
        + countWhenRef P n s (j + 1)

theorem countWhen_eq (P : Nat → Nat → Nat → Bool) (n : Nat) : ∀ s j : Nat,
    countWhen P n s j (trace n j).1 (3 ^ (trace n j).2) (2 ^ j) = countWhenRef P n s j := by
  intro s
  induction s with
  | zero => intro _; rfl
  | succ s ih =>
    intro j
    rw [countWhen, countWhenRef]
    have h1 : (trace n (j + 1)).1 = stepX (trace n j).1 := by rw [trace_step n j]
    have h3 : (3 : Nat) ^ (trace n (j + 1)).2
        = if (trace n j).1 % 2 = 1 then 3 * 3 ^ (trace n j).2 else 3 ^ (trace n j).2 := by
      rw [trace_step n j]
      by_cases h : (trace n j).1 % 2 = 1
      · rw [if_pos h, stepC, if_pos h, Nat.pow_succ, Nat.mul_comm]
      · rw [if_neg h, stepC, if_neg h]
    have h2 : (2 : Nat) ^ (j + 1) = 2 * 2 ^ j := Arith.two_pow_succ j
    rw [← h1, ← h3, ← h2, ih (j + 1)]
    congr 1

/-- Total over `n ≤ N`, `j ≤ J`, of paradoxical pairs satisfying `P`. -/
def totalWhen (P : Nat → Nat → Nat → Bool) (N J : Nat) : Nat :=
  ((List.range (N + 1)).map fun n => countWhen P n (J + 1) 0 n 1 1).sum

/-- Both endpoints even. -/
def evenEnds : Nat → Nat → Nat → Bool := fun n _ x => decide (n % 2 = 0 ∧ x % 2 = 0)

/-- A near-cycle: `T^j(n) = n + 1`. -/
def nearCycleP : Nat → Nat → Nat → Bool := fun n _ x => decide (x = n + 1)

/-- Both endpoints odd. -/
def oddEnds : Nat → Nat → Nat → Bool := fun n _ x => decide (n % 2 = 1 ∧ x % 2 = 1)

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 10000000 in
/-- The three refined counts, kernel-checked at `N = 200`.  (`N = 400` gives
`6, 11, 11` in about 25 s; kept at `200` for build speed.) -/
theorem section_five_counts_200 :
    totalWhen evenEnds 200 92 = 1 ∧ totalWhen nearCycleP 200 92 = 7 ∧
      totalWhen oddEnds 200 92 = 2 := by decide

/-! #### Agreement with Section 5, in full

Compiler-evaluated over the paper's whole range, every statistic in Section 5 is
reproduced exactly:

| statistic | `#eval` at `N = 4614`, `J = 92` | paper |
|---|---|---|
| paradoxical pairs | 593 | 593 |
| distinct starting integers | 550 | 550 |
| both endpoints even | 138 | 138 |
| near-cycles `T^j(n) = n+1` | 20 | 20 |
| both endpoints odd | 148 | 148 (the `Nodd` column of Table 1) |

Five independent counts from an independently written implementation, all
matching.  As above these are `#eval`, so evidence rather than kernel proof;
`section_five_counts_200` and `paradoxTotal_400` are the checked points. -/

/-! ### The shared value

Section 5 of the paper records a structural observation about its Table 1: *"all
sequences in Table 1 contain either the value `11` when `j = 8`, or the value
`103` otherwise"*, which is why the listed sequences largely overlap.

That is checkable on the range the census already settles.  Rewriting by
`census_two_hundred` first means the check evaluates only the twelve orbits, not
the census again. -/

/-- Does the orbit `n, T(n), …, T^j(n)` contain `v`? -/
def orbitContains (n j v : Nat) : Bool :=
  (List.range (j + 1)).any fun i => decide (acceleratedOrbit i n = v)

/-- **The paper's shared-value observation, verified below `200`.**  Every
paradoxical sequence with first term `≤ 200` passes through `11` if its length is
`8`, and through `103` otherwise. -/
theorem census_two_hundred_shared_value :
    ((census 200 92).all fun q =>
      orbitContains q.1 q.2 (if q.2 = 8 then 11 else 103)) = true := by
  rw [census_two_hundred]
  decide

/-! ### Near-cycles (Appendix B)

The paper's Appendix B studies `T^j(n) − n = 1` and shows (Lemma B.2) that
*all solutions with `n > 3` are paradoxical sequences*.  Its proof rests on
Lemma B.1, a lower bound derived from a result of Ellison, which is analytic and
is not formalized here — but the conclusion is checkable on a range. -/

/-- The pairs `(n, j)` with `T^j(n) = n + 1`, for `n ≤ N` and `1 ≤ j ≤ J`. -/
def nearCycles (N J : Nat) : List (Nat × Nat) :=
  (List.range (N + 1)).flatMap fun n =>
    (List.range (J + 1)).filterMap fun j =>
      if 1 ≤ j && (trace n j).1 == n + 1 then some (n, j) else none

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 1000000 in
/-- **Lemma B.2 verified below `200`.**  Every solution of `T^j(n) = n + 1` with
`3 < n ≤ 200` and `j ≤ 92` is paradoxical. -/
theorem nearCycles_paradoxical_200 :
    ((nearCycles 200 92).all fun q => decide (q.1 ≤ 3) || paradoxicalB q.1 q.2) = true := by
  decide

/-- Why the hypothesis is `n > 3`.  Both `n = 1` and `n = 3` solve
`T^j(n) = n + 1` and neither is paradoxical — `1` because it is excluded by
`n > 2`, and `3` because its coefficient `3^2/2^3 = 9/8` exceeds `1`. -/
theorem nearCycles_exceptions :
    (trace 1 1).1 = 2 ∧ (trace 3 3).1 = 4 ∧
      ¬ Paradoxical 1 1 ∧ ¬ Paradoxical 3 3 :=
  ⟨by decide, by decide, not_paradoxical_of_check (by decide),
   not_paradoxical_of_check (by decide)⟩

/-! ## Section 3: from divergent to paradoxical sequences

Theorem 3.2 says an `n ≥ 2` with infinite stopping time yields *infinitely many*
paradoxical sequences.  Its proof tests a pair `(a, b)` supplied by Lemma 3.1
(continued fractions / Dirichlet) against `j`, the least index with `q_j(n) = a`,
and splits:

* `j ≥ b` — elementary, and is `paradoxical_of_no_descent` below: once the
  coefficient has dropped at `j` and the orbit has not, the pair is paradoxical.
* `j < b` — needs the explicit remainder bound of the paper's Theorem 2.4
  together with the size of `(a, b)`.

The *infinitude* comes from Lemma 3.1, which is genuinely analytic.  So only the
first case is proved here; Lemma 3.1 and Theorem 3.2 are stated as cited `Prop`s.

It is worth being precise about why the analytic input is unavoidable.  A
non-descending orbit satisfies `2^{K_L} · n^L ≤ (3n+1)^L`
(`GapBarriers.noDescent_product_bound`), which bounds `K_L` from *above*.  What
the first case needs is a `j` where the coefficient has dropped, i.e. `K` bounded
*below* — the opposite direction.  Nothing elementary here supplies it. -/

/-- **Theorem 3.2, first case**, elementary.  If `n > 2` never descends and the
coefficient has dropped by index `j`, then `(n, j)` is paradoxical.  Such an `n`
is then a counterexample to CST: `τ(n) ≤ j` while `t(n) = ∞`. -/
theorem paradoxical_of_no_descent {n j : Nat} (hn : 2 < n) (hj : 1 ≤ j)
    (hnd : ∀ i : Nat, n ≤ acceleratedOrbit i n)
    (hcoeff : 3 ^ oddCount n j < 2 ^ j) : Paradoxical n j :=
  ⟨hn, hj, hcoeff, hnd j⟩

/-- And such an `n` has no stopping time at all, so CST fails at it outright. -/
theorem no_stoppingTime_of_no_descent {n : Nat}
    (hnd : ∀ i : Nat, n ≤ acceleratedOrbit i n) (t : Nat) : ¬ stoppingTime n t := by
  intro ht
  have := hnd t
  have := ht.2.1
  omega

/-- **Lemma 3.1 (Rozier–Terracol)**, cited, not proved.  For every `ε > 0` there
are infinitely many pairs `(a, b)` of positive integers with
`1 − ε < 3^a/2^b < 1`.  Written over `Nat` with `ε = 1/E`, and "infinitely many"
as "beyond every bound".  The proof is continued fractions applied to
`log 2 / log 3`, and is not formalized here. -/
def RT_Lemma31 : Prop :=
  ∀ E B : Nat, 1 ≤ E →
    ∃ a b : Nat, B < b ∧ 1 ≤ a ∧ 3 ^ a < 2 ^ b ∧ 2 ^ b * (E - 1) < 3 ^ a * E

/-- **Theorem 3.2 (Rozier–Terracol)**, cited, not proved.  An `n ≥ 2` with
infinite stopping time starts infinitely many paradoxical sequences, from
integers of the form `2^k · n`. -/
def RT_Thm32 : Prop :=
  ∀ n : Nat, 2 < n → (∀ j : Nat, n ≤ acceleratedOrbit j n) →
    ∀ B : Nat, ∃ k j : Nat, B < j ∧ Paradoxical (2 ^ k * n) j

/-! ## Rozier–Terracol, Theorem 1.3

Stated, not proved.  Its proof in the paper rests on a computational search of
the authors together with the numerical data of Oliveira e Silva and of
Roosendaal; none of that is formalized here, and none of it is used anywhere in
this repository.

> **Theorem 1.3 (Rozier–Terracol 2026).**  There are exactly 593 paradoxical
> sequences that begin with an integer lower than or equal to 4614.  If there
> are any more of them, they must start above `2.8 × 10^19`.  Conversely, if
> there exist no others, then the Collatz conjecture is true.
-/

/-- Clause one: exactly `593` paradoxical pairs have first term at most `4614`.
"Sequences differing in their first term or length are considered distinct", so
the objects counted are pairs `(n, j)`, listed here without repetition. -/
def RT13_census : Prop :=
  ∃ L : List (Nat × Nat),
    L.length = 593 ∧ L.Nodup ∧ ∀ n j : Nat, n ≤ 4614 → (Paradoxical n j ↔ (n, j) ∈ L)

/-- Clause two: no paradoxical pair has first term in `(4614, 2.8 × 10^19]`. -/
def RT13_gap : Prop :=
  ∀ n j : Nat, 4614 < n → n ≤ 28000000000000000000 → ¬ Paradoxical n j

/-- Clause three: if there are no paradoxical sequences beyond the census, the
Collatz conjecture holds.  (The paper's Corollary 3.3 in the sharpened form of
Theorem 1.3.) -/
def RT13_implies_collatz : Prop :=
  (∀ n j : Nat, 4614 < n → ¬ Paradoxical n j) → CollatzConjecture

/-- **Rozier–Terracol, Theorem 1.3**, as cited.  Discrete Mathematics 349
(2026); arXiv:2502.00948.  Not proved here. -/
def RozierTerracolThm13 : Prop :=
  RT13_census ∧ RT13_gap ∧ RT13_implies_collatz

/-- Corollary 5.4 of the paper, likewise cited: CST holds up to `2.8 × 10^19`. -/
def RT_Cor54 : Prop :=
  ∀ n t τ : Nat, 2 ≤ n → n ≤ 28000000000000000000 →
    stoppingTime n t → IsCoeffStoppingTime n τ → t = τ

/-- What the cited gap clause buys, granted: no CST failure can hide in the
range, because a failure would manufacture a paradoxical pair there.  The
implication itself is ours; the hypothesis `RT13_gap` is theirs. -/
theorem cst_of_RT13_gap (h : RT13_gap) {n t τ : Nat}
    (hn : 4614 < n) (hle : n ≤ 28000000000000000000)
    (ht : stoppingTime n t) (hτ : IsCoeffStoppingTime n τ) : t = τ := by
  have hle2 : τ ≤ t := coeffStoppingTime_le_stoppingTime ht hτ
  rcases Nat.eq_or_lt_of_le hle2 with heq | hlt
  · exact heq.symm
  · exact absurd (paradoxical_of_cst_failure (by omega) ht hτ (by omega)) (h n τ hn hle)

end Paradoxical
end Collatz
