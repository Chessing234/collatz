import Collatz.Core.Arith
import Collatz.Accelerated

/-!
# The odd-to-odd accelerated map: exact constraints and barrier theorems

This module formalizes the elementary half of an audit of the "divisions beat
multiplications" attack on Collatz.  It works with the **odd-to-odd** map

  `T(n) = (3n+1) / 2^{v₂(3n+1)}`  on odd positives,

which is *not* the Terras map `acceleratedStep` used elsewhere in this
repository (that one halves once per step).  To avoid building a 2-adic
valuation, a step is represented as a relation:

  `OddStep n k m`  means  `k ≥ 1`, `m` odd, and `2^k · m = 3n + 1`,

which for odd `n` determines `k` and `m` uniquely (`oddStep_unique`) and always
exists (`oddStep_exists`).  So `OddStep n k m ↔ (m = T n ∧ k = v₂(3n+1))`
without a valuation function ever being defined.

## What is proved

*Local structure.*  `k = 1 ↔ n ≡ 3 (mod 4)`, `k ≥ 2 ↔ n ≡ 1 (mod 4)`, the exact
descent criterion `m < n ↔ 3n + 1 < 2^k · n`, and its clean form `m < n ↔ k ≥ 2`
for `n ≥ 3`.  In particular `m > n` whenever `k = 1`: one tripling followed by
one halving *always* ascends.

*Trajectories.*  The exact affine identity `2^{K_L}·n_L = 3^L·n_0 + b` with
`b ≥ 1` for `L ≥ 1`, and the exact product estimate

  `2^{K_L} · N^L · n_L ≤ (3N+1)^L · n_0`   whenever every `n_i ≥ N`,

which is the `Nat`-form of `K log 2 ≤ L·log(3 + 1/N)`.

*Cycles.*  `3^L < 2^{K_L}`, and for a cycle with least element `N`

  `2^{K_L} · N^L ≤ (3N+1)^L`.

These two are the exact Diophantine squeeze that the continued-fraction bound on
cycle length is extracted from; the extraction itself is analytic and is not
formalized here.  Length `1` is settled outright (`cycle_length_one`).

*No descent.*  The same product estimate applied to a trajectory that fails to
descend (`noDescent_product_bound`), the `Nat` form of "the mean valuation of a
non-descending stretch is at most `log₂(3 + 1/N)`".

*Barriers.*  The ascent family `n_i = 3^i·2^{j-i} - 1` gives, for every `L`, an
odd start `2^{L+1} - 1` whose first `L` steps all have `k = 1` and strictly
increase (`asc_step`, `asc_lt`, `ascChain_traj`).  Consequences:

* `coefficient_stopping_time_unbounded` — the coefficient stopping time is
  unbounded, so
  no covering of the odd integers by residue classes with *uniformly bounded*
  descent certificates exists;
* `no_power_descent` — **no** `φ` with `B·n^e ≤ φ(n)^d ≤ A·n^e` strictly
  decreases along every odd step, for any positive `d, e, A, B`.  This kills
  `φ(n) = c(n mod 2^M)·n^{e/d}` for every modulus and every rational exponent at
  once, and in particular `n`, `√n`, and every locally reweighted power of `n`.

Nothing here proves or assumes the Collatz conjecture, the absence of divergent
orbits, or the absence of nontrivial cycles.

## Roadmap

The file grew by accretion, so the section order is partly historical.  By
theme, with the headline result of each group:

| theme | sections | headline |
|---|---|---|
| the step relation, and its local structure | "One accelerated odd step", "Local structure" | `oddStep_lt_iff_two_le` |
| the valuation as a congruence | "The valuation as a congruence" | `oddStep_iff_rk` |
| backward structure | "Predecessors", "The predecessors of `1`" | `no_pred_of_three_dvd` |
| trajectories and the affine identity | "Trajectories", "The additive accumulator" | `traj_affine_exact`, `traj_product` |
| Terras's parity-vector theorem | "…determined by a residue", "Towards realization" | `parity_vector_correspondence` |
| a *computable* map, and what it unlocks | "A computable odd map", "A bounded least-witness search" | `oddStep_oddT`, `exists_traj` |
| the two stopping times | "Terras's elementary inequality", "Machine-checking the CST conjecture" | `cst_two_sided`, `cst_below_1000` |
| cycles: the squeeze, and lengths ruled out | "Cycles", "…upper bound on the least element", "A decidable criterion", "Enumerating the compositions" | `no_short_cycle`, `cycle_length_ge_42` |
| cycles with a *prescribed valuation pattern* | "Circuits", "One big valuation before the last" | `no_circuit_below_101`, `no_oneBig_below_13` |
| valuation counting | "How many steps can have valuation ≥ 2?" | `bigCount_bound` |
| the ascent family and the barrier results | "Runs of valuation one", "The ascent family", "Barrier: …" | `no_power_descent`, `no_local_descent` |

**Why the pattern sections reach further.**  The general check
(`noCycleAtLength`) needs one test per *composition* of `K` into `L` parts, which
is exponential and stops at `L = 10`.  Fixing the valuation pattern collapses
`Sacc` to a function of finitely many parameters, so the search becomes
polynomial: no parameters for circuits (`L ≤ 100`), two for the one-big pattern
(`L ≤ 12`).  `circuit_band` explains the extreme case — for a circuit there is at
most one admissible `K` per length at all.

Two results are **conditional** and are marked as such where they appear:
`cycle_length_ge_42` assumes the cited `2^68` verification, and `cst_below_1000`
is only as strong as the range the kernel checked.  Everything else is
unconditional.

Lean 4.33.0-rc1.  No Mathlib, no `sorry`, no `axiom`, no `native_decide`.
-/

namespace Collatz
namespace GapBarriers

open Arith

set_option linter.unusedSimpArgs false

/-! ## Elementary arithmetic helpers -/

/-- Positivity of powers. -/
theorem pow_pos_of_pos {a : Nat} (ha : 0 < a) (L : Nat) : 0 < a ^ L := by
  induction L with
  | zero => rw [Nat.pow_zero]; omega
  | succ L ih => rw [Nat.pow_succ]; exact Nat.mul_pos ih ha

/-- `C < 2 ^ C`. -/
theorem lt_two_pow (C : Nat) : C < 2 ^ C := by
  induction C with
  | zero => decide
  | succ C ih =>
    have h : 2 ^ (C + 1) = 2 * 2 ^ C := two_pow_succ C
    omega

/-- Cancelling an odd factor from a power of two: `2^L ∣ c·x` with `c` odd
forces `2^L ∣ x`. -/
theorem dvd_of_odd_mul {c : Nat} (hc : c % 2 = 1) :
    ∀ (L x : Nat), 2 ^ L ∣ c * x → 2 ^ L ∣ x := by
  intro L
  induction L with
  | zero => intro x _; exact Nat.one_dvd x
  | succ L ih =>
    intro x hdvd
    obtain ⟨t, ht⟩ := hdvd
    have hsplit : c * x = 2 * (2 ^ L * t) := by
      rw [ht, two_pow_succ, Nat.mul_assoc]
    have hxeven : x % 2 = 0 := by
      have hmod : (c * x) % 2 = c % 2 * (x % 2) % 2 := Nat.mul_mod c x 2
      rw [hc, Nat.one_mul] at hmod
      have hzero : (c * x) % 2 = 0 := by omega
      have := Nat.mod_lt x (show 0 < 2 by omega)
      omega
    obtain ⟨y, hy⟩ : ∃ y, x = 2 * y := ⟨x / 2, by omega⟩
    have hcy : 2 * (c * y) = 2 * (2 ^ L * t) := by
      rw [Nat.mul_left_comm, ← hy]; exact hsplit
    have hstep : 2 ^ L ∣ c * y := ⟨t, by omega⟩
    obtain ⟨s, hs⟩ := ih y hstep
    exact ⟨s, by rw [hy, hs, two_pow_succ, Nat.mul_assoc]⟩


/-! ## One accelerated odd step, as a relation -/

/-- `OddStep n k m` : from `n`, one step of the odd-to-odd accelerated map with
2-adic valuation `k` lands on `m`.  For odd `n` such `k, m` exist and are
unique, so this is the graph of `n ↦ (3n+1)/2^{v₂(3n+1)}` without a valuation
function being defined. -/
def OddStep (n k m : Nat) : Prop := 1 ≤ k ∧ m % 2 = 1 ∧ 2 ^ k * m = 3 * n + 1

theorem oddStep_pos {n k m : Nat} (h : OddStep n k m) : 0 < m := by
  have := h.2.1; omega

/-- Stripping the twos from a positive even number. -/
theorem exists_split : ∀ f x : Nat, x ≤ f → 0 < x → x % 2 = 0 →
    ∃ k m, 1 ≤ k ∧ m % 2 = 1 ∧ 2 ^ k * m = x := by
  intro f
  induction f with
  | zero => intro x hx hpos _; omega
  | succ f ih =>
    intro x hx hpos heven
    have hhalf : 2 * (x / 2) = x := by omega
    have hhpos : 0 < x / 2 := by omega
    rcases Nat.eq_zero_or_pos ((x / 2) % 2) with hodd | hodd
    · -- `x / 2` is even: recurse
      obtain ⟨k, m, hk, hm, hkm⟩ := ih (x / 2) (by omega) hhpos hodd
      refine ⟨k + 1, m, by omega, hm, ?_⟩
      rw [two_pow_succ, Nat.mul_assoc, hkm]
      exact hhalf
    · -- `x / 2` is odd
      refine ⟨1, x / 2, by omega, by omega, ?_⟩
      rw [Nat.pow_one]
      exact hhalf

theorem oddStep_exists {n : Nat} (hn : n % 2 = 1) : ∃ k m, OddStep n k m := by
  obtain ⟨k, m, hk, hm, hkm⟩ :=
    exists_split (3 * n + 1) (3 * n + 1) (Nat.le_refl _) (by omega) (by omega)
  exact ⟨k, m, hk, hm, hkm⟩

/-- A power of two times an odd number determines both factors. -/
theorem two_pow_mul_odd_inj : ∀ (k k' m m' : Nat), m % 2 = 1 → m' % 2 = 1 →
    2 ^ k * m = 2 ^ k' * m' → k = k' ∧ m = m' := by
  intro k
  induction k with
  | zero =>
    intro k' m m' hm hm' heq
    rw [Nat.pow_zero, Nat.one_mul] at heq
    cases k' with
    | zero => rw [Nat.pow_zero, Nat.one_mul] at heq; exact ⟨rfl, heq⟩
    | succ j =>
      exfalso
      rw [two_pow_succ, Nat.mul_assoc] at heq
      omega
  | succ k ih =>
    intro k' m m' hm hm' heq
    cases k' with
    | zero =>
      exfalso
      rw [Nat.pow_zero, Nat.one_mul, two_pow_succ, Nat.mul_assoc] at heq
      omega
    | succ j =>
      rw [two_pow_succ, Nat.mul_assoc, two_pow_succ, Nat.mul_assoc] at heq
      have heq' : 2 ^ k * m = 2 ^ j * m' := by omega
      obtain ⟨h1, h2⟩ := ih j m m' hm hm' heq'
      exact ⟨by omega, h2⟩

/-- Uniqueness of the step. -/
theorem oddStep_unique {n k m k' m' : Nat} (h : OddStep n k m) (h' : OddStep n k' m') :
    k = k' ∧ m = m' :=
  two_pow_mul_odd_inj k k' m m' h.2.1 h'.2.1 (by rw [h.2.2, h'.2.2])

/-! ## Local structure: Lemmas 2.2 and 3.1–3.2 -/

/-- `v₂(3n+1) = 1 ⟺ n ≡ 3 (mod 4)`. -/
theorem oddStep_k_one_iff {n k m : Nat} (hn : n % 2 = 1) (h : OddStep n k m) :
    k = 1 ↔ n % 4 = 3 := by
  obtain ⟨hk, hm, heq⟩ := h
  constructor
  · intro h1
    subst h1
    rw [Nat.pow_one] at heq
    omega
  · intro h3
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · omega
    · exfalso
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      have hfour : 2 ^ (j + 2) = 4 * 2 ^ j := by
        rw [two_pow_succ, two_pow_succ]; omega
      rw [hfour, Nat.mul_assoc] at heq
      omega

/-- `v₂(3n+1) ≥ 2 ⟺ n ≡ 1 (mod 4)`. -/
theorem oddStep_two_le_iff {n k m : Nat} (hn : n % 2 = 1) (h : OddStep n k m) :
    2 ≤ k ↔ n % 4 = 1 := by
  have hiff := oddStep_k_one_iff hn h
  have hk := h.1
  omega

/-- **One tripling and one halving always ascend.**  If the valuation is `1`
then the step strictly increases. -/
theorem lt_of_k_one {n m : Nat} (hn : 0 < n) (h : OddStep n 1 m) : n < m := by
  have heq := h.2.2
  rw [Nat.pow_one] at heq
  omega

/-- **The exact descent criterion**: `T(n) < n ⟺ 3n + 1 < 2^k · n`, i.e.
`2^k > 3 + 1/n`. -/
theorem oddStep_lt_iff {n k m : Nat} (h : OddStep n k m) :
    m < n ↔ 3 * n + 1 < 2 ^ k * n := by
  have hpow : 0 < 2 ^ k := two_pow_pos k
  constructor
  · intro hlt
    have hstep := (Nat.mul_lt_mul_left hpow).mpr hlt
    rw [h.2.2] at hstep
    exact hstep
  · intro hlt
    rw [← h.2.2] at hlt
    exact Nat.lt_of_mul_lt_mul_left hlt

/-- For `n ≥ 3` the criterion is simply `k ≥ 2`, i.e. `n ≡ 1 (mod 4)`. -/
theorem oddStep_lt_iff_two_le {n k m : Nat} (hn : 3 ≤ n) (h : OddStep n k m) :
    m < n ↔ 2 ≤ k := by
  rw [oddStep_lt_iff h]
  constructor
  · intro hlt
    rcases Nat.lt_or_ge k 2 with hk | hk
    · exfalso
      have h1 : k = 1 := by have := h.1; omega
      subst h1
      rw [Nat.pow_one] at hlt
      omega
    · exact hk
  · intro hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have hfour : 4 ≤ 2 ^ (j + 2) := by
      rw [two_pow_succ, two_pow_succ]
      have := two_pow_pos j
      omega
    have hmul : 4 * n ≤ 2 ^ (j + 2) * n := Nat.mul_le_mul_right n hfour
    omega


/-! ## Bridge to the Terras clock

The rest of this repository iterates `acceleratedStep`, the Terras map that
halves once per step.  One odd-map step of valuation `k` is exactly `k` Terras
steps, so `OddStep` embeds in `acceleratedOrbit` and the two clocks can be
compared. -/

/-- Stripping `a` factors of two takes exactly `a` Terras steps. -/
theorem acceleratedOrbit_two_pow_mul : ∀ a m : Nat, acceleratedOrbit a (2 ^ a * m) = m := by
  intro a
  induction a with
  | zero => intro m; simp
  | succ a ih =>
    intro m
    have heven : (2 ^ (a + 1) * m) % 2 = 0 := by
      have h : 2 ^ (a + 1) * m = 2 * (2 ^ a * m) := by
        rw [two_pow_succ, Nat.mul_assoc]
      omega
    have hstep : acceleratedStep (2 ^ (a + 1) * m) = 2 ^ a * m := by
      rw [acceleratedStep, if_pos heven, two_pow_succ, Nat.mul_assoc]
      omega
    rw [acceleratedOrbit_succ, hstep]
    exact ih m

/-- **One odd-map step is `k` Terras steps.** -/
theorem oddStep_acceleratedOrbit {n k m : Nat} (hn : n % 2 = 1) (h : OddStep n k m) :
    acceleratedOrbit k n = m := by
  obtain ⟨hk, _, heq⟩ := h
  obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  subst hj
  have hstep : acceleratedStep n = 2 ^ j * m := by
    rw [acceleratedStep, if_neg (by omega)]
    rw [two_pow_succ, Nat.mul_assoc] at heq
    omega
  rw [acceleratedOrbit_succ, hstep]
  exact acceleratedOrbit_two_pow_mul j m

/-! ## The valuation as a congruence (Lemma 2.3)

`v₂(3n+1) = k` is a single congruence condition on `n` modulo `2^{k+1}`.  First
the clean form on `3n+1`, then the explicit residue for `n` itself. -/

/-- `2^k` is `1` or `2` mod `3`, according to the parity of `k`. -/
theorem two_pow_mod_three (k : Nat) :
    (k % 2 = 0 → 2 ^ k % 3 = 1) ∧ (k % 2 = 1 → 2 ^ k % 3 = 2) := by
  induction k with
  | zero => exact ⟨fun _ => rfl, fun h => by omega⟩
  | succ k ih =>
    rw [two_pow_succ]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := ih.2 (by omega)
      omega
    · have := ih.1 (by omega)
      omega

/-- `2 ^ j` is never divisible by `3`. -/
theorem two_pow_mod_three_ne (j : Nat) : 2 ^ j % 3 = 1 ∨ 2 ^ j % 3 = 2 := by
  have h := two_pow_mod_three j
  rcases Nat.eq_zero_or_pos (j % 2) with hj | hj
  · exact Or.inl (h.1 hj)
  · exact Or.inr (h.2 (by omega))

/-- **`v₂(3n+1) = k` is the congruence `3n + 1 ≡ 2^k (mod 2^{k+1})`.** -/
theorem oddStep_iff_mod {n k : Nat} (hk : 1 ≤ k) :
    (∃ m, OddStep n k m) ↔ (3 * n + 1) % 2 ^ (k + 1) = 2 ^ k := by
  constructor
  · rintro ⟨m, _, hm, heq⟩
    obtain ⟨t, ht⟩ : ∃ t, m = 2 * t + 1 := ⟨m / 2, by omega⟩
    subst ht
    have hrw : 2 ^ k * (2 * t + 1) = 2 ^ k + t * 2 ^ (k + 1) := by
      rw [two_pow_succ]
      simp [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm,
        Nat.add_comm]
    rw [← heq, hrw, Nat.add_mul_mod_self_right]
    refine Nat.mod_eq_of_lt ?_
    rw [two_pow_succ]
    have := two_pow_pos k
    omega
  · intro h
    obtain ⟨q, hq⟩ : ∃ q, 3 * n + 1 = 2 ^ (k + 1) * q + (3 * n + 1) % 2 ^ (k + 1) :=
      ⟨(3 * n + 1) / 2 ^ (k + 1), (Nat.div_add_mod _ _).symm⟩
    rw [h, two_pow_succ] at hq
    refine ⟨2 * q + 1, hk, by omega, ?_⟩
    have hrw : 2 ^ k * (2 * q + 1) = 2 * 2 ^ k * q + 2 ^ k := by
      simp [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    omega

/-- Cancelling a factor of `3` against a modulus coprime to `3`, in the
quotient-explicit form that `omega` can digest (no `/` by a non-literal). -/
theorem three_mul_cancel {P a b u v : Nat} (hP : P % 3 = 1 ∨ P % 3 = 2)
    (hu : u < 3) (hv : v < 3) (h : 3 * a + P * v = 3 * b + P * u) : a = b := by
  have cu : u = 0 ∨ u = 1 ∨ u = 2 := by omega
  have cv : v = 0 ∨ v = 1 ∨ v = 2 := by omega
  rcases hP with hP | hP <;> rcases cu with rfl | rfl | rfl <;>
    rcases cv with rfl | rfl | rfl <;> omega

/-- Reducing `3n+1` modulo `P` only depends on `n` modulo `P`. -/
theorem mod_three_shift (P n : Nat) :
    (3 * n + 1) % P = (3 * (n % P) + 1) % P := by
  simp [Nat.add_mod, Nat.mul_mod]

/-- The residue of `n` mod `2^{k+1}` that makes `v₂(3n+1) = k`. -/
def rk (k : Nat) : Nat := if k % 2 = 0 then (2 ^ k - 1) / 3 else (5 * 2 ^ k - 1) / 3

/-- `3·r_k + 1 = 2^k` for even `k` and `5·2^k` for odd `k`; in both cases it is
`2^k` plus a multiple of `2^{k+1}` with small cofactor. -/
theorem three_rk (k : Nat) :
    3 * rk k + 1 = 2 ^ (k + 1) * (if k % 2 = 0 then 0 else 2) + 2 ^ k := by
  have hp := two_pow_mod_three k
  have hpos := two_pow_pos k
  have hs : (2 : Nat) ^ (k + 1) = 2 * 2 ^ k := two_pow_succ k
  rcases Nat.eq_zero_or_pos (k % 2) with h | h
  · rw [if_pos h, rk, if_pos h, hs]
    have h1 := hp.1 h
    omega
  · have h1 : k % 2 = 1 := by omega
    rw [if_neg (by omega), rk, if_neg (by omega), hs]
    have h2 := hp.2 h1
    omega

theorem rk_lt (k : Nat) : rk k < 2 ^ (k + 1) := by
  have h := three_rk k
  have hpos := two_pow_pos k
  have hs : (2 : Nat) ^ (k + 1) = 2 * 2 ^ k := two_pow_succ k
  rcases Nat.eq_zero_or_pos (k % 2) with hk | hk
  · rw [if_pos hk] at h; omega
  · rw [if_neg (by omega)] at h; omega

/-- **Lemma 2.3.**  `v₂(3n+1) = k` holds exactly when `n ≡ r_k (mod 2^{k+1})`,
with `r_k = (2^k − 1)/3` for even `k` and `(5·2^k − 1)/3` for odd `k`.
First values: `r₁ = 3 (mod 4)`, `r₂ = 1 (mod 8)`, `r₃ = 13 (mod 16)`,
`r₄ = 5 (mod 32)`, `r₅ = 53 (mod 64)`. -/
theorem oddStep_iff_rk {n k : Nat} (hk : 1 ≤ k) :
    (∃ m, OddStep n k m) ↔ n % 2 ^ (k + 1) = rk k := by
  have hP : (0 : Nat) < 2 ^ (k + 1) := two_pow_pos (k + 1)
  have hs : (2 : Nat) ^ (k + 1) = 2 * 2 ^ k := two_pow_succ k
  have hpk : (0 : Nat) < 2 ^ k := two_pow_pos k
  have h3rk := three_rk k
  have hrklt := rk_lt k
  rw [oddStep_iff_mod hk]
  -- reduce both sides to the residue `r = n % 2^{k+1}`
  obtain ⟨s, hsplit⟩ : ∃ s, n = 2 ^ (k + 1) * s + n % 2 ^ (k + 1) :=
    ⟨n / 2 ^ (k + 1), (Nat.div_add_mod _ _).symm⟩
  have hrlt : n % 2 ^ (k + 1) < 2 ^ (k + 1) := Nat.mod_lt n hP
  have hred : (3 * n + 1) % 2 ^ (k + 1) = (3 * (n % 2 ^ (k + 1)) + 1) % 2 ^ (k + 1) :=
    mod_three_shift _ n
  rw [hred]
  constructor
  · intro h
    obtain ⟨u, hu⟩ : ∃ u, 3 * (n % 2 ^ (k + 1)) + 1 = 2 ^ (k + 1) * u + 2 ^ k :=
      ⟨(3 * (n % 2 ^ (k + 1)) + 1) / 2 ^ (k + 1), by
        rw [← h]; exact (Nat.div_add_mod _ _).symm⟩
    have hu3 : u < 3 := by
      have hlt : 2 ^ (k + 1) * u < 2 ^ (k + 1) * 3 := by omega
      exact Nat.lt_of_mul_lt_mul_left hlt
    rcases Nat.eq_zero_or_pos (k % 2) with hp | hp
    · rw [if_pos hp] at h3rk
      have heq : 3 * (n % 2 ^ (k + 1)) + 2 ^ (k + 1) * 0 = 3 * rk k + 2 ^ (k + 1) * u := by
        omega
      exact three_mul_cancel (two_pow_mod_three_ne (k + 1)) hu3 (by omega) heq
    · rw [if_neg (by omega)] at h3rk
      have heq : 3 * (n % 2 ^ (k + 1)) + 2 ^ (k + 1) * 2 = 3 * rk k + 2 ^ (k + 1) * u := by
        omega
      exact three_mul_cancel (two_pow_mod_three_ne (k + 1)) hu3 (by omega) heq
  · intro h
    rw [h]
    rcases Nat.eq_zero_or_pos (k % 2) with hp | hp
    · rw [if_pos hp] at h3rk
      rw [show 3 * rk k + 1 = 2 ^ k by omega]
      exact Nat.mod_eq_of_lt (by omega)
    · rw [if_neg (by omega)] at h3rk
      rw [show 3 * rk k + 1 = 2 ^ k + 2 ^ (k + 1) * 2 by omega,
        Nat.mul_comm (2 ^ (k + 1)) 2, Nat.add_mul_mod_self_right]
      exact Nat.mod_eq_of_lt (by omega)

/-- The first residues, matching the table in the notes. -/
theorem rk_table :
    (rk 1, rk 2, rk 3, rk 4, rk 5, rk 6) = (3, 1, 13, 5, 53, 21) := by decide

/-! ## Predecessors

Which odd `m` arise as `T(n)`, and with which valuation?  Solving `2^k·m = 3n+1`
for `n` needs only `2^k·m ≡ 1 (mod 3)`, and since `2^k ≡ (−1)^k (mod 3)` this
pins the parity of `k` against the residue of `m` mod `3`.  Multiples of `3` have
no predecessor at all — they are the leaves of the Collatz tree on odd
integers. -/

/-- A predecessor exists exactly when `2^k·m ≡ 1 (mod 3)`, and then it is
`(2^k·m − 1)/3`. -/
theorem exists_pred_iff {m k : Nat} (hm : m % 2 = 1) (hk : 1 ≤ k) :
    (∃ n, OddStep n k m) ↔ (2 ^ k * m) % 3 = 1 := by
  constructor
  · rintro ⟨n, _, _, heq⟩
    omega
  · intro h
    exact ⟨(2 ^ k * m - 1) / 3, hk, hm, by omega⟩

/-- The predecessor is automatically odd. -/
theorem pred_odd {n k m : Nat} (h : OddStep n k m) : n % 2 = 1 := by
  obtain ⟨hk, _, heq⟩ := h
  obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  subst hj
  rw [two_pow_succ, Nat.mul_assoc] at heq
  omega

/-- **Multiples of three have no predecessor.**  The image of the odd map misses
`3ℕ`, so a multiple of three is a leaf of the backward tree. -/
theorem no_pred_of_three_dvd {m : Nat} (h3 : m % 3 = 0) (k : Nat) :
    ¬ ∃ n, OddStep n k m := by
  rintro ⟨n, _, _, heq⟩
  obtain ⟨t, ht⟩ : ∃ t, m = 3 * t := ⟨m / 3, by omega⟩
  have hx : 2 ^ k * m = 3 * (2 ^ k * t) := by rw [ht, Nat.mul_left_comm]
  omega

/-- **Which valuations occur.**  `k` must be even when `m ≡ 1 (mod 3)` and odd
when `m ≡ 2 (mod 3)`; when `3 ∣ m` no `k` works. -/
theorem pred_valuation_parity {m k : Nat} (hm : m % 2 = 1) (hk : 1 ≤ k) :
    (∃ n, OddStep n k m) ↔ ((k % 2 = 0 ∧ m % 3 = 1) ∨ (k % 2 = 1 ∧ m % 3 = 2)) := by
  rw [exists_pred_iff hm hk]
  have hmul : (2 ^ k * m) % 3 = 2 ^ k % 3 * (m % 3) % 3 := Nat.mul_mod _ _ 3
  have hpar := two_pow_mod_three k
  have hm3 : m % 3 < 3 := Nat.mod_lt m (by omega)
  rcases Nat.eq_zero_or_pos (k % 2) with hke | hko
  · rw [hpar.1 hke] at hmul
    omega
  · have hk1 : k % 2 = 1 := by omega
    rw [hpar.2 hk1] at hmul
    omega

/-- **Every odd `m` not divisible by three has arbitrarily large valuations
available**, hence infinitely many predecessors. -/
theorem exists_pred_large {m : Nat} (hm : m % 2 = 1) (h3 : m % 3 ≠ 0) (B : Nat) :
    ∃ k n : Nat, B < k ∧ OddStep n k m := by
  have hm3 : m % 3 < 3 := Nat.mod_lt m (by omega)
  rcases Nat.lt_or_ge (m % 3) 2 with hlt | hge
  · obtain ⟨n, hn⟩ : ∃ n, OddStep n (2 * B + 2) m :=
      (pred_valuation_parity hm (by omega)).mpr (Or.inl ⟨by omega, by omega⟩)
    exact ⟨2 * B + 2, n, by omega, hn⟩
  · obtain ⟨n, hn⟩ : ∃ n, OddStep n (2 * B + 1) m :=
      (pred_valuation_parity hm (by omega)).mpr (Or.inr ⟨by omega, by omega⟩)
    exact ⟨2 * B + 1, n, by omega, hn⟩

/-- **The image of the odd map, exactly.**  An `m` has a predecessor precisely
when it is odd and not a multiple of three.  So the odd map is onto the odd
integers coprime to `3`, and misses the rest. -/
theorem exists_pred_iff_image {m : Nat} :
    (∃ n k : Nat, OddStep n k m) ↔ (m % 2 = 1 ∧ m % 3 ≠ 0) := by
  constructor
  · rintro ⟨n, k, hstep⟩
    refine ⟨hstep.2.1, ?_⟩
    intro h3
    exact no_pred_of_three_dvd h3 k ⟨n, hstep⟩
  · rintro ⟨hm, h3⟩
    obtain ⟨k, n, _, hstep⟩ := exists_pred_large hm h3 0
    exact ⟨n, k, hstep⟩

/-! ### The predecessors of `1`

`1 ≡ 1 (mod 3)`, so its predecessors carry even valuations `2j`, and solving
`2^{2j} = 3n + 1` gives the base-4 repunits `1, 5, 21, 85, …`. -/

/-- `(4^j − 1)/3 = 1 + 4 + ⋯ + 4^{j-1}`. -/
def predOne (j : Nat) : Nat := (4 ^ j - 1) / 3

theorem four_pow_mod_three (j : Nat) : 4 ^ j % 3 = 1 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Nat.pow_succ]; omega

theorem four_pow_pos (j : Nat) : 0 < 4 ^ j := pow_pos_of_pos (by omega) j

theorem three_mul_predOne (j : Nat) : 3 * predOne j + 1 = 4 ^ j := by
  have h := four_pow_mod_three j
  have hp := four_pow_pos j
  unfold predOne
  omega

theorem predOne_odd {j : Nat} (hj : 1 ≤ j) : predOne j % 2 = 1 := by
  have h := three_mul_predOne j
  have heven : 4 ^ j % 2 = 0 := by
    obtain ⟨t, ht⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
    subst ht
    have : (4 : Nat) ^ (t + 1) = 4 ^ t * 4 := Nat.pow_succ 4 t
    omega
  omega

/-- **The infinite family of predecessors of `1`.**  For every `j ≥ 1`,
`(4^j − 1)/3` steps to `1` with valuation `2j`: `1, 5, 21, 85, …`. -/
theorem oddStep_predOne {j : Nat} (hj : 1 ≤ j) : OddStep (predOne j) (2 * j) 1 := by
  refine ⟨by omega, by decide, ?_⟩
  have hpow : (2 : Nat) ^ (2 * j) = 4 ^ j := by rw [Nat.pow_mul]
  rw [hpow, Nat.mul_one]
  exact (three_mul_predOne j).symm

theorem predOne_values : (predOne 1, predOne 2, predOne 3, predOne 4) = (1, 5, 21, 85) := by
  decide

/-- Worked instances.  `11 ≡ 2 (mod 3)` so its predecessors use odd valuations —
`7` at `k = 1`.  `9` is a multiple of three, so it has no predecessor at all. -/
theorem pred_examples :
    OddStep 7 1 11 ∧ (¬ ∃ n, OddStep n 5 9) ∧ (¬ ∃ n, OddStep n 6 9) :=
  ⟨⟨by omega, by decide, by decide⟩,
   no_pred_of_three_dvd (by decide) 5,
   no_pred_of_three_dvd (by decide) 6⟩

/-! ## Trajectories

A trajectory is carried by two functions `n, k : Nat → Nat`; `Traj n k L` says
the first `L` steps are legitimate.  `Ksum k L = k 0 + ⋯ + k (L-1)` is the total
number of halvings, written `K_L` in the notes. -/

/-- Total halving count over the first `L` steps. -/
def Ksum (k : Nat → Nat) : Nat → Nat
  | 0 => 0
  | L + 1 => Ksum k L + k L

@[simp] theorem Ksum_zero (k : Nat → Nat) : Ksum k 0 = 0 := rfl

@[simp] theorem Ksum_succ (k : Nat → Nat) (L : Nat) :
    Ksum k (L + 1) = Ksum k L + k L := rfl

/-- `Traj n k L` : the first `L` odd steps of `n` are legitimate with
valuations `k`. -/
def Traj (n k : Nat → Nat) (L : Nat) : Prop :=
  ∀ i : Nat, i < L → OddStep (n i) (k i) (n (i + 1))

theorem Traj.le {n k : Nat → Nat} {L L' : Nat} (h : Traj n k L) (hle : L' ≤ L) :
    Traj n k L' := fun i hi => h i (by omega)

/-- **The exact affine identity.**  `2^{K_L}·n_L = 3^L·n_0 + b` with `b ≥ 1`
once at least one step has been taken. -/
theorem traj_affine {n k : Nat → Nat} : ∀ L : Nat, Traj n k L →
    ∃ b : Nat, (0 < L → 1 ≤ b) ∧ 2 ^ Ksum k L * n L = 3 ^ L * n 0 + b := by
  intro L
  induction L with
  | zero =>
    intro _
    exact ⟨0, by omega, by simp⟩
  | succ L ih =>
    intro htraj
    obtain ⟨b, _, hb⟩ := ih (htraj.le (by omega))
    have hstep := (htraj L (by omega)).2.2
    have hpow : 0 < 2 ^ Ksum k L := two_pow_pos _
    refine ⟨3 * b + 2 ^ Ksum k L, by omega, ?_⟩
    calc 2 ^ Ksum k (L + 1) * n (L + 1)
        = 2 ^ Ksum k L * (2 ^ k L * n (L + 1)) := by
          rw [Ksum_succ, Nat.pow_add, Nat.mul_assoc]
      _ = 2 ^ Ksum k L * (3 * n L + 1) := by rw [hstep]
      _ = 3 * (2 ^ Ksum k L * n L) + 2 ^ Ksum k L := by
          rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
      _ = 3 * (3 ^ L * n 0 + b) + 2 ^ Ksum k L := by rw [hb]
      _ = 3 ^ (L + 1) * n 0 + (3 * b + 2 ^ Ksum k L) := by
          rw [Nat.pow_succ, Nat.mul_add, Nat.mul_comm (3 ^ L) 3, Nat.mul_assoc]
          omega

/-- **The exact product estimate.**  If every visited value is at least `N`,
then `2^{K_L}·N^L·n_L ≤ (3N+1)^L·n_0`.  This is the `Nat` form of
`K_L·log 2 ≤ L·log(3 + 1/N) + log(n_0/n_L)`. -/
theorem traj_product {n k : Nat → Nat} {N : Nat} : ∀ L : Nat, Traj n k L →
    (∀ i : Nat, i < L → N ≤ n i) →
    2 ^ Ksum k L * (N ^ L * n L) ≤ (3 * N + 1) ^ L * n 0 := by
  intro L
  induction L with
  | zero => intro _ _; simp
  | succ L ih =>
    intro htraj hmin
    have hIH := ih (htraj.le (by omega)) (fun i hi => hmin i (by omega))
    have hstep := (htraj L (by omega)).2.2
    have hNL : N ≤ n L := hmin L (by omega)
    -- `N·(3·n L + 1) ≤ n L·(3N + 1)`
    have hkey : N * (3 * n L + 1) ≤ n L * (3 * N + 1) := by
      have h1 : N * (3 * n L + 1) = 3 * (N * n L) + N := by
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
      have h2 : n L * (3 * N + 1) = 3 * (N * n L) + n L := by
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm, Nat.mul_comm N (n L),
          Nat.mul_left_comm]
      omega
    calc 2 ^ Ksum k (L + 1) * (N ^ (L + 1) * n (L + 1))
        = 2 ^ Ksum k L * (N ^ L * (N * (2 ^ k L * n (L + 1)))) := by
          rw [Ksum_succ, Nat.pow_add, Nat.pow_succ]
          simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      _ = 2 ^ Ksum k L * (N ^ L * (N * (3 * n L + 1))) := by rw [hstep]
      _ ≤ 2 ^ Ksum k L * (N ^ L * (n L * (3 * N + 1))) := by
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hkey)
      _ = (2 ^ Ksum k L * (N ^ L * n L)) * (3 * N + 1) := by
          simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      _ ≤ ((3 * N + 1) ^ L * n 0) * (3 * N + 1) := Nat.mul_le_mul_right _ hIH
      _ = (3 * N + 1) ^ (L + 1) * n 0 := by
          rw [Nat.pow_succ]
          simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]

/-! ## The additive accumulator

`Sacc k L = ∑_{i=1}^{L} 3^{L-i}·2^{K_{i-1}}` is the exact remainder in the affine
identity.  Its lower bound `3^L ≤ Sacc + 2^L` is the `Nat` form of
`S ≥ 3^L − 2^L`, and it is what forces a cycle with small least element to have
`2^K/3^L` bounded away from `1`. -/

/-- The additive accumulator of the odd map. -/
def Sacc (k : Nat → Nat) : Nat → Nat
  | 0 => 0
  | L + 1 => 3 * Sacc k L + 2 ^ Ksum k L

@[simp] theorem Sacc_zero (k : Nat → Nat) : Sacc k 0 = 0 := rfl

@[simp] theorem Sacc_succ (k : Nat → Nat) (L : Nat) :
    Sacc k (L + 1) = 3 * Sacc k L + 2 ^ Ksum k L := rfl

/-- **The affine identity with the remainder computed.** -/
theorem traj_affine_exact {n k : Nat → Nat} : ∀ L : Nat, Traj n k L →
    2 ^ Ksum k L * n L = 3 ^ L * n 0 + Sacc k L := by
  intro L
  induction L with
  | zero => intro _; simp
  | succ L ih =>
    intro htraj
    have hIH := ih (htraj.le (by omega))
    have hstep := (htraj L (by omega)).2.2
    calc 2 ^ Ksum k (L + 1) * n (L + 1)
        = 2 ^ Ksum k L * (2 ^ k L * n (L + 1)) := by
          rw [Ksum_succ, Nat.pow_add, Nat.mul_assoc]
      _ = 2 ^ Ksum k L * (3 * n L + 1) := by rw [hstep]
      _ = 3 * (2 ^ Ksum k L * n L) + 2 ^ Ksum k L := by
          rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
      _ = 3 * (3 ^ L * n 0 + Sacc k L) + 2 ^ Ksum k L := by rw [hIH]
      _ = 3 ^ (L + 1) * n 0 + Sacc k (L + 1) := by
          rw [Nat.pow_succ, Nat.mul_comm (3 ^ L) 3, Nat.mul_assoc, Sacc_succ]
          omega

/-- Every step halves at least once, so `K_L ≥ L`. -/
theorem Ksum_ge {k : Nat → Nat} : ∀ L : Nat, (∀ i : Nat, i < L → 1 ≤ k i) →
    L ≤ Ksum k L := by
  intro L
  induction L with
  | zero => intro _; exact Nat.le_refl _
  | succ L ih =>
    intro hk
    have h1 := ih (fun i hi => hk i (by omega))
    have h2 := hk L (by omega)
    rw [Ksum_succ]
    omega

/-- **`S ≥ 3^L − 2^L`**, written without truncated subtraction. -/
theorem Sacc_lower {k : Nat → Nat} : ∀ L : Nat, (∀ i : Nat, i < L → 1 ≤ k i) →
    3 ^ L ≤ Sacc k L + 2 ^ L := by
  intro L
  induction L with
  | zero => intro _; simp
  | succ L ih =>
    intro hk
    have hIH := ih (fun i hi => hk i (by omega))
    have hKL : L ≤ Ksum k L := Ksum_ge L (fun i hi => hk i (by omega))
    have hpow : 2 ^ L ≤ 2 ^ Ksum k L := Nat.pow_le_pow_right (by omega) hKL
    have h3 : (3 : Nat) ^ (L + 1) = 3 * 3 ^ L := by
      rw [Nat.pow_succ, Nat.mul_comm]
    have h2 : (2 : Nat) ^ (L + 1) = 2 * 2 ^ L := two_pow_succ L
    rw [Sacc_succ, h3, h2]
    omega

/-- The valuations along a trajectory are all at least `1`. -/
theorem Traj.one_le {n k : Nat → Nat} {L : Nat} (h : Traj n k L) :
    ∀ i : Nat, i < L → 1 ≤ k i := fun i hi => (h i hi).1

/-! ## The valuation prefix is determined by a residue (Lemma 2.4)

Terras's parity-vector lemma, in the odd-map form: the first `L` valuations of
`n` depend only on `n` modulo `2^{K+1}`, where `K` is their sum.  Equivalently,
each admissible valuation vector picks out (at most) one residue class. -/

/-- Congruence mod a power of two passes to smaller powers. -/
theorem mod_pow_le {a b p q : Nat} (hq : q ≤ p) (h : a % 2 ^ p = b % 2 ^ p) :
    a % 2 ^ q = b % 2 ^ q := by
  have hdvd : (2 : Nat) ^ q ∣ 2 ^ p := Nat.pow_dvd_pow 2 hq
  rw [← Nat.mod_mod_of_dvd a hdvd, ← Nat.mod_mod_of_dvd b hdvd, h]

/-- `n ↦ 3n+1` respects congruences. -/
theorem three_congr {M a b : Nat} (h : a % M = b % M) :
    (3 * a + 1) % M = (3 * b + 1) % M := by
  rw [mod_three_shift M a, mod_three_shift M b, h]

/-- Cancelling a common factor `2^a` from a congruence mod `2^{a+b}`. -/
theorem two_pow_cancel_mod {a b x y : Nat}
    (h : (2 ^ a * x) % 2 ^ (a + b) = (2 ^ a * y) % 2 ^ (a + b)) :
    x % 2 ^ b = y % 2 ^ b := by
  rw [Nat.pow_add, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left] at h
  exact Nat.eq_of_mul_eq_mul_left (two_pow_pos a) h

/-- **Lemma 2.4 (determinacy).**  Two trajectories whose starting points agree
modulo `2^{K+R+1}`, where `K` is the total valuation of the first, have the same
valuations for `L` steps, and their `L`-th iterates still agree modulo `2^{R+1}`.

Taking `R = 0`: the valuation vector of length `L` is a function of
`n mod 2^{K+1}` alone. -/
theorem traj_congr : ∀ (L : Nat) (n k n' k' : Nat → Nat) (R : Nat),
    Traj n k L → Traj n' k' L →
    n 0 % 2 ^ (Ksum k L + R + 1) = n' 0 % 2 ^ (Ksum k L + R + 1) →
    (∀ i : Nat, i < L → k i = k' i) ∧ n L % 2 ^ (R + 1) = n' L % 2 ^ (R + 1) := by
  intro L
  induction L with
  | zero =>
    intro n k n' k' R _ _ hcong
    rw [Ksum_zero, Nat.zero_add] at hcong
    exact ⟨fun i hi => absurd hi (by omega), hcong⟩
  | succ L ih =>
    intro n k n' k' R htraj htraj' hcong
    rw [show Ksum k (L + 1) + R + 1 = Ksum k L + (k L + R) + 1 by rw [Ksum_succ]; omega]
      at hcong
    obtain ⟨hprefix, hmid⟩ :=
      ih n k n' k' (k L + R) (htraj.le (by omega)) (htraj'.le (by omega)) hcong
    have hstep := htraj L (by omega)
    have hstep' := htraj' L (by omega)
    -- the next valuation is read off a residue, so it is the same for both
    have hsmall : n L % 2 ^ (k L + 1) = n' L % 2 ^ (k L + 1) :=
      mod_pow_le (by omega) hmid
    have hrk : n L % 2 ^ (k L + 1) = rk (k L) :=
      (oddStep_iff_rk hstep.1).mp ⟨n (L + 1), hstep⟩
    have hex' : ∃ m, OddStep (n' L) (k L) m :=
      (oddStep_iff_rk hstep.1).mpr (by rw [← hsmall, hrk])
    obtain ⟨m', hm'⟩ := hex'
    have hkeq : k L = k' L := (oddStep_unique hm' hstep').1
    refine ⟨fun i hi => ?_, ?_⟩
    · rcases Nat.lt_or_ge i L with hlt | hge
      · exact hprefix i hlt
      · have : i = L := by omega
        rw [this]; exact hkeq
    · -- cancel `2^{k L}` from the step equations
      have e1 : 2 ^ k L * n (L + 1) = 3 * n L + 1 := hstep.2.2
      have e2 : 2 ^ k L * n' (L + 1) = 3 * n' L + 1 := by
        rw [hkeq]; exact hstep'.2.2
      have hcg : (3 * n L + 1) % 2 ^ (k L + (R + 1))
          = (3 * n' L + 1) % 2 ^ (k L + (R + 1)) := by
        refine three_congr ?_
        rw [show k L + (R + 1) = k L + R + 1 by omega]
        exact hmid
      rw [← e1, ← e2] at hcg
      exact two_pow_cancel_mod hcg

/-- **The valuation vector is a function of the residue.**  `R = 0` case. -/
theorem valuations_determined {n k n' k' : Nat → Nat} {L : Nat}
    (htraj : Traj n k L) (htraj' : Traj n' k' L)
    (h : n 0 % 2 ^ (Ksum k L + 1) = n' 0 % 2 ^ (Ksum k L + 1)) :
    ∀ i : Nat, i < L → k i = k' i :=
  (traj_congr L n k n' k' 0 htraj htraj' (by rw [Nat.add_zero] at *; exact h)).1

/-- A whole trajectory of `L` odd steps is `K_L` Terras steps. -/
theorem traj_acceleratedOrbit {n k : Nat → Nat} : ∀ L : Nat, Traj n k L →
    n 0 % 2 = 1 → acceleratedOrbit (Ksum k L) (n 0) = n L := by
  intro L
  induction L with
  | zero => intro _ _; simp
  | succ L ih =>
    intro htraj hodd
    have hIH := ih (htraj.le (by omega)) hodd
    have hstep := htraj L (by omega)
    have hoddL : n L % 2 = 1 := by
      rcases Nat.eq_zero_or_pos L with hL | hL
      · rw [hL]; exact hodd
      · obtain ⟨M, hM⟩ : ∃ M, L = M + 1 := ⟨L - 1, by omega⟩
        have h := htraj M (by omega)
        rw [← hM] at h
        exact h.2.1
    rw [Ksum_succ, ← Nat.add_comm (k L) (Ksum k L), ← acceleratedOrbit_add, hIH]
    exact oddStep_acceleratedOrbit hoddL hstep

/-- The odd-map orbit of `7`, the leading example of Rozier-Terracol: valuations
`1, 1, 2, 3, 4` summing to `11`, and indeed `T^11(7) = 1` on the Terras clock
(`Collatz.Strategy.Paradoxical` reads the same orbit at `T^8(7) = 8`). -/
theorem oddOrbit_seven :
    OddStep 7 1 11 ∧ OddStep 11 1 17 ∧ OddStep 17 2 13 ∧ OddStep 13 3 5 ∧
      OddStep 5 4 1 := by
  refine ⟨⟨by omega, by decide, by decide⟩, ⟨by omega, by decide, by decide⟩,
    ⟨by omega, by decide, by decide⟩, ⟨by omega, by decide, by decide⟩,
    ⟨by omega, by decide, by decide⟩⟩

theorem acceleratedOrbit_seven : acceleratedOrbit 11 7 = 1 := by decide

/-! ## A computable odd map

Everything above is relational: `OddStep` is a graph, not a function.  That is
convenient for proofs but means nothing can be evaluated.  This section supplies
the function, with `stripTwos` peeling the powers of two, and proves it realizes
`OddStep`.  With it, trajectories exist constructively — no choice principle is
needed to iterate. -/

/-- `stripTwos f x = (k, m)` with `x = 2^k · m` and `m` odd, given enough fuel. -/
def stripTwos : Nat → Nat → Nat × Nat
  | 0, x => (0, x)
  | f + 1, x =>
      if x % 2 = 1 then (0, x)
      else ((stripTwos f (x / 2)).1 + 1, (stripTwos f (x / 2)).2)

theorem stripTwos_spec : ∀ f x : Nat, x ≤ f → 0 < x →
    (stripTwos f x).2 % 2 = 1 ∧ 2 ^ (stripTwos f x).1 * (stripTwos f x).2 = x := by
  intro f
  induction f with
  | zero => intro x hx hpos; omega
  | succ f ih =>
    intro x hx hpos
    rcases Nat.eq_zero_or_pos (x % 2) with heven | hodd
    · have hhalf : 0 < x / 2 := by omega
      have hle : x / 2 ≤ f := by omega
      obtain ⟨h1, h2⟩ := ih (x / 2) hle hhalf
      rw [stripTwos, if_neg (by omega)]
      refine ⟨h1, ?_⟩
      rw [two_pow_succ, Nat.mul_assoc, h2]
      omega
    · rw [stripTwos, if_pos (by omega)]
      exact ⟨by omega, by simp⟩

/-- The valuation `v₂(3n+1)`, computably. -/
def oddK (n : Nat) : Nat := (stripTwos (3 * n + 1) (3 * n + 1)).1

/-- The odd map `T(n) = (3n+1)/2^{v₂(3n+1)}`, computably. -/
def oddT (n : Nat) : Nat := (stripTwos (3 * n + 1) (3 * n + 1)).2

/-- **The function realizes the relation.** -/
theorem oddStep_oddT {n : Nat} (hn : n % 2 = 1) : OddStep n (oddK n) (oddT n) := by
  obtain ⟨hm, heq⟩ := stripTwos_spec (3 * n + 1) (3 * n + 1) (Nat.le_refl _) (by omega)
  refine ⟨?_, hm, heq⟩
  rcases Nat.eq_zero_or_pos (stripTwos (3 * n + 1) (3 * n + 1)).1 with h0 | hpos
  · exfalso
    rw [h0, Nat.pow_zero, Nat.one_mul] at heq
    omega
  · exact hpos

theorem oddT_odd {n : Nat} (hn : n % 2 = 1) : oddT n % 2 = 1 := (oddStep_oddT hn).2.1

/-- Iterating the computable odd map. -/
def oddOrbit : Nat → Nat → Nat
  | 0, n => n
  | L + 1, n => oddOrbit L (oddT n)

@[simp] theorem oddOrbit_zero (n : Nat) : oddOrbit 0 n = n := rfl

theorem oddOrbit_succ_step : ∀ L n : Nat, oddOrbit (L + 1) n = oddT (oddOrbit L n) := by
  intro L
  induction L with
  | zero => intro n; rfl
  | succ L ih => intro n; rw [oddOrbit, ih (oddT n)]; rfl

theorem oddOrbit_odd {n : Nat} (hn : n % 2 = 1) : ∀ L : Nat, oddOrbit L n % 2 = 1 := by
  intro L
  induction L with
  | zero => exact hn
  | succ L ih => rw [oddOrbit_succ_step]; exact oddT_odd ih

/-- **Trajectories exist, constructively.**  Every odd `n` carries a trajectory
of every length, given by the computable orbit and its valuations. -/
theorem exists_traj {n : Nat} (hn : n % 2 = 1) (L : Nat) :
    Traj (fun i => oddOrbit i n) (fun i => oddK (oddOrbit i n)) L := by
  intro i _
  have h := oddStep_oddT (oddOrbit_odd hn i)
  rw [← oddOrbit_succ_step i n] at h
  exact h

set_option maxRecDepth 8000 in
/-- With a computable map the orbits can simply be evaluated.  `27`, the classic
long-running start, needs `41` odd-map steps to reach `1`. -/
theorem oddOrbit_twentyseven : oddOrbit 41 27 = 1 ∧ oddT 27 = 41 ∧ oddK 27 = 1 := by decide

/-- The computable map on the Rozier–Terracol example. -/
theorem oddT_seven :
    (oddT 7, oddT 11, oddT 17, oddT 13, oddT 5) = (11, 17, 13, 5, 1) ∧
      (oddK 7, oddK 11, oddK 17, oddK 13, oddK 5) = (1, 1, 2, 3, 4) := by decide

/-! ## A bounded least-witness search

Used below to compute stopping times.  `firstSuch p f m` returns the least
`j ≥ m` with `p j`, searching `f` steps, or `0` if none is found. -/

def firstSuch (p : Nat → Bool) : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, m => if p m then m else firstSuch p f (m + 1)

theorem firstSuch_found (p : Nat → Bool) : ∀ f m : Nat,
    firstSuch p f m ≠ 0 → p (firstSuch p f m) = true ∧ m ≤ firstSuch p f m := by
  intro f
  induction f with
  | zero => intro m h; simp [firstSuch] at h
  | succ f ih =>
    intro m h
    by_cases hp : p m = true
    · rw [firstSuch, if_pos hp]
      exact ⟨hp, Nat.le_refl _⟩
    · rw [firstSuch, if_neg hp] at h ⊢
      obtain ⟨h1, h2⟩ := ih (m + 1) h
      exact ⟨h1, by omega⟩

theorem firstSuch_minimal (p : Nat → Bool) : ∀ f m j : Nat,
    m ≤ j → j < firstSuch p f m → p j = false := by
  intro f
  induction f with
  | zero => intro m j _ hj; simp [firstSuch] at hj
  | succ f ih =>
    intro m j hmj hj
    by_cases hp : p m = true
    · rw [firstSuch, if_pos hp] at hj; omega
    · rw [firstSuch, if_neg hp] at hj
      rcases Nat.eq_or_lt_of_le hmj with heq | hlt
      · rw [← heq]; simpa using hp
      · exact ih (m + 1) j (by omega) hj

/-! ## Terras's elementary inequality, and the relation to `CoefficientStopping`

`Collatz.Strategy.CoefficientStopping` works with the *same* odd-to-odd map, but
supplies the bookkeeping sequences `S` (partial valuation sums) and `b` (the
accumulator) as hypotheses rather than defining them.  The correspondence is:

| there | here |
|---|---|
| `S` with `S 0 = 0`, `S (m+1) = S m + k m` | `Ksum k` (`Ksum_zero`, `Ksum_succ`) |
| `b` with `b 0 = 0`, `b (m+1) = 3·b m + 2^{S m}` | `Sacc k` (`Sacc_zero`, `Sacc_succ`) |
| `hrec : n (i+1) · 2^{k i} = 3·n i + 1` | `OddStep (n i) (k i) (n (i+1))` |
| `orbit_identity` | `traj_affine_exact` |
| `cycle_coeff_gt` | `cycle_three_pow_lt` |
| `no_drop_of_coeff_le` | `traj_no_drop_of_coeff_le`, below |

The two modules are therefore about the same objects; the difference is only
that `Traj` bundles the recurrence with `k ≥ 1` and oddness, and holds on a
bounded range rather than for all `i`.  Nothing is imported across, so neither
depends on the other. -/

/-- **Terras's elementary inequality, odd clock.**  While the coefficient has
not exceeded — `2^{K_L} ≤ 3^L` — the orbit has not dropped: `n₀ < n_L`.  The
strictness comes from the accumulator being positive once a step has been
taken.  This is `σ ≥ κ`. -/
theorem traj_no_drop_of_coeff_le {n k : Nat → Nat} {L : Nat} (hL : 0 < L)
    (htraj : Traj n k L) (hcoef : 2 ^ Ksum k L ≤ 3 ^ L) : n 0 < n L := by
  obtain ⟨b, hb1, hb2⟩ := traj_affine L htraj
  have hb := hb1 hL
  have hmul : 2 ^ Ksum k L * n 0 ≤ 3 ^ L * n 0 := Nat.mul_le_mul_right _ hcoef
  rcases Nat.lt_or_ge (n 0) (n L) with hlt | hge
  · exact hlt
  · exfalso
    have hcontra : 2 ^ Ksum k L * n L ≤ 2 ^ Ksum k L * n 0 := Nat.mul_le_mul_left _ hge
    omega

/-- **The contrapositive.**  Any stretch that fails to end strictly above its
start has already made the coefficient exceed.  `cycle_three_pow_lt` is the
special case `n_L = n₀`, and `noDescent`-style hypotheses are the case
`n_L ≤ n₀`. -/
theorem coeff_gt_of_no_rise {n k : Nat → Nat} {L : Nat} (hL : 0 < L)
    (htraj : Traj n k L) (hdrop : n L ≤ n 0) : 3 ^ L < 2 ^ Ksum k L := by
  rcases Nat.lt_or_ge (3 ^ L) (2 ^ Ksum k L) with hlt | hge
  · exact hlt
  · exact absurd (traj_no_drop_of_coeff_le hL htraj hge) (by omega)

/-- The packaged form: if the coefficient has not exceeded anywhere up to `L`,
the orbit has not dropped anywhere up to `L`.  This is `σ ≥ κ` as an inequality
between the two stopping times. -/
theorem no_drop_before_coeff {n k : Nat → Nat} {L : Nat} (htraj : Traj n k L)
    (hcoef : ∀ j : Nat, 0 < j → j ≤ L → 2 ^ Ksum k j ≤ 3 ^ j) :
    ∀ j : Nat, 0 < j → j ≤ L → n 0 < n j :=
  fun j hj hjL =>
    traj_no_drop_of_coeff_le hj (htraj.le hjL) (hcoef j hj hjL)

/-! ## Towards realization: solving `3x ≡ c` and moving along a residue class

The determinacy half of Lemma 2.4 (`traj_congr`) says the valuation vector is a
function of `n mod 2^{K+1}`.  The realization half — that every vector actually
occurs — needs two ingredients: that `3` is invertible modulo powers of two, and
that every odd number congruent to a realizer is itself a realizer. -/

/-- **`3` is invertible mod `2^m`.**  The step is the observation that of `t` and
`t + 3` exactly one is even, so `x` or `x + 2^m` lifts the solution. -/
theorem three_solve : ∀ m c : Nat, ∃ x t : Nat, 3 * x = c + 2 ^ m * t := by
  intro m
  induction m with
  | zero =>
    intro c
    refine ⟨c, 2 * c, ?_⟩
    rw [Nat.pow_zero, Nat.one_mul]
    omega
  | succ m ih =>
    intro c
    obtain ⟨x, t, hxt⟩ := ih c
    rcases Nat.eq_zero_or_pos (t % 2) with heven | hodd
    · obtain ⟨s, hs⟩ : ∃ s, t = 2 * s := ⟨t / 2, by omega⟩
      refine ⟨x, s, ?_⟩
      rw [two_pow_succ]
      have h1 : 2 ^ m * t = 2 * 2 ^ m * s := by
        rw [hs]
        simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      omega
    · obtain ⟨s, hs⟩ : ∃ s, t + 3 = 2 * s := ⟨(t + 3) / 2, by omega⟩
      refine ⟨x + 2 ^ m, s, ?_⟩
      rw [two_pow_succ]
      have h1 : 2 ^ m * t + 3 * 2 ^ m = 2 ^ m * (t + 3) := by
        rw [Nat.mul_add]
        simp [Nat.mul_comm]
      have h2 : 2 ^ m * (t + 3) = 2 * 2 ^ m * s := by
        rw [hs]
        simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      have h3 : 3 * (x + 2 ^ m) = 3 * x + 3 * 2 ^ m := by rw [Nat.mul_add]
      omega

/-- **Every odd number congruent to a realizer is a realizer.**  Combining
`exists_traj` (a trajectory exists from any odd start) with `traj_congr` (its
valuations are forced by the residue), the set of starts realizing a given
valuation vector is closed under moving within its class mod `2^{K+1}`. -/
theorem oddK_of_congr {n0' : Nat} {n k : Nat → Nat} {L : Nat}
    (htraj : Traj n k L) (hodd' : n0' % 2 = 1)
    (hcong : n 0 % 2 ^ (Ksum k L + 1) = n0' % 2 ^ (Ksum k L + 1)) :
    ∀ i : Nat, i < L → oddK (oddOrbit i n0') = k i := by
  intro i hi
  have hres := valuations_determined htraj (exists_traj hodd' L) (by simpa using hcong)
  exact (hres i hi).symm

/-- `Ksum` only depends on the valuations actually used. -/
theorem Ksum_congr {k k' : Nat → Nat} : ∀ L : Nat, (∀ i : Nat, i < L → k i = k' i) →
    Ksum k L = Ksum k' L := by
  intro L
  induction L with
  | zero => intro _; rfl
  | succ L ih =>
    intro h
    rw [Ksum_succ, Ksum_succ, ih (fun i hi => h i (by omega)), h L (by omega)]

/-- A residue class modulo a power of two meets every class modulo `3`. -/
theorem exists_shift_mod_three (m0 t c : Nat) :
    ∃ s : Nat, (m0 + 2 ^ t * s) % 3 = c % 3 := by
  have hpow := two_pow_mod_three_ne t
  rcases hpow with h1 | h2
  · refine ⟨(c + 2 * m0) % 3, ?_⟩
    have hadd : (m0 + 2 ^ t * ((c + 2 * m0) % 3)) % 3
        = (m0 % 3 + 2 ^ t * ((c + 2 * m0) % 3) % 3) % 3 := Nat.add_mod _ _ 3
    have hmul : 2 ^ t * ((c + 2 * m0) % 3) % 3
        = 2 ^ t % 3 * ((c + 2 * m0) % 3 % 3) % 3 := Nat.mul_mod _ _ 3
    rw [h1] at hmul
    omega
  · refine ⟨(2 * c + m0) % 3, ?_⟩
    have hadd : (m0 + 2 ^ t * ((2 * c + m0) % 3)) % 3
        = (m0 % 3 + 2 ^ t * ((2 * c + m0) % 3) % 3) % 3 := Nat.add_mod _ _ 3
    have hmul : 2 ^ t * ((2 * c + m0) % 3) % 3
        = 2 ^ t % 3 * ((2 * c + m0) % 3 % 3) % 3 := Nat.mul_mod _ _ 3
    rw [h2] at hmul
    omega

/-- **A predecessor can be found landing anywhere in a prescribed class.**  Given
odd `m0` and a valuation `a0 ≥ 1`, some odd `m1` congruent to `m0` mod `2^{t+1}`
has a predecessor with valuation exactly `a0`.  The freedom to slide along the
class is what supplies the residue mod `3` that `exists_pred_iff` demands. -/
theorem exists_pred_in_class {m0 a0 : Nat} (hm0 : m0 % 2 = 1) (ha0 : 1 ≤ a0) (t : Nat) :
    ∃ n0 m1 : Nat, OddStep n0 a0 m1 ∧ m1 % 2 ^ (t + 1) = m0 % 2 ^ (t + 1) := by
  -- the residue mod 3 that makes a predecessor exist
  obtain ⟨c, hc⟩ : ∃ c : Nat, ∀ m1 : Nat, m1 % 3 = c % 3 → (2 ^ a0 * m1) % 3 = 1 := by
    rcases two_pow_mod_three_ne a0 with h1 | h1
    · refine ⟨1, fun m1 hm1 => ?_⟩
      have hmm := Nat.mul_mod (2 ^ a0) m1 3
      rw [h1] at hmm
      omega
    · refine ⟨2, fun m1 hm1 => ?_⟩
      have hmm := Nat.mul_mod (2 ^ a0) m1 3
      rw [h1] at hmm
      omega
  obtain ⟨s, hs⟩ := exists_shift_mod_three m0 (t + 1) c
  have hsplit : (2 : Nat) ^ (t + 1) = 2 * 2 ^ t := two_pow_succ t
  have hm1odd : (m0 + 2 ^ (t + 1) * s) % 2 = 1 := by
    rw [hsplit, Nat.mul_assoc]
    omega
  obtain ⟨n0, hn0⟩ : ∃ n0, OddStep n0 a0 (m0 + 2 ^ (t + 1) * s) :=
    (exists_pred_iff hm1odd ha0).mpr (hc _ hs)
  exact ⟨n0, m0 + 2 ^ (t + 1) * s, hn0, Nat.add_mul_mod_self_left _ _ _⟩

/-- **Realization: every admissible valuation vector occurs.**  For any
`(a₀, …, a_{L-1})` with each `a i ≥ 1` there is an odd `n₀` whose first `L`
valuations are exactly those.

With `traj_congr` (determinacy) this completes Lemma 2.4: the valuation vectors
of length `L` and the residue classes mod `2^{K+1}` correspond exactly. -/
theorem exists_realizer : ∀ (L : Nat) (a : Nat → Nat), (∀ i : Nat, i < L → 1 ≤ a i) →
    ∃ n0 : Nat, n0 % 2 = 1 ∧ ∀ i : Nat, i < L → oddK (oddOrbit i n0) = a i := by
  intro L
  induction L with
  | zero => intro a _; exact ⟨1, by decide, fun i hi => absurd hi (by omega)⟩
  | succ L ih =>
    intro a ha
    obtain ⟨m0, hm0odd, hm0⟩ := ih (fun i => a (i + 1)) (fun i hi => ha (i + 1) (by omega))
    have htail : Traj (fun i => oddOrbit i m0) (fun i => oddK (oddOrbit i m0)) L :=
      exists_traj hm0odd L
    obtain ⟨n0, m1, hstep, hclass⟩ :=
      exists_pred_in_class hm0odd (ha 0 (by omega))
        (Ksum (fun i => oddK (oddOrbit i m0)) L)
    have hn0odd : n0 % 2 = 1 := pred_odd hstep
    -- the computable map agrees with the chosen step
    obtain ⟨hkeq, hmeq⟩ := oddStep_unique (oddStep_oddT hn0odd) hstep
    have hm1odd : m1 % 2 = 1 := hstep.2.1
    -- the tail is realized from `m1` too, since it lies in `m0`'s class
    have htailm1 : ∀ i : Nat, i < L → oddK (oddOrbit i m1) = oddK (oddOrbit i m0) :=
      oddK_of_congr htail hm1odd hclass.symm
    refine ⟨n0, hn0odd, fun i hi => ?_⟩
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · rw [hi0]
      exact hkeq
    · obtain ⟨j, hj⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      subst hj
      have hstepj : oddOrbit (j + 1) n0 = oddOrbit j m1 := by
        rw [oddOrbit, hmeq]
      rw [hstepj, htailm1 j (by omega)]
      exact hm0 j (by omega)

/-- **Lemma 2.4, both halves.**  The valuation vectors of length `L` and the
residue classes they cut out correspond exactly:

* *determined* — two odd starts agreeing mod `2^{K+1}` have the same valuations
  (`valuations_determined`);
* *realized* — every vector `a` with `a i ≥ 1` is the valuation vector of some
  odd `n₀` (`exists_realizer`).

Together with `oddK_of_congr` (every odd start congruent to a realizer is itself
a realizer) this is Terras's parity-vector theorem on the odd clock. -/
theorem parity_vector_correspondence (L : Nat) (a : Nat → Nat)
    (ha : ∀ i : Nat, i < L → 1 ≤ a i) :
    (∃ n0 : Nat, n0 % 2 = 1 ∧ ∀ i : Nat, i < L → oddK (oddOrbit i n0) = a i) ∧
      (∀ n0 n0' : Nat, n0 % 2 = 1 → n0' % 2 = 1 →
        n0 % 2 ^ (Ksum (fun i => oddK (oddOrbit i n0)) L + 1)
          = n0' % 2 ^ (Ksum (fun i => oddK (oddOrbit i n0)) L + 1) →
        ∀ i : Nat, i < L → oddK (oddOrbit i n0') = oddK (oddOrbit i n0)) :=
  ⟨exists_realizer L a ha,
   fun n0 n0' hodd hodd' hcong => oddK_of_congr (exists_traj hodd L) hodd' hcong⟩

/-! ## Machine-checking the Coefficient Stopping Time conjecture on a range

`Collatz/Strategy/CoefficientStopping.lean` records that `σ(n) = κ(n)` was
checked for odd `n ≤ 10^9` — but as an *external* claim, not a proof.  With the
computable odd map the check can be run inside the kernel instead, on a smaller
range but with the result an actual theorem.

The easy half `σ ≥ κ` is `traj_no_drop_of_coeff_le`, unconditional.  What is
verified here is the hard half on the range. -/

/-- `T^m(n) < n`, decidably. -/
def dropAt (n m : Nat) : Bool := decide (oddOrbit m n < n)

/-- `3^m < 2^{K_m}`, decidably. -/
def coeffDropAt (n m : Nat) : Bool :=
  decide (3 ^ m < 2 ^ Ksum (fun i => oddK (oddOrbit i n)) m)

/-- The stopping time, searched with fuel; `0` means "not found". -/
def sigmaOdd (fuel n : Nat) : Nat := firstSuch (dropAt n) fuel 1

/-- The coefficient stopping time, searched with fuel. -/
def kappaOdd (fuel n : Nat) : Nat := firstSuch (coeffDropAt n) fuel 1

/-- `t` is the stopping time of `n` on the odd clock. -/
def OddStoppingTime (n t : Nat) : Prop :=
  1 ≤ t ∧ oddOrbit t n < n ∧ ∀ j : Nat, 1 ≤ j → j < t → ¬(oddOrbit j n < n)

/-- `t` is the coefficient stopping time of `n` on the odd clock. -/
def OddCoeffStoppingTime (n t : Nat) : Prop :=
  1 ≤ t ∧ 3 ^ t < 2 ^ Ksum (fun i => oddK (oddOrbit i n)) t ∧
    ∀ j : Nat, 1 ≤ j → j < t →
      ¬(3 ^ j < 2 ^ Ksum (fun i => oddK (oddOrbit i n)) j)

theorem sigmaOdd_spec {fuel n : Nat} (h : sigmaOdd fuel n ≠ 0) :
    OddStoppingTime n (sigmaOdd fuel n) := by
  obtain ⟨hp, hge⟩ := firstSuch_found (dropAt n) fuel 1 h
  refine ⟨hge, by simpa [dropAt, sigmaOdd] using hp, fun j hj hlt => ?_⟩
  have := firstSuch_minimal (dropAt n) fuel 1 j (by simpa [sigmaOdd] using hj)
    (by simpa [sigmaOdd] using hlt)
  simpa [dropAt] using this

theorem kappaOdd_spec {fuel n : Nat} (h : kappaOdd fuel n ≠ 0) :
    OddCoeffStoppingTime n (kappaOdd fuel n) := by
  obtain ⟨hp, hge⟩ := firstSuch_found (coeffDropAt n) fuel 1 h
  refine ⟨hge, by simpa [coeffDropAt, kappaOdd] using hp, fun j hj hlt => ?_⟩
  have := firstSuch_minimal (coeffDropAt n) fuel 1 j (by simpa [kappaOdd] using hj)
    (by simpa [kappaOdd] using hlt)
  simpa [coeffDropAt] using this

theorem oddStoppingTime_unique {n t t' : Nat}
    (h : OddStoppingTime n t) (h' : OddStoppingTime n t') : t = t' := by
  rcases Nat.lt_trichotomy t t' with hlt | heq | hgt
  · exact absurd h.2.1 (h'.2.2 t h.1 hlt)
  · exact heq
  · exact absurd h'.2.1 (h.2.2 t' h'.1 hgt)

theorem oddCoeffStoppingTime_unique {n t t' : Nat}
    (h : OddCoeffStoppingTime n t) (h' : OddCoeffStoppingTime n t') : t = t' := by
  rcases Nat.lt_trichotomy t t' with hlt | heq | hgt
  · exact absurd h.2.1 (h'.2.2 t h.1 hlt)
  · exact heq
  · exact absurd h'.2.1 (h.2.2 t' h'.1 hgt)

/-- The per-`n` check: both searches succeed and agree. -/
def cstCheck (fuel n : Nat) : Bool :=
  !(sigmaOdd fuel n == 0) && (sigmaOdd fuel n == kappaOdd fuel n)

/-- The check over every odd `n` with `2 ≤ n ≤ N`. -/
def cstUpTo (fuel N : Nat) : Bool :=
  (List.range (N + 1)).all fun n =>
    !(decide (2 ≤ n) && decide (n % 2 = 1)) || cstCheck fuel n

/-- **CST holds at every `n` the check covers.** -/
theorem cst_of_check {n fuel t τ : Nat} (hchk : cstCheck fuel n = true)
    (ht : OddStoppingTime n t) (hτ : OddCoeffStoppingTime n τ) : t = τ := by
  simp only [cstCheck, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, beq_eq_false_iff_ne]
    at hchk
  obtain ⟨hne, heq⟩ := hchk
  have hs := sigmaOdd_spec (fuel := fuel) (n := n) hne
  have hk := kappaOdd_spec (fuel := fuel) (n := n) (by omega)
  rw [← heq] at hk
  rw [oddStoppingTime_unique ht hs, oddCoeffStoppingTime_unique hτ hk]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 2000000 in
/-- The check passes for every odd `n` with `2 ≤ n ≤ 999`, with fuel `60`.

Larger ranges also pass — `cstUpTo 60 4999` takes about 28 s of kernel time —
and are omitted only to keep the build fast. -/
theorem cstUpTo_999 : cstUpTo 60 999 = true := by decide

/-- **Terras's Conjecture 2.9, machine-checked below 1000.**  For every odd
`n` with `2 ≤ n ≤ 999`, the stopping time and the coefficient stopping time
agree.

Unlike the `10^9` figure quoted in `Collatz.Strategy.CoefficientStopping`, which
is an external claim, this is a theorem: the search is run by the kernel and its
output is tied to the definitions by `sigmaOdd_spec` and `kappaOdd_spec`.  The
easy half `σ ≥ κ` is unconditional and separate (`traj_no_drop_of_coeff_le`);
what the range check supplies is the hard half. -/
theorem cst_below_1000 {n t τ : Nat} (h2 : 2 ≤ n) (hodd : n % 2 = 1) (hle : n ≤ 999)
    (ht : OddStoppingTime n t) (hτ : OddCoeffStoppingTime n τ) : t = τ := by
  have hmem : n ∈ List.range 1000 := List.mem_range.mpr (by omega)
  have hall := List.all_eq_true.mp cstUpTo_999 n hmem
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not, decide_eq_true_eq] at hall
  rcases hall with hbad | hchk
  · rcases hbad with h | h
    · exact absurd h2 h
    · exact absurd hodd h
  · exact cst_of_check hchk ht hτ

/-- **`κ ≤ σ` on the odd clock, unconditional.**  The coefficient stopping time
never exceeds the stopping time: a drop cannot happen before the coefficient has
exceeded.  This is `traj_no_drop_of_coeff_le` read at the computable orbit. -/
theorem oddCoeffStoppingTime_le {n t τ : Nat} (hodd : n % 2 = 1)
    (ht : OddStoppingTime n t) (hτ : OddCoeffStoppingTime n τ) : τ ≤ t := by
  rcases Nat.lt_or_ge t τ with hlt | hge
  · exfalso
    have hnc := hτ.2.2 t ht.1 hlt
    have hle : 2 ^ Ksum (fun i => oddK (oddOrbit i n)) t ≤ 3 ^ t := by omega
    have hrise := traj_no_drop_of_coeff_le ht.1 (exists_traj hodd t) hle
    simp only [oddOrbit_zero] at hrise
    have hdrop := ht.2.1
    omega
  · exact hge

/-- **The two halves side by side.**  `κ ≤ σ` costs nothing; `σ ≤ κ` is the
content of Terras's conjecture, and on `2 ≤ n ≤ 999` it is checked.

Keeping them separate is the point: the first conjunct holds for every `n`, the
second is exactly as strong as the range the kernel actually verified. -/
theorem cst_two_sided {n t τ : Nat} (hodd : n % 2 = 1) (h2 : 2 ≤ n) (hle : n ≤ 999)
    (ht : OddStoppingTime n t) (hτ : OddCoeffStoppingTime n τ) : τ ≤ t ∧ t = τ :=
  ⟨oddCoeffStoppingTime_le hodd ht hτ, cst_below_1000 h2 hodd hle ht hτ⟩

set_option maxRecDepth 100000 in
/-- Concrete stopping times on the odd clock, both times agreeing. -/
theorem stoppingTimes_examples :
    (sigmaOdd 60 7, kappaOdd 60 7) = (4, 4) ∧
    (sigmaOdd 60 27, kappaOdd 60 27) = (37, 37) ∧
    (sigmaOdd 60 703, kappaOdd 60 703) = (51, 51) := by decide

/-! ## Cycles -/

/-- **On a cycle the coefficient must have exceeded:** `3^L < 2^{K_L}`. -/
theorem cycle_three_pow_lt {n k : Nat → Nat} {L : Nat} (hL : 0 < L)
    (htraj : Traj n k L) (hcyc : n L = n 0) (_hpos : 0 < n 0) :
    3 ^ L < 2 ^ Ksum k L :=
  coeff_gt_of_no_rise hL htraj (by omega)

/-- **The cycle squeeze.**  If `N` is a lower bound for the elements of a cycle
(in particular its least element), then `2^{K_L}·N^L ≤ (3N+1)^L`.  Together with
`cycle_three_pow_lt` this is the exact `Nat` form of
`0 < K_L·log 2 − L·log 3 ≤ L/(3N)`. -/
theorem cycle_min_bound {n k : Nat → Nat} {L N : Nat}
    (htraj : Traj n k L) (hcyc : n L = n 0) (hpos : 0 < n 0)
    (hmin : ∀ i : Nat, i < L → N ≤ n i) :
    2 ^ Ksum k L * N ^ L ≤ (3 * N + 1) ^ L := by
  have hprod := traj_product L htraj hmin
  rw [hcyc] at hprod
  have hrw : 2 ^ Ksum k L * (N ^ L * n 0) = (2 ^ Ksum k L * N ^ L) * n 0 := by
    rw [Nat.mul_assoc]
  rw [hrw] at hprod
  exact Nat.le_of_mul_le_mul_right hprod hpos

/-- **The no-descent bound (Gap 8, finite form).**  A stretch of `L` steps that
ends no lower than it started, and never drops below `N`, satisfies
`2^{K_L}·N^L ≤ (3N+1)^L` — the mean valuation of the stretch is at most
`log₂(3 + 1/N)`. -/
theorem noDescent_product_bound {n k : Nat → Nat} {L N : Nat}
    (htraj : Traj n k L) (hnodrop : n 0 ≤ n L) (hposL : 0 < n L)
    (hmin : ∀ i : Nat, i < L → N ≤ n i) :
    2 ^ Ksum k L * N ^ L ≤ (3 * N + 1) ^ L := by
  have hprod := traj_product L htraj hmin
  have hstep : (3 * N + 1) ^ L * n 0 ≤ (3 * N + 1) ^ L * n L :=
    Nat.mul_le_mul_left _ hnodrop
  have hrw : 2 ^ Ksum k L * (N ^ L * n L) = (2 ^ Ksum k L * N ^ L) * n L := by
    rw [Nat.mul_assoc]
  rw [hrw] at hprod
  exact Nat.le_of_mul_le_mul_right (by omega) hposL

/-- **Small cycles force the coefficient far from `1`.**  Writing
`2^{K_L} = 3^L(1 + δ)`, the identity plus `S ≥ 3^L − 2^L` gives
`δ ≥ (1 − (2/3)^L)/n₀`; over `Nat`, with no subtraction:

  `3^L·(n₀ + 1) ≤ 2^{K_L}·n₀ + 2^L`.

So a cycle whose least element is small cannot have `2^{K_L}/3^L` near `1`; and
conversely a cycle with `2^{K_L}` barely above `3^L` must have a large least
element.  This is the half of the Diophantine squeeze that `cycle_min_bound`
does not supply. -/
theorem cycle_delta_lower {n k : Nat → Nat} {L : Nat}
    (htraj : Traj n k L) (hcyc : n L = n 0) :
    3 ^ L * (n 0 + 1) ≤ 2 ^ Ksum k L * n 0 + 2 ^ L := by
  have hid := traj_affine_exact L htraj
  rw [hcyc] at hid
  have hlow := Sacc_lower L htraj.one_le
  have hexp : 3 ^ L * (n 0 + 1) = 3 ^ L * n 0 + 3 ^ L := by
    rw [Nat.mul_add, Nat.mul_one]
  omega

/-- The same bound holds for *every* trajectory, cyclic or not: the accumulator
alone forces it, with no hypothesis on how the stretch ends. -/
theorem traj_delta_lower {n k : Nat → Nat} {L : Nat} (htraj : Traj n k L) :
    3 ^ L * (n 0 + 1) ≤ 2 ^ Ksum k L * n L + 2 ^ L := by
  have hid := traj_affine_exact L htraj
  have hlow := Sacc_lower L htraj.one_le
  have hexp : 3 ^ L * (n 0 + 1) = 3 ^ L * n 0 + 3 ^ L := by
    rw [Nat.mul_add, Nat.mul_one]
  omega

/-! ## How many steps can have valuation `≥ 2`?

`K_L ≥ L + #{i : k_i ≥ 2}`, so the product estimate caps the number of "big"
valuations along a stretch that fails to descend.  In the notes this is the
statement that a non-descending stretch must be atypically rich in
valuation-one steps. -/

/-- The number of steps among the first `L` whose valuation is at least `2`. -/
def bigCount (k : Nat → Nat) : Nat → Nat
  | 0 => 0
  | L + 1 => bigCount k L + (if 2 ≤ k L then 1 else 0)

@[simp] theorem bigCount_zero (k : Nat → Nat) : bigCount k 0 = 0 := rfl

@[simp] theorem bigCount_succ (k : Nat → Nat) (L : Nat) :
    bigCount k (L + 1) = bigCount k L + (if 2 ≤ k L then 1 else 0) := rfl

theorem bigCount_le (k : Nat → Nat) : ∀ L : Nat, bigCount k L ≤ L := by
  intro L
  induction L with
  | zero => exact Nat.le_refl _
  | succ L ih => rw [bigCount_succ]; split <;> omega

/-- Each step costs at least one halving, and a "big" step at least two. -/
theorem Ksum_ge_add_bigCount {k : Nat → Nat} : ∀ L : Nat,
    (∀ i : Nat, i < L → 1 ≤ k i) → L + bigCount k L ≤ Ksum k L := by
  intro L
  induction L with
  | zero => intro _; simp
  | succ L ih =>
    intro hk
    have hIH := ih (fun i hi => hk i (by omega))
    have hkL := hk L (by omega)
    rw [Ksum_succ, bigCount_succ]
    split <;> omega

/-- **The count bound.**  A stretch of `L` steps that ends no lower than it
started and never drops below `N` satisfies `2^E · (2N)^L ≤ (3N+1)^L`, where
`E` is the number of steps with valuation `≥ 2`.

Equivalently `E ≤ L·log₂((3N+1)/(2N))`, so the fraction of valuation-one steps
is at least `1 − log₂((3N+1)/(2N))`:

| `N ≥` | `3` | `10` | `100` | `1000` | `10^6` | `→ ∞` |
|---|---|---|---|---|---|---|
| ones fraction `≥` | `0.2630` | `0.3677` | `0.4102` | `0.4146` | `0.41504` | `0.415037…` |

The limit `1 − log₂(3/2) = 2 − log₂ 3 = 0.415037…` is the asymptotic bound of
the notes; it is *not* available at any finite `N`, which is exactly why the
`41.5%` statement there is asymptotic. -/
theorem bigCount_bound {n k : Nat → Nat} {L N : Nat}
    (htraj : Traj n k L) (hnodrop : n 0 ≤ n L) (hposL : 0 < n L) (hN : 1 ≤ N)
    (hmin : ∀ i : Nat, i < L → N ≤ n i) :
    2 ^ bigCount k L * (2 * N) ^ L ≤ (3 * N + 1) ^ L := by
  have hprod := noDescent_product_bound htraj hnodrop hposL hmin
  have hge : L + bigCount k L ≤ Ksum k L := Ksum_ge_add_bigCount L htraj.one_le
  have hpow : 2 ^ (L + bigCount k L) ≤ 2 ^ Ksum k L :=
    Nat.pow_le_pow_right (by omega) hge
  have hsplit : (2 * N) ^ L = 2 ^ L * N ^ L := Nat.mul_pow 2 N L
  have hrw : 2 ^ bigCount k L * (2 * N) ^ L = 2 ^ (L + bigCount k L) * N ^ L := by
    rw [hsplit, Nat.pow_add]
    simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  have hstep : 2 ^ (L + bigCount k L) * N ^ L ≤ 2 ^ Ksum k L * N ^ L :=
    Nat.mul_le_mul_right _ hpow
  omega

/-- With `N ≥ 3` the bound reads `3^L · 2^E ≤ 5^L`: at most a `log₂(5/3) ≈ 0.737`
fraction of the steps can have valuation `≥ 2`. -/
theorem bigCount_bound_three {n k : Nat → Nat} {L : Nat}
    (htraj : Traj n k L) (hnodrop : n 0 ≤ n L) (hposL : 0 < n L)
    (hmin : ∀ i : Nat, i < L → 3 ≤ n i) :
    2 ^ bigCount k L * 3 ^ L ≤ 5 ^ L := by
  have h := bigCount_bound htraj hnodrop hposL (by omega) hmin
  have e6 : (2 * 3) ^ L = 2 ^ L * 3 ^ L := Nat.mul_pow 2 3 L
  have e10 : (3 * 3 + 1) ^ L = 2 ^ L * 5 ^ L := by
    rw [show 3 * 3 + 1 = 2 * 5 by omega]
    exact Nat.mul_pow 2 5 L
  rw [e6, e10] at h
  have hrw : 2 ^ bigCount k L * (2 ^ L * 3 ^ L)
      = 2 ^ L * (2 ^ bigCount k L * 3 ^ L) := by
    simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  rw [hrw] at h
  exact Nat.le_of_mul_le_mul_left h (two_pow_pos L)

/-- A concrete instance: over ten steps that fail to descend while staying at or
above `3`, at least three have valuation exactly `1`. -/
theorem bigCount_ten {n k : Nat → Nat}
    (htraj : Traj n k 10) (hnodrop : n 0 ≤ n 10) (hposL : 0 < n 10)
    (hmin : ∀ i : Nat, i < 10 → 3 ≤ n i) : bigCount k 10 ≤ 7 := by
  have h := bigCount_bound_three htraj hnodrop hposL hmin
  have e3 : (3 : Nat) ^ 10 = 59049 := by decide
  have e5 : (5 : Nat) ^ 10 = 9765625 := by decide
  rw [e3, e5] at h
  rcases Nat.lt_or_ge (bigCount k 10) 8 with hlt | hge
  · omega
  · exfalso
    have hb : 2 ^ 8 ≤ 2 ^ bigCount k 10 := Nat.pow_le_pow_right (by omega) hge
    have e : (2 : Nat) ^ 8 = 256 := by decide
    have : 256 * 59049 ≤ 2 ^ bigCount k 10 * 59049 := Nat.mul_le_mul_right _ (by omega)
    omega

/-- **Cycles of length one.**  The only fixed point of the odd map is `1`. -/
theorem cycle_length_one {n k : Nat} (h : OddStep n k n) :
    n = 1 ∧ k = 2 := by
  obtain ⟨hk, _, heq⟩ := h
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · have hk12 : k = 1 ∨ k = 2 := by omega
    rcases hk12 with rfl | rfl
    · rw [Nat.pow_one] at heq; omega
    · have h4 : (2 : Nat) ^ 2 = 4 := rfl
      rw [h4] at heq
      exact ⟨by omega, rfl⟩
  · exfalso
    have h8 : 8 ≤ 2 ^ k := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
      rw [two_pow_succ, two_pow_succ, two_pow_succ]
      have := two_pow_pos j
      omega
    have : 8 * n ≤ 2 ^ k * n := Nat.mul_le_mul_right n h8
    omega

/-- **Every cycle has mean valuation at most `2`:** `2^{K_L} ≤ 4^L`.  Combined
with `cycle_three_pow_lt` (`3^L < 2^{K_L}`) this pins the total valuation of a
cycle of length `L` into the window `L·log₂3 < K_L ≤ 2L`, so only finitely many
`K_L` are possible for each `L`. -/
theorem cycle_two_pow_le {n k : Nat → Nat} {L N : Nat}
    (htraj : Traj n k L) (hcyc : n L = n 0) (hpos : 0 < n 0) (hN : 1 ≤ N)
    (hmin : ∀ i : Nat, i < L → N ≤ n i) : 2 ^ Ksum k L ≤ 4 ^ L := by
  have hsq := cycle_min_bound htraj hcyc hpos hmin
  have hNpow : 0 < N ^ L := pow_pos_of_pos hN L
  have hstep : (3 * N + 1) ^ L ≤ (4 * N) ^ L := Nat.pow_le_pow_left (by omega) L
  have hsplit : (4 * N) ^ L = 4 ^ L * N ^ L := Nat.mul_pow 4 N L
  have : 2 ^ Ksum k L * N ^ L ≤ 4 ^ L * N ^ L := by omega
  exact Nat.le_of_mul_le_mul_right this hNpow

/-- The same, as a bound on the exponent: `K_L ≤ 2L`. -/
theorem cycle_Ksum_le {n k : Nat → Nat} {L N : Nat}
    (htraj : Traj n k L) (hcyc : n L = n 0) (hpos : 0 < n 0) (hN : 1 ≤ N)
    (hmin : ∀ i : Nat, i < L → N ≤ n i) : Ksum k L ≤ 2 * L := by
  have hle := cycle_two_pow_le htraj hcyc hpos hN hmin
  have h4 : (4 : Nat) ^ L = 2 ^ (2 * L) := by
    rw [Nat.pow_mul]
  rw [h4] at hle
  rcases Nat.lt_or_ge (2 * L) (Ksum k L) with hlt | hge
  · exfalso
    have hmono : 2 ^ (2 * L + 1) ≤ 2 ^ Ksum k L :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hgrow : 2 ^ (2 * L + 1) = 2 * 2 ^ (2 * L) := two_pow_succ _
    have := two_pow_pos (2 * L)
    omega
  · exact hge

/-- **A cycle avoiding `1` and `2` is even more constrained:**
`2^{K_L}·3^L ≤ 10^L`.  For `L = 3` this forces `K_L = 5`. -/
theorem cycle_two_pow_le_of_three_le {n k : Nat → Nat} {L N : Nat}
    (htraj : Traj n k L) (hcyc : n L = n 0) (hpos : 0 < n 0) (hN : 3 ≤ N)
    (hmin : ∀ i : Nat, i < L → N ≤ n i) : 2 ^ Ksum k L * 3 ^ L ≤ 10 ^ L := by
  have hsq := cycle_min_bound htraj hcyc hpos hmin
  have hNpow : 0 < N ^ L := pow_pos_of_pos (by omega) L
  have hscale : 3 ^ L * (2 ^ Ksum k L * N ^ L) ≤ 3 ^ L * (3 * N + 1) ^ L :=
    Nat.mul_le_mul_left _ hsq
  have hcomb : 3 ^ L * (3 * N + 1) ^ L = (3 * (3 * N + 1)) ^ L := (Nat.mul_pow _ _ L).symm
  have hstep : (3 * (3 * N + 1)) ^ L ≤ (10 * N) ^ L := Nat.pow_le_pow_left (by omega) L
  have hsplit : (10 * N) ^ L = 10 ^ L * N ^ L := Nat.mul_pow 10 N L
  have hfinal : (2 ^ Ksum k L * 3 ^ L) * N ^ L ≤ 10 ^ L * N ^ L := by
    have hrw : (2 ^ Ksum k L * 3 ^ L) * N ^ L = 3 ^ L * (2 ^ Ksum k L * N ^ L) := by
      simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    omega
  exact Nat.le_of_mul_le_mul_right hfinal hNpow

/-- **Cycles of length two.**  The only 2-cycle of the odd map is the trivial
one, `1 → 1`.  The composed identity is `2^{k₁+k₂}·n₁ = 9n₁ + 3 + 2^{k₁}`; since
`2^{k₁+k₂} > 9` and `2^{k₁+k₂} ≤ 24`, the total valuation is forced to be `4`,
and the three remaining splittings are checked directly. -/
theorem cycle_length_two {n1 n2 k1 k2 : Nat}
    (h1 : OddStep n1 k1 n2) (h2 : OddStep n2 k2 n1) : n1 = 1 ∧ n2 = 1 := by
  obtain ⟨hk1, _, he1⟩ := h1
  obtain ⟨hk2, hodd1, he2⟩ := h2
  have hn1 : 1 ≤ n1 := by omega
  -- the composed identity
  have hkey : 2 ^ (k1 + k2) * n1 = 9 * n1 + 3 + 2 ^ k1 := by
    have hstep : 2 ^ k1 * (2 ^ k2 * n1) = 2 ^ k1 * (3 * n2 + 1) := by rw [he2]
    have hexp : 2 ^ k1 * (3 * n2 + 1) = 3 * (2 ^ k1 * n2) + 2 ^ k1 := by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
    rw [Nat.pow_add, Nat.mul_assoc, hstep, hexp, he1]
    omega
  have hA : 2 ≤ 2 ^ k1 := by
    obtain ⟨t, ht⟩ : ∃ t, k1 = t + 1 := ⟨k1 - 1, by omega⟩
    subst ht
    have := two_pow_pos t
    rw [two_pow_succ]
    omega
  have hB : 2 ≤ 2 ^ k2 := by
    obtain ⟨t, ht⟩ : ∃ t, k2 = t + 1 := ⟨k2 - 1, by omega⟩
    subst ht
    have := two_pow_pos t
    rw [two_pow_succ]
    omega
  have hAB : 2 * 2 ^ k1 ≤ 2 ^ (k1 + k2) := by
    rw [Nat.pow_add, Nat.mul_comm 2 (2 ^ k1)]
    exact Nat.mul_le_mul_left _ hB
  -- `2^{k₁+k₂} > 9`
  have h9 : n1 * 9 < n1 * 2 ^ (k1 + k2) := by
    rw [Nat.mul_comm n1 9, Nat.mul_comm n1 (2 ^ (k1 + k2))]
    omega
  have hgt : 9 < 2 ^ (k1 + k2) := Nat.lt_of_mul_lt_mul_left h9
  -- `2^{k₁+k₂} ≤ 24`
  have hsub : (2 ^ (k1 + k2) - 9) * n1 = 3 + 2 ^ k1 := by
    rw [Nat.sub_mul]
    omega
  have hone : (2 ^ (k1 + k2) - 9) * 1 ≤ (2 ^ (k1 + k2) - 9) * n1 :=
    Nat.mul_le_mul_left _ hn1
  rw [Nat.mul_one] at hone
  have hle : 2 ^ (k1 + k2) ≤ 24 := by omega
  -- hence the total valuation is exactly `4`
  have hK4 : k1 + k2 = 4 := by
    rcases Nat.lt_or_ge (k1 + k2) 5 with hlt | hge
    · rcases Nat.lt_or_ge (k1 + k2) 4 with hlt' | hge'
      · exfalso
        have hb : 2 ^ (k1 + k2) ≤ 2 ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
        have e : (2 : Nat) ^ 3 = 8 := rfl
        omega
      · omega
    · exfalso
      have hb : 2 ^ 5 ≤ 2 ^ (k1 + k2) := Nat.pow_le_pow_right (by omega) hge
      have e : (2 : Nat) ^ 5 = 32 := rfl
      omega
  have h16 : (2 : Nat) ^ (k1 + k2) = 16 := by rw [hK4]
  rw [h16] at hkey
  have hcase : k1 = 1 ∨ k1 = 2 ∨ k1 = 3 := by omega
  rcases hcase with hc | hc | hc
  · exfalso
    rw [hc] at hkey
    have e : (2 : Nat) ^ 1 = 2 := rfl
    omega
  · rw [hc] at hkey he1
    have e : (2 : Nat) ^ 2 = 4 := rfl
    rw [e] at hkey he1
    have hn : n1 = 1 := by omega
    subst hn
    exact ⟨rfl, by omega⟩
  · exfalso
    rw [hc] at hkey
    have e : (2 : Nat) ^ 3 = 8 := rfl
    omega

/-- From `1` the only step is `1 → 1` with valuation `2`. -/
theorem oddStep_one {k m : Nat} (h : OddStep 1 k m) : k = 2 ∧ m = 1 := by
  obtain ⟨_, hm, heq⟩ := h
  have h4 : 2 ^ k * m = 2 ^ 2 * 1 := by rw [heq]
  exact two_pow_mul_odd_inj k 2 m 1 hm (by omega) h4

/-- Three iterates packaged as a periodic function, so the general trajectory
lemmas apply to an explicit 3-cycle. -/
private def cyc3 (a b c : Nat) (i : Nat) : Nat :=
  if i % 3 = 0 then a else if i % 3 = 1 then b else c

private theorem cyc3_zero (a b c : Nat) : cyc3 a b c 0 = a := rfl
private theorem cyc3_one (a b c : Nat) : cyc3 a b c 1 = b := rfl
private theorem cyc3_two (a b c : Nat) : cyc3 a b c 2 = c := rfl

/-- **Cycles of length three.**  The only 3-cycle of the odd map is the trivial
one.  `n₁` is assumed least, which any cycle achieves after a rotation.

The mechanism: `cycle_two_pow_le_of_three_le` gives `2^K·27 ≤ 1000`, so `K ≤ 5`,
while `cycle_three_pow_lt` gives `27 < 2^K`, so `K ≥ 5`.  Hence `K = 5`, and the
composed identity `5·n₁ = 9 + 3·2^{k₁} + 2^{k₁+k₂}` has right-hand side
`19, 23, 31, 29, 37, 49` over the six compositions of `5` into three positive
parts — none divisible by `5`. -/
theorem cycle_length_three {n1 n2 n3 k1 k2 k3 : Nat}
    (h1 : OddStep n1 k1 n2) (h2 : OddStep n2 k2 n3) (h3 : OddStep n3 k3 n1)
    (hm2 : n1 ≤ n2) (hm3 : n1 ≤ n3) : n1 = 1 ∧ n2 = 1 ∧ n3 = 1 := by
  have hodd1 : n1 % 2 = 1 := h3.2.1
  rcases Nat.lt_or_ge n1 3 with hsmall | hbig
  · have hn1 : n1 = 1 := by omega
    subst hn1
    obtain ⟨_, hn2⟩ := oddStep_one h1
    subst hn2
    obtain ⟨_, hn3⟩ := oddStep_one h2
    subst hn3
    exact ⟨rfl, rfl, rfl⟩
  · exfalso
    have eK : 2 ^ (k1 + k2 + k3) * n1 = 2 ^ (k1 + k2) * (2 ^ k3 * n1) := by
      rw [Nat.pow_add, Nat.mul_assoc]
    have e3 : 2 ^ (k1 + k2) * (2 ^ k3 * n1) = 2 ^ (k1 + k2) * (3 * n3 + 1) := by
      rw [h3.2.2]
    have e3' : 2 ^ (k1 + k2) * (3 * n3 + 1)
        = 3 * (2 ^ (k1 + k2) * n3) + 2 ^ (k1 + k2) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
    have e2 : 2 ^ (k1 + k2) * n3 = 2 ^ k1 * (2 ^ k2 * n3) := by
      rw [Nat.pow_add, Nat.mul_assoc]
    have e2' : 2 ^ k1 * (2 ^ k2 * n3) = 2 ^ k1 * (3 * n2 + 1) := by rw [h2.2.2]
    have e2'' : 2 ^ k1 * (3 * n2 + 1) = 3 * (2 ^ k1 * n2) + 2 ^ k1 := by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
    have e1 : 2 ^ k1 * n2 = 3 * n1 + 1 := h1.2.2
    have hkey : 2 ^ (k1 + k2 + k3) * n1
        = 27 * n1 + 9 + 3 * 2 ^ k1 + 2 ^ (k1 + k2) := by omega
    have htraj : Traj (cyc3 n1 n2 n3) (cyc3 k1 k2 k3) 3 := by
      intro i hi
      have hcase : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases hcase with hc | hc | hc <;> subst hc
      · exact h1
      · exact h2
      · exact h3
    have hKs : Ksum (cyc3 k1 k2 k3) 3 = k1 + k2 + k3 := by
      simp only [Ksum_succ, Ksum_zero, cyc3_zero, cyc3_one, cyc3_two]
      omega
    have hcyc : cyc3 n1 n2 n3 3 = cyc3 n1 n2 n3 0 := rfl
    have hpos : 0 < cyc3 n1 n2 n3 0 := by rw [cyc3_zero]; omega
    have hmin : ∀ i : Nat, i < 3 → n1 ≤ cyc3 n1 n2 n3 i := by
      intro i hi
      have hcase : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases hcase with hc | hc | hc <;> subst hc
      · exact Nat.le_refl _
      · exact hm2
      · exact hm3
    have hup := cycle_two_pow_le_of_three_le htraj hcyc hpos hbig hmin
    have hlo := cycle_three_pow_lt (by omega) htraj hcyc hpos
    rw [hKs] at hup hlo
    have e27 : (3 : Nat) ^ 3 = 27 := rfl
    have e1000 : (10 : Nat) ^ 3 = 1000 := rfl
    rw [e27, e1000] at hup
    rw [e27] at hlo
    have hK5 : k1 + k2 + k3 = 5 := by
      rcases Nat.lt_or_ge (k1 + k2 + k3) 6 with hlt | hge
      · rcases Nat.lt_or_ge (k1 + k2 + k3) 5 with hlt' | hge'
        · have hb : 2 ^ (k1 + k2 + k3) ≤ 2 ^ 4 :=
            Nat.pow_le_pow_right (by omega) (by omega)
          have e : (2 : Nat) ^ 4 = 16 := rfl
          omega
        · omega
      · have hb : 2 ^ 6 ≤ 2 ^ (k1 + k2 + k3) := Nat.pow_le_pow_right (by omega) hge
        have e : (2 : Nat) ^ 6 = 64 := rfl
        omega
    rw [hK5] at hkey
    have e32 : (2 : Nat) ^ 5 = 32 := rfl
    rw [e32] at hkey
    have hk1 : 1 ≤ k1 := h1.1
    have hk2 : 1 ≤ k2 := h2.1
    have hk3 : 1 ≤ k3 := h3.1
    have hcase : (k1 = 1 ∧ k2 = 1) ∨ (k1 = 1 ∧ k2 = 2) ∨ (k1 = 1 ∧ k2 = 3) ∨
        (k1 = 2 ∧ k2 = 1) ∨ (k1 = 2 ∧ k2 = 2) ∨ (k1 = 3 ∧ k2 = 1) := by omega
    have p1 : (2 : Nat) ^ 1 = 2 := rfl
    have p2 : (2 : Nat) ^ 2 = 4 := rfl
    have p3 : (2 : Nat) ^ 3 = 8 := rfl
    have p4 : (2 : Nat) ^ 4 = 16 := rfl
    rcases hcase with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
      subst ha <;> subst hb <;> omega


/-! ## An upper bound on the least element of a cycle

Combining `3^L < 2^{K_L}` with `2^{K_L}·N^L ≤ (3N+1)^L` bounds the least element
of a cycle *from above* in terms of its length.  Paired with a verified range
this bounds the length from below. -/

/-- `(a+1)^{L+1} ≤ a^{L+1} + (L+1)·(a+1)^L`, the integer mean-value bound. -/
theorem pow_succ_le (a : Nat) : ∀ L : Nat,
    (a + 1) ^ (L + 1) ≤ a ^ (L + 1) + (L + 1) * (a + 1) ^ L := by
  intro L
  induction L with
  | zero => simp
  | succ L ih =>
    show (a + 1) ^ (L + 2) ≤ a ^ (L + 2) + (L + 2) * (a + 1) ^ (L + 1)
    have e_a : a ^ (L + 2) = a * a ^ (L + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    have e_b : (a + 1) ^ (L + 1) = (a + 1) * (a + 1) ^ L := by
      rw [Nat.pow_succ, Nat.mul_comm]
    have e_c : (a + 1) ^ (L + 2) = (a + 1) * (a + 1) ^ (L + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm]
    have step1 : (a + 1) ^ (L + 2) ≤ (a + 1) * (a ^ (L + 1) + (L + 1) * (a + 1) ^ L) := by
      rw [e_c]
      exact Nat.mul_le_mul_left _ ih
    have step2 : (a + 1) * (a ^ (L + 1) + (L + 1) * (a + 1) ^ L)
        = a ^ (L + 2) + (a ^ (L + 1) + (L + 1) * (a + 1) ^ (L + 1)) := by
      rw [e_a, e_b]
      simp [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_assoc,
        Nat.mul_left_comm] <;> omega
    have step3 : a ^ (L + 1) ≤ (a + 1) ^ (L + 1) := Nat.pow_le_pow_left (by omega) (L + 1)
    have step4 : (L + 2) * (a + 1) ^ (L + 1)
        = (a + 1) ^ (L + 1) + (L + 1) * (a + 1) ^ (L + 1) := by
      rw [show L + 2 = 1 + (L + 1) by omega, Nat.add_mul, Nat.one_mul]
    omega

/-- The heart of the "small least element" bounds: the squeeze alone gives
`N^{L+1} ≤ (L+1)·(3N+1)^L`. -/
theorem pow_succ_le_of_squeeze {L N K : Nat}
    (hlo : 3 ^ (L + 1) < 2 ^ K) (hup : 2 ^ K * N ^ (L + 1) ≤ (3 * N + 1) ^ (L + 1)) :
    N ^ (L + 1) ≤ (L + 1) * (3 * N + 1) ^ L := by
  have hstepA : (3 ^ (L + 1) + 1) * N ^ (L + 1) ≤ (3 * N + 1) ^ (L + 1) := by
    have h1 : (3 ^ (L + 1) + 1) * N ^ (L + 1) ≤ 2 ^ K * N ^ (L + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hstepB := pow_succ_le (3 * N) L
  have hstepC : (3 * N) ^ (L + 1) = 3 ^ (L + 1) * N ^ (L + 1) :=
    Nat.mul_pow 3 N (L + 1)
  have hd : (3 ^ (L + 1) + 1) * N ^ (L + 1)
      = 3 ^ (L + 1) * N ^ (L + 1) + N ^ (L + 1) := by
    rw [Nat.add_mul, Nat.one_mul]
  omega

/-- **The arithmetic core, with a lower bound `M` supplied.**  From the squeeze
and any `3 ≤ M ≤ N`:

  `(3M)^L · N ≤ (L+1) · (9M+3)^L`,  i.e.  `N ≲ (L+1)·(3 + 1/M)^L`.

The base is `3 + 1/M`, so a *larger* known lower bound gives a sharper
conclusion — taking `M = 3` recovers `min_upper_of_squeeze` with its base `10/3`,
while `M = 2^68` pushes the base down to `3 + 2⁻⁶⁸`. -/
theorem min_upper_of_squeeze_gen {L N K M : Nat} (hM : 3 ≤ M) (hMN : M ≤ N)
    (hlo : 3 ^ (L + 1) < 2 ^ K) (hup : 2 ^ K * N ^ (L + 1) ≤ (3 * N + 1) ^ (L + 1)) :
    (3 * M) ^ L * N ≤ (L + 1) * (9 * M + 3) ^ L := by
  have hpos : 0 < N := by omega
  have hNpow : 0 < N ^ L := pow_pos_of_pos hpos L
  have hcore := pow_succ_le_of_squeeze hlo hup
  have e1 : 3 * M * (3 * N + 1) = 9 * (M * N) + 3 * M := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_left_comm M 3 N,
      ← Nat.mul_assoc]
  have e2 : (9 * M + 3) * N = 9 * (M * N) + 3 * N := by
    rw [Nat.add_mul, Nat.mul_assoc]
  have hmix : (3 * M) ^ L * (3 * N + 1) ^ L = (3 * M * (3 * N + 1)) ^ L :=
    (Nat.mul_pow _ _ L).symm
  have hup2 : (3 * M * (3 * N + 1)) ^ L ≤ ((9 * M + 3) * N) ^ L :=
    Nat.pow_le_pow_left (by omega) L
  have hsplit : ((9 * M + 3) * N) ^ L = (9 * M + 3) ^ L * N ^ L :=
    Nat.mul_pow _ _ L
  have hfinal : ((3 * M) ^ L * N) * N ^ L ≤ ((L + 1) * (9 * M + 3) ^ L) * N ^ L := by
    have hrw1 : ((3 * M) ^ L * N) * N ^ L = (3 * M) ^ L * N ^ (L + 1) := by
      rw [Nat.pow_succ]
      simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    have hrw2 : ((L + 1) * (9 * M + 3) ^ L) * N ^ L
        = (L + 1) * ((9 * M + 3) ^ L * N ^ L) := by rw [Nat.mul_assoc]
    have hstep : (3 * M) ^ L * N ^ (L + 1) ≤ (L + 1) * ((9 * M + 3) ^ L * N ^ L) :=
      calc (3 * M) ^ L * N ^ (L + 1)
          ≤ (3 * M) ^ L * ((L + 1) * (3 * N + 1) ^ L) := Nat.mul_le_mul_left _ hcore
        _ = (L + 1) * ((3 * M) ^ L * (3 * N + 1) ^ L) := by
            simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
        _ = (L + 1) * (3 * M * (3 * N + 1)) ^ L := by rw [hmix]
        _ ≤ (L + 1) * ((9 * M + 3) * N) ^ L := Nat.mul_le_mul_left _ hup2
        _ = (L + 1) * ((9 * M + 3) ^ L * N ^ L) := by rw [hsplit]
    omega
  exact Nat.le_of_mul_le_mul_right hfinal hNpow

/-- The `M = 3` instance: `3^L · N ≤ (L+1) · 10^L`. -/
theorem min_upper_of_squeeze {L N K : Nat} (hN : 3 ≤ N)
    (hlo : 3 ^ (L + 1) < 2 ^ K) (hup : 2 ^ K * N ^ (L + 1) ≤ (3 * N + 1) ^ (L + 1)) :
    3 ^ L * N ≤ (L + 1) * 10 ^ L := by
  have hgen := min_upper_of_squeeze_gen (M := 3) (by omega) hN hlo hup
  have e1 : (3 * 3 : Nat) ^ L = 3 ^ L * 3 ^ L := by
    rw [show (3 * 3 : Nat) = 3 * 3 from rfl, Nat.mul_pow]
  have e2 : (9 * 3 + 3 : Nat) ^ L = 3 ^ L * 10 ^ L := by
    rw [show (9 * 3 + 3 : Nat) = 3 * 10 by omega, Nat.mul_pow]
  rw [e1, e2] at hgen
  have hrw1 : 3 ^ L * 3 ^ L * N = 3 ^ L * (3 ^ L * N) := by rw [Nat.mul_assoc]
  have hrw2 : (L + 1) * (3 ^ L * 10 ^ L) = 3 ^ L * ((L + 1) * 10 ^ L) := by
    simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  rw [hrw1, hrw2] at hgen
  exact Nat.le_of_mul_le_mul_left hgen (three_pow_pos L)

/-- **The least element of a cycle is bounded by its length**: an instance of
`min_upper_of_squeeze`, since a cycle supplies both hypotheses. -/
theorem cycle_min_upper {n k : Nat → Nat} {L : Nat}
    (htraj : Traj n k (L + 1)) (hcyc : n (L + 1) = n 0) (hN : 3 ≤ n 0)
    (hmin : ∀ i : Nat, i < L + 1 → n 0 ≤ n i) :
    3 ^ L * n 0 ≤ (L + 1) * 10 ^ L :=
  min_upper_of_squeeze hN
    (cycle_three_pow_lt (by omega) htraj hcyc (by omega))
    (cycle_min_bound htraj hcyc (by omega) hmin)

/-! ### Excluding cycle lengths against a verified range

If the least element of a cycle is known to exceed `V`, `min_upper_of_squeeze_gen`
with `M = V` caps it at about `(L+1)·(3 + 1/V)^L`.  Feeding `V` into the
*arithmetic* — not only into the final comparison — makes the base essentially
`3` rather than `10/3`, which is what lifts the resulting length bound. -/

/-- Is length `L+1` excluded for cycles whose least element exceeds `V`? -/
def lengthExcluded (V L : Nat) : Bool :=
  decide ((L + 1) * (9 * V + 3) ^ L ≤ V * (3 * V) ^ L)

/-- Every length below `B` excluded. -/
def allLengthsExcluded (V B : Nat) : Bool := (List.range B).all (lengthExcluded V)

theorem no_cycle_of_verified {n k : Nat → Nat} {L V : Nat}
    (htraj : Traj n k (L + 1)) (hcyc : n (L + 1) = n 0)
    (hmin : ∀ i : Nat, i < L + 1 → n 0 ≤ n i) (hV : V < n 0) (h3 : 3 ≤ V)
    (hexc : lengthExcluded V L = true) : False := by
  have hpos : 0 < n 0 := by omega
  have hub := min_upper_of_squeeze_gen (M := V) h3 (by omega)
    (cycle_three_pow_lt (by omega) htraj hcyc hpos)
    (cycle_min_bound htraj hcyc hpos hmin)
  simp only [lengthExcluded, decide_eq_true_eq] at hexc
  have hlt : (3 * V) ^ L * V < (3 * V) ^ L * n 0 :=
    (Nat.mul_lt_mul_left (pow_pos_of_pos (by omega) L)).mpr hV
  have hrw : (3 * V) ^ L * V = V * (3 * V) ^ L := Nat.mul_comm _ _
  omega

theorem no_cycle_below_of_verified {n k : Nat → Nat} {L V B : Nat}
    (htraj : Traj n k (L + 1)) (hcyc : n (L + 1) = n 0)
    (hmin : ∀ i : Nat, i < L + 1 → n 0 ≤ n i) (hV : V < n 0) (h3 : 3 ≤ V)
    (hLB : L < B) (hall : allLengthsExcluded V B = true) : False :=
  no_cycle_of_verified htraj hcyc hmin hV h3
    (List.all_eq_true.mp hall L (List.mem_range.mpr hLB))

/-- Every cycle length up to `41` is excluded once the least element is known to
exceed `704·2^60`, which is `Collatz.BarinaRange.barinaBound` — this
repository's canonical statement of Barina's range.  (An earlier version of this
file used `2^68`; that is *not* the repo's constant and is smaller, so it gave a
weaker bound.) -/
theorem allLengthsExcluded_barina : allLengthsExcluded (704 * 2 ^ 60) 41 = true := by decide

/-- **A nontrivial cycle has at least 42 odd steps.**

*Conditional*, unlike `no_short_cycle`: the hypothesis `2^68 < n 0` is supplied
by the exhaustive verification of the Collatz conjecture below `704·2^60`
(D. Barina, *Convergence verification of the Collatz problem*, J. Supercomputing
76 (2020), 3818–3831), which the repository records as the explicit hypothesis
`Collatz.BarinaRange.BarinaVerified` and does **not** prove.  Everything else
here is proved.  For a version resting only on the repository's own
kernel-proved range, see `cycle_length_ge_12_of_verified`.

The route is elementary: `min_upper_of_squeeze_gen` with `M = 704·2^60` caps the
least element at about `(L+1)·(3 + 1/M)^L`.  Using the verified range inside
the arithmetic rather than only at the end is what lifts the bound from `38`
(base `10/3`) to `42` (base essentially `3`).  It remains far weaker than the
bound obtainable from linear forms in logarithms, but needs no
Diophantine-approximation input. -/
theorem cycle_length_ge_42 {n k : Nat → Nat} {L : Nat}
    (htraj : Traj n k (L + 1)) (hcyc : n (L + 1) = n 0)
    (hmin : ∀ i : Nat, i < L + 1 → n 0 ≤ n i) (hV : 704 * 2 ^ 60 < n 0) : 42 ≤ L + 1 := by
  rcases Nat.lt_or_ge L 41 with hlt | hge
  · exact absurd (no_cycle_below_of_verified htraj hcyc hmin hV (by decide) hlt
      allLengthsExcluded_barina) (fun h => h.elim)
  · omega

/-- Every cycle length up to `11` is excluded once the least element is known to
exceed `1 086 464` — this repository's *own* kernel-proved verified range
(`Collatz.Search.VerifiedRange.verified_1086464`), rather than a cited one. -/
theorem allLengthsExcluded_1086464 : allLengthsExcluded 1086464 11 = true := by decide

/-- **A nontrivial cycle has at least 12 odd steps, from the repository's own
verified range.**

This is the citation-free companion to `cycle_length_ge_42`.  That theorem needs
Barina's `2^68`, which `PROGRAM_STATUS.md` is careful to flag as an assumption;
this one needs only `1 086 464`, which the repository proves in the kernel.

The hypothesis is still supplied here rather than derived: turning
`verified_1086464` into `1086464 < n 0` needs the chain from the odd map through
`acceleratedOrbit` to the standard `orbit` used by `ReachesOne`, which is not
built.  Note also that `no_short_cycle` already gives `L ≤ 10` with *no* verified
range at all, so the unconditional gain here is one step; the point is the
weaker hypothesis, not the larger number. -/
theorem cycle_length_ge_12_of_verified {n k : Nat → Nat} {L : Nat}
    (htraj : Traj n k (L + 1)) (hcyc : n (L + 1) = n 0)
    (hmin : ∀ i : Nat, i < L + 1 → n 0 ≤ n i) (hV : 1086464 < n 0) : 12 ≤ L + 1 := by
  rcases Nat.lt_or_ge L 11 with hlt | hge
  · exact absurd (no_cycle_below_of_verified htraj hcyc hmin hV (by decide) hlt
      allLengthsExcluded_1086464) (fun h => h.elim)
  · omega

/-! ## A decidable criterion excluding cycle lengths

A nontrivial cycle of length `L` has least element `N ≥ 3`, and then

  `3^L < 2^{K_L}`   (`cycle_three_pow_lt`)   and   `2^{K_L}·3^L ≤ 10^L`
  (`cycle_two_pow_le_of_three_le`),   with   `K_L ≤ 2L`   (`cycle_Ksum_le`).

Since `log₂ 3 = 1.58496…` and `log₂(10/3) = 1.73697…`, the window for `K_L` has
width only `0.152·L`, so for small `L` it can be empty — and then no cycle of
that length exists at all.  `hasAdmissibleK` decides emptiness. -/

/-- A cycle through `1` consists entirely of `1`s. -/
theorem traj_one_of_start_one {n k : Nat → Nat} {L : Nat} (htraj : Traj n k L)
    (h0 : n 0 = 1) : ∀ i : Nat, i ≤ L → n i = 1 := by
  intro i
  induction i with
  | zero => intro _; exact h0
  | succ i ih =>
    intro hi
    have hone := ih (by omega)
    have hstep := htraj i (by omega)
    rw [hone] at hstep
    exact (oddStep_one hstep).2

/-- Is `K` an admissible total valuation for a nontrivial cycle of length `L`? -/
def admissibleK (L K : Nat) : Bool :=
  decide (3 ^ L < 2 ^ K) && decide (2 ^ K * 3 ^ L ≤ 10 ^ L)

/-- Does any admissible total valuation exist for length `L`? -/
def hasAdmissibleK (L : Nat) : Bool :=
  (List.range (2 * L + 1)).any (admissibleK L)

/-- **The criterion.**  If no total valuation is admissible at length `L`, no
cycle of that length has least element `≥ 3`. -/
theorem no_cycle_of_no_admissibleK {n k : Nat → Nat} {L N : Nat}
    (hL : 0 < L) (htraj : Traj n k L) (hcyc : n L = n 0) (hN : 3 ≤ N)
    (hmin : ∀ i : Nat, i < L → N ≤ n i) (hno : hasAdmissibleK L = false) : False := by
  have hpos : 0 < n 0 := by have := hmin 0 hL; omega
  have hlo := cycle_three_pow_lt hL htraj hcyc hpos
  have hup := cycle_two_pow_le_of_three_le htraj hcyc hpos hN hmin
  have hKle := cycle_Ksum_le htraj hcyc hpos (by omega) hmin
  have hmem : Ksum k L ∈ List.range (2 * L + 1) := List.mem_range.mpr (by omega)
  have hadm : admissibleK L (Ksum k L) = true := by
    simp only [admissibleK, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hlo, hup⟩
  have hyes : hasAdmissibleK L = true :=
    List.any_eq_true.mpr ⟨Ksum k L, hmem, hadm⟩
  rw [hno] at hyes
  exact Bool.noConfusion hyes

/-- **Consequence.**  At a length with no admissible valuation, every cycle is
the trivial one. -/
theorem cycle_trivial_of_no_admissibleK {n k : Nat → Nat} {L : Nat}
    (hL : 0 < L) (htraj : Traj n k L) (hcyc : n L = n 0)
    (hmin : ∀ i : Nat, i < L → n 0 ≤ n i) (hno : hasAdmissibleK L = false) :
    ∀ i : Nat, i ≤ L → n i = 1 := by
  obtain ⟨M, hM⟩ : ∃ M, L = M + 1 := ⟨L - 1, by omega⟩
  have hoddL : n L % 2 = 1 := by
    have := htraj M (by omega)
    rw [← hM] at this
    exact this.2.1
  rw [hcyc] at hoddL
  rcases Nat.lt_or_ge (n 0) 3 with hsmall | hbig
  · exact traj_one_of_start_one htraj (by omega)
  · exact absurd (no_cycle_of_no_admissibleK hL htraj hcyc hbig hmin hno)
      (fun h => h.elim)

/-! ### The lengths ruled out outright

`L = 1, 2, 4`.  `L = 3` survives with the single value `K = 5`, which
`cycle_length_three` disposes of by enumerating the six compositions. -/

theorem no_admissibleK_one : hasAdmissibleK 1 = false := by decide
theorem no_admissibleK_two : hasAdmissibleK 2 = false := by decide
theorem no_admissibleK_four : hasAdmissibleK 4 = false := by decide

/-- `L = 3` is the first length the criterion does *not* settle, and it leaves
exactly one candidate. -/
theorem admissibleK_three : hasAdmissibleK 3 = true := by decide
theorem admissibleK_three_only_five (K : Nat) (h : admissibleK 3 K = true) : K = 5 := by
  rcases Nat.lt_or_ge K 7 with hlt | hge
  · have hcase : K = 0 ∨ K = 1 ∨ K = 2 ∨ K = 3 ∨ K = 4 ∨ K = 5 ∨ K = 6 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> revert h <;> decide
  · exfalso
    have hb : 2 ^ 7 ≤ 2 ^ K := Nat.pow_le_pow_right (by omega) hge
    have e : (2 : Nat) ^ 7 = 128 := rfl
    simp only [admissibleK, Bool.and_eq_true, decide_eq_true_eq] at h
    have e27 : (3 : Nat) ^ 3 = 27 := rfl
    have e1000 : (10 : Nat) ^ 3 = 1000 := rfl
    rw [e27, e1000] at h
    omega

/-- **No cycle of length four**, trivial or otherwise, other than the fixed
point.  This is new relative to the hand analysis: lengths `1` and `2` were done
by explicit identities, but `4` falls out of the window criterion alone. -/
theorem cycle_length_four_trivial {n k : Nat → Nat} (htraj : Traj n k 4)
    (hcyc : n 4 = n 0) (hmin : ∀ i : Nat, i < 4 → n 0 ≤ n i) :
    ∀ i : Nat, i ≤ 4 → n i = 1 :=
  cycle_trivial_of_no_admissibleK (by omega) htraj hcyc hmin no_admissibleK_four

/-! ## Enumerating the compositions

For a cycle, `traj_affine_exact` at `n_L = n_0` gives
`(2^{K} − 3^L)·n₀ = Sacc k L`, so `D := 2^K − 3^L` divides the accumulator.
`cycleScan` enumerates every way the accumulator can arise from a valuation
vector of length `L` summing to `K`, and reports whether any is divisible by `D`.

The scan carries exactly the pair the `Sacc` recursion needs — `acc = Sacc k m`
and `p = 2^{Ksum k m}` — so the completeness proof is a single induction with no
reindexing lemmas. -/

/-- `cycleScan D r b p acc` : starting from accumulator `acc` and power `p`, can
`r` further steps with valuations summing to `b` (each `≥ 1`) reach an
accumulator divisible by `D`? -/
def cycleScan (D : Nat) : Nat → Nat → Nat → Nat → Bool
  | 0, b, _, acc => b == 0 && acc % D == 0
  | r + 1, b, p, acc =>
      -- the `r` remaining steps each need at least one halving, so `kv ≤ b - r`
      (List.range (b - r + 1)).any fun kv =>
        !(kv == 0) && cycleScan D r (b - kv) (p * 2 ^ kv) (3 * acc + p)

/-- Each of `r` further steps costs at least one halving. -/
theorem Ksum_add_ge {k : Nat → Nat} : ∀ a r : Nat,
    (∀ i : Nat, i < a + r → 1 ≤ k i) → Ksum k a + r ≤ Ksum k (a + r) := by
  intro a r
  induction r with
  | zero => intro _; simp
  | succ r ih =>
    intro hk
    have hIH := ih (fun i hi => hk i (by omega))
    have hlast := hk (a + r) (by omega)
    rw [show a + (r + 1) = (a + r) + 1 by omega, Ksum_succ]
    omega

/-- `Ksum` is monotone in the number of steps. -/
theorem Ksum_mono (k : Nat → Nat) : ∀ a b : Nat, a ≤ b → Ksum k a ≤ Ksum k b := by
  intro a b hab
  obtain ⟨t, ht⟩ : ∃ t, b = a + t := ⟨b - a, by omega⟩
  subst ht
  induction t with
  | zero => exact Nat.le_refl _
  | succ t ih =>
    rw [show a + (t + 1) = (a + t) + 1 by omega, Ksum_succ]
    omega

/-- **Completeness of the scan.**  Any valuation vector whose accumulator is
divisible by `D` is found. -/
theorem cycleScan_complete {k : Nat → Nat} {D : Nat} : ∀ r m : Nat,
    (∀ i : Nat, i < m + r → 1 ≤ k i) →
    D ∣ Sacc k (m + r) →
    cycleScan D r (Ksum k (m + r) - Ksum k m) (2 ^ Ksum k m) (Sacc k m) = true := by
  intro r
  induction r with
  | zero =>
    intro m _ hdvd
    obtain ⟨t, ht⟩ := hdvd
    rw [Nat.add_zero] at ht
    simp only [cycleScan, Nat.add_zero, Nat.sub_self]
    rw [ht]
    simp [Nat.mul_mod_right]
  | succ r ih =>
    intro m hk hdvd
    have hkm : 1 ≤ k m := hk m (by omega)
    have hstep : Ksum k (m + 1) = Ksum k m + k m := Ksum_succ k m
    have hmono : Ksum k (m + 1) ≤ Ksum k (m + (r + 1)) :=
      Ksum_mono k (m + 1) (m + (r + 1)) (by omega)
    have hspace : Ksum k (m + 1) + r ≤ Ksum k (m + (r + 1)) := by
      have h := Ksum_add_ge (k := k) (m + 1) r (fun i hi => hk i (by omega))
      rw [show m + 1 + r = m + (r + 1) by omega] at h
      exact h
    have hbud : k m ≤ Ksum k (m + (r + 1)) - Ksum k m - r := by omega
    have hIH := ih (m + 1) (by intro i hi; exact hk i (by omega))
      (by rw [show m + 1 + r = m + (r + 1) by omega]; exact hdvd)
    rw [hstep, show m + 1 + r = m + (r + 1) by omega] at hIH
    refine List.any_eq_true.mpr ⟨k m, List.mem_range.mpr (by omega), ?_⟩
    refine Bool.and_eq_true _ _ |>.mpr ⟨by simp; omega, ?_⟩
    rw [show Ksum k (m + (r + 1)) - Ksum k m - k m
          = Ksum k (m + (r + 1)) - (Ksum k m + k m) by omega,
      show (2 : Nat) ^ Ksum k m * 2 ^ k m = 2 ^ (Ksum k m + k m) by rw [Nat.pow_add],
      show 3 * Sacc k m + 2 ^ Ksum k m = Sacc k (m + 1) by rw [Sacc_succ]]
    exact hIH

/-- A cycle's accumulator is divisible by `2^{K_L} − 3^L`. -/
theorem cycle_dvd_Sacc {n k : Nat → Nat} {L : Nat} (hL : 0 < L)
    (htraj : Traj n k L) (hcyc : n L = n 0) (hpos : 0 < n 0) :
    (2 ^ Ksum k L - 3 ^ L) ∣ Sacc k L := by
  have hid := traj_affine_exact L htraj
  rw [hcyc] at hid
  refine ⟨n 0, ?_⟩
  rw [Nat.sub_mul]
  omega

/-- **The length check.**  For every admissible total valuation `K`, no
composition of `K` into `L` positive parts produces an accumulator divisible by
`2^K − 3^L`. -/
def noCycleAtLength (L : Nat) : Bool :=
  (List.range (2 * L + 1)).all fun K =>
    !(admissibleK L K) || !(cycleScan (2 ^ K - 3 ^ L) L K 1 0)

/-- **No nontrivial cycle at a checked length.** -/
theorem no_cycle_of_noCycleAtLength {n k : Nat → Nat} {L N : Nat}
    (hL : 0 < L) (htraj : Traj n k L) (hcyc : n L = n 0) (hN : 3 ≤ N)
    (hmin : ∀ i : Nat, i < L → N ≤ n i) (hchk : noCycleAtLength L = true) : False := by
  have hpos : 0 < n 0 := by have := hmin 0 hL; omega
  have hlo := cycle_three_pow_lt hL htraj hcyc hpos
  have hup := cycle_two_pow_le_of_three_le htraj hcyc hpos hN hmin
  have hKle := cycle_Ksum_le htraj hcyc hpos (by omega) hmin
  have hadm : admissibleK L (Ksum k L) = true := by
    simp only [admissibleK, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hlo, hup⟩
  have hdvd := cycle_dvd_Sacc hL htraj hcyc hpos
  have hscan : cycleScan (2 ^ Ksum k L - 3 ^ L) L (Ksum k L) 1 0 = true := by
    have h := cycleScan_complete (k := k) (D := 2 ^ Ksum k L - 3 ^ L) L 0
      (fun i _ => (htraj i (by omega)).1) (by rw [Nat.zero_add]; exact hdvd)
    rw [Nat.zero_add, Ksum_zero, Sacc_zero, Nat.sub_zero, Nat.pow_zero] at h
    exact h
  have hall := List.all_eq_true.mp hchk (Ksum k L) (List.mem_range.mpr (by omega))
  rw [hadm, hscan] at hall
  exact Bool.noConfusion hall

/-- Same conclusion, phrased as "every cycle at this length is trivial". -/
theorem cycle_trivial_of_noCycleAtLength {n k : Nat → Nat} {L : Nat}
    (hL : 0 < L) (htraj : Traj n k L) (hcyc : n L = n 0)
    (hmin : ∀ i : Nat, i < L → n 0 ≤ n i) (hchk : noCycleAtLength L = true) :
    ∀ i : Nat, i ≤ L → n i = 1 := by
  obtain ⟨M, hM⟩ : ∃ M, L = M + 1 := ⟨L - 1, by omega⟩
  have hoddL : n L % 2 = 1 := by
    have h := htraj M (by omega)
    rw [← hM] at h
    exact h.2.1
  rw [hcyc] at hoddL
  rcases Nat.lt_or_ge (n 0) 3 with hsmall | hbig
  · exact traj_one_of_start_one htraj (by omega)
  · exact absurd (no_cycle_of_noCycleAtLength hL htraj hcyc hbig hmin hchk)
      (fun h => h.elim)

/-! ### The lengths checked

Each `decide` below enumerates, for every admissible total valuation `K ≤ 2L`,
all compositions of `K` into `L` positive parts and confirms that none produces
an accumulator divisible by `2^K − 3^L`.  Lengths `1, 2, 4` are already settled
by `hasAdmissibleK` alone (no admissible `K` at all); the rest need the
enumeration.

With the budget pruning in `cycleScan` (each remaining step needs at least one
halving, so `kv ≤ b - r`) `L = 10` costs about 15 s of kernel time and is
included; `L = 11` still does not finish in two minutes and is omitted. -/

set_option maxHeartbeats 1000000 in
theorem noCycleAtLength_one : noCycleAtLength 1 = true := by decide
set_option maxHeartbeats 1000000 in
theorem noCycleAtLength_two : noCycleAtLength 2 = true := by decide
set_option maxHeartbeats 1000000 in
theorem noCycleAtLength_three : noCycleAtLength 3 = true := by decide
set_option maxHeartbeats 1000000 in
theorem noCycleAtLength_four : noCycleAtLength 4 = true := by decide
set_option maxHeartbeats 1000000 in
theorem noCycleAtLength_five : noCycleAtLength 5 = true := by decide
set_option maxHeartbeats 1000000 in
theorem noCycleAtLength_six : noCycleAtLength 6 = true := by decide
set_option maxHeartbeats 1000000 in
theorem noCycleAtLength_seven : noCycleAtLength 7 = true := by decide
set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem noCycleAtLength_eight : noCycleAtLength 8 = true := by decide
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
theorem noCycleAtLength_nine : noCycleAtLength 9 = true := by decide
set_option maxRecDepth 8000000 in
set_option maxHeartbeats 4000000 in
theorem noCycleAtLength_ten : noCycleAtLength 10 = true := by decide

/-- **No nontrivial cycle with at most ten odd steps.**  Every cycle of the
odd-to-odd accelerated map with `1 ≤ L ≤ 10` steps is the fixed point `1`.

This is unconditional and self-contained: no verified numerical range is
assumed, and no Diophantine approximation input is used.  The mechanism is the
window `3^L < 2^{K_L}` and `2^{K_L}·3^L ≤ 10^L`, which admits at most one or two
`K` per length, followed by an exhaustive check of the compositions of `K`. -/
theorem no_short_cycle {n k : Nat → Nat} {L : Nat} (hL : 0 < L) (hL9 : L ≤ 10)
    (htraj : Traj n k L) (hcyc : n L = n 0) (hmin : ∀ i : Nat, i < L → n 0 ≤ n i) :
    ∀ i : Nat, i ≤ L → n i = 1 := by
  have hcase : L = 1 ∨ L = 2 ∨ L = 3 ∨ L = 4 ∨ L = 5 ∨ L = 6 ∨ L = 7 ∨ L = 8 ∨ L = 9 ∨
      L = 10 := by omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cycle_trivial_of_noCycleAtLength hL htraj hcyc hmin noCycleAtLength_one
  · exact cycle_trivial_of_noCycleAtLength hL htraj hcyc hmin noCycleAtLength_two
  · exact cycle_trivial_of_noCycleAtLength hL htraj hcyc hmin noCycleAtLength_three
  · exact cycle_trivial_of_noCycleAtLength hL htraj hcyc hmin noCycleAtLength_four
  · exact cycle_trivial_of_noCycleAtLength hL htraj hcyc hmin noCycleAtLength_five
  · exact cycle_trivial_of_noCycleAtLength hL htraj hcyc hmin noCycleAtLength_six
  · exact cycle_trivial_of_noCycleAtLength hL htraj hcyc hmin noCycleAtLength_seven
  · exact cycle_trivial_of_noCycleAtLength hL htraj hcyc hmin noCycleAtLength_eight
  · exact cycle_trivial_of_noCycleAtLength hL htraj hcyc hmin noCycleAtLength_nine
  · exact cycle_trivial_of_noCycleAtLength hL htraj hcyc hmin noCycleAtLength_ten

/-! ## Circuits: cycles with a unique local maximum

A *circuit* is a cycle whose odd-map valuations are `1, 1, …, 1, k` — it rises
`L-1` times and then falls once.  The accumulator of an all-ones prefix is
forced, `Sacc = 3^L − 2^L` (the last valuation does not enter `Sacc` at all), so
the cycle identity collapses to a single Diophantine equation

  `(2^K − 3^L)·n₀ = 3^L − 2^L`.

That is one condition per `(L, K)` rather than one per composition, so it can be
checked far beyond the reach of `noCycleAtLength`.  Rozier–Terracol note that
circuits are known not to exist apart from the trivial cycle, but by
transcendence theory; the equation itself is elementary, and checking it on a
range is not. -/

/-- An all-ones prefix has `Ksum` equal to its length. -/
theorem Ksum_of_ones {k : Nat → Nat} : ∀ L : Nat, (∀ j : Nat, j < L → k j = 1) →
    Ksum k L = L := by
  intro L
  induction L with
  | zero => intro _; rfl
  | succ L ih =>
    intro h
    rw [Ksum_succ, ih (fun j hj => h j (by omega)), h L (by omega)]

/-- **The accumulator of an all-ones prefix is forced.**  Only the first `L-1`
valuations enter `Sacc k L`, so an all-ones prefix pins it to `3^L − 2^L`,
the minimum permitted by `Sacc_lower`. -/
theorem Sacc_ones_prefix {k : Nat → Nat} : ∀ L : Nat,
    (∀ j : Nat, j + 1 < L → k j = 1) → Sacc k L + 2 ^ L = 3 ^ L := by
  intro L
  induction L with
  | zero => intro _; simp
  | succ L ih =>
    intro hones
    have hIH := ih (fun j hj => hones j (by omega))
    have hK : Ksum k L = L := Ksum_of_ones L (fun j hj => hones j (by omega))
    have h2 : (2 : Nat) ^ (L + 1) = 2 * 2 ^ L := two_pow_succ L
    have h3 : (3 : Nat) ^ (L + 1) = 3 * 3 ^ L := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [Sacc_succ, hK, h2, h3]
    omega

/-- **The circuit equation.**  A cycle with an all-ones prefix satisfies
`2^{K}·n₀ + 2^L = 3^L·n₀ + 3^L`, i.e. `(2^K − 3^L)·n₀ = 3^L − 2^L`. -/
theorem circuit_equation {n k : Nat → Nat} {L : Nat}
    (htraj : Traj n k L) (hcyc : n L = n 0)
    (hones : ∀ j : Nat, j + 1 < L → k j = 1) :
    2 ^ Ksum k L * n 0 + 2 ^ L = 3 ^ L * n 0 + 3 ^ L := by
  have hid := traj_affine_exact L htraj
  rw [hcyc] at hid
  have hS := Sacc_ones_prefix L hones
  omega

/-- **The circuit band.**  A circuit with least element `n₀ ≥ 3` forces

  `3^L < 2^K`  and  `3·2^K + 2^L ≤ 4·3^L`,

so `2^K` lies in `(3^L, (4/3)·3^L)`.  Since that band has ratio `4/3 < 2` it
contains at most one power of two (`circuit_band_unique`), which is why the
circuit search has only one candidate `K` per length.

Empirically the band is non-empty for about `log₂(4/3) = 41.5%` of lengths —
`82` of the first `199` — matching the equidistribution of `L·log₂3` mod `1`. -/
theorem circuit_band {n k : Nat → Nat} {L : Nat} (hL : 0 < L)
    (htraj : Traj n k L) (hcyc : n L = n 0) (hN : 3 ≤ n 0)
    (hones : ∀ j : Nat, j + 1 < L → k j = 1) :
    3 * 2 ^ Ksum k L + 2 ^ L ≤ 4 * 3 ^ L := by
  have hpos : 0 < n 0 := by omega
  have hlo := cycle_three_pow_lt hL htraj hcyc hpos
  have heq := circuit_equation htraj hcyc hones
  have h2L : (2 : Nat) ^ L ≤ 3 ^ L := Nat.pow_le_pow_left (by omega) L
  have hsub : (2 ^ Ksum k L - 3 ^ L) * n 0 = 3 ^ L - 2 ^ L := by
    rw [Nat.sub_mul]
    omega
  have h3 : (2 ^ Ksum k L - 3 ^ L) * 3 ≤ (2 ^ Ksum k L - 3 ^ L) * n 0 :=
    Nat.mul_le_mul_left _ hN
  omega

/-- The band holds at most one power of two, so at most one `K` per length. -/
theorem circuit_band_unique {L K K' : Nat}
    (h1 : 3 ^ L < 2 ^ K) (h2 : 3 * 2 ^ K + 2 ^ L ≤ 4 * 3 ^ L)
    (h1' : 3 ^ L < 2 ^ K') (h2' : 3 * 2 ^ K' + 2 ^ L ≤ 4 * 3 ^ L) : K = K' := by
  have hp := three_pow_pos L
  rcases Nat.lt_trichotomy K K' with hlt | heq | hgt
  · exfalso
    have hd : 2 * 2 ^ K ≤ 2 ^ K' := by
      have hstep : 2 ^ (K + 1) ≤ 2 ^ K' := Nat.pow_le_pow_right (by omega) (by omega)
      rw [two_pow_succ] at hstep
      exact hstep
    -- `omega` mis-handles several distinct `2 ^ ·` atoms; make them opaque first
    generalize (3 : Nat) ^ L = A at *
    generalize (2 : Nat) ^ K = B at *
    generalize (2 : Nat) ^ L = C at *
    generalize (2 : Nat) ^ K' = D at *
    omega
  · exact heq
  · exfalso
    have hd : 2 * 2 ^ K' ≤ 2 ^ K := by
      have hstep : 2 ^ (K' + 1) ≤ 2 ^ K := Nat.pow_le_pow_right (by omega) (by omega)
      rw [two_pow_succ] at hstep
      exact hstep
    generalize (3 : Nat) ^ L = A at *
    generalize (2 : Nat) ^ K = B at *
    generalize (2 : Nat) ^ L = C at *
    generalize (2 : Nat) ^ K' = D at *
    omega

/-- Does the circuit equation have a solution with `n₀ ≥ 3` at `(L, K)`? -/
def circuitSolves (L K : Nat) : Bool :=
  decide (3 ^ L < 2 ^ K) &&
    decide ((3 ^ L - 2 ^ L) % (2 ^ K - 3 ^ L) = 0) &&
    decide (3 ≤ (3 ^ L - 2 ^ L) / (2 ^ K - 3 ^ L))

/-- No admissible total valuation solves the circuit equation at length `L`. -/
def noCircuitAtLength (L : Nat) : Bool :=
  (List.range (2 * L + 1)).all fun K => !(circuitSolves L K)

/-- **No nontrivial circuit at a checked length.** -/
theorem no_circuit_of_check {n k : Nat → Nat} {L : Nat} (hL : 0 < L)
    (htraj : Traj n k L) (hcyc : n L = n 0) (hN : 3 ≤ n 0)
    (hmin : ∀ i : Nat, i < L → n 0 ≤ n i)
    (hones : ∀ j : Nat, j + 1 < L → k j = 1)
    (hchk : noCircuitAtLength L = true) : False := by
  have hpos : 0 < n 0 := by omega
  have hlo := cycle_three_pow_lt hL htraj hcyc hpos
  have hKle := cycle_Ksum_le htraj hcyc hpos (by omega) hmin
  have heq := circuit_equation htraj hcyc hones
  have hsolve : circuitSolves L (Ksum k L) = true := by
    have hsub : (2 ^ Ksum k L - 3 ^ L) * n 0 = 3 ^ L - 2 ^ L := by
      rw [Nat.sub_mul]
      omega
    simp only [circuitSolves, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨hlo, ?_⟩, ?_⟩
    · rw [← hsub]; exact Nat.mul_mod_right _ _
    · rw [← hsub, Nat.mul_div_cancel_left _ (by omega)]
      exact hN
  have hall := List.all_eq_true.mp hchk (Ksum k L) (List.mem_range.mpr (by omega))
  rw [hsolve] at hall
  exact Bool.noConfusion hall

/-- No circuit at any length up to `B`. -/
def noCircuitUpTo (B : Nat) : Bool := (List.range (B + 1)).all noCircuitAtLength

set_option maxRecDepth 200000 in
set_option maxHeartbeats 2000000 in
/-- The circuit equation has no solution with `n₀ ≥ 3` at any length `≤ 100`.

Larger bounds also pass — `noCircuitUpTo 200` takes about 13 s and
`noCircuitUpTo 400` about 54 s — and are omitted only to keep the build fast. -/
theorem noCircuitUpTo_100 : noCircuitUpTo 100 = true := by decide

/-- **No nontrivial circuit with at most 100 odd steps.**

Compare `no_short_cycle`, which reaches only `L ≤ 10`: a general cycle needs one
check per *composition* of `K` into `L` parts, whereas a circuit needs one check
per `(L, K)`.  Fixing the valuation pattern to `1,…,1,k` collapses the search
from exponential to quadratic, which is the whole reason this reaches ten times
further.

Unconditional: no verified range and no transcendence input.  (The literature
excludes circuits at *every* length, but by Baker's method.) -/
theorem no_circuit_below_101 {n k : Nat → Nat} {L : Nat} (hL : 0 < L) (hB : L ≤ 100)
    (htraj : Traj n k L) (hcyc : n L = n 0) (hN : 3 ≤ n 0)
    (hmin : ∀ i : Nat, i < L → n 0 ≤ n i)
    (hones : ∀ j : Nat, j + 1 < L → k j = 1) : False :=
  no_circuit_of_check hL htraj hcyc hN hmin hones
    (List.all_eq_true.mp noCircuitUpTo_100 L (List.mem_range.mpr (by omega)))

/-! ### One big valuation before the last

The circuit collapse generalizes.  If the valuations are all `1` before the last
except at a single index `p`, where the value is `c ≥ 2`, then `Sacc` again
depends on only finitely many parameters — now `(L, p, c)` instead of nothing —
and the cycle identity becomes one Diophantine check per `(L, K, p, c)`.  This is
the case of two local minima. -/

/-- All valuations before the last are `1`, except at index `p` where it is `c`. -/
def OneBigPattern (k : Nat → Nat) (L p c : Nat) : Prop :=
  p + 1 < L ∧ 2 ≤ c ∧ k p = c ∧ ∀ j : Nat, j + 1 < L → j ≠ p → k j = 1

theorem Ksum_oneBig_le {k : Nat → Nat} {L p c : Nat} (h : OneBigPattern k L p c) :
    ∀ m : Nat, m ≤ p → Ksum k m = m := by
  have hp := h.1
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    rw [Ksum_succ, ih (by omega), h.2.2.2 m (by omega) (by omega)]

theorem Ksum_oneBig_gt {k : Nat → Nat} {L p c : Nat} (h : OneBigPattern k L p c) :
    ∀ b : Nat, p + 1 + b < L → Ksum k (p + 1 + b) + 1 = p + 1 + b + c := by
  have hp := h.1
  intro b
  induction b with
  | zero =>
    intro _
    rw [Nat.add_zero, Ksum_succ, Ksum_oneBig_le h p (Nat.le_refl _), h.2.2.1]
    omega
  | succ b ih =>
    intro hb
    have hIH := ih (by omega)
    rw [show p + 1 + (b + 1) = (p + 1 + b) + 1 by omega, Ksum_succ,
      h.2.2.2 (p + 1 + b) (by omega) (by omega)]
    omega

/-- **`Sacc` under the one-big pattern.**  With `a = p+1` and `L = a + b`,

  `Sacc + 3^b·2^a + 2^{p+c}·2^b = 3^b·3^a + 2^{p+c}·3^b`,

the subtraction-free form of
`Sacc = 3^b(3^a − 2^a) + 2^{p+c}(3^b − 2^b)`. -/
theorem Sacc_oneBig {k : Nat → Nat} {L p c : Nat} (h : OneBigPattern k L p c) :
    ∀ b : Nat, p + 1 + b < L + 1 →

      Sacc k (p + 1 + b) + 3 ^ b * 2 ^ (p + 1) + 2 ^ (p + c) * 2 ^ b
        = 3 ^ b * 3 ^ (p + 1) + 2 ^ (p + c) * 3 ^ b := by
  intro b
  induction b with
  | zero =>
    intro _
    have hbase : Sacc k (p + 1) + 2 ^ (p + 1) = 3 ^ (p + 1) := by
      refine Sacc_ones_prefix (p + 1) (fun j hj => h.2.2.2 j (by omega) (by omega))
    simp only [Nat.pow_zero, Nat.one_mul, Nat.mul_one, Nat.add_zero]
    omega
  | succ b ih =>
    intro hb
    have hIH := ih (by omega)
    have hK : Ksum k (p + 1 + b) + 1 = p + 1 + b + c := Ksum_oneBig_gt h b (by omega)
    have hKval : Ksum k (p + 1 + b) = p + c + b := by omega
    have hstep : Sacc k (p + 1 + (b + 1)) = 3 * Sacc k (p + 1 + b) + 2 ^ (p + c + b) := by
      rw [show p + 1 + (b + 1) = (p + 1 + b) + 1 by omega, Sacc_succ, hKval]
    have e2 : (2 : Nat) ^ (p + c + b) = 2 ^ (p + c) * 2 ^ b := by rw [Nat.pow_add]
    have e3 : (3 : Nat) ^ (b + 1) = 3 * 3 ^ b := by rw [Nat.pow_succ, Nat.mul_comm]
    have e4 : (2 : Nat) ^ (b + 1) = 2 * 2 ^ b := two_pow_succ b
    have d1 : (3 * 3 ^ b) * 3 ^ (p + 1) = 3 * (3 ^ b * 3 ^ (p + 1)) := by
      rw [Nat.mul_assoc]
    have d2 : (3 * 3 ^ b) * 2 ^ (p + 1) = 3 * (3 ^ b * 2 ^ (p + 1)) := by
      rw [Nat.mul_assoc]
    have d3 : 2 ^ (p + c) * (3 * 3 ^ b) = 3 * (2 ^ (p + c) * 3 ^ b) := by
      rw [Nat.mul_left_comm]
    have d4 : 2 ^ (p + c) * (2 * 2 ^ b) = 2 * (2 ^ (p + c) * 2 ^ b) := by
      rw [Nat.mul_left_comm]
    rw [hstep, e3, e4]
    omega

/-- The two sides of the one-big `Sacc` identity, kept subtraction-free. -/
def oneBigLhs (L p c : Nat) : Nat :=
  3 ^ (L - p - 1) * 2 ^ (p + 1) + 2 ^ (p + c) * 2 ^ (L - p - 1)

def oneBigRhs (L p c : Nat) : Nat := 3 ^ L + 2 ^ (p + c) * 3 ^ (L - p - 1)

theorem Sacc_oneBig_eq {k : Nat → Nat} {L p c : Nat} (h : OneBigPattern k L p c) :
    Sacc k L + oneBigLhs L p c = oneBigRhs L p c := by
  have hp := h.1
  have hb := Sacc_oneBig h (L - p - 1) (by omega)
  rw [show p + 1 + (L - p - 1) = L by omega] at hb
  have h3 : (3 : Nat) ^ (L - p - 1) * 3 ^ (p + 1) = 3 ^ L := by
    rw [← Nat.pow_add]
    congr 1
    omega
  unfold oneBigLhs oneBigRhs
  omega

/-- Does the one-big equation have a solution with `n₀ ≥ 3` at `(L, K, p, c)`? -/
def oneBigSolves (L K p c : Nat) : Bool :=
  decide (3 ^ L < 2 ^ K) && decide (oneBigLhs L p c ≤ oneBigRhs L p c) &&
    decide ((oneBigRhs L p c - oneBigLhs L p c) % (2 ^ K - 3 ^ L) = 0) &&
    decide (3 ≤ (oneBigRhs L p c - oneBigLhs L p c) / (2 ^ K - 3 ^ L))

/-- No admissible `(K, p, c)` solves it at length `L`. -/
def noOneBigAtLength (L : Nat) : Bool :=
  (List.range (2 * L + 1)).all fun K =>
    (List.range L).all fun p =>
      (List.range (2 * L + 2)).all fun c =>
        -- `c` must be consistent with `K`: the last valuation is `K - (L-2) - c ≥ 1`
        !(decide (p + 1 < L) && decide (2 ≤ c) && decide (c + L ≤ K + 1) &&
          oneBigSolves L K p c)

def noOneBigUpTo (B : Nat) : Bool := (List.range (B + 1)).all noOneBigAtLength

/-- **No nontrivial cycle with the one-big pattern at a checked length.** -/
theorem no_oneBig_of_check {n k : Nat → Nat} {L p c : Nat} (hL : 0 < L)
    (htraj : Traj n k L) (hcyc : n L = n 0) (hN : 3 ≤ n 0)
    (hmin : ∀ i : Nat, i < L → n 0 ≤ n i) (hpat : OneBigPattern k L p c)
    (hc : c < 2 * L + 2) (hchk : noOneBigAtLength L = true) : False := by
  have hpos : 0 < n 0 := by omega
  have hp1 : p + 1 < L := hpat.1
  have hlo := cycle_three_pow_lt hL htraj hcyc hpos
  have hKle := cycle_Ksum_le htraj hcyc hpos (by omega) hmin
  have hid := traj_affine_exact L htraj
  rw [hcyc] at hid
  have hS := Sacc_oneBig_eq hpat
  have hle : oneBigLhs L p c ≤ oneBigRhs L p c := by omega
  have hSacc : Sacc k L = oneBigRhs L p c - oneBigLhs L p c := by omega
  have hsub : (2 ^ Ksum k L - 3 ^ L) * n 0 = oneBigRhs L p c - oneBigLhs L p c := by
    rw [Nat.sub_mul, ← hSacc]
    omega
  have hsolve : oneBigSolves L (Ksum k L) p c = true := by
    simp only [oneBigSolves, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨hlo, hle⟩, ?_⟩, ?_⟩
    · rw [← hsub]; exact Nat.mul_mod_right _ _
    · rw [← hsub, Nat.mul_div_cancel_left _ (by omega)]; exact hN
  have hallK := List.all_eq_true.mp hchk (Ksum k L) (List.mem_range.mpr (by omega))
  have hallP := List.all_eq_true.mp hallK p (List.mem_range.mpr (by omega))
  -- the last valuation is at least 1, which pins `c` against `K`
  have hKlast : Ksum k L = Ksum k (L - 1) + k (L - 1) := by
    rw [show L = (L - 1) + 1 by omega, Ksum_succ]
    congr 1 <;> omega
  have hKmid : Ksum k (L - 1) + 1 = (L - 1) + c := by
    have h := Ksum_oneBig_gt hpat (L - p - 2) (by omega)
    rw [show p + 1 + (L - p - 2) = L - 1 by omega] at h
    omega
  have hlast : 1 ≤ k (L - 1) := (htraj (L - 1) (by omega)).1
  have hcK : c + L ≤ Ksum k L + 1 := by omega
  have hallC := List.all_eq_true.mp hallP c (List.mem_range.mpr hc)
  rw [hsolve] at hallC
  simp only [hpat.1, hpat.2.1, hcK, decide_true, Bool.and_self, Bool.and_true,
    Bool.not_eq_true'] at hallC
  exact Bool.noConfusion hallC

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- The one-big equation has no solution with `n₀ ≥ 3` at any length `≤ 12`.

Larger bounds pass too — `16` takes about 15 s and `20` about 36 s — and are
omitted to keep the build fast.  A python scan finds no solution for `L ≤ 60`. -/
theorem noOneBigUpTo_12 : noOneBigUpTo 12 = true := by decide

/-- **No nontrivial cycle with one big valuation before the last, at length
`≤ 12`.**  This is the case of two local minima.

The reach is smaller than `no_circuit_below_101` because the search now carries
two free parameters `(p, c)` rather than none, but it is still polynomial where
the general `noCycleAtLength` is exponential — which is why it passes `L = 10`,
where the unrestricted check stops. -/
theorem no_oneBig_below_13 {n k : Nat → Nat} {L p c : Nat} (hL : 0 < L) (hB : L ≤ 12)
    (htraj : Traj n k L) (hcyc : n L = n 0) (hN : 3 ≤ n 0)
    (hmin : ∀ i : Nat, i < L → n 0 ≤ n i) (hpat : OneBigPattern k L p c)
    (hc : c < 2 * L + 2) : False :=
  no_oneBig_of_check hL htraj hcyc hN hmin hpat hc
    (List.all_eq_true.mp noOneBigUpTo_12 L (List.mem_range.mpr (by omega)))

/-! ### Patterns that are already excluded

A pattern in which *every* non-final valuation is at least `2` needs no new
machinery: `bigCount_bound_three` already forbids it beyond `L = 3`, and
`no_short_cycle` covers what remains.  This is the counting bound doing real
work — a cycle simply cannot afford `L-1` valuations of size `≥ 2`. -/

theorem two_mul_five_pow_lt {L : Nat} (hL : 4 ≤ L) : 2 * 5 ^ L < 6 ^ L := by
  obtain ⟨r, hr⟩ : ∃ r, L = 4 + r := ⟨L - 4, by omega⟩
  subst hr
  induction r with
  | zero => decide
  | succ r ih =>
    have hIH := ih (by omega)
    have e5 : (5 : Nat) ^ (4 + (r + 1)) = 5 * 5 ^ (4 + r) := by
      rw [show 4 + (r + 1) = (4 + r) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    have e6 : (6 : Nat) ^ (4 + (r + 1)) = 6 * 6 ^ (4 + r) := by
      rw [show 4 + (r + 1) = (4 + r) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    omega

/-- If the first `L` valuations are all big then `bigCount` is `L`. -/
theorem bigCount_all_big {k : Nat → Nat} : ∀ L : Nat,
    (∀ j : Nat, j < L → 2 ≤ k j) → L ≤ bigCount k L := by
  intro L
  induction L with
  | zero => intro _; omega
  | succ L ih =>
    intro hbig
    have hIH := ih (fun j hj => hbig j (by omega))
    rw [bigCount_succ, if_pos (hbig L (by omega))]
    omega

/-- `bigCount` is monotone in the number of steps. -/
theorem bigCount_mono (k : Nat → Nat) : ∀ a b : Nat, a ≤ b →
    bigCount k a ≤ bigCount k b := by
  intro a b hab
  obtain ⟨t, ht⟩ : ∃ t, b = a + t := ⟨b - a, by omega⟩
  subst ht
  induction t with
  | zero => exact Nat.le_refl _
  | succ t ih =>
    rw [show a + (t + 1) = (a + t) + 1 by omega, bigCount_succ]
    split <;> omega

/-- **No cycle has every non-final valuation `≥ 2`, beyond length 3.**  With
`L - 1` big valuations, `bigCount_bound_three` gives `2^{L-1}·3^L ≤ 5^L`, i.e.
`6^L ≤ 2·5^L`, which fails from `L = 4` on. -/
theorem no_all_big_pattern {n k : Nat → Nat} {L : Nat} (hL : 4 ≤ L)
    (htraj : Traj n k L) (hcyc : n L = n 0)
    (hmin : ∀ i : Nat, i < L → 3 ≤ n i)
    (hbig : ∀ j : Nat, j + 1 < L → 2 ≤ k j) : False := by
  have hposL : 0 < n L := by
    have := hmin 0 (by omega); rw [hcyc]; omega
  have hbd := bigCount_bound_three htraj (by omega) hposL hmin
  have hge : L - 1 ≤ bigCount k L :=
    Nat.le_trans (bigCount_all_big (L - 1) (fun j hj => hbig j (by omega)))
      (bigCount_mono k (L - 1) L (by omega))
  have hmono : 2 ^ (L - 1) ≤ 2 ^ bigCount k L :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hkey : 2 ^ (L - 1) * 3 ^ L ≤ 5 ^ L := by
    have := Nat.mul_le_mul_right (3 ^ L) hmono
    omega
  have hsix : 2 ^ (L - 1) * 3 ^ L * 2 = 6 ^ L := by
    have e : (6 : Nat) ^ L = 2 ^ L * 3 ^ L := by rw [← Nat.mul_pow]
    have e2 : (2 : Nat) ^ L = 2 ^ (L - 1) * 2 := by
      rw [show L = (L - 1) + 1 by omega, Nat.pow_succ]
      congr 2 <;> omega
    rw [e, e2]
    simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  have hlt := two_mul_five_pow_lt hL
  omega

/-! ### The pattern checks are not vacuous

A search that passes because its condition never fires proves nothing.  Both
pattern checks *do* fire: the divisibility holds in each family, and it is the
`n₀ ≥ 3` guard — not the divisibility — that rejects the hit.

* Circuits: at `L = 1`, `K = 2` the equation reads `1·n₀ = 1`, so `n₀ = 1`.
* One big: at `L = 2`, `K = 4`, `p = 0`, `c = 2` it reads `7·n₀ = 7`, so `n₀ = 1`.

Both are the trivial cycle.  Over the whole checked range these are the *only*
solutions of the divisibility at all — for the one-big family, exactly one tuple
in `72 671` is divisible up to `L = 30`. -/

theorem circuit_check_nonvacuous :
    (3 ^ 1 - 2 ^ 1) % (2 ^ 2 - 3 ^ 1) = 0 ∧ (3 ^ 1 - 2 ^ 1) / (2 ^ 2 - 3 ^ 1) = 1 := by
  decide

theorem oneBig_check_nonvacuous :
    (oneBigRhs 2 0 2 - oneBigLhs 2 0 2) % (2 ^ 4 - 3 ^ 2) = 0 ∧
      (oneBigRhs 2 0 2 - oneBigLhs 2 0 2) / (2 ^ 4 - 3 ^ 2) = 1 := by decide

/-! ## Runs of valuation one are bounded (Lemma 5.3) -/

theorem three_pow_odd (L : Nat) : 3 ^ L % 2 = 1 := by
  induction L with
  | zero => rfl
  | succ L ih => rw [Nat.pow_succ]; omega

/-- Along a run of steps all of valuation `1`, `n_i + 1` scales by exactly
`3/2` each step. -/
theorem ones_identity {n k : Nat → Nat} : ∀ L : Nat, Traj n k L →
    (∀ i : Nat, i < L → k i = 1) →
    2 ^ L * (n L + 1) = 3 ^ L * (n 0 + 1) := by
  intro L
  induction L with
  | zero => intro _ _; simp
  | succ L ih =>
    intro htraj hones
    have hIH := ih (htraj.le (by omega)) (fun i hi => hones i (by omega))
    have hstep := (htraj L (by omega)).2.2
    rw [hones L (by omega), Nat.pow_one] at hstep
    calc 2 ^ (L + 1) * (n (L + 1) + 1)
        = 2 ^ L * (2 * (n (L + 1) + 1)) := by
          rw [two_pow_succ, Nat.mul_assoc, Nat.mul_left_comm]
      _ = 2 ^ L * (3 * (n L + 1)) :=
          congrArg (fun t => 2 ^ L * t) (show 2 * (n (L + 1) + 1) = 3 * (n L + 1) by omega)
      _ = 3 * (2 ^ L * (n L + 1)) := by rw [Nat.mul_left_comm]
      _ = 3 * (3 ^ L * (n 0 + 1)) := by rw [hIH]
      _ = 3 ^ (L + 1) * (n 0 + 1) := by
          rw [Nat.pow_succ, Nat.mul_comm (3 ^ L) 3, Nat.mul_assoc]

/-- **A run of `L` steps of valuation `1` forces `2^L ∣ n₀ + 1`.**  Hence the
number of consecutive initial steps with valuation `1` is at most `v₂(n₀+1)`,
and in `ℤ` no trajectory has valuation `1` forever. -/
theorem ones_two_pow_dvd {n k : Nat → Nat} (L : Nat) (htraj : Traj n k L)
    (hones : ∀ i : Nat, i < L → k i = 1) : 2 ^ L ∣ n 0 + 1 := by
  have hid := ones_identity L htraj hones
  exact dvd_of_odd_mul (three_pow_odd L) L (n 0 + 1) ⟨n L + 1, by omega⟩

/-- Concretely: a run of `L` valuation-one steps forces `2 ^ L ≤ n 0 + 1`. -/
theorem ones_run_le {n k : Nat → Nat} (L : Nat) (htraj : Traj n k L)
    (hones : ∀ i : Nat, i < L → k i = 1) : 2 ^ L ≤ n 0 + 1 :=
  Nat.le_of_dvd (by omega) (ones_two_pow_dvd L htraj hones)

/-! ## The ascent family (Theorem 4.1 / Gap 1)

`asc i j = 3^i · 2^j − 1`.  One step of valuation `1` sends `asc i (j+1)` to
`asc (i+1) j`, strictly upwards.  Starting from `asc 0 (L+1) = 2^{L+1} − 1`,
`L` such steps reach `asc L 1 = 2·3^L − 1`. -/

/-- The ascent family. -/
def asc (i j : Nat) : Nat := 3 ^ i * 2 ^ j - 1

theorem asc_base_pos (i j : Nat) : 1 ≤ 3 ^ i * 2 ^ j :=
  Nat.mul_pos (three_pow_pos i) (two_pow_pos j)

theorem asc_base_succ (i j : Nat) : 3 ^ i * 2 ^ (j + 1) = 2 * (3 ^ i * 2 ^ j) := by
  rw [two_pow_succ, Nat.mul_left_comm]

theorem asc_base_succ' (i j : Nat) : 3 ^ (i + 1) * 2 ^ j = 3 * (3 ^ i * 2 ^ j) := by
  rw [Nat.pow_succ, Nat.mul_comm (3 ^ i) 3, Nat.mul_assoc]

theorem asc_even_base {i j : Nat} (hj : 1 ≤ j) : (3 ^ i * 2 ^ j) % 2 = 0 := by
  obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
  rw [asc_base_succ]
  omega

/-- **One ascending step.** -/
theorem asc_step {i j : Nat} (hj : 1 ≤ j) : OddStep (asc i (j + 1)) 1 (asc (i + 1) j) := by
  have hA := asc_base_pos i j
  have h2 := asc_base_succ i j
  have h3 := asc_base_succ' i j
  have heven := asc_even_base (i := i) hj
  refine ⟨by omega, ?_, ?_⟩
  · unfold asc; omega
  · rw [Nat.pow_one]; unfold asc; omega

/-- **The step ascends.** -/
theorem asc_lt {i j : Nat} (hj : 1 ≤ j) : asc i (j + 1) < asc (i + 1) j := by
  have hA := asc_base_pos i j
  have h2 := asc_base_succ i j
  have h3 := asc_base_succ' i j
  unfold asc; omega

/-- The chain of length `L` starting at `2^{L+1} − 1`. -/
def ascChain (L : Nat) (i : Nat) : Nat := asc i (L + 1 - i)

theorem ascChain_zero (L : Nat) : ascChain L 0 = 2 ^ (L + 1) - 1 := by
  unfold ascChain asc
  simp

theorem ascChain_last (L : Nat) : ascChain L L = 2 * 3 ^ L - 1 := by
  unfold ascChain asc
  rw [show L + 1 - L = 1 by omega, Nat.pow_one, Nat.mul_comm]

theorem ascChain_step {L i : Nat} (hi : i < L) :
    OddStep (ascChain L i) 1 (ascChain L (i + 1)) := by
  unfold ascChain
  rw [show L + 1 - i = (L - i - 1) + 1 + 1 by omega,
    show L + 1 - (i + 1) = (L - i - 1) + 1 by omega]
  exact asc_step (by omega)

theorem ascChain_lt {L i : Nat} (hi : i < L) : ascChain L i < ascChain L (i + 1) := by
  unfold ascChain
  rw [show L + 1 - i = (L - i - 1) + 1 + 1 by omega,
    show L + 1 - (i + 1) = (L - i - 1) + 1 by omega]
  exact asc_lt (by omega)

theorem ascChain_traj (L : Nat) : Traj (ascChain L) (fun _ => 1) L :=
  fun _ hi => ascChain_step hi

/-! ## Chain helpers -/

theorem chain_mono (f : Nat → Nat) : ∀ L : Nat,
    (∀ i : Nat, i < L → f i < f (i + 1)) → f 0 ≤ f L := by
  intro L
  induction L with
  | zero => intro _; exact Nat.le_refl _
  | succ L ih =>
    intro h
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h L (by omega)
    omega

theorem chain_le (f : Nat → Nat) : ∀ L : Nat,
    (∀ i : Nat, i < L → f (i + 1) < f i) → f L ≤ f 0 := by
  intro L
  induction L with
  | zero => intro _; exact Nat.le_refl _
  | succ L ih =>
    intro h
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h L (by omega)
    omega

theorem chain_lt (f : Nat → Nat) {L : Nat} (hL : 0 < L)
    (h : ∀ i : Nat, i < L → f (i + 1) < f i) : f L < f 0 := by
  obtain ⟨M, rfl⟩ : ∃ M, L = M + 1 := ⟨L - 1, by omega⟩
  have h1 := chain_le f M (fun i hi => h i (by omega))
  have h2 := h M (by omega)
  omega

@[simp] theorem Ksum_const_one (L : Nat) : Ksum (fun _ => 1) L = L := by
  induction L with
  | zero => rfl
  | succ L ih => rw [Ksum_succ, ih]

/-! ### The all-ones class, exactly

`ones_two_pow_dvd` says a run of `L` valuation-one steps forces `2^L ∣ n₀+1`.
Conversely the whole residue class `n ≡ −1 (mod 2^{L+1})` realizes such a run,
so Corollary 4.2 of the notes — "`{n : k₁ = ⋯ = k_L = 1}` is a nonempty residue
class, hence infinite" — is exact and not merely an example. -/

/-- The ascent family with an arbitrary odd-class parameter `t`. -/
def ascT (i j t : Nat) : Nat := 3 ^ i * 2 ^ j * t - 1

theorem ascT_base_pos {i j t : Nat} (ht : 1 ≤ t) : 1 ≤ 3 ^ i * 2 ^ j * t :=
  Nat.mul_pos (Nat.mul_pos (three_pow_pos i) (two_pow_pos j)) (by omega)

theorem ascT_step {i j t : Nat} (hj : 1 ≤ j) (ht : 1 ≤ t) :
    OddStep (ascT i (j + 1) t) 1 (ascT (i + 1) j t) := by
  have hA := ascT_base_pos (i := i) (j := j) (t := t) ht
  have h2 : 3 ^ i * 2 ^ (j + 1) * t = 2 * (3 ^ i * 2 ^ j * t) := by
    rw [two_pow_succ]
    simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  have h3 : 3 ^ (i + 1) * 2 ^ j * t = 3 * (3 ^ i * 2 ^ j * t) := by
    rw [Nat.pow_succ]
    simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  have heven : (3 ^ i * 2 ^ j * t) % 2 = 0 := by
    obtain ⟨u, hu⟩ : ∃ u, j = u + 1 := ⟨j - 1, by omega⟩
    subst hu
    have : 3 ^ i * 2 ^ (u + 1) * t = 2 * (3 ^ i * 2 ^ u * t) := by
      rw [two_pow_succ]
      simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    omega
  refine ⟨by omega, ?_, ?_⟩
  · unfold ascT; omega
  · rw [Nat.pow_one]; unfold ascT; omega

/-- The `L`-step chain living in the class `n ≡ −1 (mod 2^{L+1})`. -/
def ascTChain (L t : Nat) (i : Nat) : Nat := ascT i (L + 1 - i) t

theorem ascTChain_zero (L t : Nat) : ascTChain L t 0 = 2 ^ (L + 1) * t - 1 := by
  unfold ascTChain ascT
  simp

theorem ascTChain_step {L t i : Nat} (ht : 1 ≤ t) (hi : i < L) :
    OddStep (ascTChain L t i) 1 (ascTChain L t (i + 1)) := by
  unfold ascTChain
  rw [show L + 1 - i = (L - i - 1) + 1 + 1 by omega,
    show L + 1 - (i + 1) = (L - i - 1) + 1 by omega]
  exact ascT_step (by omega) ht

theorem ascTChain_traj (L t : Nat) (ht : 1 ≤ t) :
    Traj (ascTChain L t) (fun _ => 1) L :=
  fun _ hi => ascTChain_step ht hi

/-- **The all-ones class is realized in full.**  Every `n` with
`n + 1 = 2^{L+1}·t` (`t ≥ 1`) begins with `L` steps of valuation `1`.  With
`ones_two_pow_dvd` in the other direction, this pins the class exactly. -/
theorem ones_run_of_class {L t : Nat} (ht : 1 ≤ t) :
    ∃ n : Nat → Nat, n 0 = 2 ^ (L + 1) * t - 1 ∧
      Traj n (fun _ => 1) L ∧ (∀ i : Nat, i < L → (fun _ => 1) i = 1) :=
  ⟨ascTChain L t, ascTChain_zero L t, ascTChain_traj L t ht, fun _ _ => rfl⟩

/-! ## Barrier: the ascent chain, and what it forbids

`ascChain L` starts at `2^{L+1} − 1`, takes `L` steps of valuation `1`, and
ends at `2·3^L − 1`.  Every intermediate value is larger than the previous. -/

/-- **Gap 1, exact form.**  For every `L` there is an odd start `2^{L+1} − 1`
whose orbit rises monotonically to `2·3^L − 1` in `L` steps.  Since
`2^{L+1} − 1 < 2^{L+1}` and `3^L ≤ 2·3^L − 1`, any bound `F` on the excursion
must satisfy `F(2^{L+1} − 1) ≥ 3^L` for every `L`: excursions are provably
super-linear with exponent at least `log₂ 3`. -/
theorem excursion_unbounded (L : Nat) :
    ascChain L 0 = 2 ^ (L + 1) - 1 ∧
    ascChain L L = 2 * 3 ^ L - 1 ∧
    3 ^ L ≤ ascChain L L ∧
    Traj (ascChain L) (fun _ => 1) L ∧
    (∀ i : Nat, i < L → ascChain L i < ascChain L (i + 1)) := by
  refine ⟨ascChain_zero L, ascChain_last L, ?_, ascChain_traj L, fun i hi => ascChain_lt hi⟩
  rw [ascChain_last]
  have := three_pow_pos L
  omega

/-- **Gap 5, exact form.**  The coefficient stopping time is unbounded: the
first `L` steps from `2^{L+1} − 1` all have valuation `1`, so `2^{K_i} ≤ 3^i`
for every `i ≤ L` and no coefficient drop has occurred.  Hence no covering of
the odd integers by residue classes carrying descent certificates of
*uniformly bounded* length can exist. -/
theorem coefficient_stopping_time_unbounded (L : Nat) :
    Traj (ascChain L) (fun _ => 1) L ∧
    ascChain L 0 = 2 ^ (L + 1) - 1 ∧
    (∀ i : Nat, i ≤ L → 2 ^ Ksum (fun _ => 1) i ≤ 3 ^ i) ∧
    (∀ i : Nat, i ≤ L → ascChain L 0 ≤ ascChain L i) := by
  refine ⟨ascChain_traj L, ascChain_zero L, ?_, ?_⟩
  · intro i _
    rw [Ksum_const_one]
    exact Nat.pow_le_pow_left (by omega) i
  · intro i _
    exact chain_mono (ascChain L) i (fun t ht => ascChain_lt (by omega))

/-! ## Barrier: no locally reweighted power of `n` can be a descent function -/

/-- `C · 2^t ≤ 3^t` as soon as `t ≥ 2C`. -/
theorem pow_bound {C t : Nat} (ht : 2 * C ≤ t) : C * 2 ^ t ≤ 3 ^ t := by
  obtain ⟨r, rfl⟩ : ∃ r, t = 2 * C + r := ⟨t - 2 * C, by omega⟩
  induction r with
  | zero =>
    have h9 : (3 : Nat) ^ (2 * C) = 9 ^ C := by rw [Nat.pow_mul]
    have h4 : (2 : Nat) ^ (2 * C) = 4 ^ C := by rw [Nat.pow_mul]
    have hmp : (2 : Nat) ^ C * 4 ^ C = 8 ^ C := by rw [← Nat.mul_pow]
    have hC : C ≤ 2 ^ C := Nat.le_of_lt (lt_two_pow C)
    calc C * 2 ^ (2 * C + 0) = C * 4 ^ C := by rw [Nat.add_zero, h4]
      _ ≤ 2 ^ C * 4 ^ C := Nat.mul_le_mul_right _ hC
      _ = 8 ^ C := hmp
      _ ≤ 9 ^ C := Nat.pow_le_pow_left (by omega) C
      _ = 3 ^ (2 * C + 0) := by rw [Nat.add_zero, h9]
  | succ r ih =>
    have hih := ih (by omega)
    have e2 : (2 : Nat) ^ (2 * C + (r + 1)) = 2 * 2 ^ (2 * C + r) := by
      rw [show 2 * C + (r + 1) = (2 * C + r) + 1 by omega, two_pow_succ]
    have e3 : (3 : Nat) ^ (2 * C + (r + 1)) = 3 * 3 ^ (2 * C + r) := by
      rw [show 2 * C + (r + 1) = (2 * C + r) + 1 by omega, Nat.pow_succ,
        Nat.mul_comm]
    rw [e2, e3, Nat.mul_left_comm]
    omega

/-- **Gap 6, exact form.**  Let `φ` be comparable to `n^{e/d}` in the sense
`B·n^e ≤ φ(n)^d ≤ A·n^e`.  Then `φ` does **not** strictly decrease along every
odd step from an odd `n > 1`.

Taking `d = e = 1` and `φ(n) = c(n mod 2^M)·n` with `B ≤ c ≤ A` rules out every
2-adically local reweighting of `n`; taking `d = 2, e = 1` rules out `√n`; and
`e/d` arbitrary rules out every rational power.  So any descent function for the
Collatz map must depend on `n` beyond every fixed 2-adic precision. -/
theorem no_power_descent {d e A B : Nat} (hd : 1 ≤ d) (he : 1 ≤ e)
    (hA : 1 ≤ A) (hB : 1 ≤ B) (φ : Nat → Nat)
    (hlow : ∀ x : Nat, B * x ^ e ≤ φ x ^ d)
    (hhigh : ∀ x : Nat, φ x ^ d ≤ A * x ^ e) :
    ¬ (∀ x k y : Nat, 1 < x → OddStep x k y → φ y < φ x) := by
  intro hdesc
  -- the length of the ascent we need
  obtain ⟨C, hCdef⟩ : ∃ C : Nat, C = A * 2 ^ e := ⟨_, rfl⟩
  have h2e : 2 ≤ 2 ^ e := by
    obtain ⟨t, rfl⟩ : ∃ t, e = t + 1 := ⟨e - 1, by omega⟩
    rw [two_pow_succ]
    have := two_pow_pos t
    omega
  have hC : 2 ≤ C := by
    have h := Nat.mul_le_mul hA h2e
    omega
  obtain ⟨L, hLdef⟩ : ∃ L : Nat, L = 2 * C := ⟨_, rfl⟩
  have hL : 1 ≤ L := by omega
  -- every value on the chain exceeds 1
  have hzero : 1 < ascChain L 0 := by
    rw [ascChain_zero]
    have h1 : 2 ^ 2 ≤ 2 ^ (L + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : (2 : Nat) ^ 2 = 4 := rfl
    omega
  have hgt1 : ∀ i : Nat, i ≤ L → 1 < ascChain L i := by
    intro i _
    have := chain_mono (ascChain L) i (fun t ht => ascChain_lt (by omega))
    omega
  -- φ strictly decreases at each step, hence over the whole chain
  have hfin : φ (ascChain L L) < φ (ascChain L 0) :=
    chain_lt (fun i => φ (ascChain L i)) hL
      (fun i hi => hdesc _ 1 _ (hgt1 i (by omega)) (ascChain_step hi))
  -- the two sides of the comparison
  have hn0 : ascChain L 0 ≤ 2 ^ (L + 1) := by
    rw [ascChain_zero]; exact Nat.sub_le _ 1
  have hnL : 3 ^ L ≤ ascChain L L := by
    rw [ascChain_last]; have := three_pow_pos L; omega
  have hexp : (2 ^ (L + 1)) ^ e = 2 ^ (L * e) * 2 ^ e := by
    rw [← Nat.pow_mul, Nat.add_mul, Nat.one_mul, Nat.pow_add]
  have hupper : A * (ascChain L 0) ^ e ≤ C * 2 ^ (L * e) := by
    have h1 : A * (ascChain L 0) ^ e ≤ A * (2 ^ (L + 1)) ^ e :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn0 e)
    have h2 : A * (2 ^ (L + 1)) ^ e = C * 2 ^ (L * e) := by
      rw [hexp, hCdef]
      simp [Nat.mul_comm, Nat.mul_assoc]
    omega
  have hbound : C * 2 ^ (L * e) ≤ 3 ^ (L * e) := by
    refine pow_bound ?_
    rw [hLdef]
    have h := Nat.mul_le_mul_left (2 * C) he
    omega
  have hlower : 3 ^ (L * e) ≤ (ascChain L L) ^ e := by
    rw [Nat.pow_mul]
    exact Nat.pow_le_pow_left hnL e
  -- assemble the contradiction
  have c1 : B * (ascChain L L) ^ e ≤ φ (ascChain L L) ^ d := hlow _
  have c2 : φ (ascChain L L) ^ d < φ (ascChain L 0) ^ d :=
    Nat.pow_lt_pow_left hfin (by omega)
  have c3 : φ (ascChain L 0) ^ d ≤ A * (ascChain L 0) ^ e := hhigh _
  have c4 : (ascChain L L) ^ e ≤ B * (ascChain L L) ^ e := by
    have : 1 * (ascChain L L) ^ e ≤ B * (ascChain L L) ^ e :=
      Nat.mul_le_mul_right _ hB
    omega
  omega

/-! ### The locally reweighted case, with the max and min supplied

`no_power_descent` takes the bounds `A` and `B` as hypotheses.  For
`φ(n) = c(n mod 2^M)·n` they exist because there are only finitely many
residues; these helpers produce them. -/

def listMax : List Nat → Nat
  | [] => 0
  | x :: xs => Nat.max x (listMax xs)

def listMin (d : Nat) : List Nat → Nat
  | [] => d
  | x :: xs => Nat.min x (listMin d xs)

theorem le_listMax {a : Nat} : ∀ l : List Nat, a ∈ l → a ≤ listMax l := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (by simp)
  | cons x xs ih =>
    intro h
    rcases List.mem_cons.mp h with hx | hx
    · rw [hx]; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hx) (Nat.le_max_right _ _)

theorem listMin_le {a d : Nat} : ∀ l : List Nat, a ∈ l → listMin d l ≤ a := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (by simp)
  | cons x xs ih =>
    intro h
    rcases List.mem_cons.mp h with hx | hx
    · rw [hx]; exact Nat.min_le_left _ _
    · exact Nat.le_trans (Nat.min_le_right _ _) (ih hx)

theorem listMin_pos {d : Nat} (hd : 0 < d) : ∀ l : List Nat, (∀ x ∈ l, 0 < x) →
    0 < listMin d l := by
  intro l
  induction l with
  | nil => intro _; exact hd
  | cons x xs ih =>
    intro h
    have hx : 0 < x := h x (by simp)
    have hxs : 0 < listMin d xs := ih (fun y hy => h y (by simp [hy]))
    exact Nat.lt_min.mpr ⟨hx, hxs⟩

/-- **No 2-adically local reweighting of `n` is a descent function.**  For every
modulus `2^M` and every positive weight `c`, the function
`φ(n) = c(n mod 2^M)·n` fails to decrease at some odd step from an odd `n > 1`.

This is the `d = e = 1` case of `no_power_descent` with the max and min of `c`
over the `2^M` residues supplied explicitly. -/
theorem no_local_descent (M : Nat) (c : Nat → Nat) (hc : ∀ x : Nat, 0 < c x) :
    ¬ (∀ x k y : Nat, 1 < x → OddStep x k y →
        c (y % 2 ^ M) * y < c (x % 2 ^ M) * x) := by
  have hvals : ∀ x : Nat, c (x % 2 ^ M) ∈ (List.range (2 ^ M)).map c := by
    intro x
    exact List.mem_map.mpr ⟨x % 2 ^ M, List.mem_range.mpr (Nat.mod_lt x (two_pow_pos M)), rfl⟩
  have hA : ∀ x : Nat, c (x % 2 ^ M) ≤ listMax ((List.range (2 ^ M)).map c) :=
    fun x => le_listMax _ (hvals x)
  have hB : ∀ x : Nat, listMin 1 ((List.range (2 ^ M)).map c) ≤ c (x % 2 ^ M) :=
    fun x => listMin_le _ (hvals x)
  have hBpos : 0 < listMin 1 ((List.range (2 ^ M)).map c) := by
    refine listMin_pos (by omega) _ ?_
    intro y hy
    obtain ⟨z, _, hz⟩ := List.mem_map.mp hy
    rw [← hz]
    exact hc z
  have hApos : 0 < listMax ((List.range (2 ^ M)).map c) :=
    Nat.lt_of_lt_of_le (hc (0 % 2 ^ M)) (hA 0)
  refine no_power_descent (d := 1) (e := 1)
    (A := listMax ((List.range (2 ^ M)).map c))
    (B := listMin 1 ((List.range (2 ^ M)).map c))
    (by omega) (by omega) (by omega) (by omega)
    (fun x => c (x % 2 ^ M) * x) ?_ ?_
  · intro x
    rw [Nat.pow_one, Nat.pow_one]
    exact Nat.mul_le_mul_right x (hB x)
  · intro x
    rw [Nat.pow_one, Nat.pow_one]
    exact Nat.mul_le_mul_right x (hA x)

end GapBarriers
end Collatz
