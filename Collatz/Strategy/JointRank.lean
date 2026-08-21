import Collatz.Strategy.AnyModulusRanking
import Collatz.Strategy.ExchangeRate

/-!
# The last hypothesis class: congruence *plus* the archimedean datum

`NoFiniteRanking.no_class_ranking`, `AnyModulusRanking.no_ranking_any_modulus`
and `AnyModulusRanking.no_ranking_general` kill every rank that factors through a
**finite quotient**, at every modulus, over every well-order.
`NewModels.no_variable_window_ranking` and `NewModels.no_ranking_on_heavy_prefix`
close variable windows and finite heaviness filters.  Exactly one hypothesis
class survived all of them:

> `Φ(x) = f (x % m, ⌊log₂ x⌋)`

— a rank on the residue class **together with** the archimedean datum.  This is
not a finite quotient (the second coordinate is unbounded), so none of the
impossibility theorems above reach it.  This file closes it.

## Why the old witness does not settle it

The classic witness is `n = 2 ^ L · m − 1`, with `T^L(n) = 3 ^ L · m − 1`.  Both
endpoints are `−1` modulo `m`, so a pure class function is blind to the step —
but the *sizes* differ by a factor `(3/2)^L`, and for `L ≥ 2` that is at least
`2`, so `⌊log₂⌋` **strictly increases** (`classic_witness_log_increases`).  The
joint rank sees the step, and the old proof does not apply.

At `L = 1` the same family already contains same-bucket steps: `9 ↦ 14` is a
same-class, same-bucket step modulo `5` (`same_bucket_witness_five`).  So the
class dies immediately at `L = 1`; the content of this file is `L ≥ 2`.

## What actually kills it

The `−1` family is not one witness but a family indexed by every multiple of `m`,
and the log-bucket of its starting point can be **prescribed**.  Given a target
bucket `H` (large enough), put

`P = 2 ^ (H − L)`,  `M = m · (P / m + 1)`,  `wit m L H = 2 ^ L · M − 1`.

Then `P < M ≤ 2P`, hence `2 ^ H ≤ wit < 2 ^ (H+1)`, i.e. `⌊log₂ wit⌋ = H`
exactly, while `T^L(wit) + 1 = 3 ^ L · M ≥ 2 ^ (L+1) · P = 2 ^ (H+1)` forces
`⌊log₂ T^L(wit)⌋ > H` (`joint_step`).  Both endpoints are still `−1` mod `m`.

So writing `g H = Φ (wit m L H)`, the descent hypothesis supplies, **for every**
`H ≥ H₀`, some `H' > H` with `g H' < g H`.  Iterating gives an infinite strictly
decreasing sequence of ranks along a strictly *increasing* sequence of buckets.
In a well-founded codomain that is a contradiction: `no_joint_ranking`,
`no_joint_ranking_wf`.

## The exact shape of the obstruction — and why "look for a cycle" is the wrong test

The natural test is: build the graph on `(residue, bucket)` pairs and look for a
cycle.  That test is *insufficient*, and this file says why.  The graph is
**infinite** (buckets are unbounded), and an infinite acyclic graph can still
carry no ranking, because it may carry an infinite path.  The witness above
supplies exactly that path: strictly increasing buckets, constant residue.  No
cycle is used anywhere in the proof.

(Empirically the graph does also contain genuine cycles at every `m ≤ 64`,
`L ≤ 12` tried — e.g. `m = 8, L = 4` has a self-loop at bucket `15` — but a
cycle-based argument would have to prove such loops persist at arbitrarily large
buckets.  The increasing-path argument needs no such statement.)

## Does the joint object collapse to a pure congruence rank?

The tempting reduction is: by Terras, the class of `x` mod `2 ^ L` determines the
parity word of the next `L` steps, hence `a = oddCount x L`, hence the drift
`⌊log₂ T^L(x)⌋ − ⌊log₂ x⌋ ≈ a·log₂ 3 − L`.  If the drift were a *function of the
residue*, the second coordinate would be redundant and the joint rank would
collapse into `AnyModulusRanking`'s already-closed class.

**It does not collapse.**  The residue mod `2 ^ L` determines the drift only up
to `1`: measured over 200000 consecutive `x` near `2 ^ 20`, every residue class
mod `2 ^ L` for `L = 3, 5, 8, 10` realises **two** distinct drift values, spread
exactly `1`.  The reason is exact: `2 ^ L · T^L(x) = 3 ^ a · x + C` with `a` and
`C` functions of the residue, so the *ratio* `T^L(x)/x` is pinned by the residue,
but `⌊log₂⌋` of a pinned ratio still depends on the mantissa of `x`, which the
residue does not see.  So the joint rank is a genuinely larger hypothesis class,
and the theorems below are not corollaries of the old ones — they need the new
prescribed-bucket witness.

## Soundness filter

Every theorem here is an **impossibility** result, and impossibility results are
correctly `d`-free.  Nothing below uses the verified range, `accOrbit_small`,
`sign(d) = +1` or `|d| < 2`.  That is the expected footprint for a no-go: it says
the hypothesis class is dead for `3x + d` for every `d`, consistent with `3x − 1`
and `3x + 5` having genuine cycles.
-/

namespace Collatz
namespace JointRank

open Reach Congruence NoFiniteRanking ExchangeRate

/-! ## Arithmetic input: `2 ^ (L+1) ≤ 3 ^ L` for `L ≥ 2` -/

/-- `2 ^ (k+3) ≤ 3 ^ (k+2)`: the doubling threshold for the window ratio. -/
theorem two_pow_succ_le_three_pow (k : Nat) : 2 ^ (k + 3) ≤ 3 ^ (k + 2) := by
  induction k with
  | zero => decide
  | succ c ih =>
    have e2 : c + 1 + 3 = (c + 3) + 1 := by omega
    have e3 : c + 1 + 2 = (c + 2) + 1 := by omega
    rw [e2, e3, Arith.two_pow_succ, Arith.three_pow_succ]
    omega

/-- For a window of length `L ≥ 2`, one all-odd window at least doubles. -/
theorem window_doubles {L : Nat} (hL : 2 ≤ L) : 2 ^ (L + 1) ≤ 3 ^ L := by
  obtain ⟨k, hk⟩ : ∃ k : Nat, L = k + 2 := ⟨L - 2, by omega⟩
  have h := two_pow_succ_le_three_pow k
  have e : k + 2 + 1 = k + 3 := by omega
  rw [hk, e]
  exact h

/-! ## Task 1: the classic witness does **not** defeat the joint rank -/

/-- **The old witness is seen by the archimedean coordinate.**  For `L ≥ 2` the
returning witness `n = 2 ^ L · m − 1` of `AnyModulusRanking.exists_growing_return`
has `⌊log₂ T^L(n)⌋ > ⌊log₂ n⌋`.  So it forces no equality of joint ranks, and the
hypothesis class is not closed by the old proof. -/
theorem classic_witness_log_increases {m L : Nat} (hm : 0 < m) (hL : 2 ≤ L)
    (lg : Nat → Nat) (hlg : IsLog2 lg) :
    lg (2 ^ L * m - 1) < lg (acceleratedOrbit L (2 ^ L * m - 1)) := by
  have h2L : (1:Nat) ≤ 2 ^ L := Arith.one_le_two_pow L
  have hbig : 2 ≤ 2 ^ L * m := by
    have h1 : (2:Nat) ≤ 2 ^ L := Arith.two_le_two_pow (by omega)
    have h2 := Nat.le_mul_of_pos_right ((2:Nat) ^ L) hm
    omega
  have hn : (2 ^ L * m - 1) + 1 = 2 ^ (0 + L) * m := by rw [Nat.zero_add]; omega
  have hval := heavy_return_value hn
  rw [Nat.pow_zero, Nat.one_mul] at hval
  have hdbl : 2 ^ (L + 1) * m ≤ 3 ^ L * m := Nat.mul_le_mul_right m (window_doubles hL)
  have hsplit : (2:Nat) ^ (L + 1) * m = 2 * (2 ^ L * m) := by
    rw [Arith.two_pow_succ, Nat.mul_assoc]
  have hpos : 0 < 2 ^ L * m - 1 := by omega
  obtain ⟨hlo, _⟩ := hlg _ hpos
  have horbpos : 0 < acceleratedOrbit L (2 ^ L * m - 1) := by omega
  obtain ⟨_, hhi⟩ := hlg _ horbpos
  have hstep : (2:Nat) ^ (lg (2 ^ L * m - 1) + 1) = 2 * 2 ^ (lg (2 ^ L * m - 1)) :=
    Arith.two_pow_succ _
  have hlt : (2:Nat) ^ (lg (2 ^ L * m - 1) + 1) <
      2 ^ (lg (acceleratedOrbit L (2 ^ L * m - 1)) + 1) := by omega
  have := lt_of_two_pow_lt hlt
  omega

/-- **At `L = 1` the joint rank dies outright**, by a same-class *and*
same-bucket step: `9 ↦ 14`, both `4` modulo `5`, both in `[8, 16)`. -/
theorem same_bucket_witness_five (lg : Nat → Nat) (hlg : IsLog2 lg) :
    acceleratedOrbit 1 9 = 14 ∧ 9 % 5 = 14 % 5 ∧ lg 9 = lg 14 := by
  refine ⟨by decide, by decide, ?_⟩
  have h9 : lg 9 = 3 := log2_eq hlg (by decide) (by decide)
  have h14 : lg 14 = 3 := log2_eq hlg (by decide) (by decide)
  rw [h9, h14]

/-! ## The prescribed-bucket witness -/

/-- The witness with prescribed log-bucket `H`: the first multiple of `m`
strictly above `2 ^ (H − L)`, scaled by `2 ^ L`, minus one. -/
def wit (m L H : Nat) : Nat :=
  2 ^ L * (m * (2 ^ (H - L) / m + 1)) - 1

/-- **The witness with a prescribed starting bucket.**  For every modulus `m ≥ 1`,
window `L ≥ 2`, threshold `B` and every target bucket `H ≥ L + m + B`:

* `wit m L H > B`;
* `wit m L H ≡ T^L(wit m L H) ≡ −1  (mod m)`;
* `⌊log₂ (wit m L H)⌋ = H` exactly;
* `⌊log₂ T^L(wit m L H)⌋ > H`.

The residue is fixed while the bucket is prescribed and strictly increases: that
is the infinite ascending path the joint rank cannot survive. -/
theorem joint_step {m L B H : Nat} (hm : 0 < m) (hL : 2 ≤ L) (hH : L + m + B ≤ H)
    (lg : Nat → Nat) (hlg : IsLog2 lg) :
    B < wit m L H ∧ 0 < wit m L H ∧ 0 < acceleratedOrbit L (wit m L H) ∧
      wit m L H % m = m - 1 ∧ acceleratedOrbit L (wit m L H) % m = m - 1 ∧
      lg (wit m L H) = H ∧ H < lg (acceleratedOrbit L (wit m L H)) := by
  have hPsplit : (2:Nat) ^ L * 2 ^ (H - L) = 2 ^ H := by
    rw [← Arith.two_pow_add]
    have e : L + (H - L) = H := by omega
    rw [e]
  have hPsplit' : (2:Nat) ^ (L + 1) * 2 ^ (H - L) = 2 ^ (H + 1) := by
    rw [← Arith.two_pow_add]
    have e : L + 1 + (H - L) = H + 1 := by omega
    rw [e]
  have hmP : m ≤ 2 ^ (H - L) := by
    have h1 : m < 2 ^ m := Arith.lt_two_pow_self m
    have h2 : (2:Nat) ^ m ≤ 2 ^ (H - L) := Arith.two_pow_le_two_pow (by omega)
    omega
  have hmod : 2 ^ (H - L) % m < m := Nat.mod_lt _ hm
  have hdivmod : m * (2 ^ (H - L) / m) + 2 ^ (H - L) % m = 2 ^ (H - L) :=
    Nat.div_add_mod _ _
  -- `P < M ≤ 2 P`
  have hMlo : 2 ^ (H - L) < m * (2 ^ (H - L) / m + 1) := by
    rw [Nat.mul_add, Nat.mul_one]; omega
  have hMhi : m * (2 ^ (H - L) / m + 1) ≤ 2 * 2 ^ (H - L) := by
    rw [Nat.mul_add, Nat.mul_one]; omega
  have h2Lpos : (1:Nat) ≤ 2 ^ L := Arith.one_le_two_pow L
  have h2Hpos : (1:Nat) ≤ 2 ^ H := Arith.one_le_two_pow H
  -- the bracketing of `2 ^ L · M`
  have hlo2 : 2 ^ H + 2 ^ L ≤ 2 ^ L * (m * (2 ^ (H - L) / m + 1)) := by
    have h : (2:Nat) ^ L * (2 ^ (H - L) + 1) ≤ 2 ^ L * (m * (2 ^ (H - L) / m + 1)) :=
      Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_add, Nat.mul_one, hPsplit] at h
    omega
  have hhi2 : 2 ^ L * (m * (2 ^ (H - L) / m + 1)) ≤ 2 ^ (H + 1) := by
    have h : (2:Nat) ^ L * (m * (2 ^ (H - L) / m + 1)) ≤ 2 ^ L * (2 * 2 ^ (H - L)) :=
      Nat.mul_le_mul_left _ hMhi
    have he : (2:Nat) ^ L * (2 * 2 ^ (H - L)) = 2 ^ (H + 1) := by
      rw [Nat.mul_left_comm, hPsplit]
      exact (Arith.two_pow_succ H).symm
    omega
  -- the run identity
  have hn1 : wit m L H + 1 = 2 ^ (0 + L) * (m * (2 ^ (H - L) / m + 1)) := by
    rw [Nat.zero_add]; unfold wit; omega
  have hval := heavy_return_value hn1
  rw [Nat.pow_zero, Nat.one_mul] at hval
  -- the endpoint is at least `2 ^ (H+1)`
  have hdbl : 2 ^ (L + 1) * (m * (2 ^ (H - L) / m + 1)) ≤
      3 ^ L * (m * (2 ^ (H - L) / m + 1)) :=
    Nat.mul_le_mul_right _ (window_doubles hL)
  have hhalf : (2:Nat) ^ (L + 1) * (2 ^ (H - L) + 1) ≤
      2 ^ (L + 1) * (m * (2 ^ (H - L) / m + 1)) :=
    Nat.mul_le_mul_left _ (by omega)
  have hexp : (2:Nat) ^ (L + 1) * (2 ^ (H - L) + 1) = 2 ^ (H + 1) + 2 ^ (L + 1) := by
    rw [Nat.mul_add, Nat.mul_one, hPsplit']
  have h2L1 : (1:Nat) ≤ 2 ^ (L + 1) := Arith.one_le_two_pow (L + 1)
  have horb : 2 ^ (H + 1) ≤ acceleratedOrbit L (wit m L H) := by omega
  have h2H1 : (1:Nat) ≤ 2 ^ (H + 1) := Arith.one_le_two_pow (H + 1)
  have hBH : B < 2 ^ H := by
    have h1 : B < 2 ^ B := Arith.lt_two_pow_self B
    have h2 : (2:Nat) ^ B ≤ 2 ^ H := Arith.two_pow_le_two_pow (by omega)
    omega
  have hwitval : wit m L H = 2 ^ L * (m * (2 ^ (H - L) / m + 1)) - 1 := rfl
  refine ⟨by omega, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · refine pred_mod_of_dvd hm ⟨2 ^ L * (2 ^ (H - L) / m + 1), ?_⟩
    rw [hn1, Nat.zero_add, ← Nat.mul_assoc, Nat.mul_comm ((2:Nat) ^ L) m,
      Nat.mul_assoc]
  · refine pred_mod_of_dvd hm ⟨3 ^ L * (2 ^ (H - L) / m + 1), ?_⟩
    rw [hval, ← Nat.mul_assoc, Nat.mul_comm ((3:Nat) ^ L) m, Nat.mul_assoc]
  · exact log2_eq hlg (by omega) (by omega)
  · obtain ⟨_, hhi⟩ := hlg _ (show 0 < acceleratedOrbit L (wit m L H) by omega)
    have hlt : (2:Nat) ^ (H + 1) <
        2 ^ (lg (acceleratedOrbit L (wit m L H)) + 1) := by omega
    have := lt_of_two_pow_lt hlt
    omega

/-! ## The impossibility -/

/-- **No rank on `(class mod m, ⌊log₂ x⌋)` can decrease over a window of length
`L ≥ 2`.**  Stated for a `Φ` that is merely *constant on* pairs (residue, bucket),
which is the weakest form of the hypothesis.  The descent is demanded only above
an arbitrary threshold `B`; `m` and `L` are arbitrary.

This is the last hypothesis class left open by `NoFiniteRanking`,
`AnyModulusRanking` and `NewModels`, and it is false. -/
theorem no_joint_class_ranking (m L B : Nat) (hm : 0 < m) (hL : 2 ≤ L)
    (lg : Nat → Nat) (hlg : IsLog2 lg) (φ : Nat → Nat)
    (hclass : ∀ x y : Nat, 0 < x → 0 < y → x % m = y % m → lg x = lg y → φ x = φ y) :
    ¬ (∀ x : Nat, B < x → φ (acceleratedOrbit L x) < φ x) := by
  intro hdec
  have step : ∀ H : Nat, L + m + B ≤ H →
      ∃ H' : Nat, L + m + B ≤ H' ∧ φ (wit m L H') < φ (wit m L H) := by
    intro H hH
    obtain ⟨hB, hpos, hopos, hr1, hr2, hlgn, hlgo⟩ := joint_step hm hL hH lg hlg
    refine ⟨lg (acceleratedOrbit L (wit m L H)), by omega, ?_⟩
    obtain ⟨_, hpos', _, hr1', _, hlgn', _⟩ :=
      joint_step (m := m) (L := L) (B := B)
        (H := lg (acceleratedOrbit L (wit m L H))) hm hL (by omega) lg hlg
    have hsame : φ (wit m L (lg (acceleratedOrbit L (wit m L H))))
        = φ (acceleratedOrbit L (wit m L H)) :=
      hclass _ _ hpos' hopos (by rw [hr1', hr2]) (by rw [hlgn'])
    have := hdec (wit m L H) hB
    omega
  have key : ∀ v H : Nat, L + m + B ≤ H → φ (wit m L H) ≤ v → False := by
    intro v
    induction v with
    | zero =>
      intro H hH hle
      obtain ⟨H', _, hlt⟩ := step H hH
      omega
    | succ w ih =>
      intro H hH hle
      obtain ⟨H', hH', hlt⟩ := step H hH
      exact ih H' hH' (by omega)
  exact key (φ (wit m L (L + m + B))) (L + m + B) (Nat.le_refl _) (Nat.le_refl _)

/-- The same statement in the form the hypothesis class was posed in: `Φ` is
literally a function `f` of the pair `(x % m, ⌊log₂ x⌋)`. -/
theorem no_joint_ranking (m L B : Nat) (hm : 0 < m) (hL : 2 ≤ L)
    (lg : Nat → Nat) (hlg : IsLog2 lg)
    (f : Nat → Nat → Nat) (φ : Nat → Nat)
    (hφ : ∀ x : Nat, 0 < x → φ x = f (x % m) (lg x)) :
    ¬ (∀ x : Nat, B < x → φ (acceleratedOrbit L x) < φ x) := by
  refine no_joint_class_ranking m L B hm hL lg hlg φ ?_
  intro x y hx hy hr hl
  rw [hφ x hx, hφ y hy, hr, hl]

/-- **The codomain does not help, as long as it is well-founded.**  The joint
rank may take values in any type carrying a well-founded relation — ordinals
included.

Note the contrast with `AnyModulusRanking.no_ranking_general`, where mere
*irreflexivity* sufficed because the witness forced an *equality* of ranks.  Here
the witness forces a strict decrease along a strictly ascending chain of buckets,
so well-foundedness is exactly what is consumed — and it is exactly what
"ranking function" means. -/
theorem no_joint_ranking_wf {β : Type} (m L B : Nat) (hm : 0 < m) (hL : 2 ≤ L)
    (lg : Nat → Nat) (hlg : IsLog2 lg)
    (lt : β → β → Prop) (hwf : WellFounded lt)
    (φ : Nat → β)
    (hclass : ∀ x y : Nat, 0 < x → 0 < y → x % m = y % m → lg x = lg y → φ x = φ y) :
    ¬ (∀ x : Nat, B < x → lt (φ (acceleratedOrbit L x)) (φ x)) := by
  intro hdec
  have step : ∀ H : Nat, L + m + B ≤ H →
      ∃ H' : Nat, L + m + B ≤ H' ∧ lt (φ (wit m L H')) (φ (wit m L H)) := by
    intro H hH
    obtain ⟨hB, hpos, hopos, hr1, hr2, hlgn, hlgo⟩ := joint_step hm hL hH lg hlg
    refine ⟨lg (acceleratedOrbit L (wit m L H)), by omega, ?_⟩
    obtain ⟨_, hpos', _, hr1', _, hlgn', _⟩ :=
      joint_step (m := m) (L := L) (B := B)
        (H := lg (acceleratedOrbit L (wit m L H))) hm hL (by omega) lg hlg
    have hsame : φ (wit m L (lg (acceleratedOrbit L (wit m L H))))
        = φ (acceleratedOrbit L (wit m L H)) :=
      hclass _ _ hpos' hopos (by rw [hr1', hr2]) (by rw [hlgn'])
    rw [hsame]
    exact hdec (wit m L H) hB
  have key : ∀ b : β, ∀ H : Nat, L + m + B ≤ H → φ (wit m L H) ≠ b := by
    intro b
    induction b using WellFounded.induction (r := lt) hwf with
    | _ b ih =>
      intro H hH hEq
      obtain ⟨H', hH', hlt⟩ := step H hH
      rw [hEq] at hlt
      exact ih (φ (wit m L H')) hlt H' hH' rfl
  exact key (φ (wit m L (L + m + B))) (L + m + B) (Nat.le_refl _) rfl

end JointRank
end Collatz
