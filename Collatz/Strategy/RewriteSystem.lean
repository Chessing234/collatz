import Collatz.Accelerated
import Collatz.Strategy.ReverseTree
import Collatz.Strategy.ScaleRecord

/-!
# Even-choice completion of the shift ARS

The accelerated map is a function, so `n → n/2` and `n → (3n+1)/2` never
overlap: no critical pairs, confluence is vacuous, and Knuth–Bendix /
decreasing diagrams have nothing to act on.  This file does **not** try to
prove termination of that system (that is Collatz).

It studies a *related* nondeterministic ARS on the shift `u = n + 1`, in
which the Collatz even branch and the `expStep` even branch are both legal
at every odd `u`.  The critical pair of that overlap admits a strictly
monotone decreasing-diagram label if and only if the even reduct contracts.
Contraction is true of `3n+1` and false of `expStep`.

The inverse system `{y → 2y, y → (2y−1)/3}` supplies a second overlap, whose
forward diamond is a decreasing diagram *because* `T(2y) = y`.  The same
putative `D`-step is not an inverse of `expStep`.  Knuth–Bendix modulo
doubling is therefore sound for Collatz joinability and unsound for
`expStep`.

None of this is a residue sieve.  None of it orients the odd-`n` rule.
-/

namespace Collatz
namespace RewriteSystem

open Collatz.ReverseTree Collatz.ScaleRecord


/-! ## 1.  Orthogonality of the deterministic map -/

/-- The two accelerated rules have disjoint domains.  There is no critical
pair in the map itself. -/
theorem no_overlap_accelerated (n : Nat) :
    ¬ (n % 2 = 0 ∧ n % 2 = 1) := by
  omega

/-- Each `n` has exactly one accelerated redex. -/
theorem unique_redex (n : Nat) :
    n % 2 = 0 ∨ n % 2 = 1 :=
  Arith.mod_two_eq_zero_or_one n


/-! ## 2.  Shift encoding of both even branches -/

/-- Forward odd-`n` rule on the shift: `u` even maps to `3u/2`. -/
def tau (u : Nat) : Nat := 3 * u / 2

/-- Collatz even-`n` rule on the shift: `u` odd maps to `(u+1)/2`. -/
def eta (u : Nat) : Nat := (u + 1) / 2

/-- `expStep` even-`n` rule on the shift: `u` odd maps to `(3u−1)/2`. -/
def eps (u : Nat) : Nat := (3 * u - 1) / 2

/-- **Bridge.**  Odd `n` is even `u = n+1`, and both maps act as `τ`. -/
theorem tau_of_odd {n : Nat} (ho : n % 2 = 1) :
    acceleratedStep n + 1 = tau (n + 1) ∧
    expStep n + 1 = tau (n + 1) := by
  have hT : acceleratedStep n = (3 * n + 1) / 2 := by
    rw [acceleratedStep, if_neg (by omega)]
  have hE : expStep n = (3 * n + 1) / 2 := by
    rw [expStep_odd_eq ho, acceleratedStep, if_neg (by omega)]
  have htau : tau (n + 1) = 3 * (n + 1) / 2 := rfl
  refine ⟨?_, ?_⟩
  · rw [hT, htau]; omega
  · rw [hE, htau]; omega

/-- **Bridge.**  Even `n` is odd `u = n+1`, and Collatz acts as `η`. -/
theorem eta_of_even {n : Nat} (he : n % 2 = 0) :
    acceleratedStep n + 1 = eta (n + 1) := by
  have hT : acceleratedStep n = n / 2 := by
    rw [acceleratedStep, if_pos he]
  rw [hT, eta]
  omega

/-- **Bridge.**  Even positive `n` is odd `u = n+1`, and `expStep` acts as `ε`. -/
theorem eps_of_even {n : Nat} (he : n % 2 = 0) (hn : 0 < n) :
    expStep n + 1 = eps (n + 1) := by
  have hE : expStep n = 3 * n / 2 := by
    unfold expStep
    rw [if_pos he]
  rw [hE, eps]
  omega


/-! ## 3.  The even-choice critical pair -/

/-- Both even-branch rules apply at every odd `u`.  This is the overlap the
deterministic map does not have. -/
def EvenChoicePeak (u : Nat) : Prop :=
  u % 2 = 1 ∧ 1 < u

/-- The two reducts of the even-choice peak. -/
def evenChoicePair (u : Nat) : Nat × Nat := (eta u, eps u)

/-- The two reducts coincide only at `u = 1`, which is excluded from the peak. -/
theorem evenChoice_unequal {u : Nat} (h : EvenChoicePeak u) :
    eta u ≠ eps u := by
  rcases h with ⟨ho, hu⟩
  intro heq
  have : (u + 1) / 2 = (3 * u - 1) / 2 := heq
  omega

/-- **Collatz even contraction on the shift.** -/
theorem eta_contracts {u : Nat} (h : EvenChoicePeak u) : eta u < u := by
  rcases h with ⟨_, hu⟩
  unfold eta
  omega

/-- **`expStep` even expansion on the shift.** -/
theorem eps_expands {u : Nat} (h : EvenChoicePeak u) : u < eps u := by
  rcases h with ⟨ho, hu⟩
  unfold eps
  omega

/-- The simplification-order orientation of the critical pair is `ε → η`. -/
theorem kb_orients_toward_collatz {u : Nat} (h : EvenChoicePeak u) :
    eta u < eps u := by
  have := eta_contracts h
  have := eps_expands h
  omega


/-! ## 4.  The rewrite lemma: monotone labels decrease iff the reduct contracts -/

/-- A `Nat`-label is strictly monotone. -/
def StrictMono (μ : Nat → Nat) : Prop :=
  ∀ a b : Nat, a < b → μ a < μ b

/-- The identity is strictly monotone. -/
theorem id_strictMono : StrictMono (fun n => n) :=
  fun _ _ h => h

/-- **Rewrite lemma.**  A strictly monotone labeling of the even-choice peak
decreases on a reduct `r` if and only if `r` itself contracts.  The left-to-right
direction is the contrapositive of monotonicity; the converse applies `μ` to a
genuine `<`. -/
theorem mono_label_descends_iff {r μ : Nat → Nat} (hμ : StrictMono μ) :
    (∀ u, EvenChoicePeak u → μ (r u) < μ u) ↔
    (∀ u, EvenChoicePeak u → r u < u) := by
  constructor
  · intro hdesc u hu
    have hμr : μ (r u) < μ u := hdesc u hu
    cases Nat.lt_or_ge (r u) u with
    | inl hlt => exact hlt
    | inr hge =>
      cases Nat.eq_or_lt_of_le hge with
      | inl heq =>
        have hr : r u = u := heq.symm
        rw [hr] at hμr
        exact False.elim (Nat.lt_irrefl (μ u) hμr)
      | inr hgt =>
        have hμu : μ u < μ (r u) := hμ u (r u) hgt
        exact False.elim (Nat.lt_irrefl (μ u) (Nat.lt_trans hμu hμr))
  · intro hcontr u hu
    exact hμ (r u) u (hcontr u hu)

/-- The `3n+1` even reduct admits a strictly monotone decreasing label. -/
theorem collatz_even_has_mono_label :
    ∀ u, EvenChoicePeak u → eta u < u :=
  fun _ hu => eta_contracts hu

/-- Instantiating the lemma at `η` with the identity. -/
theorem collatz_even_id_descends :
    ∀ u, EvenChoicePeak u → eta u < u :=
  (mono_label_descends_iff (r := eta) (μ := fun n => n) id_strictMono).mpr
    collatz_even_has_mono_label

/-- The `expStep` even reduct admits **no** strictly monotone decreasing label. -/
theorem expStep_even_no_mono_label (μ : Nat → Nat) (hμ : StrictMono μ) :
    ¬ (∀ u, EvenChoicePeak u → μ (eps u) < μ u) := by
  intro hdesc
  have hiff := mono_label_descends_iff (r := eps) (μ := μ) hμ
  have hcontr : ∀ u, EvenChoicePeak u → eps u < u := hiff.mp hdesc
  have hu : EvenChoicePeak 3 := ⟨by omega, by omega⟩
  have := hcontr 3 hu
  have := eps_expands hu
  omega

/-- Package: well-founded (monotone) complexity of the even-choice critical
pair exists if and only if the reduct is the Collatz even branch, not
`expStep`. -/
theorem evenChoice_complexity_iff :
    (∀ u, EvenChoicePeak u → eta u < u) ∧
    ¬ (∀ u, EvenChoicePeak u → eps u < u) := by
  refine ⟨collatz_even_has_mono_label, ?_⟩
  intro h
  have hu : EvenChoicePeak 3 := ⟨by omega, by omega⟩
  have := h 3 hu
  have := eps_expands hu
  omega


/-! ## 5.  Inverse overlap: decreasing diamond, false of `expStep` -/

/-- The inverse peak at a branch point joins in one forward Collatz step on
each side.  Labels `fwd < inv` make this a decreasing diagram. -/
theorem inverse_peak_diamond {y : Nat} (h : y % 3 = 2) (hy : 2 ≤ y) :
    acceleratedStep (2 * y) = y ∧
    acceleratedStep (oddPred y) = y :=
  ⟨step_two_mul y, step_oddPred h hy⟩

/-- The `D`-side of the diamond is a value decrease. -/
theorem inverse_peak_D_decreases {y : Nat} (hy : 0 < y) :
    y < 2 * y ∧ acceleratedStep (2 * y) = y :=
  ⟨by omega, step_two_mul y⟩

/-- Doubling is **not** an `expStep`-preimage.  The putative `D`-step of the
inverse peak does not join at `y` under `expStep`, and `y` is not a forward
`expStep`-descendant of `2y`. -/
theorem expStep_not_D_join {y : Nat} (hy : 0 < y) :
    expStep (2 * y) = 3 * y ∧ y < 3 * y := by
  have he : (2 * y) % 2 = 0 := by omega
  have hE : expStep (2 * y) = 3 * (2 * y) / 2 := by
    unfold expStep
    rw [if_pos he]
  have h3 : 3 * (2 * y) / 2 = 3 * y := by omega
  exact ⟨by rw [hE, h3], by omega⟩

/-- Consequently `y` itself is strictly below every forward `expStep` iterate
of `2y` that we can name from the first step. -/
theorem expStep_two_mul_escapes {y : Nat} (hy : 0 < y) :
    2 * y < expStep (2 * y) := by
  have ⟨hE, _⟩ := expStep_not_D_join hy
  rw [hE]
  omega


/-! ## 6.  Residual inverse family after the doubling quotient -/

/-- Residual inverse rule of depth `k`, after collapsing `y ≈ 2y`. -/
def syrPred (k y : Nat) : Nat := (2 ^ k * y - 1) / 3

/-- `k = 1` is the odd preimage of `ReverseTree`. -/
theorem syrPred_one (y : Nat) : syrPred 1 y = oddPred y := by
  unfold syrPred oddPred
  simp

/-- Powers of two modulo three: `2^k ≡ (−1)^k (mod 3)`. -/
theorem two_pow_mod_three (k : Nat) :
    2 ^ k % 3 = if k % 2 = 0 then 1 else 2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hsucc : 2 ^ (k + 1) % 3 = (2 * (2 ^ k % 3)) % 3 := by
      rw [Arith.two_pow_succ, Nat.mul_mod]
    rw [hsucc, ih]
    rcases Arith.mod_two_eq_zero_or_one k with he | ho
    · rw [if_pos he, if_neg (by omega)]
    · rw [if_neg (by omega), if_pos (by omega)]

/-- `R_k` is integral precisely on one residue of `y` modulo 3, selected by
the parity of `k`.  Two residuals therefore overlap only when `k ≡ k' (mod 2)`. -/
theorem syrPred_legal_iff {k y : Nat} :
    (2 ^ k * y) % 3 = 1 ↔
      (y % 3 = 1 ∧ k % 2 = 0) ∨ (y % 3 = 2 ∧ k % 2 = 1) := by
  have hmul : (2 ^ k * y) % 3 = (2 ^ k % 3 * (y % 3)) % 3 := Nat.mul_mod _ _ _
  rw [hmul, two_pow_mod_three]
  rcases Arith.mod_two_eq_zero_or_one k with he | ho
  · rw [if_pos he]
    have h1 : (1 * (y % 3)) % 3 = y % 3 := by
      have : y % 3 < 3 := Nat.mod_lt y (by omega)
      omega
    rw [h1]
    constructor
    · intro hy1; exact Or.inl ⟨hy1, he⟩
    · intro h
      rcases h with ⟨hy1, _⟩ | ⟨_, hk⟩
      · exact hy1
      · omega
  · rw [if_neg (by omega)]
    constructor
    · intro hprod
      refine Or.inr ⟨?_, ho⟩
      have hy3 : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2 := by
        have : y % 3 < 3 := Nat.mod_lt y (by omega)
        omega
      rcases hy3 with h0 | h1 | h2
      · rw [h0] at hprod; cases hprod
      · rw [h1] at hprod; cases hprod
      · exact h2
    · intro h
      rcases h with ⟨_, hk⟩ | ⟨hy2, _⟩
      · omega
      · rw [hy2]

/-- Critical pairs of the residual family: both depths legal implies equal parity. -/
theorem residual_overlap {k k' y : Nat}
    (h : (2 ^ k * y) % 3 = 1) (h' : (2 ^ k' * y) % 3 = 1) :
    k % 2 = k' % 2 := by
  have hk := (syrPred_legal_iff (k := k) (y := y)).mp h
  have hk' := (syrPred_legal_iff (k := k') (y := y)).mp h'
  rcases hk with ⟨_, he⟩ | ⟨_, ho⟩
  · rcases hk' with ⟨_, he'⟩ | ⟨_, ho'⟩
    · rw [he, he']
    · omega
  · rcases hk' with ⟨_, he'⟩ | ⟨_, ho'⟩
    · omega
    · rw [ho, ho']

/-- Integrality of `R_k`: `3 ∣ 2^k y − 1` iff the residue condition. -/
theorem syrPred_exact {k y : Nat} (hy : 0 < y)
    (h : (2 ^ k * y) % 3 = 1) :
    3 * syrPred k y + 1 = 2 ^ k * y := by
  have hdiv := Nat.div_add_mod (2 ^ k * y) 3
  rw [h] at hdiv
  unfold syrPred
  have hpos : 1 ≤ 2 ^ k * y := by
    have := Arith.two_pow_pos k
    exact Nat.mul_pos this hy
  omega

/-- **Forward join of a residual inverse.**  After one odd accelerated step
the state is a pure doubling ray, which `T` contracts back to `y` in `k`
further even steps.  This uses `T(2z) = z`, false of `expStep`. -/
theorem residual_joins {k y : Nat} (hy : 0 < y)
    (hleg : (2 ^ (k + 1) * y) % 3 = 1)
    (hodd : syrPred (k + 1) y % 2 = 1) :
    acceleratedOrbit (k + 1) (syrPred (k + 1) y) = y := by
  have hexact := syrPred_exact (k := k + 1) hy hleg
  have hstep : acceleratedStep (syrPred (k + 1) y) = 2 ^ k * y := by
    rw [acceleratedStep, if_neg (by omega)]
    have : (3 * syrPred (k + 1) y + 1) / 2 = 2 ^ k * y := by
      rw [hexact]
      have hpow : 2 ^ (k + 1) * y = 2 * (2 ^ k * y) := by
        rw [Arith.two_pow_succ, Nat.mul_assoc]
      rw [hpow]
      omega
    exact this
  rw [acceleratedOrbit_succ, hstep]
  exact orbit_two_pow_mul k y

/-- Already the next `expStep` after that shared odd step multiplies by `3/2`
instead of dividing by `2`.  Depth `k ≥ 1` in the residual family is the
extra-halving slot that `expStep` leaves empty. -/
theorem residual_expStep_diverges {k y : Nat} (hy : 0 < y) :
    expStep (2 ^ (k + 1) * y) = 3 * (2 ^ k * y) := by
  have hpow : 2 ^ (k + 1) * y = 2 * (2 ^ k * y) := by
    rw [Arith.two_pow_succ, Nat.mul_assoc]
  rw [hpow]
  have he : (2 * (2 ^ k * y)) % 2 = 0 := by omega
  unfold expStep
  rw [if_pos he]
  have hz : 0 < 2 ^ k * y := Nat.mul_pos (Arith.two_pow_pos k) hy
  omega

/-- The residual `expStep` step is strictly larger than the Collatz even
step on the same doubling ray. -/
theorem residual_expStep_ne_half {k y : Nat} (hy : 0 < y) :
    expStep (2 ^ (k + 1) * y) ≠ 2 ^ k * y := by
  rw [residual_expStep_diverges hy]
  have hpos : 0 < 2 ^ k * y := Nat.mul_pos (Arith.two_pow_pos k) hy
  omega

end RewriteSystem
end Collatz
