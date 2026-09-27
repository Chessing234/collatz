import CollatzTargetDensity.ResidueDensity
import Erdos1135.Terras.Parity.Residue

/-!
# Positive predecessor density in every class modulo 2^p * 3^q

The affine formula for a fixed parity prefix pulls ternary density back to
any prescribed mixed residue class. This uses the preceding density theorem;
it adds no hypothesis about individual orbits converging.
-/
namespace CollatzTargetDensity
open Erdos1135
noncomputable section

theorem reaches_accelerated_step (n : ℕ) : Reaches n (Terras.accelerated n) := by
  by_cases he : Even n
  · apply reaches_of_step_eq
    exact (Terras.accelerated_eq_standard_of_even he).symm
  · have hstep := Terras.standard_eq_two_mul_accelerated_of_not_even he
    have htail : Reaches (2 * Terras.accelerated n) (Terras.accelerated n) := by
      simpa using Tao.reaches_powTwo_mul 1 (Terras.accelerated n)
    exact (reaches_of_step_eq hstep).trans htail

theorem reaches_accelerated_iterate (k n : ℕ) :
    Reaches n ((Terras.accelerated^[k]) n) := by
  induction k generalizing n with
  | zero => exact reaches_refl n
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact (reaches_accelerated_step n).trans (ih (Terras.accelerated n))

theorem accelerated_iterate_zero (k : ℕ) : (Terras.accelerated^[k]) 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Function.iterate_succ_apply', ih, Terras.accelerated]

theorem decode_affine_residue {D v y : ℕ} (hmod : y % D = v % D) (hvy : v ≤ y) :
    v + D * ((y - v) / D) = y := by
  have hd : D ∣ y - v := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hmod)
  rw [Nat.mul_div_cancel' hd]
  omega

def inMixedClass (B : Set ℕ) (p q : ℕ) (r : Fin (2 ^ p * 3 ^ q)) : Set ℕ :=
  {n | n ∈ B ∧ n % (2 ^ p * 3 ^ q) = r}

/-- For every eligible target and every mixed residue class, there are c>0
and X₀ such that at least c*X positive starts below X in that class hit the
target, for every X≥X₀. This includes arbitrary powers of 2 or 3 separately. -/
theorem positive_density_every_mixed_class {target : ℕ}
    (hthree : target % 3 ≠ 0) (p q : ℕ) (r : Fin (2 ^ p * 3 ^ q)) :
    HasPositiveLowerDensity (inMixedClass (rawReaches target) p q r) := by
  let u : ℕ := r
  let M := 2 ^ p * 3 ^ q
  let v := (Terras.accelerated^[p]) u
  let s := Terras.numOdd (Terras.parityPrefix p u)
  let D := 3 ^ (s + q)
  let source := {y | y ∈ inTernaryClass (rawReaches target) (s + q)
    ⟨v % D, Nat.mod_lt _ (by positivity)⟩ ∧ v ≤ y}
  let dest := inMixedClass (rawReaches target) p q r
  let f : ℕ → ℕ := fun y => u + M * ((y - v) / D)
  have hM : 0 < M := by dsimp [M]; positivity
  have hsource : HasPositiveLowerDensity source :=
    positive_density_tail (positive_density_every_ternary_class hthree (s + q)
      ⟨v % D, Nat.mod_lt _ (by positivity)⟩) v
  have hdecode (y : ℕ) (hy : y ∈ source) :
      v + D * ((y - v) / D) = y := decode_affine_residue hy.1.2 hy.2
  have hhit (y : ℕ) (hy : y ∈ source) : (Terras.accelerated^[p]) (f y) = y := by
    have h := Terras.accelerated_iterate_add_two_pow_mul_of_prefix
      (q := p) (u := u) (t := 3 ^ q * ((y - v) / D)) rfl
    calc
      _ = (Terras.accelerated^[p]) (u + 2 ^ p * (3 ^ q * ((y - v) / D))) := by
        dsimp [f, M]
        rw [Nat.mul_assoc]
      _ = v + 3 ^ s * (3 ^ q * ((y - v) / D)) := h
      _ = v + D * ((y - v) / D) := by dsimp [D]; rw [pow_add]; ring
      _ = y := hdecode y hy
  have hinj : source.InjOn f := by
    intro y hy z hz he
    have h : (y - v) / D = (z - v) / D :=
      Nat.eq_of_mul_eq_mul_left hM (Nat.add_left_cancel he)
    have hdy := hdecode y hy
    have hdz := hdecode z hz
    rw [h] at hdy
    exact hdy.symm.trans hdz
  have hmem (y : ℕ) (hy : y ∈ source) : f y ∈ dest := by
    have hpos : 0 < f y := by
      by_contra h
      have hz : f y = 0 := by omega
      have he := hhit y hy
      rw [hz, accelerated_iterate_zero] at he
      have hyp : 0 < y := hy.1.1.1
      omega
    refine ⟨⟨hpos, ?_⟩, ?_⟩
    · have hreach : Reaches (f y) y := by
        simpa only [hhit y hy] using reaches_accelerated_iterate p (f y)
      exact hreach.trans hy.1.1.2
    · change (u + M * ((y - v) / D)) % M = r
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt r.isLt]
  have hsize (y : ℕ) (_hy : y ∈ source) (X : ℕ) (hyX : y < X) :
      f y < (u + M + 1) * X := by
    have hz : (y - v) / D ≤ y := (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
    have hm := Nat.mul_le_mul_left M hz
    have hu := Nat.mul_le_mul_left u (show 1 ≤ X by omega)
    dsimp [f]
    nlinarith
  apply positive_density_of_count_transport (Q := 1) (K := u + M + 1)
    (by decide) (by omega) ?_ hsource
  intro X
  simpa only [one_mul] using count_le_of_injection_on source dest (u + M + 1) f
    hinj hmem hsize X

theorem positive_density_mixed_class_iff {target : ℕ} (hpos : 0 < target)
    (p q : ℕ) (r : Fin (2 ^ p * 3 ^ q)) :
    HasPositiveLowerDensity (inMixedClass (rawReaches target) p q r) ↔
      target % 3 ≠ 0 := by
  constructor
  · rintro ⟨c, hc, X₀, hX₀⟩ hthree
    apply no_positive_lower_density_three_divisible hpos hthree
    refine ⟨c, hc, X₀, fun X hX => (hX₀ X hX).trans ?_⟩
    exact_mod_cast Terras.natCount_mono (show
      inMixedClass (rawReaches target) p q r ⊆ rawReaches target from fun _ hn => hn.1) X
  · exact fun h => positive_density_every_mixed_class h p q r

theorem counterexamples_positive_density_every_mixed_class
    (hbad : rawBad.Nonempty) (p q : ℕ) (r : Fin (2 ^ p * 3 ^ q)) :
    HasPositiveLowerDensity (inMixedClass rawBad p q r) := by
  obtain ⟨n, hn⟩ := hbad
  obtain ⟨a, ha, hnot⟩ := bad_three_unit_of_bad hn
  obtain ⟨c, hc, X₀, hX₀⟩ := positive_density_every_mixed_class ha p q r
  refine ⟨c, hc, X₀, fun X hX => (hX₀ X hX).trans ?_⟩
  exact_mod_cast Terras.natCount_mono (show
    inMixedClass (rawReaches a) p q r ⊆ inMixedClass rawBad p q r from
    fun _ hn => ⟨rawReaches_subset_bad hnot hn.1, hn.2⟩) X

def SparseBadInMixedClass (p q : ℕ) (r : Fin (2 ^ p * 3 ^ q)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ X₀ : ℕ, ∃ X : ℕ, X₀ ≤ X ∧ 0 < X ∧
    (Terras.natCount (inMixedClass rawBad p q r) X : ℝ) < ε * (X : ℝ)

/-- Any single fixed residue class modulo 2^p*3^q detects a counterexample
through positive lower density. Sparsity in that class is still unproved. -/
theorem collatz_iff_sparse_bad_in_one_mixed_class (p q : ℕ) (r : Fin (2 ^ p * 3 ^ q)) :
    (∀ n : ℕ, 0 < n → Reaches n 1) ↔ SparseBadInMixedClass p q r := by
  constructor
  · intro hall ε hε X₀
    have hempty : inMixedClass rawBad p q r = ∅ := by
      ext n
      simp only [inMixedClass, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hn => hn.1.2 (hall n hn.1.1)
    let X := max X₀ 1
    have hXpos : 0 < X := by dsimp [X]; omega
    refine ⟨X, le_max_left _ _, hXpos, ?_⟩
    rw [hempty]
    simpa [Terras.natCount] using mul_pos hε (show (0 : ℝ) < X by exact_mod_cast hXpos)
  · intro hsparse n hn
    by_contra hnot
    obtain ⟨c, hc, X₀, hX₀⟩ :=
      counterexamples_positive_density_every_mixed_class ⟨n, hn, hnot⟩ p q r
    obtain ⟨X, hX, _, hsmall⟩ := hsparse c hc X₀
    exact (not_lt_of_ge (hX₀ X hX)) hsmall

end
end CollatzTargetDensity
