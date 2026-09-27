import CollatzTargetDensity.PadicInverseBoundary

/-! An unconditional rational example distinguishing the two limit operations.
This is not a Collatz orbit and does not refute additional arithmetic hypotheses. -/
namespace CollatzTargetDensity.TwoTopologyExample
open Filter InverseBoundary
open scoped Topology
noncomputable section

def q (k : ℕ) : ℚ := (2 : ℚ) ^ k * (3 ^ k / 2 ^ k : ℕ) / (3 : ℚ) ^ k

theorem real_bounds (k : ℕ) :
    1 - (2 / 3 : ℝ) ^ k ≤ (q k : ℝ) ∧ (q k : ℝ) ≤ 1 := by
  have hd := Nat.mod_add_div (3 ^ k) (2 ^ k)
  have hr := Nat.mod_lt (3 ^ k) (show 0 < 2 ^ k by positivity)
  have huN : 2 ^ k * (3 ^ k / 2 ^ k) ≤ 3 ^ k := by omega
  have hlN : 3 ^ k ≤ 2 ^ k * ((3 ^ k / 2 ^ k) + 1) := by nlinarith
  have hu : (2 : ℝ) ^ k * (3 ^ k / 2 ^ k : ℕ) ≤ (3 : ℝ) ^ k := by exact_mod_cast huN
  have hl : (3 : ℝ) ^ k ≤ (2 : ℝ) ^ k * ((3 ^ k / 2 ^ k : ℕ) + 1) := by exact_mod_cast hlN
  have hden : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  have hq : (q k : ℝ) = (2 : ℝ) ^ k * (3 ^ k / 2 ^ k : ℕ) / (3 : ℝ) ^ k := by simp [q]
  rw [hq]
  constructor
  · rw [div_pow]
    apply (le_div_iff₀ hden).mpr
    have he : (1 - (2 : ℝ) ^ k / (3 : ℝ) ^ k) * (3 : ℝ) ^ k =
        (3 : ℝ) ^ k - (2 : ℝ) ^ k := by field_simp
    rw [he]
    nlinarith
  · exact (div_le_one hden).mpr hu

theorem tends_to_one_real : Tendsto (fun k => (q k : ℝ)) atTop (nhds 1) := by
  have ht : Tendsto (fun k : ℕ => (2 / 3 : ℝ) ^ k) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hl : Tendsto (fun k : ℕ => 1 - (2 / 3 : ℝ) ^ k) atTop (nhds 1) := by
    simpa using (show Tendsto (fun k : ℕ => 1 - (2 / 3 : ℝ) ^ k) atTop (nhds (1 - 0)) from
      tendsto_const_nhds.sub ht)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds
    (fun k => (real_bounds k).1) (fun k => (real_bounds k).2)

theorem norm_two_adic_le (k : ℕ) : ‖(q k : ℚ_[2])‖ ≤ (1 / 2 : ℝ) ^ k := by
  have h2 : ‖(2 : ℚ_[2])‖ = (1 / 2 : ℝ) := by simpa using Padic.norm_p (p := 2)
  have ha : ‖((3 ^ k / 2 ^ k : ℕ) : ℚ_[2])‖ ≤ 1 := by
    simpa only [Int.cast_natCast] using Padic.norm_int_le_one (p := 2) (3 ^ k / 2 ^ k : ℕ)
  have hq : (q k : ℚ_[2]) = (2 : ℚ_[2]) ^ k * (3 ^ k / 2 ^ k : ℕ) / (3 : ℚ_[2]) ^ k := by
    simp [q]
  rw [hq, norm_div, norm_mul, norm_pow, norm_pow, h2, norm_three_two_adic, one_pow, div_one]
  simpa using mul_le_mul_of_nonneg_left ha (show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k by positivity)

theorem tends_to_zero_two_adic : Tendsto (fun k => (q k : ℚ_[2])) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) norm_two_adic_le
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))

/-- One explicit sequence of rationals has distinct limits in the two completions. -/
theorem explicit_distinct_limits :
    Tendsto (fun k => (q k : ℝ)) atTop (nhds 1) ∧
      Tendsto (fun k => (q k : ℚ_[2])) atTop (nhds 0) :=
  ⟨tends_to_one_real, tends_to_zero_two_adic⟩

theorem no_unconditional_transfer_of_zero_limit :
    ¬∀ f : ℕ → ℚ, Tendsto (fun k => (f k : ℚ_[2])) atTop (nhds 0) →
      Tendsto (fun k => (f k : ℝ)) atTop (nhds 0) := by
  intro h
  have he := tendsto_nhds_unique tends_to_one_real (h q tends_to_zero_two_adic)
  norm_num at he

end
end CollatzTargetDensity.TwoTopologyExample
