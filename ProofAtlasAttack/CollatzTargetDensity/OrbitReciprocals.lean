import CollatzTargetDensity.SyracusePacking
import CollatzTargetDensity.TernarySpread
import Mathlib.Analysis.PSeries

/-! Reciprocal summability for injective Syracuse orbits. This is a necessary
condition on a divergent orbit; it does not exclude such an orbit. -/
namespace CollatzTargetDensity.OrbitReciprocals
open Erdos1135 SyracusePacking ND.PositiveDensity
open scoped BigOperators
noncomputable section

def side (n : ℕ) : ℕ := if n % 3 = 2 then 16 * n + 5 else 4 * n + 1

theorem side_pos (n : ℕ) : 0 < side n := by unfold side; split_ifs <;> omega

theorem side_odd (n : ℕ) : Odd (side n) := by
  unfold side
  split_ifs
  · exact ⟨8 * n + 2, by omega⟩
  · exact ⟨2 * n, by omega⟩

theorem side_coprime (n : ℕ) : Nat.Coprime (side n) 3 := by
  have hn := Nat.mod_lt n (by decide : 0 < 3)
  have hmod : side n % 3 = 1 ∨ side n % 3 = 2 := by
    unfold side
    split_ifs <;> omega
  rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec]
  rcases hmod with h | h <;> rw [h] <;> decide

theorem side_ne (n : ℕ) : side n ≠ n := by unfold side; split_ifs <;> omega

theorem side_le {n : ℕ} (hn : 0 < n) : side n ≤ 21 * n := by
  unfold side
  split_ifs <;> omega

theorem side_syracuse (n : ℕ) : Tao.syracuse (side n) = Tao.syracuse n := by
  unfold side
  split_ifs
  · simpa [sibling, ndA5PreviousPhysicalCollapseSource] using sibling_syracuse 2 n
  · simpa [sibling, ndA5PreviousPhysicalCollapseSource] using sibling_syracuse 1 n

def orbit (n i : ℕ) : ℕ := Tao.syracuse^[i] n

theorem orbit_succ (n i : ℕ) : Tao.syracuse (orbit n i) = orbit n (i + 1) := by
  simp only [orbit, Function.iterate_succ_apply']

theorem orbit_pos {n : ℕ} (hn : 0 < n) (i : ℕ) : 0 < orbit n i := by
  cases i with
  | zero => exact hn
  | succ i => rw [← orbit_succ]; exact Tao.syracuse_pos _

theorem side_off_orbit (n : ℕ) (hi : Function.Injective (orbit n)) (i j : ℕ) :
    side (orbit n i) ≠ orbit n j := by
  intro h
  have he := congrArg Tao.syracuse h
  rw [side_syracuse, orbit_succ, orbit_succ] at he
  have hij : i = j := by have := hi he; omega
  subst j
  exact side_ne _ h

theorem iterate_side_succ (n i k : ℕ) :
    Tao.syracuse^[k + 1] (side (orbit n i)) = orbit n (k + (i + 1)) := by
  rw [Function.iterate_succ_apply, side_syracuse, orbit_succ]
  exact (Function.iterate_add_apply _ _ _ _).symm

theorem side_nonperiodic (n : ℕ) (hi : Function.Injective (orbit n)) (i : ℕ) :
    Nonperiodic Tao.syracuse (side (orbit n i)) := by
  intro k hk he
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [iterate_side_succ] at he
  exact side_off_orbit n hi i (l + (i + 1)) he.symm

theorem side_hit_forces_same_index (n : ℕ) (hi : Function.Injective (orbit n))
    (i j k : ℕ) (hhit : Tao.syracuse^[k] (side (orbit n i)) = side (orbit n j)) : i = j := by
  cases k with
  | zero =>
    have he := congrArg Tao.syracuse hhit
    simp only [Function.iterate_zero, id_eq, side_syracuse, orbit_succ] at he
    have := hi he
    omega
  | succ k =>
    rw [iterate_side_succ] at hhit
    exact False.elim (side_off_orbit n hi j (k + (i + 1)) hhit.symm)

theorem common_predecessor_comparable {α : Type*} (f : α → α) {x a b : α}
    {p q : ℕ} (ha : f^[p] x = a) (hb : f^[q] x = b) :
    (∃ k, f^[k] a = b) ∨ (∃ k, f^[k] b = a) := by
  rcases le_total p q with hpq | hqp
  · left
    refine ⟨q - p, ?_⟩
    rw [← ha, ← Function.iterate_add_apply, Nat.sub_add_cancel hpq, hb]
  · right
    refine ⟨p - q, ?_⟩
    rw [← hb, ← Function.iterate_add_apply, Nat.sub_add_cancel hqp, ha]

/-- Each side branch along an injective orbit has a disjoint Syracuse basin. -/
theorem side_basins_disjoint (n : ℕ) (hi : Function.Injective (orbit n)) :
    Pairwise (fun i j => Disjoint (oddReaches (side (orbit n i)))
      (oddReaches (side (orbit n j)))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  obtain ⟨_, p, hp⟩ := hxi
  obtain ⟨_, q, hq⟩ := hxj
  rcases common_predecessor_comparable Tao.syracuse hp hq with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact hij (side_hit_forces_same_index n hi i j k hk)
  · exact hij (side_hit_forces_same_index n hi j i k hk).symm

/-- One absolute constant bounds reciprocal partial sums on every positive
injective Syracuse orbit. Repeated or periodic orbits are not covered. -/
theorem uniform_orbit_reciprocal_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → Function.Injective (orbit n) →
      ∀ t : Finset ℕ, (∑ i ∈ t, 1 / (orbit n i : ℝ)) ≤ C := by
  obtain ⟨C, hC, hpack⟩ := uniform_reciprocal_packing
  refine ⟨21 * C, by positivity, ?_⟩
  intro n hn hi t
  have hp := hpack t (fun i => side (orbit n i))
    (fun i _ => ⟨side_pos _, side_odd _, side_coprime _, side_nonperiodic n hi i⟩)
    (fun i _ j _ hij => side_basins_disjoint n hi hij)
  calc
    _ ≤ ∑ i ∈ t, 21 * (1 / (side (orbit n i) : ℝ)) := by
      apply Finset.sum_le_sum
      intro i _
      have ha : (0 : ℝ) < orbit n i := by exact_mod_cast orbit_pos hn i
      have hb : (0 : ℝ) < side (orbit n i) := by exact_mod_cast side_pos (orbit n i)
      rw [mul_one_div]
      apply (div_le_div_iff₀ ha hb).mpr
      simpa using (show (side (orbit n i) : ℝ) ≤ 21 * orbit n i by
        exact_mod_cast side_le (orbit_pos hn i))
    _ = 21 * ∑ i ∈ t, 1 / (side (orbit n i) : ℝ) := by rw [Finset.mul_sum]
    _ ≤ 21 * C := mul_le_mul_of_nonneg_left hp (by norm_num)

theorem orbit_reciprocals_summable {n : ℕ} (hn : 0 < n)
    (hi : Function.Injective (orbit n)) : Summable (fun i => 1 / (orbit n i : ℝ)) := by
  obtain ⟨C, _, hC⟩ := uniform_orbit_reciprocal_bound
  exact summable_of_sum_le (fun _ => by positivity) (hC n hn hi)

theorem orbit_reciprocals_uniform_tsum :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → Function.Injective (orbit n) →
      (∑' i, 1 / (orbit n i : ℝ)) ≤ C := by
  obtain ⟨C, hC, hbound⟩ := uniform_orbit_reciprocal_bound
  exact ⟨C, hC, fun n hn hi => Real.tsum_le_of_sum_le (fun _ => by positivity) (hbound n hn hi)⟩

end
end CollatzTargetDensity.OrbitReciprocals
