import Collatz.Strategy.HeavyResidue

/-! A finite-horizon, all-starting-values coefficient-descent theorem.
No assertion that every starting value has a first light prefix is made. -/
namespace Collatz.FirstLightDescent
open AffineExact

def FirstLight (n k : Nat) : Prop :=
  3^oddCount n k < 2^k ∧ ∀ i, i<k → 2^i ≤ 3^oddCount n i

instance (n k : Nat) : Decidable (FirstLight n k) :=
  inferInstanceAs (Decidable (_ ∧ ∀ i, i<k → _))

theorem first_light_accumulator {n k : Nat} (h : FirstLight n k) :
    3*affineC k n ≤ oddCount n k * 3^oddCount n k := by
  cases k with
  | zero => simp [affineC, oddCount]
  | succ k =>
    have hb := HeavyResidue.heavy_accumulator_bound_sharp n k
      (fun i hi => h.2 i (by omega))
    have hlast := Density.oddCount_succ_last n k
    have hh := h.2 k (by omega)
    have hl := h.1
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit k n) with he | ho
    · have hc : oddCount n (k+1) = oddCount n k := by omega
      rw [hc, affineC_even he]
      exact hb
    · have hc : oddCount n (k+1) = oddCount n k + 1 := by omega
      rw [hc, Arith.three_pow_succ, Arith.two_pow_succ] at hl
      omega

/-- Any failure at the first coefficient crossing has an explicit size bound. -/
theorem failure_bound {n k : Nat} (h : FirstLight n k)
    (hf : n ≤ acceleratedOrbit k n) :
    3*(2^k-3^oddCount n k)*n ≤ oddCount n k * 3^oddCount n k := by
  have ha := affine_exact n k
  have hb := first_light_accumulator h
  have hm := Nat.mul_le_mul_left (2^k) hf
  have hd : (2^k-3^oddCount n k)*n + 3^oddCount n k*n = 2^k*n := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt h.1)]
  have hc : (2^k-3^oddCount n k)*n ≤ affineC k n := by omega
  have ht := Nat.mul_le_mul_left 3 hc
  rw [← Nat.mul_assoc] at ht
  exact Nat.le_trans ht hb

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem gap_table : ∀ k : Fin 129, ∀ a : Fin (k.val+1),
    3^a.val < 2^k.val → a.val*3^a.val < 3*(2^k.val-3^a.val)*1186 := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem small_starts : ∀ n : Fin 1186, 1<n.val →
    ∃ k : Fin 129, FirstLight n.val k.val ∧ acceleratedOrbit k.val n.val < n.val := by
  decide

theorem first_light_unique {n j k : Nat} (hj : FirstLight n j) (hk : FirstLight n k) :
    j=k := by
  rcases Nat.lt_trichotomy j k with hlt | heq | hgt
  · have := hk.2 j hlt
    have := hj.1
    omega
  · exact heq
  · have := hj.2 k hgt
    have := hk.1
    omega

/-- Every integer >1 descends at its first coefficient crossing if that
crossing occurs by step 128. There is no upper bound on the starting integer. -/
theorem descent_at_first_light_le_128 {n k : Nat} (hn : 1<n)
    (hk : k≤128) (hfirst : FirstLight n k) : acceleratedOrbit k n < n := by
  by_cases hsmall : n<1186
  · obtain ⟨j, hj, hd⟩ := small_starts ⟨n,hsmall⟩ hn
    have he := first_light_unique hj hfirst
    simpa only [he] using hd
  · have ha := oddCount_le_self n k
    have ht := gap_table ⟨k,by omega⟩ ⟨oddCount n k,by change oddCount n k < k+1; omega⟩ hfirst.1
    change oddCount n k * 3^oddCount n k <
      3*(2^k-3^oddCount n k)*1186 at ht
    by_cases hd : acceleratedOrbit k n < n
    · exact hd
    · have hb := failure_bound hfirst (by omega)
      have hm := Nat.mul_le_mul_left (3*(2^k-3^oddCount n k))
        (show 1186≤n by omega)
      omega

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
/-- This theorem cannot be read as a uniform 128-step descent bound:
a positive Mersenne starting value has no coefficient crossing by step 128. -/
theorem no_crossing_128_witness : ∀ k : Fin 129,
    2^k.val ≤ 3^oddCount (2^129-1) k.val := by decide

end Collatz.FirstLightDescent
