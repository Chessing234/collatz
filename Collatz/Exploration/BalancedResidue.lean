import Collatz.Structure.Density

/-! Construct residues whose finite homogeneous accelerated dynamics remain
between one and three times their initial scale. No infinite realizer is asserted. -/
namespace Collatz.Exploration.BalancedResidue

/-- Taking a shorter prefix commutes with recording the parity vector. -/
theorem vector_prefix (n j K : Nat) (hj : j ≤ K) :
    (parityVector n K).take j = parityVector n j := by
  simp only [parityVector, ← List.map_take, List.take_range, Nat.min_eq_left hj]

theorem counts_of_vector {n r K : Nat} (h : parityVector n K = parityVector r K)
    (j : Nat) (hj : j ≤ K) : oddCount n j = oddCount r j := by
  have hv := congrArg (fun xs : List Nat => xs.take j) h
  rw [vector_prefix n j K hj, vector_prefix r j K hj] at hv
  exact congrArg (fun xs : List Nat => xs.count 1) hv

theorem bit_of_vector {n r K j : Nat} (h : parityVector n K = parityVector r K)
    (hj : j < K) : acceleratedOrbit j n % 2 = acceleratedOrbit j r % 2 := by
  have h0 := counts_of_vector h j (by omega)
  have h1 := counts_of_vector h (j+1) (by omega)
  rw [Density.oddCount_succ_last, Density.oddCount_succ_last] at h1
  omega

theorem vector_class (K m r : Nat) (hr : r < 2^K) :
    parityVector (2^K*m+r) K = parityVector r K := by
  have hm : (2^K*m+r)%2^K = r := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  rw [parityVector_mod_pow_two, hm]

/-- The two extensions of a residue have opposite next parity bits. -/
theorem extend_bit (K r bit : Nat) (hr : r < 2^K) (hb : bit = 0 ∨ bit = 1) :
    ∃ s, s < 2^(K+1) ∧ parityVector s K = parityVector r K ∧
      acceleratedOrbit K s % 2 = bit := by
  have hp : 0 < (2:Nat)^K := Nat.pow_pos (by decide)
  have hs : (2:Nat)^(K+1) = 2*2^K := by rw [Nat.pow_succ]; omega
  by_cases he : acceleratedOrbit K r % 2 = bit
  · exact ⟨r,by omega,rfl,he⟩
  · refine ⟨2^K+r,by omega,?_,?_⟩
    · simpa using vector_class K 1 r hr
    · have ho : (3^oddCount r K)%2 = 1 := by simp [Nat.pow_mod]
      have hv := Congruence.accOrbit_pow_two_mul_add K 1 r
      simp only [Nat.mul_one] at hv
      rw [hv, Nat.add_mod, ho]
      have hm : acceleratedOrbit K r % 2 < 2 := Nat.mod_lt _ (by decide)
      rcases hb with hb | hb <;> omega

/-- Homogeneous coefficient safety, including the tighter margin before odd steps. -/
def Safe (K r : Nat) : Prop :=
  (∀ j, j ≤ K → 2^j ≤ 3^oddCount r j ∧ 3^oddCount r j < 3*2^j) ∧
  (∀ j, j < K → acceleratedOrbit j r % 2 = 1 → 3^oddCount r j < 2*2^j)

/-- A balanced residue exists for every finite horizon. Its future is unrestricted. -/
theorem exists_safe (K : Nat) : ∃ r, r < 2^K ∧ Safe K r := by
  induction K with
  | zero =>
    refine ⟨0,by decide,?_,?_⟩
    · intro j hj
      have : j = 0 := by omega
      subst j
      simp [oddCount,parityVector]
    · intro j hj; omega
  | succ K ih =>
    obtain ⟨r,hr,hbounds,hodd⟩ := ih
    let bit := if 3^oddCount r K < 2*2^K then 1 else 0
    have hb : bit = 0 ∨ bit = 1 := by dsimp [bit]; split <;> simp
    obtain ⟨s,hs,hvector,hbit⟩ := extend_bit K r bit hr hb
    have hc := counts_of_vector hvector K (by omega)
    have hnext := Density.oddCount_succ_last s K
    rw [hc, hbit] at hnext
    have hpow : (2:Nat)^(K+1) = 2*2^K := by rw [Nat.pow_succ]; omega
    refine ⟨s,hs,?_,?_⟩
    · intro j hj
      by_cases he : j = K+1
      · subst j
        rw [hnext, hpow]
        have hold := hbounds K (by omega)
        by_cases hlt : 3^oddCount r K < 2*2^K
        · have hval : bit = 1 := by simp [bit,hlt]
          rw [hval, Nat.pow_succ]
          omega
        · have hval : bit = 0 := by simp [bit,hlt]
          rw [hval, Nat.add_zero]
          omega
      · rw [counts_of_vector hvector j (by omega)]
        exact hbounds j (by omega)
    · intro j hj hparity
      by_cases he : j = K
      · subst j
        rw [hc]
        have hval : bit = 1 := by omega
        by_cases hlt : 3^oddCount r K < 2*2^K
        · exact hlt
        · have : bit = 0 := by simp [bit,hlt]
          omega
      · have hprior := bit_of_vector hvector (show j < K by omega)
        rw [counts_of_vector hvector j (by omega)]
        exact hodd j (by omega) (by omega)

end Collatz.Exploration.BalancedResidue
