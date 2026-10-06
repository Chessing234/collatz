import Collatz.Exploration.ResiduePotential

/-!
# Bounded adaptive horizons do not rescue residue-monotone potentials

The fixed-block obstruction can be strengthened. For any positive modulus M
and any prescribed horizon H, one input remains in the residue -1 modulo M
and never decreases during *all* the first H accelerated steps. Consequently
no residue-monotone potential can guarantee a decrease within a universally
bounded adaptive lookahead either.

The concrete witness is 2^(H+2)*M-1. The extra factor of four ensures it exceeds
1 even for H=0 and M=1. At time j≤H, its exact value is
3^j * 2^(H+2-j) * M - 1. This is a finite-prefix obstruction; it says nothing
about its eventual descent beyond H.
-/
namespace Collatz.Exploration.AdaptiveResidueObstruction

open ResiduePotential

/-- A long all-odd input supplies the exact endpoint at every earlier time. -/
theorem prefix_endpoint (H M j : Nat) (hM : 0 < M) (hj : j ≤ H) :
    acceleratedOrbit j (2^(H+2)*M-1) = 3^j*2^(H+2-j)*M-1 := by
  have he : j+(H+2-j) = H+2 := by omega
  have hin : 2^(H+2)*M-1 = 2^j*(2^(H+2-j)*M)-1 := by
    have hsplit : (2:Nat)^(H+2) = 2^j*2^(H+2-j) := by rw [← Nat.pow_add, he]
    rw [hsplit]
    congr 1
    ac_rfl
  rw [hin, odd_prefix j _ (Nat.mul_pos (Nat.two_pow_pos _) hM)]
  congr 1
  ac_rfl

/-- Every endpoint in the prescribed prefix is at least its starting value. -/
theorem prefix_non_decreasing_from_start (H M j : Nat)
    (hM : 0 < M) (hj : j ≤ H) :
    2^(H+2)*M-1 ≤ acceleratedOrbit j (2^(H+2)*M-1) := by
  rw [prefix_endpoint H M j hM hj]
  have he : j+(H+2-j) = H+2 := by omega
  have hpow : (2:Nat)^j ≤ 3^j := Nat.pow_le_pow_left (by decide) j
  have hmul := Nat.mul_le_mul_right (2^(H+2-j)*M) hpow
  have hin : 2^(H+2)*M = 2^j*(2^(H+2-j)*M) := by
    have hsplit : (2:Nat)^(H+2) = 2^j*2^(H+2-j) := by rw [← Nat.pow_add, he]
    rw [hsplit]
    ac_rfl
  have hout : 3^j*2^(H+2-j)*M = 3^j*(2^(H+2-j)*M) := by ac_rfl
  rw [hin, hout]
  omega

/-- The entire prefix stays in the same residue, for arbitrary positive M. -/
theorem prefix_same_residue (H M j : Nat) (hM : 0 < M) (hj : j ≤ H) :
    (2^(H+2)*M-1)%M = acceleratedOrbit j (2^(H+2)*M-1)%M := by
  rw [prefix_endpoint H M j hM hj]
  rw [multiple_pred_mod _ M (Nat.two_pow_pos _) hM]
  exact (multiple_pred_mod (3^j*2^(H+2-j)) M
    (Nat.mul_pos (Nat.pow_pos (by decide : 0 < (3:Nat)))
      (Nat.two_pow_pos (H+2-j))) hM).symm

/-- The chosen starting point is always nontrivial, including horizon zero. -/
theorem witness_nontrivial (H M : Nat) (hM : 0 < M) : 1 < 2^(H+2)*M-1 := by
  have hfour : 4 ≤ (2:Nat)^(H+2) :=
    Nat.pow_le_pow_right (by decide : 1 ≤ (2:Nat)) (show 2 ≤ H+2 by omega)
  have hmul := Nat.mul_le_mul_left (2^(H+2)) (show 1 ≤ M by omega)
  omega

/-- Every residue-monotone potential survives a prescribed adaptive horizon. -/
theorem potential_prefix (H M : Nat) (hM : 0 < M) {P : Nat → Nat}
    (hP : ResidueMonotone M P) :
    ∃ n, 1 < n ∧ ∀ j, j ≤ H → P n ≤ P (acceleratedOrbit j n) := by
  refine ⟨2^(H+2)*M-1, witness_nontrivial H M hM, ?_⟩
  intro j hj
  exact hP _ _ (prefix_same_residue H M j hM hj)
    (prefix_non_decreasing_from_start H M j hM hj)

/-- Choosing the best time in a bounded lookahead cannot give a global rank
certificate when the potential is monotone on each residue class. -/
theorem no_bounded_adaptive_potential (H M : Nat) (hM : 0 < M)
    {P : Nat → Nat} (hP : ResidueMonotone M P) :
    ¬ (∀ n, 1 < n → ∃ j, j ≤ H ∧ P (acceleratedOrbit j n) < P n) := by
  intro h
  obtain ⟨n, hn, hprefix⟩ := potential_prefix H M hM hP
  obtain ⟨j, hj, hdrop⟩ := h n hn
  have := hprefix j hj
  omega

/-- The obstruction includes arbitrary nonnegative affine formulas by residue. -/
theorem no_bounded_adaptive_affine (H M : Nat) (hM : 0 < M)
    (a b : Nat → Nat) :
    ¬ (∀ n, 1 < n → ∃ j, j ≤ H ∧
      a (acceleratedOrbit j n%M)*acceleratedOrbit j n+b (acceleratedOrbit j n%M) <
        a (n%M)*n+b (n%M)) :=
  no_bounded_adaptive_potential H M hM (affine_residue_monotone M a b)

/-- Size descent itself is a special case, and therefore needs unbounded
lookahead as a function of the input if universal descent is true. -/
theorem no_bounded_size_descent (H : Nat) :
    ¬ (∀ n, 1 < n → ∃ j, j ≤ H ∧ acceleratedOrbit j n < n) :=
  no_bounded_adaptive_potential H 1 (by decide) (fun _ _ _ h => h)

end Collatz.Exploration.AdaptiveResidueObstruction
