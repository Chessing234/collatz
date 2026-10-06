import Collatz.Accelerated

/-!
# Fixed-block residue-monotone potentials cannot prove universal descent

A common Lyapunov proposal allows different formulas on finitely many residue
classes but requires each formula to be nondecreasing as the input grows.
The obstruction below applies to arbitrary natural-valued formulas, not just
affine functions. For every positive modulus M and fixed positive horizon L,
there is an input above 1 that grows under L accelerated steps and returns to
the same residue modulo M. A residue-monotone potential therefore cannot
strictly decrease there.

The witness is n = 2^(L+1)*M - 1, whose first L accelerated steps are odd,
ending at 2*3^L*M - 1. Both endpoints are -1 modulo M.
This does not exclude adaptive horizons or nonmonotone residue formulas.
-/
namespace Collatz.Exploration.ResiduePotential

/-- A potential is monotone separately on each arithmetic progression. -/
def ResidueMonotone (M : Nat) (P : Nat → Nat) : Prop :=
  ∀ x y, x % M = y % M → x ≤ y → P x ≤ P y

/-- The basic odd transition, written without natural subtraction ambiguity. -/
theorem odd_step (v : Nat) (hv : 0 < v) :
    acceleratedStep (2*v-1) = 3*v-1 := by
  rw [acceleratedStep, if_neg (by omega : ¬ (2*v-1)%2 = 0)]
  omega

/-- A prescribed all-odd prefix has this exact affine endpoint. -/
theorem odd_prefix (L u : Nat) (hu : 0 < u) :
    acceleratedOrbit L (2^L*u-1) = 3^L*u-1 := by
  induction L generalizing u with
  | zero => simp
  | succ L ih =>
    have hv : 0 < 2^L*u := Nat.mul_pos (Nat.two_pow_pos L) hu
    have hin : 2^(L+1)*u-1 = 2*(2^L*u)-1 := by
      rw [Nat.pow_succ]
      congr 1
      ac_rfl
    rw [hin, acceleratedOrbit_succ, odd_step _ hv]
    have he : 3*(2^L*u)-1 = 2^L*(3*u)-1 := by congr 1; ac_rfl
    rw [he, ih (3*u) (by omega), Nat.pow_succ]
    congr 1
    ac_rfl

/-- Every positive multiple minus one represents the same residue. -/
theorem multiple_pred_mod (a M : Nat) (ha : 0 < a) (hM : 0 < M) :
    (a*M-1) % M = M-1 := by
  have hle : M ≤ a*M := by
    have h := Nat.mul_le_mul_right M (show 1 ≤ a by omega)
    simpa using h
  have hsub : (a-1)*M = a*M-M := by simpa using Nat.sub_mul a 1 M
  have he : a*M-1 = (a-1)*M+(M-1) := by omega
  rw [he, Nat.add_mod, Nat.mul_mod]
  simp [Nat.mod_eq_of_lt (show M-1 < M by omega)]

/-- The endpoint is strictly larger for a positive all-odd horizon. -/
theorem prefix_grows (L M : Nat) (hL : 0 < L) (hM : 0 < M) :
    2^(L+1)*M-1 < 2*3^L*M-1 := by
  have hp : (2:Nat)^L < 3^L := Nat.pow_lt_pow_left (by omega) (by omega : L ≠ 0)
  have hscaled := Nat.mul_lt_mul_of_pos_right hp hM
  have htwo : 2^(L+1)*M = 2*(2^L*M) := by
    rw [Nat.pow_succ]
    ac_rfl
  have hpos : 0 < 2^L*M := Nat.mul_pos (Nat.two_pow_pos L) hM
  rw [htwo, Nat.mul_assoc]
  omega

/-- An explicit growing witness above 1 returns to its residue after L steps. -/
theorem growing_same_residue (L M : Nat) (hL : 0 < L) (hM : 0 < M) :
    ∃ n, 1 < n ∧ n < acceleratedOrbit L n ∧
      n % M = acceleratedOrbit L n % M := by
  let n := 2^(L+1)*M-1
  have hend : acceleratedOrbit L n = 2*3^L*M-1 := by
    have hin : n = 2^L*(2*M)-1 := by
      dsimp [n]
      rw [Nat.pow_succ]
      congr 1
      ac_rfl
    rw [hin, odd_prefix L (2*M) (by omega)]
    congr 1
    ac_rfl
  have hfour : 4 ≤ 2^(L+1) := by
    have h := Nat.pow_le_pow_right (show 1 ≤ (2:Nat) by omega)
      (show 2 ≤ L+1 by omega)
    exact h
  have hstart : 1 < n := by
    have h := Nat.mul_le_mul_left (2^(L+1)) (show 1 ≤ M by omega)
    dsimp [n]
    omega
  refine ⟨n, hstart, ?_, ?_⟩
  · rw [hend]
    exact prefix_grows L M hL hM
  · rw [hend]
    dsimp [n]
    rw [multiple_pred_mod _ M (Nat.two_pow_pos _) hM,
      multiple_pred_mod _ M (Nat.mul_pos (by omega) (Nat.pow_pos (by omega))) hM]

/-- No residue-monotone potential strictly decreases after a fixed block on
all nontrivial inputs. The function need not be affine or computable. -/
theorem no_fixed_block_potential {M L : Nat} {P : Nat → Nat}
    (hM : 0 < M) (hL : 0 < L) (hP : ResidueMonotone M P) :
    ¬ (∀ n, 1 < n → P (acceleratedOrbit L n) < P n) := by
  intro hdrop
  obtain ⟨n, hn, hg, hr⟩ := growing_same_residue L M hL hM
  have hmono := hP n (acceleratedOrbit L n) hr (Nat.le_of_lt hg)
  have hstrict := hdrop n hn
  omega

/-- In particular, no such potential decreases at every accelerated step. -/
theorem no_single_step_potential {M : Nat} {P : Nat → Nat}
    (hM : 0 < M) (hP : ResidueMonotone M P) :
    ¬ (∀ n, 1 < n → P (acceleratedStep n) < P n) := by
  simpa [acceleratedOrbit] using no_fixed_block_potential hM (by decide : 0 < 1) hP

/-- Piecewise affine formulas with nonnegative slopes are residue-monotone.
The intercepts and slopes may be arbitrary functions of the residue. -/
theorem affine_residue_monotone (M : Nat) (a b : Nat → Nat) :
    ResidueMonotone M (fun n => a (n%M)*n+b (n%M)) := by
  intro x y hr hxy
  dsimp only
  rw [hr]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hxy) _

/-- Finite-residue affine Lyapunov candidates fail at every fixed horizon. -/
theorem no_affine_residue_potential (M L : Nat) (a b : Nat → Nat)
    (hM : 0 < M) (hL : 0 < L) :
    ¬ (∀ n, 1 < n →
      a (acceleratedOrbit L n % M)*acceleratedOrbit L n+
        b (acceleratedOrbit L n % M) < a (n%M)*n+b (n%M)) :=
  no_fixed_block_potential hM hL (affine_residue_monotone M a b)

end Collatz.Exploration.ResiduePotential
