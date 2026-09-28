import Collatz.Accelerated

/-!
A failed route to universal descent, checked without assuming convergence.
For n = 8^r - 5, the first r accelerated blocks have parity odd, odd, even
and none of their intermediate values is below n. The endpoint is 9^r - 5.
This refutes a uniform bound on the number of these blocks needed for descent.
It neither refutes eventual descent nor establishes a new result in the literature.

Check with: lake env lean Research/UniversalDescentBlockAttempt.lean
-/

namespace Collatz.UniversalDescentBlockAttempt

theorem block_values (u : Nat) (hu : 0 < u) :
    acceleratedOrbit 1 (8*u-5) = 12*u-7 ∧
    acceleratedOrbit 2 (8*u-5) = 18*u-10 ∧
    acceleratedOrbit 3 (8*u-5) = 9*u-5 := by
  have h1 : acceleratedStep (8*u-5) = 12*u-7 := by
    rw [acceleratedStep, if_neg (by omega : (8*u-5)%2 ≠ 0)]
    omega
  have h2 : acceleratedStep (12*u-7) = 18*u-10 := by
    rw [acceleratedStep, if_neg (by omega : (12*u-7)%2 ≠ 0)]
    omega
  have h3 : acceleratedStep (18*u-10) = 9*u-5 := by
    rw [acceleratedStep, if_pos (by omega : (18*u-10)%2 = 0)]
    omega
  exact ⟨h1, by simp [acceleratedOrbit, h1, h2],
    by simp [acceleratedOrbit, h1, h2, h3]⟩

theorem block_never_below_start (u : Nat) (hu : 0 < u) (s : Nat) (hs : s ≤ 3) :
    8*u-5 ≤ acceleratedOrbit s (8*u-5) := by
  obtain ⟨h1, h2, h3⟩ := block_values u hu
  have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 := by omega
  rcases hcases with h | h | h | h <;> subst s
  · simp
  · rw [h1]; omega
  · rw [h2]; omega
  · rw [h3]; omega

/-- The exact orbit at the boundaries of the repeated odd-odd-even blocks. -/
theorem block_orbit (r j : Nat) (hj : j ≤ r) :
    acceleratedOrbit (3*j) (8^r-5) = 9^j * 8^(r-j)-5 := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hjr : j ≤ r := by omega
    have he : r-j = (r-(j+1))+1 := by omega
    let u := 9^j * 8^(r-(j+1))
    have hu : 0 < u := Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
    have hsplit : 9^j * 8^(r-j) = 8*u := by
      rw [he, Nat.pow_succ]
      dsimp [u]
      ac_rfl
    rw [show 3*(j+1) = 3+3*j by omega, ← acceleratedOrbit_add,
      ih hjr, hsplit, (block_values u hu).2.2]
    congr 1
    rw [Nat.pow_succ]
    dsimp [u]
    ac_rfl

theorem block_boundaries_ge_start (r j : Nat) (hj : j ≤ r) :
    8^r-5 ≤ acceleratedOrbit (3*j) (8^r-5) := by
  rw [block_orbit r j hj]
  have hsplit : (8 : Nat)^r = 8^j * 8^(r-j) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hj]
  have hpow : (8 : Nat)^j ≤ 9^j := Nat.pow_le_pow_left (by decide) j
  have hprod := Nat.mul_le_mul_right (8^(r-j)) hpow
  rw [← hsplit] at hprod
  exact Nat.sub_le_sub_right hprod 5

/-- Includes every intermediate iterate, not just the block endpoints. -/
theorem no_drop_through_blocks (r k : Nat) (hk : k ≤ 3*r) :
    8^r-5 ≤ acceleratedOrbit k (8^r-5) := by
  let j := k/3
  have hj : j ≤ r := by dsimp [j]; omega
  by_cases hjr : j = r
  · have he : k = 3*r := by dsimp [j] at hjr; omega
    rw [he]
    exact block_boundaries_ge_start r r (Nat.le_refl _)
  · have hjlt : j < r := by omega
    let u := 9^j * 8^(r-j-1)
    have hu : 0 < u := Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
    have he : r-j = (r-j-1)+1 := by omega
    have hsplit : 9^j * 8^(r-j) = 8*u := by
      rw [he, Nat.pow_succ]
      dsimp [u]
      ac_rfl
    have hb : acceleratedOrbit (3*j) (8^r-5) = 8*u-5 := by
      rw [block_orbit r j hj, hsplit]
    calc
      8^r-5 ≤ acceleratedOrbit (3*j) (8^r-5) := block_boundaries_ge_start r j hj
      _ ≤ acceleratedOrbit (k%3) (acceleratedOrbit (3*j) (8^r-5)) := by
        rw [hb]
        exact block_never_below_start u hu (k%3) (by omega)
      _ = acceleratedOrbit k (8^r-5) := by
        rw [acceleratedOrbit_add]
        congr 1
        dsimp [j]
        omega

/-- The family gives genuine starting values greater than 1 for every r > 0. -/
theorem witness (r : Nat) (hr : 0 < r) :
    1 < 8^r-5 ∧
    (∀ k : Nat, k ≤ 3*r → 8^r-5 ≤ acceleratedOrbit k (8^r-5)) ∧
    acceleratedOrbit (3*r) (8^r-5) = 9^r-5 := by
  have hp : 8 ≤ (8 : Nat)^r := by
    have h := Nat.pow_le_pow_right (by decide : 0 < (8 : Nat)) hr
    simpa using h
  refine ⟨by omega, no_drop_through_blocks r, ?_⟩
  simpa using block_orbit r r (Nat.le_refl _)

/-- Reserving one extra factor of 8 makes every one of the first r block
endpoints odd. Thus these blocks each include the entire halving run, rather
than stopping halfway through a longer run of even inputs. -/
theorem complete_block_witness (r : Nat) :
    1 < 8^(r+1)-5 ∧
    (∀ k : Nat, k ≤ 3*r → 8^(r+1)-5 ≤ acceleratedOrbit k (8^(r+1)-5)) ∧
    (∀ j : Nat, j ≤ r → acceleratedOrbit (3*j) (8^(r+1)-5) % 2 = 1) ∧
    acceleratedOrbit (3*r) (8^(r+1)-5) = 8*9^r-5 := by
  have hw := witness (r+1) (by omega)
  refine ⟨hw.1, ?_, ?_, ?_⟩
  · intro k hk
    exact no_drop_through_blocks (r+1) k (by omega)
  · intro j hj
    rw [block_orbit (r+1) j (by omega)]
    have he : r+1-j = (r-j)+1 := by omega
    rw [he, Nat.pow_succ]
    have hp : 0 < 9^j * 8^(r-j) :=
      Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
    have hsplit : 9^j * (8^(r-j)*8) = 8*(9^j * 8^(r-j)) := by ac_rfl
    rw [hsplit]
    omega
  · have hb := block_orbit (r+1) r (by omega)
    simpa [Nat.mul_comm] using hb

theorem complete_blocks_increase (r : Nat) (hr : 0 < r) :
    8^(r+1)-5 < acceleratedOrbit (3*r) (8^(r+1)-5) := by
  rw [(complete_block_witness r).2.2.2, Nat.pow_succ]
  have hp : (8 : Nat)^r < 9^r := Nat.pow_lt_pow_left (by decide) (by omega)
  have hmul := Nat.mul_lt_mul_of_pos_left hp (by decide : 0 < (8 : Nat))
  have hpos : 0 < (8 : Nat)^r := Nat.pow_pos (by decide)
  rw [Nat.mul_comm (8^r) 8]
  omega

/-- A growing prefix is not a counterexample to eventual descent:
the r=1 example starts at 59, grows to 67 after one block, then drops to 38. -/
example : acceleratedOrbit 3 59 = 67 ∧ acceleratedOrbit 7 59 = 38 := by decide

end Collatz.UniversalDescentBlockAttempt

#print axioms Collatz.UniversalDescentBlockAttempt.block_values
#print axioms Collatz.UniversalDescentBlockAttempt.block_orbit
#print axioms Collatz.UniversalDescentBlockAttempt.no_drop_through_blocks
#print axioms Collatz.UniversalDescentBlockAttempt.witness
#print axioms Collatz.UniversalDescentBlockAttempt.complete_block_witness
#print axioms Collatz.UniversalDescentBlockAttempt.complete_blocks_increase
