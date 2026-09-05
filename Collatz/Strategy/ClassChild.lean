import Collatz.Strategy.TreeBranching

/-!
# Residue classes along the inverse tree

Two facts that make residue-class refinements of the inverse-tree count
possible (`TreeBranching` counts without classes; the Krasikov–Lagarias
refinement needs these):

* **The child's class is one level coarser than the parent's.**
  `child a v mod 3 ^ k` is decided by `2 ^ v · a mod 3 ^ (k+1)`
  (`child_mod_pow`): writing `2 ^ v a = 3 ^ (k+1) q + s` with `s ≡ 1 (mod 3)`,
  the child `(2 ^ v a − 1)/3` is `3 ^ k q + (s − 1)/3`.
* **The fertile valuations depend on the parent only modulo `9`**
  (`fval_eq_of_mod_nine`): `v₀` reads `a mod 3`, the phase reads
  `2 ^ v₀ a mod 9`.

Consequently the `i`-th fertile child of `a` has residue modulo `27` equal to
`((2 ^ fval (a % 81) i · (a % 81)) % 81 − 1) / 3` (`fch_mod_27`), a function of
`a % 81` alone — the transition of the class system at level `81`.
-/

namespace Collatz
namespace ClassChild

open TreeCount TreeBranching

/-! ## 1. The child's residue -/

/-- `child a v` modulo `3 ^ k` is decided by `2 ^ v · a` modulo `3 ^ (k+1)`. -/
theorem child_mod_pow {a v : Nat} (h3 : (2 ^ v * a) % 3 = 1) (k : Nat) :
    child a v % 3 ^ k = ((2 ^ v * a) % 3 ^ (k + 1) - 1) / 3 := by
  have hP : 0 < 3 ^ k := Nat.pow_pos (by decide)
  have h3P : (3:Nat) ^ (k + 1) = 3 * 3 ^ k := Nat.pow_succ' (n := k) (m := 3)
  have hdiv := Nat.div_add_mod (2 ^ v * a) (3 ^ (k + 1))
  have hlt : (2 ^ v * a) % 3 ^ (k + 1) < 3 ^ (k + 1) := Nat.mod_lt _ (Nat.pow_pos (by decide))
  have hs3 : ((2 ^ v * a) % 3 ^ (k + 1)) % 3 = 1 := by
    rw [Nat.mod_mod_of_dvd _ ⟨3 ^ k, h3P⟩]
    exact h3
  -- name the pieces
  generalize hm : 2 ^ v * a = m at h3 hdiv hlt hs3 ⊢
  generalize hq : m / 3 ^ (k + 1) = q at hdiv
  generalize hs : m % 3 ^ (k + 1) = s at hdiv hlt hs3 ⊢
  rw [h3P] at hdiv hlt
  -- child = 3^k * q + (s - 1) / 3
  have hchild : child a v = 3 ^ k * q + (s - 1) / 3 := by
    unfold child
    rw [hm]
    have : 3 * 3 ^ k * q = 3 * (3 ^ k * q) := Nat.mul_assoc 3 (3 ^ k) q
    rw [this] at hdiv
    omega
  rw [hchild, Nat.add_comm, Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  omega

/-! ## 2. The valuations depend only on `a mod 9` -/

theorem v0_eq_of_mod_three {a b : Nat} (h : a % 3 = b % 3) : v0 a = v0 b := by
  unfold v0
  rw [h]

theorem base_mod_nine_eq {a b : Nat} (h : a % 9 = b % 9) : base a % 9 = base b % 9 := by
  unfold base
  have h3 : a % 3 = b % 3 := by omega
  rw [v0_eq_of_mod_three h3, Nat.mul_mod, h, ← Nat.mul_mod]

theorem phase_eq_of_mod_nine {a b : Nat} (h : a % 9 = b % 9) : phase a = phase b := by
  unfold phase
  rw [base_mod_nine_eq h]

/-- The `i`-th fertile valuation is a function of `a mod 9`. -/
theorem fval_eq_of_mod_nine {a b : Nat} (h : a % 9 = b % 9) (i : Nat) : fval a i = fval b i := by
  unfold fval jidx
  rw [v0_eq_of_mod_three (a := a) (b := b) (by omega), phase_eq_of_mod_nine h]

/-- In particular `fval a i = fval (a % 81) i`. -/
theorem fval_eq_mod_81 (a i : Nat) : fval a i = fval (a % 81) i :=
  fval_eq_of_mod_nine (by rw [Nat.mod_mod_of_dvd a (⟨9, rfl⟩ : (9:Nat) ∣ 81)]) i

/-! ## 3. The class transition at level `81` -/

/-- The `i`-th fertile child of `a`, modulo `27`, is decided by `a mod 81`. -/
theorem fch_mod_27 {a : Nat} (ha : Good a) (i : Nat) :
    fch a i % 27 = ((2 ^ fval (a % 81) i * (a % 81)) % 81 - 1) / 3 := by
  have h3 := (fval_admissible ha i).1
  have h := child_mod_pow h3 3
  have e27 : (3:Nat) ^ 3 = 27 := rfl
  have e81 : (3:Nat) ^ (3 + 1) = 81 := rfl
  rw [e27, e81] at h
  have e : (2 ^ fval a i * a) % 81 = (2 ^ fval (a % 81) i * (a % 81)) % 81 := by
    rw [Nat.mul_mod, Nat.mul_mod (2 ^ fval (a % 81) i) (a % 81) 81, Nat.mod_mod,
      fval_eq_mod_81 a i]
  unfold fch
  rw [h, e]

/-- The children's residues are again prime to `3` (they are fertile), read at level `27`. -/
theorem fch_mod_27_fertile {a : Nat} (ha : Good a) (i : Nat) : fch a i % 27 % 3 ≠ 0 := by
  rw [Nat.mod_mod_of_dvd _ (⟨9, rfl⟩ : (3:Nat) ∣ 27)]
  exact (fch_good ha i).2

end ClassChild
end Collatz
