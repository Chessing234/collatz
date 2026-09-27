import Mathlib.Logic.Function.Iterate
import Lean.Elab.Tactic.Omega

/-!+# Nonperiodic seed selection

Elementary deterministic dynamics used by the proposed all-target extension.
No Collatz convergence hypothesis occurs in these statements.
-/

namespace CollatzTargetDensity

def Nonperiodic {α : Type*} (f : α → α) (x : α) : Prop :=
  ∀ k : ℕ, 0 < k → (f^[k]) x ≠ x

theorem periodic_multiples {α : Type*} {f : α → α} {x : α} {p : ℕ}
    (hp : (f^[p]) x = x) (q : ℕ) : (f^[q * p]) x = x := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.succ_mul, Function.iterate_add_apply, hp, ih]

/-- The restriction of any function to its periodic points is injective. -/
theorem periodic_predecessors_eq {α : Type*} {f : α → α} {x y : α}
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpx : (f^[p]) x = x) (hqy : (f^[q]) y = y)
    (hxy : f x = f y) : x = y := by
  have hprod : 0 < q * p := Nat.mul_pos hq hp
  have hx := periodic_multiples hpx q
  have hy : (f^[q * p]) y = y := by
    simpa only [Nat.mul_comm] using periodic_multiples hqy p
  have he : q * p = (q * p - 1) + 1 := by omega
  have hiter : (f^[q * p]) x = (f^[q * p]) y := by
    rw [he, Function.iterate_add_apply, Function.iterate_add_apply]
    simp only [Function.iterate_one, hxy]
  exact hx.symm.trans (hiter.trans hy)

/-- Two distinct immediate predecessors provide a nonperiodic choice. -/
theorem nonperiodic_choice {α : Type*} {f : α → α} {x y : α}
    (hne : x ≠ y) (hxy : f x = f y) : Nonperiodic f x ∨ Nonperiodic f y := by
  classical
  by_cases hx : Nonperiodic f x
  · exact Or.inl hx
  · right
    obtain ⟨p, hp, hpx⟩ : ∃ p, ∃ _ : 0 < p, (f^[p]) x = x := by
      simpa only [Nonperiodic, not_forall, not_not] using hx
    intro q hq hqy
    exact hne (periodic_predecessors_eq hp hq hpx hqy hxy)

/-- Repeated hits would make the target itself periodic. -/
theorem nonperiodic_hit_time_unique {α : Type*} {f : α → α} {source target : α}
    (ht : Nonperiodic f target) {d e : ℕ}
    (hd : (f^[d]) source = target) (he : (f^[e]) source = target) : d = e := by
  have hnot (a b : ℕ) (ha : (f^[a]) source = target)
      (hb : (f^[b]) source = target) (hab : a < b) : False := by
    have hsplit : b = (b - a) + a := by omega
    rw [hsplit, Function.iterate_add_apply, ha] at hb
    exact ht (b - a) (by omega) hb
  by_cases hde : d < e
  · exact False.elim (hnot d e hd he hde)
  · by_cases hed : e < d
    · exact False.elim (hnot e d he hd hed)
    · omega

/-- A residue-wise supply of two distinct children is enough; neither child's
    eventual convergence is required. The predicate records residue and size. -/
theorem select_nonperiodic_child {α : Type*} {f : α → α} (target : α)
    (P : α → Prop)
    (hchildren : ∃ x y, P x ∧ P y ∧ f x = target ∧ f y = target ∧ x ≠ y) :
    ∃ x, P x ∧ f x = target ∧ Nonperiodic f x := by
  obtain ⟨x, y, hx, hy, hfx, hfy, hne⟩ := hchildren
  rcases nonperiodic_choice hne (hfx.trans hfy.symm) with h | h
  · exact ⟨x, hx, hfx, h⟩
  · exact ⟨y, hy, hfy, h⟩

end CollatzTargetDensity
