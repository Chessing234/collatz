import Collatz.Structure.PeriodicCounting
import Collatz.Core.Sum

/-! Translation invariance of one-period counts and predicate inclusion.
These finite identities let residue estimates apply to a shifted interval. -/
namespace Collatz.PeriodicCounting

/-- Counting a predicate after a cutoff gives an exact interval decomposition. -/
theorem count_add_shift (P : Nat → Bool) (s N : Nat) :
    countBelow P (s+N) = countBelow P s + countBelow (fun n => P (s+n)) N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.add_succ, count_succ, ih, count_succ]
    omega

/-- Every interval of a full period has the same count. -/
theorem count_shift_period (P : Nat → Bool) (M s : Nat)
    (hp : ∀ n, P (n+M)=P n) :
    countBelow (fun n => P (s+n)) M = countBelow P M := by
  have h1 := count_add_shift P s M
  have h2 := count_add_period P M s hp
  rw [Nat.add_comm M s] at h2
  omega

/-- Pointwise inclusion implies inclusion of finite counts. -/
theorem count_le_of_imp (P Q : Nat → Bool) (N : Nat)
    (h : ∀ n, P n=true → Q n=true) : countBelow P N ≤ countBelow Q N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [count_succ, count_succ]
    have hb : (if P N then 1 else 0) ≤ (if Q N then 1 else 0) := by
      cases hp : P N <;> cases hq : Q N <;> simp_all
    exact Nat.add_le_add ih hb

/-- Compatibility with the repository's sum-of-indicators counting interface. -/
theorem count_eq_countRange (P : Nat → Bool) (N : Nat) :
    countBelow P N = Sum.countRange N P := by
  induction N with
  | zero => rfl
  | succ N ih => rw [count_succ, Sum.countRange_succ, ih]

end Collatz.PeriodicCounting
