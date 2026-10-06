import Collatz.Research.StoppingAtlas.Events

/-! A period-composition-sensitive finite error bound. This elementary bound
improves the generic M² estimate to A(M-A), where A is the success count. -/
namespace Collatz.Research.StoppingAtlas
open PeriodicCounting

/-- Increasing a counting window adds at most one success per added input. -/
theorem count_increment_bound (P : Nat → Bool) {r M : Nat} (hr : r ≤ M) :
    countBelow P M ≤ countBelow P r + (M - r) := by
  induction M with
  | zero => have he : r = 0 := by omega
            subst r
            simp
  | succ M ih =>
    by_cases hm : r ≤ M
    · have := ih hm
      rw [count_succ]
      split <;> omega
    · have he : r = M + 1 := by omega
      subst r
      omega

/-- Finite binary prefixes obey a composition-sensitive upper discrepancy bound. -/
theorem prefix_error_upper {M A r R : Nat} (hA : A ≤ M) (hRr : R ≤ r)
    (hRA : R ≤ A) : M * R ≤ A * r + A * (M - A) := by
  have he : M = A + (M - A) := by omega
  by_cases hr : r ≤ A
  · calc
      M * R ≤ M * r := Nat.mul_le_mul_left M hRr
      _ = A * r + (M - A) * r := by calc
        M * r = (A + (M - A)) * r := congrArg (fun x => x * r) he
        _ = _ := Nat.add_mul _ _ _
      _ ≤ A * r + A * (M - A) := by
        have := Nat.mul_le_mul_left (M - A) hr
        simpa only [Nat.mul_comm] using Nat.add_le_add_left this (A * r)
  · have har : A ≤ r := by omega
    calc
      M * R ≤ M * A := Nat.mul_le_mul_left M hRA
      _ = A * A + A * (M - A) := by calc
        M * A = (A + (M - A)) * A := congrArg (fun x => x * A) he
        _ = _ := by rw [Nat.add_mul, Nat.mul_comm (M - A) A]
      _ ≤ A * r + A * (M - A) := Nat.add_le_add_right (Nat.mul_le_mul_left A har) _

/-- The complementary prefix constraint supplies the other error direction. -/
theorem prefix_error_lower {M A r R : Nat} (hA : A ≤ M)
    (hcomp : r + A ≤ M + R) : A * r ≤ M * R + A * (M - A) := by
  have hr : r ≤ R + (M - A) := by omega
  calc
    A * r ≤ A * (R + (M - A)) := Nat.mul_le_mul_left A hr
    _ = A * R + A * (M - A) := Nat.mul_add _ _ _
    _ ≤ M * R + A * (M - A) := Nat.add_le_add_right (Nat.mul_le_mul_right R hA) _

/-- Uniform discrepancy using only the number of successful residues in a period. -/
theorem composition_error (P : Nat → Bool) (M N : Nat) (hM : 0 < M)
    (hp : ∀ n, P (n + M) = P n) :
    M * countBelow P N ≤ N * countBelow P M + countBelow P M * (M - countBelow P M) ∧
    N * countBelow P M ≤ M * countBelow P N + countBelow P M * (M - countBelow P M) := by
  let A := countBelow P M
  let R := countBelow P (N % M)
  let r := N % M
  let q := N / M
  have hA : A ≤ M := count_le P M
  have hr : r ≤ M := Nat.le_of_lt (Nat.mod_lt N hM)
  have hRr : R ≤ r := count_le P r
  have hRA : R ≤ A := count_mono P hr
  have hinc : A ≤ R + (M - r) := count_increment_bound P hr
  have hu := prefix_error_upper hA hRr hRA
  have hl := prefix_error_lower hA (show r + A ≤ M + R by omega)
  have hc : countBelow P N = q * A + R := count_div_mod P M N hp
  have hn : N = q * M + r := by
    have := Nat.mod_add_div N M
    simpa only [Nat.mul_comm, Nat.add_comm] using this.symm
  change M * countBelow P N ≤ N * A + A * (M - A) ∧
    N * A ≤ M * countBelow P N + A * (M - A)
  rw [hc, hn]
  constructor
  · simpa only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm, Nat.add_assoc] using Nat.add_le_add_left hu (q * M * A)
  · simpa only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm, Nat.add_assoc] using Nat.add_le_add_left hl (q * M * A)

/-- Apply the sharper bound to exact coefficient-crossing times. -/
theorem firstEvent_composition_error (k N : Nat) :
    let A := countBelow (firstEventB k) (2 ^ k)
    (2 ^ k) * countBelow (firstEventB k) N ≤ N * A + A * (2 ^ k - A) ∧
    N * A ≤ (2 ^ k) * countBelow (firstEventB k) N + A * (2 ^ k - A) :=
  composition_error _ _ _ (Nat.two_pow_pos k) (firstEvent_period k)

end Collatz.Research.StoppingAtlas
