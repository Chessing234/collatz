import Collatz.Basic

/-!
The cycle-descent argument, including the exact hypothesis needed to turn it
into a proof of Collatz. All statements use the standard 3n+1 map.
-/
namespace Collatz.CycleDescentBridge

/-- Starting later in a closed orbit, follow its remaining steps back. -/
theorem returns_to_base {m L i : Nat}
    (hcycle : orbit L m = m) (hi : i ≤ L) :
    orbit (L-i) (orbit i m) = m := by
  rw [← orbit_add, Nat.sub_add_cancel hi, hcycle]

/-- Every member above a chosen lower member of its cycle eventually descends.
In particular, choose the lower member to be the cycle minimum. -/
theorem higher_cycle_member_descends {m L i : Nat}
    (hcycle : orbit L m = m) (hi : i ≤ L) (hhigher : m < orbit i m) :
    ∃ j, 0 < j ∧ orbit j (orbit i m) < orbit i m := by
  have hr := returns_to_base hcycle hi
  have hj : 0 < L-i := by
    by_cases hz : L-i = 0
    · rw [hz, orbit_zero_steps] at hr
      omega
    · omega
  exact ⟨L-i, hj, by rw [hr]; exact hhigher⟩

/-- A minimum on one full period remains a minimum for all future time. -/
theorem cycle_minimum_never_descends {m L : Nat}
    (hL : 0 < L) (hcycle : orbit L m = m)
    (hmin : ∀ i, i < L → m ≤ orbit i m) :
    ∀ k, m ≤ orbit k m := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    by_cases hk : k < L
    · exact hmin k hk
    · have hle : L ≤ k := by omega
      have hsmall : k-L < k := by omega
      have hr := ih (k-L) hsmall
      have he : orbit k m = orbit (k-L) m := by
        calc
          orbit k m = orbit ((k-L)+L) m := by rw [Nat.sub_add_cancel hle]
          _ = orbit (k-L) (orbit L m) := orbit_add _ _ _
          _ = orbit (k-L) m := by rw [hcycle]
      rw [he]
      exact hr

/-- This is the universal descent hypothesis, not an established fact. -/
def UniversalDescent : Prop :=
  ∀ n : Nat, 1 < n → ∃ k, orbit k n < n

/-- The proposed induction works if universal descent is supplied. -/
theorem collatz_of_universal_descent (hd : UniversalDescent) : CollatzConjecture := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    by_cases h1 : n = 1
    · exact ⟨0, by simp [h1]⟩
    · obtain ⟨k, hk⟩ := hd n (by omega)
      obtain ⟨j, hj⟩ := ih (orbit k n) hk (orbit_positive hn k)
      exact ⟨j+k, by rw [orbit_add, hj]⟩

/-- Universal descent is exactly equivalent to Collatz. -/
theorem universal_descent_iff_collatz : UniversalDescent ↔ CollatzConjecture := by
  constructor
  · exact collatz_of_universal_descent
  · intro hc n hn
    obtain ⟨k, hk⟩ := hc n (by omega)
    exact ⟨k, by rw [hk]; exact hn⟩

/-- The cycle minimum can be forced to 1 only after supplying the missing
universal descent hypothesis (or a separate result sufficient for minima). -/
theorem cycle_minimum_eq_one_of_descent {m L : Nat}
    (hm : 0 < m) (hL : 0 < L) (hcycle : orbit L m = m)
    (hmin : ∀ i, i < L → m ≤ orbit i m) (hd : UniversalDescent) : m = 1 := by
  have hnever := cycle_minimum_never_descends hL hcycle hmin
  by_cases h1 : m = 1
  · exact h1
  · obtain ⟨k, hk⟩ := hd m (by omega)
    have := hnever k
    omega

end Collatz.CycleDescentBridge
