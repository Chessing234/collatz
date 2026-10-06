import Collatz.Strategy.PowerStoppingTimeBarrier

/-!
# Repeating the first-descent map

Each fixed number of first-descent rounds succeeds on a density-one set.
Every individual chain nevertheless stabilizes after finitely many rounds.
The diagonal endpoint need not be 1: proving that for every positive start
would still require ruling out nontrivial never-droppers.
-/
namespace Collatz.DescentRounds
open FirstDescentDensityTransport NaturalDensity StepDensityTransport

/-- Iterate the totalized first-descent map, counting descents rather than
accelerated steps. This remains noncomputable because firstTime is classical. -/
noncomputable def rounds : Nat → Nat → Nat
  | 0, n => n
  | k+1, n => descentMap (rounds k n)

/-- Inputs without finite stopping time are fixed by the totalization. -/
theorem descentMap_eq_of_no_drop {n : Nat} (h : ¬hasFiniteStoppingTime n) :
    descentMap n=n := by
  classical
  simp only [descentMap, firstTime, dif_neg h, acceleratedOrbit_zero]

/-- The induced map never increases its input. -/
theorem descentMap_le (n : Nat) : descentMap n≤n := by
  by_cases h : hasFiniteStoppingTime n
  · exact Nat.le_of_lt ((descentMap_lt_iff n).mpr h)
  · rw [descentMap_eq_of_no_drop h]
    exact Nat.le_refl _

/-- Exactly the non-descending starts are fixed points of the induced map. -/
theorem descentMap_fixed_iff (n : Nat) : descentMap n=n ↔ ¬hasFiniteStoppingTime n := by
  constructor
  · intro he hd
    have := (descentMap_lt_iff n).mpr hd
    omega
  · exact descentMap_eq_of_no_drop

/-- Successive rounds stay on the original accelerated orbit. -/
theorem rounds_reachable (k n : Nat) : ∃ t, acceleratedOrbit t n=rounds k n := by
  induction k with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨firstTime (rounds k n)+t, ?_⟩
    rw [← acceleratedOrbit_add, ht]
    rfl

/-- Positivity is preserved through any fixed number of rounds. -/
theorem rounds_positive {n : Nat} (hn : 0<n) (k : Nat) : 0<rounds k n := by
  obtain ⟨t, ht⟩ := rounds_reachable k n
  rw [← ht]
  exact acceleratedOrbit_positive hn t

/-- Nonincrease holds at every round. -/
theorem rounds_succ_le (k n : Nat) : rounds (k+1) n≤rounds k n :=
  descentMap_le _

/-- A fixed point remains unchanged in all subsequent rounds. -/
theorem rounds_fixed {n : Nat} (h : descentMap n=n) (k : Nat) : rounds k n=n := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [rounds, ih] using h

/-- Composition law for the induced map's iteration. -/
theorem rounds_add (a b n : Nat) : rounds (a+b) n=rounds a (rounds b n) := by
  induction a with
  | zero => simp only [Nat.zero_add, rounds]
  | succ a ih =>
    rw [show a+1+b=(a+b)+1 by omega]
    simp only [rounds, ih]

/-- Every chain finds a fixed point within n rounds. This counts rounds,
not accelerated transitions, and is not an executable stopping bound. -/
theorem stabilizes (n : Nat) : ∃ k, k≤n ∧ descentMap (rounds k n)=rounds k n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : hasFiniteStoppingTime n
    · have hd := (descentMap_lt_iff n).mpr h
      obtain ⟨k, hk, hf⟩ := ih (descentMap n) hd
      refine ⟨k+1, by omega, ?_⟩
      have he : rounds (k+1) n=rounds k (descentMap n) := rounds_add k 1 n
      rw [he]
      exact hf
    · exact ⟨0, Nat.zero_le _, descentMap_eq_of_no_drop h⟩

/-- The diagonal n-round endpoint always has no further descent. -/
theorem diagonal_no_drop (n : Nat) : ¬hasFiniteStoppingTime (rounds n n) := by
  obtain ⟨k, hk, hf⟩ := stabilizes n
  have he : rounds n n=rounds k n := by
    calc
      rounds n n = rounds ((n-k)+k) n := congrArg (fun j => rounds j n) (by omega)
      _ = rounds (n-k) (rounds k n) := rounds_add _ _ _
      _ = rounds k n := rounds_fixed hf _
  rw [he]
  exact (descentMap_fixed_iff _).mp hf

/-- Every fixed number of rounds preserves density one under preimage. -/
theorem density_one_rounds {P : Nat → Prop} (hP : DensityOne P) (k : Nat) :
    DensityOne (fun n => P (rounds k n)) := by
  induction k with
  | zero => exact hP
  | succ k ih =>
    -- Pull the fixed-round property back through one more descent.
    have he (n : Nat) : rounds (k+1) n=rounds k (descentMap n) := by
      exact rounds_add k 1 n
    have ht := density_one_descentMap ih
    exact densityOne_mono (fun n h => by simpa only [he] using h) ht

/-- There are arbitrarily many consecutive first descents at density one,
when the number of requested rounds is fixed before taking density. -/
theorem density_one_descending_round (k : Nat) :
    DensityOne (fun n => hasFiniteStoppingTime (rounds k n)) :=
  density_one_rounds StoppingNaturalDensity.finite_stopping_time_density_one k

/-- All of the first K rounds strictly descend, with K chosen in advance. -/
def DropsThrough (K n : Nat) : Prop :=
  ∀ k, k<K → hasFiniteStoppingTime (rounds k n)

/-- Finite intersection makes the consecutive-round interpretation explicit. -/
theorem density_one_dropsThrough (K : Nat) : DensityOne (DropsThrough K) := by
  induction K with
  | zero =>
    apply densityOne_mono (P := hasFiniteStoppingTime) _
      StoppingNaturalDensity.finite_stopping_time_density_one
    intro n _ k hk
    omega
  | succ K ih =>
    apply densityOne_mono (P := fun n => DropsThrough K n ∧
      hasFiniteStoppingTime (rounds K n)) _
      (density_one_and ih (density_one_descending_round K))
    intro n hn k hk
    by_cases hl : k<K
    · exact hn.1 k hl
    · have he : k=K := by omega
      simpa only [he] using hn.2

/-- No uniform-in-round density statement can justify diagonal substitution:
the diagonal endpoint lies in the exceptional set on every input. -/
theorem fixed_rounds_vs_diagonal :
    (∀ k, DensityOne (fun n => hasFiniteStoppingTime (rounds k n))) ∧
    (∀ n, ¬hasFiniteStoppingTime (rounds n n)) :=
  ⟨density_one_descending_round, diagonal_no_drop⟩

/-- Even repeated first descents cannot shrink faster than a factor two per
round. This is independent of the number of accelerated transitions used. -/
theorem rounds_halving_lower (k n : Nat) : n≤2^k*rounds k n := by
  induction k with
  | zero => simp only [rounds, Nat.pow_zero, Nat.one_mul]; exact Nat.le_refl _
  | succ k ih =>
    have hm := Nat.mul_le_mul_left (2^k) (descentMap_half_bound (rounds k n))
    have ht := Nat.le_trans ih hm
    simpa only [rounds, Nat.pow_succ, Nat.mul_assoc] using ht

/-- A lower bound for the orbit after the first descent is already a lower
bound for the whole orbit: the omitted prefix stays above the starting value. -/
theorem orbit_lower_bound_back {b n : Nat}
    (hb : ∀ t, b≤acceleratedOrbit t (descentMap n)) :
    ∀ t, b≤acceleratedOrbit t n := by
  by_cases hd : hasFiniteStoppingTime n
  · intro t
    have hs := firstTime_spec hd
    by_cases ht : t<firstTime n
    · have hb0 := hb 0
      have hp := hs.2 t ht
      have hm := descentMap_le n
      simp only [acceleratedOrbit_zero] at hb0
      omega
    · have h := hb (t-firstTime n)
      change b≤acceleratedOrbit (t-firstTime n) (acceleratedOrbit (firstTime n) n) at h
      rw [acceleratedOrbit_add] at h
      have he : t-firstTime n+firstTime n=t := by omega
      simpa only [he] using h
  · simpa only [descentMap_eq_of_no_drop hd] using hb

/-- Pull orbit lower bounds back across any finite number of first descents. -/
theorem rounds_lower_bound_back {b n : Nat} (k : Nat)
    (hb : ∀ t, b≤acceleratedOrbit t (rounds k n)) :
    ∀ t, b≤acceleratedOrbit t n := by
  induction k generalizing n with
  | zero => exact hb
  | succ k ih =>
    have he : rounds (k+1) n=rounds k (descentMap n) := rounds_add k 1 n
    rw [he] at hb
    exact orbit_lower_bound_back (ih hb)

/-- The endpoint obtained after n descent rounds. It is defined even if the
original accelerated orbit diverges, but is not an executable algorithm. -/
noncomputable def orbitMinimum (n : Nat) : Nat := rounds n n

/-- The endpoint is attained on the actual orbit. -/
theorem orbitMinimum_attained (n : Nat) :
    ∃ t, acceleratedOrbit t n=orbitMinimum n := rounds_reachable n n

/-- The endpoint is below every original orbit value, including the prefix. -/
theorem orbitMinimum_le (n t : Nat) : orbitMinimum n≤acceleratedOrbit t n := by
  apply rounds_lower_bound_back n
  intro j
  have h := diagonal_no_drop n
  have he := StoppingNaturalDensity.eventuallyDrops_iff_hasFiniteStoppingTime (rounds n n)
  by_cases hl : acceleratedOrbit j (rounds n n)<rounds n n
  · exact False.elim (h (he.mp ⟨j, hl⟩))
  · change rounds n n≤acceleratedOrbit j (rounds n n)
    omega

/-- For positive inputs, identifying this minimum with 1 is exactly the
convergence problem. Stabilization of the descent map alone does not solve it. -/
theorem orbitMinimum_eq_one_iff {n : Nat} (hn : 0<n) :
    orbitMinimum n=1 ↔ ∃ t, acceleratedOrbit t n=1 := by
  constructor
  · intro he
    obtain ⟨t, ht⟩ := orbitMinimum_attained n
    exact ⟨t, ht.trans he⟩
  · rintro ⟨t, ht⟩
    have hlo := rounds_positive hn n
    have hhi := orbitMinimum_le n t
    change 0<orbitMinimum n at hlo
    rw [ht] at hhi
    omega

/-- Reapplying the minimum operation cannot change its result. -/
theorem orbitMinimum_idempotent (n : Nat) :
    orbitMinimum (orbitMinimum n)=orbitMinimum n := by
  apply rounds_fixed
  exact (descentMap_fixed_iff _).mpr (diagonal_no_drop n)

end Collatz.DescentRounds
