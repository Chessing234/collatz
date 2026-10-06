import Collatz.Structure.StoppingNaturalDensity
import Collatz.Structure.PositiveCounting

/-! The diagonal bounded stopping-time count inherits the actual-orbit bounds. -/
namespace Collatz.StoppingNaturalDensity
open NaturalDensity

/-- Exact bounded-witness interpretation of the existing Boolean checker. -/
theorem hasStoppingTimeBy_iff_bounded (n H : Nat) :
    hasStoppingTimeBy n H=true ↔
      ∃ k, 1≤k ∧ k≤H ∧ acceleratedOrbit k n<n := by
  induction H with
  | zero =>
    simp only [hasStoppingTimeBy, Bool.false_eq_true, false_iff]
    rintro ⟨k, hk, hzero, _⟩
    omega
  | succ H ih =>
    rw [hasStoppingTimeBy, Bool.or_eq_true, decide_eq_true_eq, ih]
    constructor
    · rintro (⟨k, hk, hH, hd⟩ | hd)
      · exact ⟨k, hk, by omega, hd⟩
      · exact ⟨H+1, by omega, Nat.le_refl _, hd⟩
    · rintro ⟨k, hk, hH, hd⟩
      by_cases hb : k≤H
      · exact Or.inl ⟨k, hk, hb, hd⟩
      · have he : k=H+1 := by omega
        exact Or.inr (by simpa only [he] using hd)

/-- The Boolean checker succeeds exactly outside the no-descent window. -/
theorem bounded_iff_not_noDrop (n H : Nat) :
    hasStoppingTimeBy n H=true ↔ ¬ NoDropThrough H n := by
  rw [hasStoppingTimeBy_iff_bounded]
  constructor
  · rintro ⟨k, _, hk, hd⟩ h
    have := h k hk
    omega
  · intro h
    classical
    by_cases hex : ∃ k, 1≤k ∧ k≤H ∧ acceleratedOrbit k n<n
    · exact hex
    · apply False.elim
      apply h
      intro k hk
      by_cases hd : acceleratedOrbit k n<n
      · have hpos : 1≤k := by
          cases k with
          | zero => simp only [acceleratedOrbit_zero] at hd; omega
          | succ k => omega
        exact False.elim (hex ⟨k, hpos, hk, hd⟩)
      · omega

/-- A zero start never passes the bounded stopping test. -/
theorem zero_not_bounded (H : Nat) : ¬ hasStoppingTimeBy 0 H=true := by
  rw [hasStoppingTimeBy_iff_bounded]
  rintro ⟨k, _, _, hd⟩
  omega

/-- The full counting cutoff can serve as the stopping horizon. -/
theorem diagonal_integer_precision (q N : Nat) (hq : 0<q)
    (hlarge : (2*q)*((160*q)*3^(160*q)+1+2^(160*q))≤N)
    (horizon : 160*q≤N) :
    (q-1)*N ≤ q*countUpTo (fun n => hasStoppingTimeBy n N=true) N := by
  have hbad := noDrop_precision q N hq hlarge
  have hparts := predicateCount_complement (NoDropThrough (160*q)) N
  have hgood := predicateCount_mono
    (P := fun n => ¬ NoDropThrough (160*q) n)
    (Q := fun n => hasStoppingTimeBy n N=true) (by
      intro n h
      exact hasStoppingTimeBy_monotone ((bounded_iff_not_noDrop n (160*q)).mpr h) horizon) N
  have hpos := predicateCount_le_countUpTo (fun n => hasStoppingTimeBy n N=true)
    (zero_not_bounded N) N
  have hsum : N≤predicateCount (NoDropThrough (160*q)) N+
      countUpTo (fun n => hasStoppingTimeBy n N=true) N := by omega
  have hs := Nat.mul_le_mul_left q hsum
  rw [Nat.mul_add] at hs
  have he : q*N=(q-1)*N+N := by
    have hq' : q=q-1+1 := by omega
    calc q*N=(q-1+1)*N := congrArg (fun x => x*N) hq'
         _ = (q-1)*N+N := by rw [Nat.add_mul, Nat.one_mul]
  omega

end Collatz.StoppingNaturalDensity
