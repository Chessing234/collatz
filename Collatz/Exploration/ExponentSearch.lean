import Collatz.Exploration.ThreePowerUnits

/-!
# Verified finite exponent search for inverse constructions

The arithmetic coverage theorem becomes an executable search through a known
finite ternary period. Soundness checks the returned exponent, and completeness
shows that a solution within the search interval prevents failure. A successful
result is the first exponent in that interval.

This searches a modular equation, not all Collatz trajectories. The existence
proof for a convergent member of a dyadic class remains distinct from a proof
that every member of that class converges.
-/
namespace Collatz.Exploration.ExponentSearch

open ThreePowerUnits

/-- Search a consecutive interval of exponents, starting at `start`. -/
def search (q z : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel+1, start =>
      if (2:Nat)^start%q = z%q then some start else search q z fuel (start+1)

/-- Successful search returns a valid exponent within its requested interval. -/
theorem search_sound {q z fuel start e : Nat} (h : search q z fuel start = some e) :
    start ≤ e ∧ e < start+fuel ∧ (2:Nat)^e%q = z%q := by
  induction fuel generalizing start with
  | zero => simp [search] at h
  | succ fuel ih =>
    rw [search] at h
    by_cases hm : (2:Nat)^start%q = z%q
    · rw [if_pos hm] at h
      have he : start = e := Option.some.inj h
      subst e
      exact ⟨Nat.le_refl _, by omega, hm⟩
    · rw [if_neg hm] at h
      obtain ⟨hlo, hhi, he⟩ := ih h
      exact ⟨by omega, by omega, he⟩

/-- Any matching exponent in the interval supplies a successful result no later
than that exponent. This is a completeness theorem for the finite search. -/
theorem search_complete {q z fuel start e : Nat} (hlo : start ≤ e)
    (hhi : e < start+fuel) (hm : (2:Nat)^e%q = z%q) :
    ∃ f, search q z fuel start = some f ∧ f ≤ e := by
  induction fuel generalizing start with
  | zero => omega
  | succ fuel ih =>
    by_cases hs : (2:Nat)^start%q = z%q
    · exact ⟨start, by simp [search, hs], hlo⟩
    · have hne : start ≠ e := by intro he; subst e; exact hs hm
      obtain ⟨f, hf, hfe⟩ := ih (start := start+1) (by omega) (by omega)
      exact ⟨f, by simpa [search, hs] using hf, hfe⟩

/-- Failure certifies absence of solutions throughout the whole interval. -/
theorem search_none_iff (q z fuel start : Nat) :
    search q z fuel start = none ↔
      ∀ e, start ≤ e → e < start+fuel → (2:Nat)^e%q ≠ z%q := by
  constructor
  · intro h e hlo hhi hm
    obtain ⟨f, hf, _⟩ := search_complete hlo hhi hm
    rw [h] at hf
    cases hf
  · intro h
    cases hs : search q z fuel start with
    | none => rfl
    | some e =>
      obtain ⟨hlo, hhi, hm⟩ := search_sound hs
      exact False.elim (h e hlo hhi hm)

/-- All earlier indices in a successful interval fail the modular equation. -/
theorem search_first {q z fuel start e : Nat} (h : search q z fuel start = some e) :
    ∀ f, start ≤ f → f < e → (2:Nat)^f%q ≠ z%q := by
  induction fuel generalizing start with
  | zero => simp [search] at h
  | succ fuel ih =>
    rw [search] at h
    by_cases hs : (2:Nat)^start%q = z%q
    · rw [if_pos hs] at h
      have he : start = e := Option.some.inj h
      intro f hlo hhi
      omega
    · rw [if_neg hs] at h
      intro f hlo hhi
      by_cases hf : f = start
      · subst f
        exact hs
      · exact ih h f (by omega) hhi

/-- The known complete search length, including the trivial modulus 3^0=1. -/
def periodLength (a : Nat) : Nat := if a = 0 then 1 else 2*3^(a-1)

/-- Complete executable search for a power-of-two representative of a unit. -/
def findUnitExponent (a z : Nat) : Option Nat := search (3^a) z (periodLength a) 0

/-- The period used by the algorithm is strictly positive. -/
theorem periodLength_positive (a : Nat) : 0 < periodLength a := by
  unfold periodLength
  split
  · decide
  · exact Nat.mul_pos (by decide) (Nat.pow_pos (by decide))

/-- Exponent search succeeds for every unit, or for the trivial modulus. -/
theorem findUnitExponent_success (a z : Nat) (hz : a = 0 ∨ z%3 ≠ 0) :
    ∃ e, findUnitExponent a z = some e ∧ e < periodLength a ∧
      (2:Nat)^e%3^a = z%3^a := by
  cases a with
  | zero => exact ⟨0, by simp [findUnitExponent, periodLength, search, Nat.mod_one], by decide,
      by simp [Nat.mod_one]⟩
  | succ j =>
    have hunit : z%3 ≠ 0 := hz.resolve_left (by omega)
    obtain ⟨e, he, hm⟩ := bounded_exponent j z hunit
    have hperiod : periodLength (j+1) = 2*3^j := by simp [periodLength]
    obtain ⟨f, hf, hfe⟩ := search_complete (q := 3^(j+1)) (z := z)
      (fuel := periodLength (j+1)) (start := 0) (e := e) (Nat.zero_le _)
      (by rw [hperiod]; omega) hm
    obtain ⟨_, hbound, hmod⟩ := search_sound hf
    exact ⟨f, hf, by omega, hmod⟩

/-- Every reported representative is checked even if no success premise holds. -/
theorem findUnitExponent_sound {a z e : Nat} (he : findUnitExponent a z = some e) :
    e < periodLength a ∧ (2:Nat)^e%3^a = z%3^a := by
  obtain ⟨_, hbound, hmod⟩ := search_sound he
  exact ⟨by omega, hmod⟩

end Collatz.Exploration.ExponentSearch
