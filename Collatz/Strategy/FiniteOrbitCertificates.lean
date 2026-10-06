import Collatz.Structure.AccDivergence

/-!
# Finite certificates for bounded nonconvergence

A repeated orbit value, together with avoidance of 1 on the finite prefix,
certifies bounded nonconvergence. Exiting a finite interval is a different
certificate: it proves only that the specified bound was exceeded.
-/
namespace Collatz.FiniteOrbitCertificates
open AccCycle AccDivergence

/-- Reduction modulo a period for the accelerated map. -/
theorem orbit_mod_period {n L : Nat} (h : acceleratedOrbit L n=n) (t : Nat) :
    acceleratedOrbit t n=acceleratedOrbit (t%L) n := by
  calc
    acceleratedOrbit t n=acceleratedOrbit (t%L+L*(t/L)) n := by
      rw [Nat.mod_add_div]
    _ = acceleratedOrbit (t%L) (acceleratedOrbit (L*(t/L)) n) :=
      (acceleratedOrbit_add _ _ _).symm
    _ = acceleratedOrbit (t%L) n := by rw [accOrbit_mul_period h]

/-- A repeat makes every orbit value equal to one strictly before the second
occurrence. This supplies a finite certificate for the whole infinite orbit. -/
theorem repeat_reduces {n i j : Nat} (hij : i<j)
    (he : acceleratedOrbit i n=acceleratedOrbit j n) (t : Nat) :
    ∃ s, s<j ∧ acceleratedOrbit t n=acceleratedOrbit s n := by
  by_cases ht : t<i
  · exact ⟨t, by omega, rfl⟩
  · have hp : acceleratedOrbit (j-i) (acceleratedOrbit i n)=acceleratedOrbit i n := by
      rw [acceleratedOrbit_add, Nat.sub_add_cancel (by omega)]
      exact he.symm
    refine ⟨(t-i)%(j-i)+i, ?_, ?_⟩
    · have hm := Nat.mod_lt (t-i) (by omega : 0<j-i)
      omega
    · calc
        acceleratedOrbit t n=acceleratedOrbit ((t-i)+i) n := by
          rw [Nat.sub_add_cancel (by omega : i≤t)]
        _ = acceleratedOrbit (t-i) (acceleratedOrbit i n) :=
          (acceleratedOrbit_add _ _ _).symm
        _ = acceleratedOrbit ((t-i)%(j-i)) (acceleratedOrbit i n) := orbit_mod_period hp _
        _ = acceleratedOrbit ((t-i)%(j-i)+i) n := acceleratedOrbit_add _ _ _

/-- Maximum of a finite orbit prefix, including time zero. -/
def prefixMax (n : Nat) : Nat → Nat
  | 0 => n
  | k+1 => max (prefixMax n k) (acceleratedOrbit (k+1) n)

theorem le_prefixMax (n H t : Nat) (ht : t≤H) : acceleratedOrbit t n≤prefixMax n H := by
  induction H with
  | zero =>
    have he : t=0 := by omega
    subst t
    exact Nat.le_refl _
  | succ H ih =>
    by_cases h : t≤H
    · exact Nat.le_trans (ih h) (Nat.le_max_left _ _)
    · have he : t=H+1 := by omega
      subst t
      exact Nat.le_max_right _ _

/-- Every repeat proves boundedness, without assumptions about hitting 1. -/
theorem bounded_of_repeat {n i j : Nat} (hij : i<j)
    (he : acceleratedOrbit i n=acceleratedOrbit j n) : AccBounded n := by
  refine ⟨prefixMax n j, ?_⟩
  intro t
  obtain ⟨s, hs, ht⟩ := repeat_reduces hij he t
  rw [ht]
  exact le_prefixMax n j s (by omega)

/-- Finite avoidance of 1 combined with a repeat proves nonconvergence. -/
theorem never_one_of_repeat {n i j : Nat} (hij : i<j)
    (he : acceleratedOrbit i n=acceleratedOrbit j n)
    (ha : ∀ t, t≤j → acceleratedOrbit t n≠1) :
    ¬∃ t, acceleratedOrbit t n=1 := by
  rintro ⟨t, ht⟩
  obtain ⟨s, hs, heq⟩ := repeat_reduces hij he t
  exact ha s (by omega) (heq.symm.trans ht)

/-- Executable finite-prefix avoidance test. -/
def avoidsOne (n H : Nat) : Bool :=
  (List.range (H+1)).all (fun t => decide (acceleratedOrbit t n≠1))

theorem avoidsOne_iff (n H : Nat) : avoidsOne n H=true ↔
    ∀ t, t≤H → acceleratedOrbit t n≠1 := by
  simp [avoidsOne, List.all_eq_true, Nat.lt_succ_iff]

/-- Check a supplied pair of repeat indices and avoidance of 1. -/
def repeatCheck (n i j : Nat) : Bool :=
  decide (i<j) && decide (acceleratedOrbit i n=acceleratedOrbit j n) && avoidsOne n j

theorem repeatCheck_iff (n i j : Nat) : repeatCheck n i j=true ↔
    i<j ∧ acceleratedOrbit i n=acceleratedOrbit j n ∧
    (∀ t, t≤j → acceleratedOrbit t n≠1) := by
  simp only [repeatCheck, Bool.and_eq_true, decide_eq_true_eq, avoidsOne_iff]
  exact and_assoc

/-- Soundness of a finite, executable bounded-nonconvergence certificate. -/
theorem repeatCheck_sound {n i j : Nat} (h : repeatCheck n i j=true) :
    AccBounded n ∧ ¬∃ t, acceleratedOrbit t n=1 := by
  obtain ⟨hij, he, ha⟩ := (repeatCheck_iff n i j).mp h
  exact ⟨bounded_of_repeat hij he, never_one_of_repeat hij he ha⟩

/-- Completeness for bounded nonconvergence, not for divergent counterexamples. -/
theorem repeat_certificate_iff (n : Nat) :
    (∃ i j, repeatCheck n i j=true) ↔
      AccBounded n ∧ ¬∃ t, acceleratedOrbit t n=1 := by
  constructor
  · rintro ⟨i, j, h⟩; exact repeatCheck_sound h
  · rintro ⟨⟨B, hB⟩, hn⟩
    obtain ⟨i, j, hij, he⟩ := Pigeonhole.exists_repeat_of_le hB
    exact ⟨i, j, (repeatCheck_iff n i j).mpr
      ⟨hij, he, fun t _ ht => hn ⟨t, ht⟩⟩⟩

/-- Search repeat certificates through time B+1. -/
def repeatSearch (n B : Nat) : Bool :=
  (List.range (B+2)).any (fun j => (List.range j).any (fun i => repeatCheck n i j))

theorem repeatSearch_iff (n B : Nat) : repeatSearch n B=true ↔
    ∃ j, j≤B+1 ∧ ∃ i, i<j ∧ repeatCheck n i j=true := by
  simp [repeatSearch, List.any_eq_true, Nat.lt_succ_iff]

/-- Search for a hit on 1 through time B+1. -/
def oneSearch (n B : Nat) : Bool :=
  (List.range (B+2)).any (fun t => decide (acceleratedOrbit t n=1))

theorem oneSearch_iff (n B : Nat) : oneSearch n B=true ↔
    ∃ t, t≤B+1 ∧ acceleratedOrbit t n=1 := by
  simp [oneSearch, List.any_eq_true, Nat.lt_succ_iff]

/-- Search for an exit above B through time B+1. -/
def exitSearch (n B : Nat) : Bool :=
  (List.range (B+2)).any (fun t => decide (B<acceleratedOrbit t n))

theorem exitSearch_iff (n B : Nat) : exitSearch n B=true ↔
    ∃ t, t≤B+1 ∧ B<acceleratedOrbit t n := by
  simp [exitSearch, List.any_eq_true, Nat.lt_succ_iff]

/-- Every bounded search supplies at least one of three certificates. The
alternatives are not asserted to be mutually exclusive. -/
theorem finite_search_complete (n B : Nat) :
    oneSearch n B=true ∨ exitSearch n B=true ∨ repeatSearch n B=true := by
  by_cases ho : oneSearch n B=true
  · exact Or.inl ho
  · by_cases hx : exitSearch n B=true
    · exact Or.inr (Or.inl hx)
    · have hb : ∀ t, t≤B+1 → acceleratedOrbit t n<B+1 := by
        intro t ht
        have hn : ¬B<acceleratedOrbit t n := fun h =>
          hx ((exitSearch_iff n B).mpr ⟨t, ht, h⟩)
        omega
      obtain ⟨i, j, hij, hj, he⟩ := Pigeonhole.exists_repeat hb (Nat.le_refl _)
      apply Or.inr ∘ Or.inr
      apply (repeatSearch_iff n B).mpr
      refine ⟨j, hj, i, hij, (repeatCheck_iff n i j).mpr ⟨hij, he, ?_⟩⟩
      intro t ht hone
      exact ho ((oneSearch_iff n B).mpr ⟨t, by omega, hone⟩)

/-- A successful repeat search has the same global meaning as a supplied
repeat certificate. -/
theorem repeatSearch_sound {n B : Nat} (h : repeatSearch n B=true) :
    AccBounded n ∧ ¬∃ t, acceleratedOrbit t n=1 := by
  obtain ⟨j, _, i, _, hc⟩ := (repeatSearch_iff n B).mp h
  exact repeatCheck_sound hc

/-- Requiring an exit certificate at every bound is exactly unboundedness.
This is an infinite family of checks, not a finite certificate of divergence. -/
theorem all_exits_iff_divergent (n : Nat) :
    (∀ B, exitSearch n B=true) ↔ AccDivergent n := by
  constructor
  · intro h B
    obtain ⟨t, _, ht⟩ := (exitSearch_iff n B).mp (h B)
    exact ⟨t, ht⟩
  · intro hd B
    by_cases hx : exitSearch n B=true
    · exact hx
    · have hb : ∀ t, t≤B+1 → acceleratedOrbit t n<B+1 := by
        intro t ht
        have hn : ¬B<acceleratedOrbit t n := fun h =>
          hx ((exitSearch_iff n B).mpr ⟨t, ht, h⟩)
        omega
      obtain ⟨i, j, hij, _, he⟩ := Pigeonhole.exists_repeat hb (Nat.le_refl _)
      exact False.elim ((accDivergent_iff_not_accBounded n).mp hd (bounded_of_repeat hij he))

/-- Zero is a genuine bounded nonconvergent input, outside positive Collatz. -/
theorem zero_repeat : repeatCheck 0 0 1=true := by decide

/-- Leaving an interval can occur on an orbit that later reaches 1. -/
theorem exit_is_not_nonconvergence : exitSearch 3 3=true ∧
    acceleratedOrbit 5 3=1 := by decide

/-- Repeats on the trivial cycle cannot certify nonconvergence. -/
theorem trivial_repeat_rejected : repeatCheck 1 0 2=false := by decide

end Collatz.FiniteOrbitCertificates
