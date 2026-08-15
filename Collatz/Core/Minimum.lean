/-!
# The least element principle

Minimal-counterexample arguments need to extract a smallest witness from a
nonempty set of naturals.  Without a library this has to be proved, and it has
to be proved *classically*, because the predicate "does not reach `1`" carries
no decision procedure.

`exists_min` below is the general statement; `exists_min_pos` is the variant
used for counterexamples, where the witness is additionally required to be
positive.
-/

namespace Collatz
namespace Minimum

/-- **Least element principle.**  Any inhabited predicate on `Nat` has a least
witness. -/
theorem exists_min {P : Nat → Prop} (h : ∃ n, P n) :
    ∃ m, P m ∧ ∀ k, k < m → ¬ P k := by
  obtain ⟨n, hn⟩ := h
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hlow : ∃ k, k < n ∧ P k
    · obtain ⟨k, hk, hPk⟩ := hlow
      exact ih k hk hPk
    · exact ⟨n, hn, fun k hk hPk => hlow ⟨k, hk, hPk⟩⟩

/-- The least witness, packaged with strict minimality stated positively. -/
theorem exists_min_lt {P : Nat → Prop} (h : ∃ n, P n) :
    ∃ m, P m ∧ ∀ k, P k → m ≤ k := by
  obtain ⟨m, hm, hmin⟩ := exists_min h
  refine ⟨m, hm, fun k hk => ?_⟩
  by_cases hle : m ≤ k
  · exact hle
  · exact absurd hk (hmin k (by omega))

/-- A least witness among positive naturals. -/
theorem exists_min_pos {P : Nat → Prop} (h : ∃ n, 0 < n ∧ P n) :
    ∃ m, 0 < m ∧ P m ∧ ∀ k, 0 < k → k < m → ¬ P k := by
  obtain ⟨m, ⟨hpos, hm⟩, hmin⟩ := exists_min (P := fun n => 0 < n ∧ P n) h
  exact ⟨m, hpos, hm, fun k hk hkm hPk => hmin k hkm ⟨hk, hPk⟩⟩

/-- Strong induction packaged as a descent principle: if every counterexample
admits a strictly smaller one, there are none. -/
theorem no_counterexample_of_descent {P : Nat → Prop}
    (hdesc : ∀ n, ¬ P n → ∃ m, m < n ∧ ¬ P m) : ∀ n, P n := by
  intro n
  by_cases hn : P n
  · exact hn
  · exfalso
    obtain ⟨m, hm, hmin⟩ := exists_min (P := fun k => ¬ P k) ⟨n, hn⟩
    obtain ⟨j, hj, hjP⟩ := hdesc m hm
    exact hmin j hj hjP

/-- The positive-domain version of the descent principle, which is the form the
Collatz minimal-counterexample arguments use. -/
theorem no_pos_counterexample_of_descent {P : Nat → Prop}
    (hdesc : ∀ n, 0 < n → ¬ P n → ∃ m, 0 < m ∧ m < n ∧ ¬ P m) :
    ∀ n, 0 < n → P n := by
  intro n hn
  by_cases hP : P n
  · exact hP
  · exfalso
    obtain ⟨m, hmpos, hm, hmin⟩ :=
      exists_min_pos (P := fun k => ¬ P k) ⟨n, hn, hP⟩
    obtain ⟨j, hjpos, hj, hjP⟩ := hdesc m hmpos hm
    exact hmin j hjpos hj hjP

end Minimum
end Collatz
