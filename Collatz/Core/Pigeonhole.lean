/-!
# A pigeonhole principle

To split "does not reach `1`" into "diverges" versus "falls into a cycle" one
needs the fact that a bounded orbit must repeat a value.  That is a pigeonhole
statement, and since this project imports no library it is proved here.

The statement proved is the sharp one:

> if `f i < B` for all `i ≤ N` and `B ≤ N`, then two distinct indices `i < j`
> in `[0, N]` satisfy `f i = f j`.

The proof is by induction on the number of available values `B`.  The inductive
step removes the unique index (if any) carrying the top value `B`, reindexing
through the strictly monotone map `k ↦ if k < i₀ then k else k + 1`.
-/

namespace Collatz
namespace Pigeonhole

/-- The reindexing map that skips over the index `i₀`. -/
def skip (i₀ k : Nat) : Nat := if k < i₀ then k else k + 1

/-- The skip map never hits the omitted index. -/
theorem skip_ne (i₀ k : Nat) : skip i₀ k ≠ i₀ := by
  rw [skip]
  by_cases h : k < i₀
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

/-- The skip map is strictly monotone. -/
theorem skip_lt_skip {i₀ a b : Nat} (h : a < b) : skip i₀ a < skip i₀ b := by
  rw [skip, skip]
  by_cases ha : a < i₀ <;> by_cases hb : b < i₀
  · rw [if_pos ha, if_pos hb]; omega
  · rw [if_pos ha, if_neg hb]; omega
  · rw [if_neg ha, if_pos hb]; omega
  · rw [if_neg ha, if_neg hb]; omega

/-- The skip map stays inside the interval when the omitted index does. -/
theorem skip_le {i₀ k N : Nat} (hk : k + 1 ≤ N) : skip i₀ k ≤ N := by
  rw [skip]
  by_cases h : k < i₀
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

/-- **Pigeonhole.**  A function taking fewer than `B` values on `B ≤ N` or more
indices must repeat. -/
theorem exists_repeat {f : Nat → Nat} {B N : Nat}
    (hval : ∀ i, i ≤ N → f i < B) (hBN : B ≤ N) :
    ∃ i j : Nat, i < j ∧ j ≤ N ∧ f i = f j := by
  induction B generalizing f N with
  | zero =>
    exact absurd (hval 0 (by omega)) (by omega)
  | succ B ih =>
    by_cases htop : ∃ i, i ≤ N ∧ f i = B
    · obtain ⟨i₀, hi₀N, hi₀⟩ := htop
      by_cases hsecond : ∃ j, j ≤ N ∧ j ≠ i₀ ∧ f j = B
      · -- two indices carry the top value
        obtain ⟨j₀, hj₀N, hj₀ne, hj₀⟩ := hsecond
        by_cases hlt : i₀ < j₀
        · exact ⟨i₀, j₀, hlt, hj₀N, by rw [hi₀, hj₀]⟩
        · exact ⟨j₀, i₀, by omega, hi₀N, by rw [hi₀, hj₀]⟩
      · -- exactly one index carries the top value: delete it and recurse
        have hother : ∀ j, j ≤ N → j ≠ i₀ → f j < B := by
          intro j hjN hjne
          have h1 : f j < B + 1 := hval j hjN
          have h2 : f j ≠ B := by
            intro heq
            exact hsecond ⟨j, hjN, hjne, heq⟩
          omega
        have hval' : ∀ k, k ≤ N - 1 → f (skip i₀ k) < B := by
          intro k hk
          have hkN : skip i₀ k ≤ N := skip_le (by omega)
          exact hother _ hkN (skip_ne i₀ k)
        obtain ⟨i, j, hij, hjN, hfij⟩ := ih hval' (by omega)
        refine ⟨skip i₀ i, skip i₀ j, skip_lt_skip hij, ?_, hfij⟩
        exact skip_le (by omega)
    · -- the top value is never attained, so `B` values suffice
      have hval' : ∀ i, i ≤ N → f i < B := by
        intro i hi
        have h1 : f i < B + 1 := hval i hi
        have h2 : f i ≠ B := by
          intro heq
          exact htop ⟨i, hi, heq⟩
        omega
      exact ih hval' (by omega)

/-- A bounded function repeats a value: the form used by the orbit dichotomy. -/
theorem exists_repeat_of_le {f : Nat → Nat} {B : Nat}
    (hval : ∀ i, f i ≤ B) : ∃ i j : Nat, i < j ∧ f i = f j := by
  obtain ⟨i, j, hij, _, hf⟩ :=
    exists_repeat (f := f) (B := B + 1) (N := B + 1)
      (fun i _ => Nat.lt_succ_of_le (hval i)) (Nat.le_refl _)
  exact ⟨i, j, hij, hf⟩

end Pigeonhole
end Collatz
