import CollatzTargetDensity.SeedSupply
import Erdos1135.Tao.Syracuse.CollatzBridge
import Erdos1135.Parity

/-! Deterministic reachability and transfer to even targets. -/
namespace CollatzTargetDensity
open Erdos1135
noncomputable section

def oddReaches (target : ℕ) : Set ℕ :=
  {n | Odd n ∧ ∃ k : ℕ, (Tao.syracuse^[k]) n = target}

/-- Choose an odd predecessor prime to 3 of any target prime to 3.
    This construction also works when the target is even. -/
theorem exists_fertile_raw_child {target : ℕ} (hthree : target % 3 ≠ 0) :
    ∃ c : ℕ, Odd c ∧ c % 3 ≠ 0 ∧ Reaches c target := by
  have hbase : ∃ c v : ℕ, Odd c ∧ 3 * c + 1 = 2 ^ v * target := by
    by_cases h : target % 3 = 1
    · let c := (4 * target - 1) / 3
      have he : 3 * c + 1 = 4 * target := by dsimp [c]; omega
      exact ⟨c, 2, ⟨c / 2, by omega⟩, he⟩
    · let c := (2 * target - 1) / 3
      have he : 3 * c + 1 = 2 * target := by dsimp [c]; omega
      exact ⟨c, 1, ⟨c / 2, by omega⟩, he⟩
  have hfertile : ∃ c v : ℕ, Odd c ∧ c % 3 ≠ 0 ∧ 3 * c + 1 = 2 ^ v * target := by
    obtain ⟨c, v, hc, he⟩ := hbase
    by_cases h : c % 3 ≠ 0
    · exact ⟨c, v, hc, h, he⟩
    · refine ⟨4 * c + 1, v + 2, ⟨2 * c, by omega⟩, by omega, ?_⟩
      calc
        _ = 4 * (3 * c + 1) := by ring
        _ = 4 * (2 ^ v * target) := by rw [he]
        _ = _ := by rw [pow_add]; ring
  obtain ⟨c, v, hc, hunit, he⟩ := hfertile
  refine ⟨c, hc, hunit, v + 1, ?_⟩
  rw [Function.iterate_add_apply, Function.iterate_one,
    collatzStep_eq_three_mul_add_one_of_odd hc, he]
  exact Tao.collatz_iterate_powTwo_mul v target

def rawReaches (target : ℕ) : Set ℕ :=
  {n | 0 < n ∧ Reaches n target}

theorem oddReaches_subset_rawReaches {seed target : ℕ} (hseed : Reaches seed target) :
    oddReaches seed ⊆ rawReaches target := by
  intro n hn
  obtain ⟨hnodd, k, hk⟩ := hn
  have hreach : Reaches n seed := by
    simpa only [hk] using Tao.reaches_syracuse_iterate hnodd k
  exact ⟨hnodd.pos, hreach.trans hseed⟩

end
end CollatzTargetDensity
