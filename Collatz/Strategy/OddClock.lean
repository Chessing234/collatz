import Collatz.Strategy.GapBarriers
import Collatz.Strategy.Paradoxical

/-!
# The odd clock and the Terras clock, reconciled

`Collatz.Strategy.Paradoxical` states Rozier–Terracol's Definition 1.1 on the
Terras clock: `j` total halving steps, `q = oddCount n j` of them triplings.
`Collatz.Strategy.GapBarriers` works on the odd-to-odd clock: `L` steps with
valuations `k i` summing to `K_L`.

`Collatz.Strategy.GapBarriers.traj_acceleratedOrbit` already matches the
*states*.  This file matches the *counters*: over the `K_L` Terras steps that an
`L`-step odd trajectory occupies, exactly `L` are triplings
(`traj_oddCount`).  Hence at an odd-step boundary the paradoxical conditions of
the two formalisms coincide (`paradoxical_iff_oddClock`), which is the precise
content of Remark 5.1 of the paper — restricting to sequences that start and end
at odd integers gives the same set of paradoxical sequences.

Lean 4.33.0-rc1.  No Mathlib, no `sorry`, no `axiom`.
-/

namespace Collatz
namespace OddClock

open Arith GapBarriers

/-! ## Where the Terras orbit sits inside one odd step -/

/-- Stripping `i ≤ a` factors of two takes exactly `i` Terras steps. -/
theorem acceleratedOrbit_two_pow_mul_le : ∀ i a m : Nat, i ≤ a →
    acceleratedOrbit i (2 ^ a * m) = 2 ^ (a - i) * m := by
  intro i
  induction i with
  | zero => intro a m _; simp
  | succ i ih =>
    intro a m hle
    obtain ⟨b, hb⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    subst hb
    have heven : (2 ^ (b + 1) * m) % 2 = 0 := by
      have h : 2 ^ (b + 1) * m = 2 * (2 ^ b * m) := by
        rw [two_pow_succ, Nat.mul_assoc]
      omega
    have hstep : acceleratedStep (2 ^ (b + 1) * m) = 2 ^ b * m := by
      rw [acceleratedStep, if_pos heven, two_pow_succ, Nat.mul_assoc]
      omega
    rw [show b + 1 - (i + 1) = b - i by omega, acceleratedOrbit_succ, hstep]
    exact ih b m (by omega)

/-- The Terras iterates strictly inside one odd step are even. -/
theorem oddStep_orbit {n k m : Nat} (hn : n % 2 = 1) (h : OddStep n k m) :
    ∀ i : Nat, 1 ≤ i → i ≤ k → acceleratedOrbit i n = 2 ^ (k - i) * m := by
  obtain ⟨hk, _, heq⟩ := h
  intro i h1 h2
  obtain ⟨j, hj⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  obtain ⟨c, hc⟩ : ∃ c, k = c + 1 := ⟨k - 1, by omega⟩
  subst hj; subst hc
  have hstep : acceleratedStep n = 2 ^ c * m := by
    rw [acceleratedStep, if_neg (by omega)]
    rw [two_pow_succ, Nat.mul_assoc] at heq
    omega
  rw [show c + 1 - (j + 1) = c - j by omega, acceleratedOrbit_succ, hstep]
  exact acceleratedOrbit_two_pow_mul_le j c m (by omega)

/-! ## The tripling count -/

/-- `oddCount` splits along the orbit. -/
theorem oddCount_add (x a : Nat) : ∀ b : Nat,
    oddCount x (a + b) = oddCount x a + oddCount (acceleratedOrbit a x) b := by
  intro b
  induction b with
  | zero => simp [oddCount, parityVector]
  | succ b ih =>
    have hlast := Density.oddCount_succ_last x (a + b)
    have hlast' := Density.oddCount_succ_last (acceleratedOrbit a x) b
    have hshift : acceleratedOrbit b (acceleratedOrbit a x) = acceleratedOrbit (a + b) x := by
      rw [acceleratedOrbit_add, Nat.add_comm]
    rw [show a + (b + 1) = (a + b) + 1 by omega, hlast, hlast', hshift, ih]
    omega

/-- **One odd step contributes exactly one tripling.** -/
theorem oddStep_oddCount {n k m : Nat} (hn : n % 2 = 1) (h : OddStep n k m) :
    oddCount n k = 1 := by
  have hk : 1 ≤ k := h.1
  have horb := oddStep_orbit hn h
  have key : ∀ j : Nat, 1 ≤ j → j ≤ k → oddCount n j = 1 := by
    intro j
    induction j with
    | zero => intro h1 _; omega
    | succ j ih =>
      intro _ h2
      have hlast := Density.oddCount_succ_last n j
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj
        simp [oddCount, parityVector, hn]
      · have hprev := ih (by omega) (by omega)
        have hev : acceleratedOrbit j n = 2 ^ (k - j) * m := horb j (by omega) (by omega)
        have hpos : 0 < k - j := by omega
        obtain ⟨c, hc⟩ : ∃ c, k - j = c + 1 := ⟨k - j - 1, by omega⟩
        rw [hc] at hev
        have : 2 ^ (c + 1) * m = 2 * (2 ^ c * m) := by
          rw [two_pow_succ, Nat.mul_assoc]
        omega
  exact key k hk (Nat.le_refl _)

/-- **The counters match.**  An `L`-step odd trajectory occupies `K_L` Terras
steps, of which exactly `L` are triplings. -/
theorem traj_oddCount {n k : Nat → Nat} : ∀ L : Nat, Traj n k L → n 0 % 2 = 1 →
    oddCount (n 0) (Ksum k L) = L := by
  intro L
  induction L with
  | zero => intro _ _; simp [oddCount, parityVector]
  | succ L ih =>
    intro htraj hodd
    have hIH := ih (htraj.le (by omega)) hodd
    have hstep := htraj L (by omega)
    have hoddL : n L % 2 = 1 := by
      rcases Nat.eq_zero_or_pos L with hL | hL
      · rw [hL]; exact hodd
      · obtain ⟨M, hM⟩ : ∃ M, L = M + 1 := ⟨L - 1, by omega⟩
        have h := htraj M (by omega)
        rw [← hM] at h
        exact h.2.1
    have hstate := traj_acceleratedOrbit L (htraj.le (by omega)) hodd
    rw [Ksum_succ, oddCount_add, hIH, hstate, oddStep_oddCount hoddL hstep]

/-- Cross-check on the leading Rozier-Terracol example.  The odd trajectory
`7 → 11 → 17 → 13 → 5 → 1` has `L = 5` steps with valuations `1,1,2,3,4`, total
`K = 11`; `traj_oddCount` predicts `oddCount 7 11 = 5`, and it does.  (Note
`Paradoxical.trace_seven` reads the same orbit at `j = 8`, where the tripling
count is also `5` — the last three Terras steps `8 → 4 → 2 → 1` are halvings.) -/
theorem oddCount_seven : oddCount 7 11 = 5 := by decide

theorem oddCount_seven_eight : oddCount 7 8 = 5 := by decide

/-! ## The two definitions of "paradoxical" agree at an odd-step boundary -/

/-- **Remark 5.1, formalized.**  At a boundary between odd steps the Terras-clock
condition of Rozier–Terracol's Definition 1.1 is exactly the odd-clock condition
`3^L < 2^{K_L}` together with the failure to descend. -/
theorem paradoxical_iff_oddClock {n k : Nat → Nat} {L : Nat}
    (htraj : Traj n k L) (hodd : n 0 % 2 = 1) (hn : 2 < n 0) (hL : 1 ≤ L) :
    Paradoxical.Paradoxical (n 0) (Ksum k L) ↔ (3 ^ L < 2 ^ Ksum k L ∧ n 0 ≤ n L) := by
  have hK : 1 ≤ Ksum k L := by
    have := Ksum_ge (k := k) L htraj.one_le
    omega
  have hcount := traj_oddCount L htraj hodd
  have hstate := traj_acceleratedOrbit L htraj hodd
  unfold Paradoxical.Paradoxical
  rw [hcount, hstate]
  constructor
  · intro h; exact ⟨h.2.2.1, h.2.2.2⟩
  · intro h; exact ⟨hn, hK, h.1, h.2⟩

/-! ## The paradoxical window (Theorem 4.2 and Corollary 4.3, weakened form)

Rozier–Terracol's Theorem 4.2 bounds the remainder ratio `E/n` above by
`((3 + 1/h)^q − 3^q)/2^j`, where `h` is the harmonic mean of the odd terms; the
essential consequence is `2^j ≤ (3 + 1/h)^q`.  The paper notes that "in practice
we often use a weakened form of these results where the harmonic mean `h` is
replaced by the smallest term of the sequence".

That weakened form is exactly `GapBarriers.noDescent_product_bound` read through
the bridge: with `q = L` odd steps and `j = K_L` total steps,

  `2^{K_L} · N^L ≤ (3N+1)^L`   is   `2^j ≤ (3 + 1/N)^q`.

So the bound obtained here from the affine identity coincides with the one the
paper obtains by Eliahou's method.  Pairing it with condition (i) gives the
two-sided window below, the paradoxical analogue of `GapBarriers.admissibleK`
for cycles. -/

/-- **The window.**  A paradoxical pair read at an odd-step boundary satisfies
`3^q < 2^j` and `2^j · N^q ≤ (3N+1)^q`, where `N` bounds the odd terms below. -/
theorem paradoxical_window {n k : Nat → Nat} {L N : Nat}
    (htraj : Traj n k L) (hodd : n 0 % 2 = 1) (hn : 2 < n 0) (hL : 1 ≤ L)
    (hpar : Paradoxical.Paradoxical (n 0) (Ksum k L))
    (hmin : ∀ i : Nat, i < L → N ≤ n i) :
    3 ^ L < 2 ^ Ksum k L ∧ 2 ^ Ksum k L * N ^ L ≤ (3 * N + 1) ^ L := by
  obtain ⟨hcoeff, hnodrop⟩ := (paradoxical_iff_oddClock htraj hodd hn hL).mp hpar
  refine ⟨hcoeff, ?_⟩
  have hposL : 0 < n L := by
    obtain ⟨M, hM⟩ : ∃ M, L = M + 1 := ⟨L - 1, by omega⟩
    have h := htraj M (by omega)
    rw [← hM] at h
    have := h.2.1
    omega
  exact noDescent_product_bound htraj hnodrop hposL hmin

/-- **Corollary 4.3, weakened.**  With the odd terms at least `3`, the window
closes to `3^q < 2^j` and `2^j · 3^q ≤ 10^q` — the same two-sided squeeze that
`GapBarriers.admissibleK` applies to cycles, now for paradoxical pairs. -/
theorem paradoxical_window_three {n k : Nat → Nat} {L : Nat}
    (htraj : Traj n k L) (hodd : n 0 % 2 = 1) (hn : 2 < n 0) (hL : 1 ≤ L)
    (hpar : Paradoxical.Paradoxical (n 0) (Ksum k L))
    (hmin : ∀ i : Nat, i < L → 3 ≤ n i) :
    3 ^ L < 2 ^ Ksum k L ∧ 2 ^ Ksum k L * 3 ^ L ≤ 10 ^ L := by
  obtain ⟨hcoeff, hprod⟩ := paradoxical_window htraj hodd hn hL hpar hmin
  refine ⟨hcoeff, ?_⟩
  have e6 : (3 * 3 + 1) ^ L = 2 ^ L * 5 ^ L := by
    rw [show 3 * 3 + 1 = 2 * 5 by omega]
    exact Nat.mul_pow 2 5 L
  have e3 : (3 : Nat) ^ L * 2 ^ L = 6 ^ L := by
    rw [← Nat.mul_pow]
  have hten : (10 : Nat) ^ L = 2 ^ L * 5 ^ L := by
    rw [show (10 : Nat) = 2 * 5 by omega]
    exact Nat.mul_pow 2 5 L
  rw [e6] at hprod
  rw [hten]
  omega

/-- **Corollary 4.4, `Nat` form.**  The paper solves `2^j ≤ (3 + 1/h)^q` for the
harmonic mean `h`, which needs real exponents.  Over `Nat` the same content is
the bound on the least odd term:

  `3^q⁻¹ · N ≤ q · 10^q⁻¹`,  i.e.  `N ≲ q·(10/3)^{q-1}`,

an instance of `GapBarriers.min_upper_of_squeeze` — the identical arithmetic that
bounds the least element of a cycle.  A paradoxical sequence with few odd steps
cannot have a large least odd term. -/
theorem paradoxical_min_upper {n k : Nat → Nat} {L N : Nat}
    (htraj : Traj n k (L + 1)) (hodd : n 0 % 2 = 1) (hn : 2 < n 0)
    (hpar : Paradoxical.Paradoxical (n 0) (Ksum k (L + 1)))
    (hN : 3 ≤ N) (hmin : ∀ i : Nat, i < L + 1 → N ≤ n i) :
    3 ^ L * N ≤ (L + 1) * 10 ^ L := by
  obtain ⟨hlo, hup⟩ := paradoxical_window htraj hodd hn (by omega) hpar hmin
  exact GapBarriers.min_upper_of_squeeze hN hlo hup

/-- The bound at the smallest admissible length.  With `q = 5` odd steps — the
`(8,5)` row of Table 1 — the least odd term is at most `617`; the row's actual
starting values are `7, 9, 18, 19, 25`. -/
theorem paradoxical_min_upper_five {N : Nat} (h : 3 ^ 4 * N ≤ 5 * 10 ^ 4) : N ≤ 617 := by
  omega

/-- The cycle case, seen through the bridge: `cycle_three_pow_lt` is exactly
condition (i) of Definition 1.1, so a nontrivial cycle is paradoxical on either
clock. -/
theorem paradoxical_of_cycle_oddClock {n k : Nat → Nat} {L : Nat}
    (htraj : Traj n k L) (hodd : n 0 % 2 = 1) (hn : 2 < n 0) (hL : 1 ≤ L)
    (hcyc : n L = n 0) : Paradoxical.Paradoxical (n 0) (Ksum k L) := by
  refine (paradoxical_iff_oddClock htraj hodd hn hL).mpr ⟨?_, by omega⟩
  exact cycle_three_pow_lt hL htraj hcyc (by omega)

end OddClock
end Collatz
