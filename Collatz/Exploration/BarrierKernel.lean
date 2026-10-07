import Collatz.Exploration.OrbitFloor
import Collatz.Core.Pigeonhole

/-!
# Anchored barriers and sharp finite cycle extraction

A local no-descent test moves its comparison level with its input. It is
therefore not forward invariant. Keep the barrier fixed when shifting an
orbit. The all-horizon intersection is the greatest forward invariant set
above that barrier. A finite orbit confined to [b,u] repeats after at most
u-b+1 steps, with no assumption about the unobserved future.

These are structural reductions, not claims of literature novelty or Collatz.
-/
namespace Collatz.Exploration.BarrierKernel

/-- Survival above a fixed barrier through a finite, inclusive time window. -/
def Survives (b K n : Nat) : Prop := ∀ k, k ≤ K → b ≤ orbit k n

/-- The all-horizon kernel keeps the same barrier at every future state. -/
def Kernel (b n : Nat) : Prop := ∀ k, b ≤ orbit k n

theorem survives_zero (b n : Nat) : Survives b 0 n ↔ b ≤ n := by
  constructor
  · intro h; exact h 0 (by omega)
  · intro h k hk
    have he : k = 0 := by omega
    subst k
    exact h

/-- Exact predecessor recursion; suitable for finite certificate checkers. -/
theorem survives_succ (b K n : Nat) :
    Survives b (K+1) n ↔ b ≤ n ∧ Survives b K (step n) := by
  constructor
  · intro h
    refine ⟨h 0 (by omega), ?_⟩
    intro k hk
    exact h (k+1) (by omega)
  · rintro ⟨hn, hs⟩ k hk
    cases k with
    | zero => exact hn
    | succ k => exact hs k (by omega)

theorem survives_mono_time {b K L n : Nat} (h : Survives b K n)
    (hLK : L ≤ K) : Survives b L n := by
  intro k hk; exact h k (by omega)

theorem survives_mono_barrier {a b K n : Nat} (h : Survives b K n)
    (hab : a ≤ b) : Survives a K n := by
  intro k hk; exact Nat.le_trans hab (h k hk)

/-- Splitting a window at j preserves the anchor, including both endpoints. -/
theorem survives_split (b j K n : Nat) :
    Survives b (j+K) n ↔ Survives b j n ∧ Survives b K (orbit j n) := by
  constructor
  · intro h
    refine ⟨survives_mono_time h (by omega), ?_⟩
    intro k hk
    rw [← orbit_add]
    exact h (k+j) (by omega)
  · rintro ⟨hp, ht⟩ k hk
    by_cases hkj : k ≤ j
    · exact hp k hkj
    · have hs := ht (k-j) (by omega)
      rw [← orbit_add, Nat.sub_add_cancel (by omega : j ≤ k)] at hs
      exact hs

theorem kernel_iff_all_windows (b n : Nat) :
    Kernel b n ↔ ∀ K, Survives b K n := by
  constructor
  · intro h K k _; exact h k
  · intro h k; exact h k k (Nat.le_refl k)

theorem kernel_forward {b n : Nat} (h : Kernel b n) (j : Nat) :
    Kernel b (orbit j n) := by
  intro k; rw [← orbit_add]; exact h (k+j)

theorem kernel_step (b n : Nat) : Kernel b n ↔ b ≤ n ∧ Kernel b (step n) := by
  constructor
  · intro h; exact ⟨h 0, fun k => h (k+1)⟩
  · rintro ⟨hn, hs⟩ k
    cases k with
    | zero => exact hn
    | succ k => exact hs k

/-- Any invariant set above b is contained in the kernel. -/
theorem greatest_invariant {S : Nat → Prop} {b : Nat}
    (hbound : ∀ n, S n → b ≤ n)
    (hclosed : ∀ n, S n → S (step n)) :
    ∀ n, S n → Kernel b n := by
  intro n hn k
  induction k generalizing n with
  | zero => exact hbound n hn
  | succ k ih => exact ih (step n) (hclosed n hn)

theorem kernel_trap {b : Nat} (hb : 1 < b) :
    OrbitFloor.Trap (Kernel b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn; have := hn 0; simp at this; omega
  · intro h; have := h 0; simp at this; omega
  · intro n hn; exact (kernel_step b n).mp hn |>.2

/-- A kernel above 1 contains only nonconvergent states. -/
theorem kernel_failure {b n : Nat} (hb : 1 < b) (h : Kernel b n) :
    ¬ OrbitFloor.Converges n :=
  (OrbitFloor.trap_failure (kernel_trap hb) h).2

/-- Nonconvergence is equivalent to membership in the single kernel b=2. -/
theorem kernel_two_iff_failure {n : Nat} (hp : 0 < n) :
    Kernel 2 n ↔ ¬ OrbitFloor.Converges n := by
  constructor
  · exact kernel_failure (by decide)
  · intro hf k
    have hpos := orbit_positive hp k
    have hne : orbit k n ≠ 1 := fun he => hf ⟨k, he⟩
    omega

/-- The empty-kernel obligation is still precisely the original conjecture. -/
theorem empty_kernel_two_iff_collatz :
    (∀ n, ¬ Kernel 2 n) ↔ CollatzConjecture := by
  constructor
  · intro he n hp
    by_cases hc : OrbitFloor.Converges n
    · exact hc
    · exact False.elim (he n ((kernel_two_iff_failure hp).mpr hc))
  · intro hc n hn
    have hpos : 0 < n := by have := hn 0; simp at this; omega
    exact kernel_failure (by decide) hn (hc n hpos)

/-- Fixed anchors characterize the existing attained orbit-floor reduction. -/
theorem floor_iff_kernel (m : Nat) :
    OrbitFloor.Floor m ↔ 1 < m ∧ Kernel m m := Iff.rfl

/-- A sharp finite interval certificate extracts a closed orbit above the barrier.
There are u-b+1 available values and one more sampled orbit point. -/
theorem cycle_of_interval_prefix {b u n : Nat} (hbu : b ≤ u)
    (hlo : Survives b (u-b+1) n)
    (hhi : ∀ k, k ≤ u-b+1 → orbit k n ≤ u) :
    ∃ i j, i < j ∧ j ≤ u-b+1 ∧
      b ≤ orbit i n ∧ orbit (j-i) (orbit i n) = orbit i n := by
  obtain ⟨i, j, hij, hj, heq⟩ := Pigeonhole.exists_repeat
    (f := fun k => orbit k n - b) (B := u-b+1) (N := u-b+1)
    (fun k hk => by have := hlo k hk; have := hhi k hk; omega)
    (Nat.le_refl _)
  have hi : i ≤ u-b+1 := by omega
  have hbi := hlo i hi
  have hbj := hlo j hj
  have he : orbit i n = orbit j n := by omega
  refine ⟨i, j, hij, hj, hbi, ?_⟩
  rw [← orbit_add, Nat.sub_add_cancel (by omega : i ≤ j), ← he]

/-- An executable inclusive interval-prefix checker. -/
def intervalCheck (b u : Nat) : Nat → Nat → Bool
  | 0, n => decide (b ≤ n ∧ n ≤ u)
  | K+1, n => decide (b ≤ n ∧ n ≤ u) && intervalCheck b u K (step n)

/-- The checker certifies all sampled states, including time zero. -/
theorem intervalCheck_iff (b u K n : Nat) :
    intervalCheck b u K n = true ↔
      ∀ k, k ≤ K → b ≤ orbit k n ∧ orbit k n ≤ u := by
  induction K generalizing n with
  | zero =>
    simp only [intervalCheck, decide_eq_true_eq]
    constructor
    · intro h k hk
      have he : k = 0 := by omega
      subst k
      exact h
    · intro h; exact h 0 (by omega)
  | succ K ih =>
    simp only [intervalCheck, Bool.and_eq_true, decide_eq_true_eq, ih]
    constructor
    · rintro ⟨hn, ht⟩ k hk
      cases k with
      | zero => exact hn
      | succ k => exact ht k (by omega)
    · intro h
      exact ⟨h 0 (by omega), fun k hk => h (k+1) (by omega)⟩

/-- A successful sharp-budget computation supplies a genuine closed orbit. -/
theorem cycle_of_intervalCheck {b u n : Nat}
    (h : intervalCheck b u (u-b+1) n = true) :
    ∃ i j, i < j ∧ j ≤ u-b+1 ∧
      b ≤ orbit i n ∧ orbit (j-i) (orbit i n) = orbit i n := by
  have hs := (intervalCheck_iff b u (u-b+1) n).mp h
  have hz := hs 0 (by omega)
  have hbu : b ≤ u := by simp only [orbit_zero_steps] at hz; omega
  exact cycle_of_interval_prefix hbu (fun k hk => (hs k hk).1)
    (fun k hk => (hs k hk).2)

/-- Positive control: the trivial cycle is accepted at the sharp budget. -/
theorem trivial_cycle_control : intervalCheck 1 4 4 1 = true := by decide

/-- A short accepted prefix is insufficient for cycle extraction. -/
theorem short_prefix_control :
    intervalCheck 3 10 1 3 = true ∧ intervalCheck 3 10 8 3 = false := by decide

/-- Resetting the comparison level invalidates even one-step forward closure. -/
theorem moving_barrier_counterexample :
    Survives 3 1 3 ∧ ¬ Survives (step 3) 1 (step 3) := by
  constructor
  · intro k hk
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl <;> decide
  · intro h
    have := h 1 (by decide)
    change 10 ≤ 5 at this
    omega

/-- A fixed barrier survives that same shift for the remaining budget. -/
theorem fixed_barrier_control : Survives 3 1 (step 3) := by
  intro k hk
  have : k = 0 ∨ k = 1 := by omega
  rcases this with rfl | rfl <;> decide

end Collatz.Exploration.BarrierKernel
