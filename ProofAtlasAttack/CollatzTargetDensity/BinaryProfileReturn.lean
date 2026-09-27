import CollatzTargetDensity.BinaryPatternPotential
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
Rising returns to the same binary-pattern histogram obstruct nonlinear
potentials at variable-length checkpoints. The checkpoint from n consists
of exactly v₂(n+1) actual Syracuse steps. No convergence claim is made.
-/
namespace CollatzTargetDensity.BinaryProfileReturn
open Erdos1135 BinaryPatternPotential
noncomputable section

abbrev Histogram := List (ℕ × ℕ)

def histogram (k n : ℕ) : Histogram :=
  normalize ((patterns k n).map (fun p => (p, 1)))

/-- The number of odd steps depends on the starting integer and is unbounded. -/
def checkpoint (n : ℕ) : ℕ := (Tao.syracuse^[padicValNat 2 (n + 1)]) n

def pathCheck (start finish : ℕ) : List Edge → Bool
  | [] => decide (start = finish)
  | e :: es => decide (start = e.source ∧ e.valid) && pathCheck e.target finish es

theorem pathCheck_sound {start finish : ℕ} {es : List Edge}
    (h : pathCheck start finish es = true) :
    (Tao.syracuse^[es.length]) start = finish := by
  induction es generalizing start with
  | nil => simpa [pathCheck] using h
  | cons e es ih =>
    have hh : (start = e.source ∧ e.valid) ∧ pathCheck e.target finish es = true := by
      simpa [pathCheck, Bool.and_eq_true] using h
    rw [List.length_cons, Function.iterate_succ_apply, hh.1.1, Edge.successor hh.1.2]
    exact ih hh.2

structure Chunk where
  source : ℕ
  target : ℕ
  oddPart : ℕ
  edges : List Edge
deriving DecidableEq, Repr

def Chunk.valid (c : Chunk) : Prop :=
  1 < c.source ∧ Odd c.source ∧ Odd c.oddPart ∧ 0 < c.edges.length ∧
    c.source + 1 = 2 ^ c.edges.length * c.oddPart ∧
    pathCheck c.source c.target c.edges = true

instance (c : Chunk) : Decidable c.valid :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

theorem Chunk.successor {c : Chunk} (h : c.valid) : checkpoint c.source = c.target := by
  have hnot : ¬2 ∣ c.oddPart := by
    intro hd
    exact (Nat.not_even_iff_odd.mpr h.2.2.1) (even_iff_two_dvd.mpr hd)
  have hv : padicValNat 2 (c.source + 1) = c.edges.length := by
    rw [h.2.2.2.2.1, padicValNat.mul (by positivity) (ne_of_gt h.2.2.1.pos),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hnot, Nat.add_zero]
  rw [checkpoint, hv]
  exact pathCheck_sound h.2.2.2.2.2

def chainCheck (start finish : ℕ) : List Chunk → Bool
  | [] => decide (start = finish)
  | c :: cs => decide (start = c.source ∧ c.valid) && chainCheck c.target finish cs

theorem chain_le {start finish : ℕ} {cs : List Chunk}
    (hc : chainCheck start finish cs = true) (V : ℕ → ℝ)
    (hV : ∀ n, 1 < n → Odd n → V (checkpoint n) ≤ V n) : V finish ≤ V start := by
  induction cs generalizing start with
  | nil =>
    have h : start = finish := by simpa [chainCheck] using hc
    simp [h]
  | cons c cs ih =>
    have hh : (start = c.source ∧ c.valid) ∧ chainCheck c.target finish cs = true := by
      simpa [chainCheck, Bool.and_eq_true] using hc
    have hstep := hV c.source hh.1.2.1 hh.1.2.2.1
    rw [Chunk.successor hh.1.2] at hstep
    rw [hh.1.1]
    exact (ih hh.2).trans hstep

theorem chain_lt {start finish : ℕ} {cs : List Chunk} (hne : cs ≠ [])
    (hc : chainCheck start finish cs = true) (V : ℕ → ℝ)
    (hV : ∀ n, 1 < n → Odd n → V (checkpoint n) < V n) : V finish < V start := by
  cases cs with
  | nil => contradiction
  | cons c cs =>
    have hh : (start = c.source ∧ c.valid) ∧ chainCheck c.target finish cs = true := by
      simpa [chainCheck, Bool.and_eq_true] using hc
    have hstep := hV c.source hh.1.2.1 hh.1.2.2.1
    rw [Chunk.successor hh.1.2] at hstep
    rw [hh.1.1]
    exact (chain_le hh.2 V (fun n hn ho => (hV n hn ho).le)).trans_lt hstep

def returnCheck (k start finish : ℕ) (cs : List Chunk) : Bool :=
  !cs.isEmpty && decide (start < finish ∧ histogram k start = histogram k finish) &&
    chainCheck start finish cs

/-- This includes arbitrary nonlinear histogram functions (constant in the
second argument), as well as monotone size terms with histogram corrections. -/
theorem checked_return_not_strict {k start finish : ℕ} {cs : List Chunk}
    (hc : returnCheck k start finish cs = true) (F : Histogram → ℕ → ℝ)
    (hF : ∀ p, Monotone (F p)) :
    ¬(∀ n, 1 < n → Odd n →
      F (histogram k (checkpoint n)) (checkpoint n) < F (histogram k n) n) := by
  have hh : cs ≠ [] ∧ (start < finish ∧ histogram k start = histogram k finish) ∧
      chainCheck start finish cs = true := by
    simpa [returnCheck, Bool.and_eq_true, and_assoc] using hc
  intro h
  have hlt := chain_lt hh.1 hh.2.2 (fun n => F (histogram k n) n) h
  dsimp only at hlt
  have hle := hF (histogram k start) hh.2.1.1.le
  rw [hh.2.1.2] at hle
  rw [hh.2.1.2] at hlt
  exact (not_lt_of_ge hle) hlt

/-- If size is strictly increasing at fixed histogram, some checkpoint must
actually increase the potential; even weak nonincrease is impossible. -/
theorem checked_return_not_nonincreasing {k start finish : ℕ} {cs : List Chunk}
    (hc : returnCheck k start finish cs = true) (F : Histogram → ℕ → ℝ)
    (hF : ∀ p, StrictMono (F p)) :
    ¬(∀ n, 1 < n → Odd n →
      F (histogram k (checkpoint n)) (checkpoint n) ≤ F (histogram k n) n) := by
  have hh : cs ≠ [] ∧ (start < finish ∧ histogram k start = histogram k finish) ∧
      chainCheck start finish cs = true := by
    simpa [returnCheck, Bool.and_eq_true, and_assoc] using hc
  intro h
  have hle := chain_le hh.2.2 (fun n => F (histogram k n) n) h
  dsimp only at hle
  have hlt := hF (histogram k start) hh.2.1.1
  rw [hh.2.1.2] at hle hlt
  exact (not_lt_of_ge hle) hlt

end
end CollatzTargetDensity.BinaryProfileReturn
