import Collatz.Exploration.FirstDescent

/-!
# Checked finite traces as Collatz certificates

A list contains the successive *standard* states after the initial input.
Checking every transition, rather than trusting an endpoint or an external
program, proves that the list endpoint is the corresponding actual iterate.
Separate checks certify convergence, descent, or exact first descent.

The checker is executable, and its soundness is proved by structural induction.
A finite successful trace is evidence only for its supplied initial value.
No external bound or universal convergence claim is embedded in the checker.
-/
namespace Collatz.Exploration.TraceCertificate

open OrbitFloor FirstDescent

/-- Endpoint of a supplied trace, retaining the initial value for an empty list. -/
def endpoint (current : Nat) : List Nat → Nat
  | [] => current
  | next::rest => endpoint next rest

/-- Check that every successive value is the exact standard Collatz step. -/
def valid (current : Nat) : List Nat → Bool
  | [] => true
  | next::rest => (next == step current) && valid next rest

/-- Check a lower bound at each state before a supplied transition.
The endpoint itself is excluded, so a final strict descent is allowed. -/
def preAbove (bound current : Nat) : List Nat → Bool
  | [] => true
  | next::rest => decide (bound ≤ current) && preAbove bound next rest

/-- Every successful transition check implies the exact endpoint identity. -/
theorem endpoint_sound {xs : List Nat} : ∀ current,
    valid current xs = true → orbit xs.length current = endpoint current xs := by
  induction xs with
  | nil => intro current _; rfl
  | cons next rest ih =>
    intro current h
    rw [valid, Bool.and_eq_true] at h
    have he : next = step current := by simpa using h.1
    rw [List.length_cons, orbit_succ_steps]
    change orbit rest.length (step current) = endpoint next rest
    rw [← he]
    exact ih next h.2

/-- Every index before the checked endpoint obeys the supplied lower bound. -/
theorem preAbove_sound {xs : List Nat} : ∀ bound current,
    valid current xs = true → preAbove bound current xs = true →
    ∀ i, i < xs.length → bound ≤ orbit i current := by
  induction xs with
  | nil => intro bound current _ _ i hi; simp at hi
  | cons next rest ih =>
    intro bound current hv hp i hi
    rw [valid, Bool.and_eq_true] at hv
    rw [preAbove, Bool.and_eq_true] at hp
    have hcur : bound ≤ current := by simpa using hp.1
    have he : next = step current := by simpa using hv.1
    by_cases hz : i = 0
    · rw [hz, orbit_zero_steps]
      exact hcur
    · obtain ⟨j, hj⟩ : ∃ j, i = j+1 := ⟨i-1, by omega⟩
      rw [hj, orbit_succ_steps, ← he]
      exact ih bound next hv.2 hp.2 j (by simp at hi; omega)

/-- Complete finite certificate for reaching 1. -/
def convergenceCheck (n : Nat) (xs : List Nat) : Bool :=
  valid n xs && (endpoint n xs == 1)

/-- Complete finite certificate for an endpoint below the initial state. -/
def descentCheck (n : Nat) (xs : List Nat) : Bool :=
  valid n xs && decide (endpoint n xs < n)

/-- Exact first descent additionally checks every state before the endpoint. -/
def firstDescentCheck (n : Nat) (xs : List Nat) : Bool :=
  descentCheck n xs && preAbove n n xs

/-- A convergence certificate proves actual standard reachability. -/
theorem convergence_sound {n : Nat} {xs : List Nat}
    (h : convergenceCheck n xs = true) : Converges n := by
  rw [convergenceCheck, Bool.and_eq_true] at h
  have he : endpoint n xs = 1 := by simpa using h.2
  exact ⟨xs.length, by rw [endpoint_sound n h.1, he]⟩

/-- A descent certificate proves a genuine orbit drop at the supplied length. -/
theorem descent_sound {n : Nat} {xs : List Nat}
    (h : descentCheck n xs = true) : orbit xs.length n < n := by
  rw [descentCheck, Bool.and_eq_true] at h
  have he : endpoint n xs < n := by simpa using h.2
  rw [endpoint_sound n h.1]
  exact he

/-- The strongest checker certifies the exact least standard descent time. -/
theorem first_descent_sound {n : Nat} {xs : List Nat}
    (h : firstDescentCheck n xs = true) : FirstStandard n xs.length := by
  rw [firstDescentCheck, Bool.and_eq_true] at h
  refine ⟨descent_sound h.1, ?_⟩
  have hv := h.1
  rw [descentCheck, Bool.and_eq_true] at hv
  exact preAbove_sound n n hv.1 h.2

/-- A checked descent also supplies an accelerated descent witness. -/
theorem accelerated_descent_sound {n : Nat} {xs : List Nat}
    (h : descentCheck n xs = true) :
    ∃ j, j ≤ xs.length ∧ acceleratedOrbit j n < n :=
  TimeChange.accelerated_drop_of_standard (descent_sound h)

/-- An exact checked first descent supplies its exact accelerated clock index. -/
theorem accelerated_first_sound {n : Nat} {xs : List Nat}
    (h : firstDescentCheck n xs = true) :
    ∃ j, xs.length = TimeChange.clock n j ∧ FirstAccelerated n j :=
  accelerated_first_of_standard (first_descent_sound h)

/-- A descent trace cannot be empty: the initial value is not below itself. -/
theorem descent_nonempty {n : Nat} {xs : List Nat}
    (h : descentCheck n xs = true) : xs ≠ [] := by
  intro he
  subst xs
  simp [descentCheck, valid, endpoint] at h

/-- Initial 1 is certified by the empty convergence trace. -/
theorem convergence_empty_one : convergenceCheck 1 [] = true := rfl

/-- Appending traces composes endpoints. This is independent of validation. -/
theorem endpoint_append (n : Nat) (xs ys : List Nat) :
    endpoint n (xs++ys) = endpoint (endpoint n xs) ys := by
  induction xs generalizing n with
  | nil => rfl
  | cons next rest ih => exact ih next

/-- Validated trace fragments can be concatenated without replaying the orbit. -/
theorem valid_append {n : Nat} {xs ys : List Nat}
    (hx : valid n xs = true) (hy : valid (endpoint n xs) ys = true) :
    valid n (xs++ys) = true := by
  induction xs generalizing n with
  | nil => exact hy
  | cons next rest ih =>
    rw [valid, Bool.and_eq_true] at hx
    change ((next == step n) && valid next (rest++ys)) = true
    rw [Bool.and_eq_true]
    exact ⟨hx.1, ih hx.2 hy⟩

/-- Generate the exact standard trajectory of a requested finite length. -/
def trace (n : Nat) : Nat → List Nat
  | 0 => []
  | k+1 => step n :: trace (step n) k

/-- Generated traces have exactly their requested number of transitions. -/
theorem trace_length (k n : Nat) : (trace n k).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [trace, ih]

/-- The generator always passes the transition checker. -/
theorem trace_valid (k n : Nat) : valid n (trace n k) = true := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [trace, valid, ih]

/-- A generated endpoint is precisely the requested actual iterate. -/
theorem trace_endpoint (k n : Nat) : endpoint n (trace n k) = orbit k n := by
  have h := endpoint_sound n (trace_valid k n)
  rw [trace_length] at h
  exact h.symm

/-- Generated convergence certificates recognize all successful finite times. -/
theorem convergence_complete (k n : Nat) :
    convergenceCheck n (trace n k) = true ↔ orbit k n = 1 := by
  simp [convergenceCheck, trace_valid, trace_endpoint]

/-- Generated descent certificates recognize all finite descent endpoints. -/
theorem descent_complete (k n : Nat) :
    descentCheck n (trace n k) = true ↔ orbit k n < n := by
  simp [descentCheck, trace_valid, trace_endpoint]

/-- The pre-endpoint checker has an exact specification on generated traces. -/
theorem preAbove_complete (k bound current : Nat) :
    preAbove bound current (trace current k) = true ↔
      ∀ i, i < k → bound ≤ orbit i current := by
  induction k generalizing current with
  | zero => simp [trace, preAbove]
  | succ k ih =>
    simp only [trace, preAbove, Bool.and_eq_true, decide_eq_true_eq]
    rw [ih (step current)]
    constructor
    · rintro ⟨hcur, htail⟩ i hi
      by_cases hz : i = 0
      · rw [hz, orbit_zero_steps]; exact hcur
      · obtain ⟨j, hj⟩ : ∃ j, i = j+1 := ⟨i-1, by omega⟩
        rw [hj, orbit_succ_steps]
        exact htail j (by omega)
    · intro h
      refine ⟨h 0 (by omega), ?_⟩
      intro i hi
      have hs := h (i+1) (by omega)
      rw [orbit_succ_steps] at hs
      exact hs

/-- The exact first-descent checker is sound and complete on generated traces. -/
theorem first_descent_complete (k n : Nat) :
    firstDescentCheck n (trace n k) = true ↔ FirstStandard n k := by
  rw [firstDescentCheck, Bool.and_eq_true, descent_complete, preAbove_complete]
  rfl

end Collatz.Exploration.TraceCertificate
