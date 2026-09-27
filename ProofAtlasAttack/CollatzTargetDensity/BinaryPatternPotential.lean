import CollatzTargetDensity.RawBridge
import Mathlib.Data.Nat.Digits.Defs

/-!
Finite certificates against strict one-step descent of additive local binary
pattern potentials. The width is fixed, but every digit of the integer is read.
Boundary markers are included. No claim covers all finite widths.
-/
namespace CollatzTargetDensity.BinaryPatternPotential
open Erdos1135
noncomputable section

/-- The symbol 2 is an end marker; the ordinary digits are 0 and 1. -/
def paddedBits (k n : ℕ) : List ℕ :=
  List.replicate (k - 1) 2 ++ (Nat.digits 2 n).reverse ++ List.replicate (k - 1) 2

def patternCode (xs : List ℕ) : ℕ := xs.foldl (fun a b => 3 * a + b) 0

def windows (k : ℕ) : List ℕ → List ℕ
  | [] => []
  | x :: xs => if k ≤ (x :: xs).length then
      patternCode ((x :: xs).take k) :: windows k xs else []

def patterns (k n : ℕ) : List ℕ := windows k (paddedBits k n)

def potential (k : ℕ) (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((patterns k n).map w).sum

/-- Insert one weighted pattern into a sorted histogram, merging equal keys. -/
def insertCharge (p c : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [(p, c)]
  | (q, d) :: xs => if p < q then (p, c) :: (q, d) :: xs
    else if p = q then (q, c + d) :: xs else (q, d) :: insertCharge p c xs

def normalize : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | (p, c) :: xs => insertCharge p c (normalize xs)

def evaluate (w : ℕ → ℝ) (xs : List (ℕ × ℕ)) : ℝ :=
  (xs.map (fun pc => (pc.2 : ℝ) * w pc.1)).sum

theorem evaluate_insertCharge (w : ℕ → ℝ) (p c : ℕ) (xs : List (ℕ × ℕ)) :
    evaluate w (insertCharge p c xs) = (c : ℝ) * w p + evaluate w xs := by
  induction xs with
  | nil => simp [insertCharge, evaluate]
  | cons x xs ih =>
    rcases x with ⟨q, d⟩
    simp only [insertCharge]
    split_ifs with hlt heq
    · simp [evaluate]
    · subst p
      simp [evaluate, Nat.cast_add]
      ring
    · simp only [evaluate, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      ring

theorem evaluate_normalize (w : ℕ → ℝ) (xs : List (ℕ × ℕ)) :
    evaluate w (normalize xs) = evaluate w xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨p, c⟩
    rw [normalize, evaluate_insertCharge, ih]
    rfl

structure Edge where
  source : ℕ
  target : ℕ
  exponent : ℕ
  multiplicity : ℕ
deriving DecidableEq, Repr

def Edge.valid (e : Edge) : Prop :=
  1 < e.source ∧ Odd e.source ∧ Odd e.target ∧ 0 < e.exponent ∧
    2 ^ e.exponent * e.target = 3 * e.source + 1 ∧ 0 < e.multiplicity

instance (e : Edge) : Decidable e.valid := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

theorem Edge.successor {e : Edge} (h : e.valid) : Tao.syracuse e.source = e.target := by
  have hnot : ¬2 ∣ e.target := by
    intro hd
    exact (Nat.not_even_iff_odd.mpr h.2.2.1) (even_iff_two_dvd.mpr hd)
  rw [Tao.syracuse_eq_ordCompl_two, ← h.2.2.2.2.1]
  exact Nat.ordCompl_pow_mul_of_not_dvd e.exponent Nat.prime_two hnot

def charges (k : ℕ) (endpoint : Edge → ℕ) (es : List Edge) : List (ℕ × ℕ) :=
  es.flatMap (fun e => (patterns k (endpoint e)).map (fun p => (p, e.multiplicity)))

theorem evaluate_charges (k : ℕ) (w : ℕ → ℝ) (endpoint : Edge → ℕ) (es : List Edge) :
    evaluate w (charges k endpoint es) =
      (es.map (fun e => (e.multiplicity : ℝ) * potential k w (endpoint e))).sum := by
  induction es with
  | nil => simp [charges, evaluate]
  | cons e es ih =>
    simp only [charges, List.flatMap_cons, evaluate, List.map_append, List.sum_append,
      List.map_map, Function.comp_def] at ih ⊢
    rw [ih]
    simp only [List.map_cons, List.sum_cons, potential]
    congr 1
    induction patterns k (endpoint e) with
    | nil => simp
    | cons p ps ih => simp only [List.map_cons, List.sum_cons, mul_add]; rw [ih]

def check (k : ℕ) (es : List Edge) : Bool :=
  !es.isEmpty && es.all (fun e => decide e.valid) &&
    decide (normalize (charges k Edge.source es) = normalize (charges k Edge.target es))

theorem weighted_sum_lt {es : List Edge} (hne : es ≠ []) (f g : Edge → ℝ)
    (h : ∀ e ∈ es, 0 < e.multiplicity ∧ f e < g e) :
    (es.map (fun e => (e.multiplicity : ℝ) * f e)).sum <
      (es.map (fun e => (e.multiplicity : ℝ) * g e)).sum := by
  induction es with
  | nil => contradiction
  | cons e es ih =>
    have he := h e (by simp)
    have he' := mul_lt_mul_of_pos_left he.2 (by exact_mod_cast he.1 : (0 : ℝ) < e.multiplicity)
    cases es with
    | nil => simpa using he'
    | cons e' es =>
      have ht := ih (by simp) (fun z hz => h z (by simp [hz]))
      simpa only [List.map_cons, List.sum_cons] using add_lt_add he' ht

/-- The checker is connected to the actual Syracuse map. Weights may have
either sign; even boundedness below is not needed for this obstruction. -/
theorem check_sound (k : ℕ) (es : List Edge) (hc : check k es = true) (w : ℕ → ℝ) :
    ∃ e ∈ es, 1 < e.source ∧ Odd e.source ∧ Tao.syracuse e.source = e.target ∧
      potential k w e.source ≤ potential k w e.target := by
  classical
  have hc' : es ≠ [] ∧ (∀ e ∈ es, e.valid) ∧
      normalize (charges k Edge.source es) = normalize (charges k Edge.target es) := by
    simpa [check, Bool.and_eq_true, List.all_eq_true, and_assoc] using hc
  have hsum : (es.map (fun e => (e.multiplicity : ℝ) * potential k w e.source)).sum =
      (es.map (fun e => (e.multiplicity : ℝ) * potential k w e.target)).sum := by
    rw [← evaluate_charges, ← evaluate_charges, ← evaluate_normalize w (charges k Edge.source es),
      ← evaluate_normalize w (charges k Edge.target es), hc'.2.2]
  by_contra hno
  have hh : ∀ e ∈ es, 0 < e.multiplicity ∧ potential k w e.target < potential k w e.source := by
    intro e he
    have hv := hc'.2.1 e he
    refine ⟨hv.2.2.2.2.2, lt_of_not_ge ?_⟩
    intro hle
    exact hno ⟨e, he, hv.1, hv.2.1, Edge.successor hv, hle⟩
  have hlt := weighted_sum_lt hc'.1 (fun e => potential k w e.target)
    (fun e => potential k w e.source) hh
  linarith

def StrictDescent (k : ℕ) (w : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 1 < n → Odd n → potential k w (Tao.syracuse n) < potential k w n

theorem check_not_descent (k : ℕ) (es : List Edge) (hc : check k es = true)
    (w : ℕ → ℝ) : ¬StrictDescent k w := by
  intro h
  obtain ⟨e, _, hn, hodd, hnext, hle⟩ := check_sound k es hc w
  have hlt := h e.source hn hodd
  rw [hnext] at hlt
  exact (not_lt_of_ge hle) hlt

end
end CollatzTargetDensity.BinaryPatternPotential
