import Collatz.Strategy.PhantomMediant
import Init.Data.Int.Gcd
import Collatz.Accelerated

/-!
Uniform cancellation certificates for the infinite word family `u^k v`.
The signed gap allows either block to expand or contract. These are statements
about exact affine cycle candidates, not a proof of Collatz or a priority claim.
-/
namespace Collatz.RepeatedBlockCancellation

open DeltaSpectrum

def signedGap (w : List Bool) : Int :=
  (2 : Int) ^ w.length - (3 : Int) ^ DeltaSpectrum.oddCount w

def numerator (w : List Bool) : Int := C w

def defect (u v : List Bool) : Int :=
  signedGap u * numerator v - numerator u * signedGap v

def padded (u : List Bool) : Nat → List Bool → List Bool
  | 0, v => v
  | k + 1, v => u ++ padded u k v

theorem padded_length (u v : List Bool) (k : Nat) :
    (padded u k v).length = k * u.length + v.length := by
  induction k with
  | zero => simp [padded]
  | succ k ih => simp only [padded, List.length_append, ih, Nat.succ_mul]; omega

theorem padded_oddCount (u v : List Bool) (k : Nat) :
    DeltaSpectrum.oddCount (padded u k v) =
      k * DeltaSpectrum.oddCount u + DeltaSpectrum.oddCount v := by
  induction k with
  | zero => simp [padded]
  | succ k ih =>
    simp only [padded, PhantomMediant.oddCount_append, ih, Nat.succ_mul]; omega

theorem gap_padded_closed (u v : List Bool) (k : Nat) :
    signedGap (padded u k v) =
      ((2 : Int) ^ u.length)^k * (2 : Int)^v.length -
      ((3 : Int) ^ DeltaSpectrum.oddCount u)^k * (3 : Int)^DeltaSpectrum.oddCount v := by
  simp only [signedGap, padded_length, padded_oddCount, Int.pow_add,
    Nat.mul_comm k, Int.pow_mul]

macro "cancellation_ring" : tactic =>
  `(tactic| (simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
    Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] <;> omega))

theorem numerator_append (u v : List Bool) :
    numerator (u ++ v) = (3 : Int) ^ DeltaSpectrum.oddCount v * numerator u +
      (2 : Int) ^ u.length * numerator v := by
  simp [numerator, PhantomMediant.C_append, Int.natCast_add, Int.natCast_mul,
    Int.natCast_pow]

theorem gap_append (u v : List Bool) :
    signedGap (u ++ v) = (3 : Int) ^ DeltaSpectrum.oddCount v * signedGap u +
      (2 : Int) ^ u.length * signedGap v := by
  simp only [signedGap, List.length_append, PhantomMediant.oddCount_append,
    Int.pow_add]
  cancellation_ring

/-- Prepending a copy of the reference block only scales the defect by a
power of two. No hypothesis about the signs of either gap is needed. -/
theorem defect_prepend (u v : List Bool) :
    defect u (u ++ v) = (2 : Int) ^ u.length * defect u v := by
  simp only [defect, numerator_append, gap_append]
  cancellation_ring

theorem defect_padded (u v : List Bool) (k : Nat) :
    defect u (padded u k v) = (2 : Int) ^ (k * u.length) * defect u v := by
  induction k with
  | zero => simp [padded]
  | succ k ih =>
    rw [padded, defect_prepend, ih]
    simp only [Nat.succ_mul, Int.pow_add]
    <;> cancellation_ring

theorem gap_coprime_two (w : List Bool) (hw : 0 < w.length) :
    Int.gcd (signedGap w) 2 = 1 := by
  obtain ⟨l, hl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : w.length ≠ 0)
  rw [signedGap, hl, Int.pow_succ]
  rw [Int.gcd_mul_right_sub_left]
  exact Int.gcd_pow_left_of_gcd_eq_one (by decide : Int.gcd 3 2 = 1)

/-- The exact arithmetic bridge: all cancellation in `u^k v` is controlled
by one fixed integer, the defect of `u` and `v`. -/
theorem cancellation_dvd_defect (u v : List Bool) (k : Nat)
    (hw : 0 < (padded u k v).length) :
    Int.gcd (numerator (padded u k v)) (signedGap (padded u k v)) ∣
      (defect u v).natAbs := by
  let w := padded u k v
  let d := Int.gcd (numerator w) (signedGap w)
  have hdC : (d : Int) ∣ numerator w := Int.gcd_dvd_left _ _
  have hdG : (d : Int) ∣ signedGap w := Int.gcd_dvd_right _ _
  have hdD : (d : Int) ∣ defect u w :=
    Int.dvd_sub (Int.dvd_trans hdC (Int.dvd_mul_left _ _))
      (Int.dvd_trans hdG (Int.dvd_mul_left _ _))
  have hc : Int.gcd (d : Int) 2 = 1 := by
    apply Nat.dvd_one.mp
    have h := Int.dvd_gcd (Int.dvd_trans (Int.gcd_dvd_left _ _) hdG)
      (Int.gcd_dvd_right (d : Int) 2)
    rw [gap_coprime_two w hw] at h
    exact h
  have hp : Int.gcd (d : Int) ((2 : Int) ^ (k * u.length)) = 1 :=
    Int.gcd_pow_right_of_gcd_eq_one hc
  change (d : Int) ∣ defect u (padded u k v) at hdD
  rw [defect_padded] at hdD
  have he := (Int.dvd_gcd_mul_iff_dvd_mul).mpr hdD
  rw [hp] at he
  exact Int.ofNat_dvd_left.mp (by simpa using he)

/-- A nonzero fixed defect bounds cancellation at every repetition count. -/
theorem cancellation_le_defect (u v : List Bool) (k : Nat)
    (hw : 0 < (padded u k v).length) (hD : defect u v ≠ 0) :
    Int.gcd (numerator (padded u k v)) (signedGap (padded u k v)) ≤
      (defect u v).natAbs :=
  Nat.le_of_dvd (Int.natAbs_pos.mpr hD) (cancellation_dvd_defect u v k hw)

def reducedDenominator (w : List Bool) : Nat :=
  (signedGap w).natAbs / Int.gcd (numerator w) (signedGap w)

/-- Cross-multiplied lower bound for the reduced denominator. -/
theorem denominator_lower_bound (u v : List Bool) (k : Nat)
    (hw : 0 < (padded u k v).length) (hD : defect u v ≠ 0) :
    (signedGap (padded u k v)).natAbs ≤
      reducedDenominator (padded u k v) * (defect u v).natAbs := by
  have h := Nat.mul_le_mul_left (reducedDenominator (padded u k v))
    (cancellation_le_defect u v k hw hD)
  simpa only [reducedDenominator,
    Nat.div_mul_cancel (Int.gcd_dvd_natAbs_right _ _)] using h

/-- If the two block gaps are coprime, this remains true after every
prepending of the first block. -/
theorem gap_gcd_padded (u v : List Bool) (k : Nat) (hu : 0 < u.length) :
    Int.gcd (signedGap u) (signedGap (padded u k v)) =
      Int.gcd (signedGap u) (signedGap v) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [padded, gap_append, Int.gcd_mul_right_add_right]
    rw [Int.gcd_mul_right_right_of_gcd_eq_one
      (Int.gcd_pow_right_of_gcd_eq_one (gap_coprime_two u hu)), ih]

/-- Exact cancellation formula under coprime block gaps. The huge numerator
need not be computed: one takes the gcd of the gap with the fixed defect. -/
theorem exact_cancellation (u v : List Bool) (k : Nat)
    (hu : 0 < u.length) (hw : 0 < (padded u k v).length)
    (hcop : Int.gcd (signedGap u) (signedGap v) = 1) :
    Int.gcd (numerator (padded u k v)) (signedGap (padded u k v)) =
      Int.gcd (defect u v) (signedGap (padded u k v)) := by
  let w := padded u k v
  have hcop' : Int.gcd (signedGap u) (signedGap w) = 1 := by
    rw [gap_gcd_padded u v k hu, hcop]
  have htwo : Int.gcd ((2 : Int) ^ (k * u.length)) (signedGap w) = 1 :=
    Int.gcd_pow_left_of_gcd_eq_one (by
      rw [Int.gcd_comm]; exact gap_coprime_two w hw)
  have h : Int.gcd (defect u w) (signedGap w) =
      Int.gcd (numerator w) (signedGap w) := by
    rw [defect, Int.gcd_sub_mul_right_left,
      Int.gcd_mul_right_left_of_gcd_eq_one hcop']
  change Int.gcd (defect u (padded u k v)) (signedGap w) = _ at h
  rw [defect_padded, Int.gcd_mul_right_left_of_gcd_eq_one htwo] at h
  exact h.symm

/-- A certificate excluding every integer fixed point at this repetition
count; it does not require checking individual starting integers. -/
theorem excludes_integral_fixed_point (u v : List Bool) (k : Nat)
    (hw : 0 < (padded u k v).length) (hD : defect u v ≠ 0)
    (hlarge : (defect u v).natAbs < (signedGap (padded u k v)).natAbs) :
    ¬ signedGap (padded u k v) ∣ numerator (padded u k v) := by
  intro hdiv
  have he := Int.gcd_eq_natAbs_right_iff_dvd.mpr hdiv
  have hle := cancellation_le_defect u v k hw hD
  rw [he] at hle
  omega

/-- Same certificate expressed directly as the affine cycle equation. -/
theorem excludes_cycle_equation (u v : List Bool) (k : Nat)
    (hw : 0 < (padded u k v).length) (hD : defect u v ≠ 0)
    (hlarge : (defect u v).natAbs < (signedGap (padded u k v)).natAbs) :
    ¬ ∃ n : Int, (2 : Int) ^ (padded u k v).length * n =
      (3 : Int) ^ DeltaSpectrum.oddCount (padded u k v) * n + numerator (padded u k v) := by
  rintro ⟨n, hn⟩
  apply excludes_integral_fixed_point u v k hw hD hlarge
  refine ⟨n, ?_⟩
  simp only [signedGap, Int.sub_mul]
  omega

/-- A positive gap grows when a contracting block is prepended. -/
theorem gap_grows (u w : List Bool) (hu : 0 ≤ signedGap u)
    (hw : 0 ≤ signedGap w) : signedGap w ≤ signedGap (u ++ w) := by
  rw [gap_append]
  have htwo : (1 : Int) ≤ 2 ^ u.length := by
    have : (0 : Int) < 2 ^ u.length := Int.pow_pos (by decide)
    omega
  have hthree : (0 : Int) ≤ 3 ^ DeltaSpectrum.oddCount w :=
    Int.le_of_lt (Int.pow_pos (by decide))
  have h1 := Int.mul_le_mul_of_nonneg_right htwo hw
  have h2 := Int.mul_nonneg hthree hu
  simp only [Int.one_mul] at h1
  omega

/-- One checked threshold eliminates the entire tail of a repetition family. -/
theorem tail_exclusion (u v : List Bool) (K : Nat)
    (hv : 0 < v.length) (hu : 0 ≤ signedGap u) (hD : defect u v ≠ 0)
    (hK : ((defect u v).natAbs : Int) < signedGap (padded u K v)) :
    ∀ j : Nat, ¬ signedGap (padded u (K + j) v) ∣ numerator (padded u (K + j) v) := by
  have hlen : ∀ k, 0 < (padded u k v).length := by
    intro k
    induction k with
    | zero => exact hv
    | succ k ih => simp only [padded, List.length_append]; omega
  have hg : ∀ j, ((defect u v).natAbs : Int) < signedGap (padded u (K + j) v) := by
    intro j
    induction j with
    | zero => simpa using hK
    | succ j ih =>
      have hn : 0 ≤ signedGap (padded u (K + j) v) := by omega
      have h := gap_grows u (padded u (K + j) v) hu hn
      change ((defect u v).natAbs : Int) < signedGap (u ++ padded u (K+j) v)
      exact Int.lt_of_lt_of_le ih h
  intro j
  apply excludes_integral_fixed_point u v (K+j) (hlen _) hD
  have h := hg j
  have ha : signedGap (padded u (K+j) v) ≤ ((signedGap (padded u (K+j) v)).natAbs : Int) := Int.le_natAbs
  omega

/-- The prescribed parity word is the actual deterministic orbit's word. -/
def Follows : List Bool → Nat → Prop
  | [], _ => True
  | b :: w, n => (if b then n % 2 = 1 else n % 2 = 0) ∧
      Follows w (acceleratedStep n)

/-- Bridge to the actual accelerated Collatz map, not merely formal words. -/
theorem follows_affine (w : List Bool) (n : Nat) (h : Follows w n) :
    (2 : Int) ^ w.length * (acceleratedOrbit w.length n : Int) =
      (3 : Int) ^ DeltaSpectrum.oddCount w * (n : Int) + numerator w := by
  induction w generalizing n with
  | nil => simp [numerator, C, accC, DeltaSpectrum.oddCount]
  | cons b w ih =>
    obtain ⟨hb, ht⟩ := h
    have hi := congrArg (fun z : Int => 2*z) (ih (acceleratedStep n) ht)
    have hc := numerator_append [b] w
    change numerator (b :: w) = _ at hc
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte] at hb
      have hs : 2 * (acceleratedStep n : Int) = (n : Int) := by
        simp only [acceleratedStep, if_pos hb]
        omega
      have hs' := congrArg (fun z : Int => (3 : Int)^DeltaSpectrum.oddCount w*z) hs
      simp only [List.length_cons, acceleratedOrbit_succ, DeltaSpectrum.oddCount,
        Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Int.pow_succ]
      simp only [List.length_singleton, Int.pow_one, show numerator [false] = 0 from rfl, Int.mul_zero, Int.zero_add] at hc
      rw [hc]
      simp only [Int.mul_add, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] at hi hs' ⊢
      omega
    · simp only [↓reduceIte] at hb
      have hs : 2 * (acceleratedStep n : Int) = 3 * (n : Int) + 1 := by
        simp only [acceleratedStep, if_neg (by omega : n % 2 ≠ 0)]
        omega
      have hs' := congrArg (fun z : Int => (3 : Int)^DeltaSpectrum.oddCount w*z) hs
      simp only [List.length_cons, acceleratedOrbit_succ, DeltaSpectrum.oddCount,
        ↓reduceIte, Int.pow_add, Int.pow_succ]
      simp only [List.length_singleton, Int.pow_one, show numerator [true] = 1 from rfl, Int.mul_one] at hc
      rw [hc]
      simp only [Int.pow_zero, Int.one_mul, Int.mul_add, Int.add_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] at hi hs' ⊢
      omega

theorem actual_cycle_exclusion (u v : List Bool) (k n : Nat)
    (hw : 0 < (padded u k v).length) (hD : defect u v ≠ 0)
    (hlarge : (defect u v).natAbs < (signedGap (padded u k v)).natAbs)
    (hword : Follows (padded u k v) n) :
    acceleratedOrbit (padded u k v).length n ≠ n := by
  intro hc
  apply excludes_cycle_equation u v k hw hD hlarge
  have h := follows_affine (padded u k v) n hword
  rw [hc] at h
  exact ⟨(n : Int), h⟩

/-! A complete infinite-family application, and negative controls. -/

def exampleBlock : List Bool := [false, false, true, true]
def exampleSuffix : List Bool := [true, true]

theorem example_parameters :
    signedGap exampleBlock = 7 ∧ numerator exampleBlock = 20 ∧
    signedGap exampleSuffix = -5 ∧ numerator exampleSuffix = 5 ∧
    defect exampleBlock exampleSuffix = 135 := by decide

theorem example_exact_cancellation (k : Nat) :
    Int.gcd (numerator (padded exampleBlock k exampleSuffix))
      (signedGap (padded exampleBlock k exampleSuffix)) =
    Int.gcd 135 (signedGap (padded exampleBlock k exampleSuffix)) := by
  have hlen : 0 < (padded exampleBlock k exampleSuffix).length := by
    induction k with
    | zero => decide
    | succ k ih => simp only [padded, List.length_append]; omega
  simpa only [example_parameters.2.2.2.2] using
    exact_cancellation exampleBlock exampleSuffix k (by decide) hlen (by decide)

/-- One finite calculation at k=2 excludes the entire infinite tail. -/
theorem example_tail (j : Nat) :
    ¬ signedGap (padded exampleBlock (2+j) exampleSuffix) ∣
      numerator (padded exampleBlock (2+j) exampleSuffix) :=
  tail_exclusion exampleBlock exampleSuffix 2 (by decide) (by decide)
    (by decide) (by decide) j

theorem example_no_integral_fixed_point (k : Nat) (hk : 0 < k) :
    ¬ signedGap (padded exampleBlock k exampleSuffix) ∣
      numerator (padded exampleBlock k exampleSuffix) := by
  by_cases h1 : k = 1
  · subst k; decide
  · have h := example_tail (k-2)
    simpa only [show 2+(k-2) = k by omega] using h

/-- No deterministic natural-number cycle has parity word `(0011)^k 11`
for any positive k. This family alone cannot settle the cycle problem. -/
theorem example_no_actual_cycle (k n : Nat) (hk : 0 < k)
    (hword : Follows (padded exampleBlock k exampleSuffix) n) :
    acceleratedOrbit (padded exampleBlock k exampleSuffix).length n ≠ n := by
  intro hc
  have h := follows_affine (padded exampleBlock k exampleSuffix) n hword
  rw [hc] at h
  apply example_no_integral_fixed_point k hk
  refine ⟨(n : Int), ?_⟩
  simp only [signedGap, Int.sub_mul]
  omega

/-- Coprimeness in the exact formula cannot simply be dropped. -/
theorem coprime_hypothesis_needed :
    let u := [true, true]
    let v := [false, false, true]
    Int.gcd (numerator (padded u 1 v)) (signedGap (padded u 1 v)) = 1 ∧
    Int.gcd (defect u v) (signedGap (padded u 1 v)) = 5 := by decide

/-- Pure repetition has zero defect: the uniform bound deliberately does
not exclude repetitions of an existing cycle. -/
theorem same_block_defect_zero (u : List Bool) : defect u u = 0 := by
  simp [defect, Int.mul_comm]

/-! Two independently repeated blocks. -/

def geometric (u : List Bool) : Nat → Int
  | 0 => 0
  | k+1 => (3 : Int)^(k * DeltaSpectrum.oddCount u) +
      (2 : Int)^u.length * geometric u k

theorem power_coefficients (u : List Bool) (k : Nat) :
    numerator (padded u k []) = numerator u * geometric u k ∧
    signedGap (padded u k []) = signedGap u * geometric u k := by
  induction k with
  | zero => simp [padded, numerator, C, accC, signedGap, DeltaSpectrum.oddCount, geometric]
  | succ k ih =>
    rw [padded, numerator_append, gap_append, ih.1, ih.2, geometric]
    simp only [padded_oddCount, DeltaSpectrum.oddCount, Nat.add_zero]
    constructor <;> cancellation_ring

theorem defect_power (u v : List Bool) (k : Nat) :
    defect u (padded v k []) = geometric v k * defect u v := by
  rw [defect, (power_coefficients v k).1, (power_coefficients v k).2]
  simp only [defect]
  cancellation_ring

theorem padded_as_append (u v : List Bool) (k : Nat) :
    padded u k v = padded u k [] ++ v := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [padded, ih, List.append_assoc]

theorem gap_rotation (u v : List Bool) : signedGap (u++v) = signedGap (v++u) := by
  simp only [signedGap, List.length_append, PhantomMediant.oddCount_append,
    Nat.add_comm]

private theorem cancellation_dvd_rotated (u v : List Bool)
    (hw : 0 < (u++v).length) :
    Int.gcd (numerator (u++v)) (signedGap (u++v)) ∣
      Int.gcd (numerator (v++u)) (signedGap (v++u)) := by
  let d := Int.gcd (numerator (u++v)) (signedGap (u++v))
  have hc : (d : Int) ∣ numerator (u++v) := Int.gcd_dvd_left _ _
  have hg : (d : Int) ∣ signedGap (u++v) := Int.gcd_dvd_right _ _
  have htwo : Int.gcd (d : Int) 2 = 1 := by
    apply Nat.dvd_one.mp
    have h := Int.gcd_dvd_gcd_of_dvd_left 2 hg
    rwa [gap_coprime_two (u++v) hw] at h
  have he : (2 : Int)^u.length * numerator (v++u) =
      (3 : Int)^DeltaSpectrum.oddCount u * numerator (u++v) +
        numerator u * signedGap (u++v) := by
    rw [numerator_append, numerator_append, gap_append]
    simp only [signedGap]
    cancellation_ring
  have hm : (d : Int) ∣ (2 : Int)^u.length * numerator (v++u) := by
    rw [he]
    exact Int.dvd_add (Int.dvd_trans hc (Int.dvd_mul_left _ _))
      (Int.dvd_trans hg (Int.dvd_mul_left _ _))
  have hr := Int.dvd_gcd_mul_iff_dvd_mul.mpr hm
  rw [Int.gcd_pow_right_of_gcd_eq_one htwo, Int.natCast_one, Int.one_mul] at hr
  apply Int.dvd_gcd hr
  rwa [← gap_rotation]

/-- Classical rotation invariance of the numerator–gap common divisor. -/
theorem cancellation_rotation (u v : List Bool) (hw : 0 < (u++v).length) :
    Int.gcd (numerator (u++v)) (signedGap (u++v)) =
      Int.gcd (numerator (v++u)) (signedGap (v++u)) := by
  apply Nat.dvd_antisymm (cancellation_dvd_rotated u v hw)
  apply cancellation_dvd_rotated v u
  simp only [List.length_append] at hw ⊢
  omega

/-- With both repetition counts free, only a common geometric-sum factor
can enlarge cancellation beyond the fixed two-block determinant. -/
theorem two_block_cancellation (u v : List Bool) (k l : Nat)
    (hw : 0 < (padded u k [] ++ padded v l []).length) :
    Int.gcd (numerator (padded u k [] ++ padded v l []))
      (signedGap (padded u k [] ++ padded v l [])) ∣
    (defect u v).natAbs * Nat.gcd (geometric u k).natAbs (geometric v l).natAbs := by
  have h1 := cancellation_dvd_defect u (padded v l []) k
    (by rwa [padded_as_append])
  rw [padded_as_append, defect_power, Int.natAbs_mul, Nat.mul_comm] at h1
  have h2 := cancellation_dvd_defect v (padded u k []) l
    (by rw [padded_as_append]; simp only [List.length_append] at hw ⊢; omega)
  rw [padded_as_append, ← cancellation_rotation _ _ hw, defect_power,
    Int.natAbs_mul, Nat.mul_comm] at h2
  have hflip : defect v u = -defect u v := by
    simp only [defect]
    cancellation_ring
  rw [hflip, Int.natAbs_neg] at h2
  have h := Nat.dvd_gcd h2 h1
  rwa [Nat.gcd_mul_left] at h

theorem two_block_coprime_bound (u v : List Bool) (k l : Nat)
    (hw : 0 < (padded u k [] ++ padded v l []).length)
    (hD : defect u v ≠ 0)
    (hcop : Nat.gcd (geometric u k).natAbs (geometric v l).natAbs = 1) :
    Int.gcd (numerator (padded u k [] ++ padded v l []))
      (signedGap (padded u k [] ++ padded v l [])) ≤ (defect u v).natAbs := by
  have h := two_block_cancellation u v k l hw
  rw [hcop, Nat.mul_one] at h
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hD) h

/-- Any actual cycle with two repeated blocks must satisfy this finite
divisibility obstruction. Both repetition counts are universally quantified. -/
theorem two_block_actual_cycle_constraint (u v : List Bool) (k l n : Nat)
    (hw : 0 < (padded u k [] ++ padded v l []).length)
    (hword : Follows (padded u k [] ++ padded v l []) n)
    (hcycle : acceleratedOrbit (padded u k [] ++ padded v l []).length n = n) :
    (signedGap (padded u k [] ++ padded v l [])).natAbs ∣
      (defect u v).natAbs * Nat.gcd (geometric u k).natAbs (geometric v l).natAbs := by
  have ha := follows_affine (padded u k [] ++ padded v l []) n hword
  rw [hcycle] at ha
  have hd : signedGap (padded u k [] ++ padded v l []) ∣
      numerator (padded u k [] ++ padded v l []) := by
    refine ⟨(n : Int), ?_⟩
    simp only [signedGap, Int.sub_mul]
    omega
  have h := two_block_cancellation u v k l hw
  rwa [Int.gcd_eq_natAbs_right_iff_dvd.mpr hd] at h

end Collatz.RepeatedBlockCancellation
