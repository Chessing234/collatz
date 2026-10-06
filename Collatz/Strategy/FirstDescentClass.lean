import Collatz.Structure.Congruence
import Collatz.Search.FirstDescentCertificate
import Collatz.Strategy.FirstDescentScale

/-!
# Exact first-descent certificates for complete dyadic classes

The soundness argument checks the endpoint and every proper prefix.
Each proper prefix has a noncontracting multiplier, while the endpoint
contracts. Together with a checked base first descent, these conditions
lift the base certificate to every natural class index.
-/

namespace Collatz.FirstDescentClass

/-- Noncontracting multipliers for every prefix before the proposed stopping time. -/
def prefixHeavyB (k r : Nat) : Bool :=
  (List.range k).all (fun j => decide (2 ^ j ≤ 3 ^ oddCount r j))

/-- A finite checker for exact first descent of the complete class `2^k*m+r`. -/
def classCertificateB (k r : Nat) : Bool :=
  decide (3 ^ oddCount r k < 2 ^ k) &&
    (Search.firstDescentB r k && prefixHeavyB k r)

/-- Specification of the prefix multiplier checker. -/
theorem prefixHeavyB_spec (k r : Nat) :
    prefixHeavyB k r = true ↔ ∀ j : Nat, j < k → 2 ^ j ≤ 3 ^ oddCount r j := by
  simp only [prefixHeavyB, List.all_eq_true, List.mem_range, decide_eq_true_eq]

/-- Specification of the complete-class checker. -/
theorem classCertificateB_spec (k r : Nat) :
    classCertificateB k r = true ↔
      3 ^ oddCount r k < 2 ^ k ∧ stoppingTime r k ∧
        ∀ j : Nat, j < k → 2 ^ j ≤ 3 ^ oddCount r j := by
  simp only [classCertificateB, Bool.and_eq_true, decide_eq_true_eq,
    Search.firstDescentB_spec, prefixHeavyB_spec]

/-- Factor the input modulus at any earlier depth. -/
theorem split_modulus {j k : Nat} (hj : j ≤ k) :
    2 ^ k = 2 ^ j * 2 ^ (k - j) := by
  rw [← Nat.pow_add]
  congr 1
  omega

/-- Exact action of every prefix on the complete input class. -/
theorem prefix_orbit {j k : Nat} (hj : j ≤ k) (r m : Nat) :
    acceleratedOrbit j (2 ^ k * m + r) =
      (3 ^ oddCount r j * 2 ^ (k - j)) * m + acceleratedOrbit j r := by
  have hi : 2 ^ k * m = 2 ^ j * (2 ^ (k - j) * m) := by
    rw [split_modulus hj]
    ac_rfl
  rw [hi, Congruence.accOrbit_pow_two_mul_add]
  ac_rfl

/-- A noncontracting prefix multiplier remains noncontracting after rescaling. -/
theorem scaled_multiplier_ge {j k r : Nat} (hj : j ≤ k)
    (hheavy : 2 ^ j ≤ 3 ^ oddCount r j) :
    2 ^ k ≤ 3 ^ oddCount r j * 2 ^ (k - j) := by
  rw [split_modulus hj]
  exact Nat.mul_le_mul_right _ hheavy

/-- A base prefix that has not dropped stays above the input on the whole class. -/
theorem class_prefix_no_drop {j k r : Nat} (hj : j ≤ k)
    (hheavy : 2 ^ j ≤ 3 ^ oddCount r j) (hbase : r ≤ acceleratedOrbit j r) (m : Nat) :
    2 ^ k * m + r ≤ acceleratedOrbit j (2 ^ k * m + r) := by
  rw [prefix_orbit hj]
  have hc := scaled_multiplier_ge hj hheavy
  have hm := Nat.mul_le_mul_right m hc
  omega

/-- A contracting endpoint that drops at the base drops on every class member. -/
theorem class_endpoint_drop {k r : Nat} (hc : 3 ^ oddCount r k < 2 ^ k)
    (hd : acceleratedOrbit k r < r) (m : Nat) :
    acceleratedOrbit k (2 ^ k * m + r) < 2 ^ k * m + r := by
  rw [Congruence.accOrbit_pow_two_mul_add]
  have hm := Nat.mul_le_mul_right m (Nat.le_of_lt hc)
  omega

/-- Universal soundness: one finite certificate fixes the exact time of every member. -/
theorem stoppingTime_of_classCertificate {k r : Nat}
    (h : classCertificateB k r = true) (m : Nat) : stoppingTime (2 ^ k * m + r) k := by
  obtain ⟨hc, hs, hp⟩ := (classCertificateB_spec k r).mp h
  refine ⟨hs.1, class_endpoint_drop hc hs.2.1 m, ?_⟩
  intro j _ hj
  have hbase := FirstDescentResidue.before_first_descent hs j hj
  have hnodrop := class_prefix_no_drop (Nat.le_of_lt hj) (hp j hj) hbase m
  omega

/-- The base checker and prefix constraints imply all class members have finite stopping time. -/
theorem finiteStoppingTime_of_classCertificate {k r : Nat}
    (h : classCertificateB k r = true) (m : Nat) : hasFiniteStoppingTime (2 ^ k * m + r) := by
  have hs := stoppingTime_of_classCertificate h m
  exact ⟨k, hs.1, hs.2.1⟩

/-- A checked class witness already encodes every proper prefix. -/
example : Search.firstDescentB 3 4 = true ∧ classCertificateB 4 3 = true := by decide

end Collatz.FirstDescentClass
