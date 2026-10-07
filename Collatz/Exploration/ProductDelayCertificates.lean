import Collatz.Exploration.FloorProductDescent

/-! Exact finite first-event certificates for observed product-test delays.
No assertion is made that these are the only delayed sources. -/
set_option maxRecDepth 10000

namespace Collatz.Exploration.ProductDelayCertificates
open FloorAffineError FloorProductError

def certificate (n j : Nat) : Prop :=
  3^oddCount n j*weight n^oddCount n j < 2^j*base n^oddCount n j

instance (n j : Nat) : Decidable (certificate n j) := inferInstanceAs (Decidable (_ < _))

def FirstCertificate (n j : Nat) : Prop :=
  certificate n j ∧ ∀ i : Fin j, ¬ certificate n i.val

instance (n j : Nat) : Decidable (FirstCertificate n j) :=
  inferInstanceAs (Decidable (_ ∧ _))

def FirstDescent (n j : Nat) : Prop :=
  acceleratedOrbit j n < n ∧ ∀ i : Fin j, n ≤ acceleratedOrbit i.val n

instance (n j : Nat) : Decidable (FirstDescent n j) :=
  inferInstanceAs (Decidable (_ ∧ _))

set_option maxHeartbeats 0 in
theorem delay27 : FirstDescent 27 59 ∧ FirstCertificate 27 65 := by decide

set_option maxHeartbeats 0 in
theorem delay31 : FirstDescent 31 56 ∧ FirstCertificate 31 61 := by decide

set_option maxHeartbeats 0 in
theorem delay47 : FirstDescent 47 54 ∧ FirstCertificate 47 55 := by decide

set_option maxHeartbeats 0 in
theorem delay63 : FirstDescent 63 54 ∧ FirstCertificate 63 56 := by decide

/-- Any first product certificate follows some genuine descent, by the general theorem. -/
theorem certificate_sound {n j : Nat} (hn : 0 < n) (hc : FirstCertificate n j) :
    ∃ i, i ≤ j ∧ acceleratedOrbit i n < n :=
  FloorProductDescent.descent_before hn hc.1

end Collatz.Exploration.ProductDelayCertificates
