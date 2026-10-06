import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch099

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 6567. -/
theorem certificate_6567 : classCertificateB 10 6567 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6567 (m : Nat) : stoppingTime (2 ^ 10 * m + 6567) 10 :=
  stoppingTime_of_classCertificate certificate_6567 m

/-- Checked base and every prefix for input 6569. -/
theorem certificate_6569 : classCertificateB 2 6569 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6569 (m : Nat) : stoppingTime (2 ^ 2 * m + 6569) 2 :=
  stoppingTime_of_classCertificate certificate_6569 m

/-- Checked base and every prefix for input 6571. -/
theorem certificate_6571 : classCertificateB 5 6571 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6571 (m : Nat) : stoppingTime (2 ^ 5 * m + 6571) 5 :=
  stoppingTime_of_classCertificate certificate_6571 m

/-- Checked base and every prefix for input 6573. -/
theorem certificate_6573 : classCertificateB 2 6573 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6573 (m : Nat) : stoppingTime (2 ^ 2 * m + 6573) 2 :=
  stoppingTime_of_classCertificate certificate_6573 m

/-- Checked base and every prefix for input 6575. -/
theorem certificate_6575 : classCertificateB 8 6575 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6575 (m : Nat) : stoppingTime (2 ^ 8 * m + 6575) 8 :=
  stoppingTime_of_classCertificate certificate_6575 m

/-- Checked base and every prefix for input 6577. -/
theorem certificate_6577 : classCertificateB 2 6577 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6577 (m : Nat) : stoppingTime (2 ^ 2 * m + 6577) 2 :=
  stoppingTime_of_classCertificate certificate_6577 m

/-- Checked base and every prefix for input 6579. -/
theorem certificate_6579 : classCertificateB 4 6579 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6579 (m : Nat) : stoppingTime (2 ^ 4 * m + 6579) 4 :=
  stoppingTime_of_classCertificate certificate_6579 m

/-- Checked base and every prefix for input 6581. -/
theorem certificate_6581 : classCertificateB 2 6581 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6581 (m : Nat) : stoppingTime (2 ^ 2 * m + 6581) 2 :=
  stoppingTime_of_classCertificate certificate_6581 m

/-- Checked base and every prefix for input 6583. -/
theorem certificate_6583 : classCertificateB 5 6583 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6583 (m : Nat) : stoppingTime (2 ^ 5 * m + 6583) 5 :=
  stoppingTime_of_classCertificate certificate_6583 m

/-- Checked base and every prefix for input 6585. -/
theorem certificate_6585 : classCertificateB 2 6585 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6585 (m : Nat) : stoppingTime (2 ^ 2 * m + 6585) 2 :=
  stoppingTime_of_classCertificate certificate_6585 m

/-- Checked base and every prefix for input 6587. -/
theorem certificate_6587 : classCertificateB 7 6587 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6587 (m : Nat) : stoppingTime (2 ^ 7 * m + 6587) 7 :=
  stoppingTime_of_classCertificate certificate_6587 m

/-- Checked base and every prefix for input 6589. -/
theorem certificate_6589 : classCertificateB 2 6589 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6589 (m : Nat) : stoppingTime (2 ^ 2 * m + 6589) 2 :=
  stoppingTime_of_classCertificate certificate_6589 m

/-- Checked base and every prefix for input 6591. -/
theorem certificate_6591 : classCertificateB 46 6591 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6591 (m : Nat) : stoppingTime (2 ^ 46 * m + 6591) 46 :=
  stoppingTime_of_classCertificate certificate_6591 m

/-- Checked base and every prefix for input 6593. -/
theorem certificate_6593 : classCertificateB 2 6593 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6593 (m : Nat) : stoppingTime (2 ^ 2 * m + 6593) 2 :=
  stoppingTime_of_classCertificate certificate_6593 m

/-- Checked base and every prefix for input 6595. -/
theorem certificate_6595 : classCertificateB 4 6595 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6595 (m : Nat) : stoppingTime (2 ^ 4 * m + 6595) 4 :=
  stoppingTime_of_classCertificate certificate_6595 m

/-- Checked base and every prefix for input 6597. -/
theorem certificate_6597 : classCertificateB 2 6597 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6597 (m : Nat) : stoppingTime (2 ^ 2 * m + 6597) 2 :=
  stoppingTime_of_classCertificate certificate_6597 m

/-- Checked base and every prefix for input 6599. -/
theorem certificate_6599 : classCertificateB 8 6599 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6599 (m : Nat) : stoppingTime (2 ^ 8 * m + 6599) 8 :=
  stoppingTime_of_classCertificate certificate_6599 m

/-- Checked base and every prefix for input 6601. -/
theorem certificate_6601 : classCertificateB 2 6601 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6601 (m : Nat) : stoppingTime (2 ^ 2 * m + 6601) 2 :=
  stoppingTime_of_classCertificate certificate_6601 m

/-- Checked base and every prefix for input 6603. -/
theorem certificate_6603 : classCertificateB 5 6603 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6603 (m : Nat) : stoppingTime (2 ^ 5 * m + 6603) 5 :=
  stoppingTime_of_classCertificate certificate_6603 m

/-- Checked base and every prefix for input 6605. -/
theorem certificate_6605 : classCertificateB 2 6605 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6605 (m : Nat) : stoppingTime (2 ^ 2 * m + 6605) 2 :=
  stoppingTime_of_classCertificate certificate_6605 m

/-- Checked base and every prefix for input 6607. -/
theorem certificate_6607 : classCertificateB 13 6607 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6607 (m : Nat) : stoppingTime (2 ^ 13 * m + 6607) 13 :=
  stoppingTime_of_classCertificate certificate_6607 m

/-- Checked base and every prefix for input 6609. -/
theorem certificate_6609 : classCertificateB 2 6609 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6609 (m : Nat) : stoppingTime (2 ^ 2 * m + 6609) 2 :=
  stoppingTime_of_classCertificate certificate_6609 m

/-- Checked base and every prefix for input 6611. -/
theorem certificate_6611 : classCertificateB 4 6611 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6611 (m : Nat) : stoppingTime (2 ^ 4 * m + 6611) 4 :=
  stoppingTime_of_classCertificate certificate_6611 m

/-- Checked base and every prefix for input 6613. -/
theorem certificate_6613 : classCertificateB 2 6613 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6613 (m : Nat) : stoppingTime (2 ^ 2 * m + 6613) 2 :=
  stoppingTime_of_classCertificate certificate_6613 m

/-- Checked base and every prefix for input 6615. -/
theorem certificate_6615 : classCertificateB 5 6615 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6615 (m : Nat) : stoppingTime (2 ^ 5 * m + 6615) 5 :=
  stoppingTime_of_classCertificate certificate_6615 m

/-- Checked base and every prefix for input 6617. -/
theorem certificate_6617 : classCertificateB 2 6617 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6617 (m : Nat) : stoppingTime (2 ^ 2 * m + 6617) 2 :=
  stoppingTime_of_classCertificate certificate_6617 m

/-- Checked base and every prefix for input 6619. -/
theorem certificate_6619 : classCertificateB 8 6619 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6619 (m : Nat) : stoppingTime (2 ^ 8 * m + 6619) 8 :=
  stoppingTime_of_classCertificate certificate_6619 m

/-- Checked base and every prefix for input 6621. -/
theorem certificate_6621 : classCertificateB 2 6621 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6621 (m : Nat) : stoppingTime (2 ^ 2 * m + 6621) 2 :=
  stoppingTime_of_classCertificate certificate_6621 m

/-- Checked base and every prefix for input 6623. -/
theorem certificate_6623 : classCertificateB 26 6623 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6623 (m : Nat) : stoppingTime (2 ^ 26 * m + 6623) 26 :=
  stoppingTime_of_classCertificate certificate_6623 m

/-- Checked base and every prefix for input 6625. -/
theorem certificate_6625 : classCertificateB 2 6625 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6625 (m : Nat) : stoppingTime (2 ^ 2 * m + 6625) 2 :=
  stoppingTime_of_classCertificate certificate_6625 m

/-- Checked base and every prefix for input 6627. -/
theorem certificate_6627 : classCertificateB 4 6627 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6627 (m : Nat) : stoppingTime (2 ^ 4 * m + 6627) 4 :=
  stoppingTime_of_classCertificate certificate_6627 m

/-- Checked base and every prefix for input 6629. -/
theorem certificate_6629 : classCertificateB 2 6629 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6629 (m : Nat) : stoppingTime (2 ^ 2 * m + 6629) 2 :=
  stoppingTime_of_classCertificate certificate_6629 m

/-- Checked base and every prefix for input 6631. -/
theorem certificate_6631 : classCertificateB 13 6631 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_6631 (m : Nat) : stoppingTime (2 ^ 13 * m + 6631) 13 :=
  stoppingTime_of_classCertificate certificate_6631 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 6567 6633 := by
  intro n hlo hhi hodd
  have hn : n = 6567 ∨ n = 6569 ∨ n = 6571 ∨ n = 6573 ∨ n = 6575 ∨ n = 6577 ∨ n = 6579 ∨ n = 6581 ∨ n = 6583 ∨ n = 6585 ∨ n = 6587 ∨ n = 6589 ∨ n = 6591 ∨ n = 6593 ∨ n = 6595 ∨ n = 6597 ∨ n = 6599 ∨ n = 6601 ∨ n = 6603 ∨ n = 6605 ∨ n = 6607 ∨ n = 6609 ∨ n = 6611 ∨ n = 6613 ∨ n = 6615 ∨ n = 6617 ∨ n = 6619 ∨ n = 6621 ∨ n = 6623 ∨ n = 6625 ∨ n = 6627 ∨ n = 6629 ∨ n = 6631 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨10, witness_of_certificate certificate_6567⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6569⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6571⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6573⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_6575⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6577⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6579⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6581⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6583⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6585⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_6587⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6589⟩
  · subst n
    exact ⟨46, witness_of_certificate certificate_6591⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6593⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6595⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6597⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_6599⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6601⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6603⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6605⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_6607⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6609⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6611⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6613⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_6615⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6617⟩
  · subst n
    exact ⟨8, witness_of_certificate certificate_6619⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6621⟩
  · subst n
    exact ⟨26, witness_of_certificate certificate_6623⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6625⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_6627⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_6629⟩
  · subst n
    exact ⟨13, witness_of_certificate certificate_6631⟩

end Collatz.Research.CoefficientDescent.Batch099
