import Collatz.Research.CoefficientDescent.Basic

namespace Collatz.Research.CoefficientDescent.Batch054

open FirstDescentClass

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Checked base and every prefix for input 3551. -/
theorem certificate_3551 : classCertificateB 13 3551 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3551 (m : Nat) : stoppingTime (2 ^ 13 * m + 3551) 13 :=
  stoppingTime_of_classCertificate certificate_3551 m

/-- Checked base and every prefix for input 3553. -/
theorem certificate_3553 : classCertificateB 2 3553 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3553 (m : Nat) : stoppingTime (2 ^ 2 * m + 3553) 2 :=
  stoppingTime_of_classCertificate certificate_3553 m

/-- Checked base and every prefix for input 3555. -/
theorem certificate_3555 : classCertificateB 4 3555 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3555 (m : Nat) : stoppingTime (2 ^ 4 * m + 3555) 4 :=
  stoppingTime_of_classCertificate certificate_3555 m

/-- Checked base and every prefix for input 3557. -/
theorem certificate_3557 : classCertificateB 2 3557 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3557 (m : Nat) : stoppingTime (2 ^ 2 * m + 3557) 2 :=
  stoppingTime_of_classCertificate certificate_3557 m

/-- Checked base and every prefix for input 3559. -/
theorem certificate_3559 : classCertificateB 12 3559 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3559 (m : Nat) : stoppingTime (2 ^ 12 * m + 3559) 12 :=
  stoppingTime_of_classCertificate certificate_3559 m

/-- Checked base and every prefix for input 3561. -/
theorem certificate_3561 : classCertificateB 2 3561 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3561 (m : Nat) : stoppingTime (2 ^ 2 * m + 3561) 2 :=
  stoppingTime_of_classCertificate certificate_3561 m

/-- Checked base and every prefix for input 3563. -/
theorem certificate_3563 : classCertificateB 5 3563 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3563 (m : Nat) : stoppingTime (2 ^ 5 * m + 3563) 5 :=
  stoppingTime_of_classCertificate certificate_3563 m

/-- Checked base and every prefix for input 3565. -/
theorem certificate_3565 : classCertificateB 2 3565 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3565 (m : Nat) : stoppingTime (2 ^ 2 * m + 3565) 2 :=
  stoppingTime_of_classCertificate certificate_3565 m

/-- Checked base and every prefix for input 3567. -/
theorem certificate_3567 : classCertificateB 35 3567 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3567 (m : Nat) : stoppingTime (2 ^ 35 * m + 3567) 35 :=
  stoppingTime_of_classCertificate certificate_3567 m

/-- Checked base and every prefix for input 3569. -/
theorem certificate_3569 : classCertificateB 2 3569 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3569 (m : Nat) : stoppingTime (2 ^ 2 * m + 3569) 2 :=
  stoppingTime_of_classCertificate certificate_3569 m

/-- Checked base and every prefix for input 3571. -/
theorem certificate_3571 : classCertificateB 4 3571 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3571 (m : Nat) : stoppingTime (2 ^ 4 * m + 3571) 4 :=
  stoppingTime_of_classCertificate certificate_3571 m

/-- Checked base and every prefix for input 3573. -/
theorem certificate_3573 : classCertificateB 2 3573 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3573 (m : Nat) : stoppingTime (2 ^ 2 * m + 3573) 2 :=
  stoppingTime_of_classCertificate certificate_3573 m

/-- Checked base and every prefix for input 3575. -/
theorem certificate_3575 : classCertificateB 5 3575 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3575 (m : Nat) : stoppingTime (2 ^ 5 * m + 3575) 5 :=
  stoppingTime_of_classCertificate certificate_3575 m

/-- Checked base and every prefix for input 3577. -/
theorem certificate_3577 : classCertificateB 2 3577 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3577 (m : Nat) : stoppingTime (2 ^ 2 * m + 3577) 2 :=
  stoppingTime_of_classCertificate certificate_3577 m

/-- Checked base and every prefix for input 3579. -/
theorem certificate_3579 : classCertificateB 10 3579 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3579 (m : Nat) : stoppingTime (2 ^ 10 * m + 3579) 10 :=
  stoppingTime_of_classCertificate certificate_3579 m

/-- Checked base and every prefix for input 3581. -/
theorem certificate_3581 : classCertificateB 2 3581 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3581 (m : Nat) : stoppingTime (2 ^ 2 * m + 3581) 2 :=
  stoppingTime_of_classCertificate certificate_3581 m

/-- Checked base and every prefix for input 3583. -/
theorem certificate_3583 : classCertificateB 18 3583 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3583 (m : Nat) : stoppingTime (2 ^ 18 * m + 3583) 18 :=
  stoppingTime_of_classCertificate certificate_3583 m

/-- Checked base and every prefix for input 3585. -/
theorem certificate_3585 : classCertificateB 2 3585 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3585 (m : Nat) : stoppingTime (2 ^ 2 * m + 3585) 2 :=
  stoppingTime_of_classCertificate certificate_3585 m

/-- Checked base and every prefix for input 3587. -/
theorem certificate_3587 : classCertificateB 4 3587 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3587 (m : Nat) : stoppingTime (2 ^ 4 * m + 3587) 4 :=
  stoppingTime_of_classCertificate certificate_3587 m

/-- Checked base and every prefix for input 3589. -/
theorem certificate_3589 : classCertificateB 2 3589 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3589 (m : Nat) : stoppingTime (2 ^ 2 * m + 3589) 2 :=
  stoppingTime_of_classCertificate certificate_3589 m

/-- Checked base and every prefix for input 3591. -/
theorem certificate_3591 : classCertificateB 7 3591 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3591 (m : Nat) : stoppingTime (2 ^ 7 * m + 3591) 7 :=
  stoppingTime_of_classCertificate certificate_3591 m

/-- Checked base and every prefix for input 3593. -/
theorem certificate_3593 : classCertificateB 2 3593 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3593 (m : Nat) : stoppingTime (2 ^ 2 * m + 3593) 2 :=
  stoppingTime_of_classCertificate certificate_3593 m

/-- Checked base and every prefix for input 3595. -/
theorem certificate_3595 : classCertificateB 5 3595 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3595 (m : Nat) : stoppingTime (2 ^ 5 * m + 3595) 5 :=
  stoppingTime_of_classCertificate certificate_3595 m

/-- Checked base and every prefix for input 3597. -/
theorem certificate_3597 : classCertificateB 2 3597 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3597 (m : Nat) : stoppingTime (2 ^ 2 * m + 3597) 2 :=
  stoppingTime_of_classCertificate certificate_3597 m

/-- Checked base and every prefix for input 3599. -/
theorem certificate_3599 : classCertificateB 7 3599 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3599 (m : Nat) : stoppingTime (2 ^ 7 * m + 3599) 7 :=
  stoppingTime_of_classCertificate certificate_3599 m

/-- Checked base and every prefix for input 3601. -/
theorem certificate_3601 : classCertificateB 2 3601 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3601 (m : Nat) : stoppingTime (2 ^ 2 * m + 3601) 2 :=
  stoppingTime_of_classCertificate certificate_3601 m

/-- Checked base and every prefix for input 3603. -/
theorem certificate_3603 : classCertificateB 4 3603 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3603 (m : Nat) : stoppingTime (2 ^ 4 * m + 3603) 4 :=
  stoppingTime_of_classCertificate certificate_3603 m

/-- Checked base and every prefix for input 3605. -/
theorem certificate_3605 : classCertificateB 2 3605 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3605 (m : Nat) : stoppingTime (2 ^ 2 * m + 3605) 2 :=
  stoppingTime_of_classCertificate certificate_3605 m

/-- Checked base and every prefix for input 3607. -/
theorem certificate_3607 : classCertificateB 5 3607 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3607 (m : Nat) : stoppingTime (2 ^ 5 * m + 3607) 5 :=
  stoppingTime_of_classCertificate certificate_3607 m

/-- Checked base and every prefix for input 3609. -/
theorem certificate_3609 : classCertificateB 2 3609 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3609 (m : Nat) : stoppingTime (2 ^ 2 * m + 3609) 2 :=
  stoppingTime_of_classCertificate certificate_3609 m

/-- Checked base and every prefix for input 3611. -/
theorem certificate_3611 : classCertificateB 15 3611 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3611 (m : Nat) : stoppingTime (2 ^ 15 * m + 3611) 15 :=
  stoppingTime_of_classCertificate certificate_3611 m

/-- Checked base and every prefix for input 3613. -/
theorem certificate_3613 : classCertificateB 2 3613 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3613 (m : Nat) : stoppingTime (2 ^ 2 * m + 3613) 2 :=
  stoppingTime_of_classCertificate certificate_3613 m

/-- Checked base and every prefix for input 3615. -/
theorem certificate_3615 : classCertificateB 18 3615 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3615 (m : Nat) : stoppingTime (2 ^ 18 * m + 3615) 18 :=
  stoppingTime_of_classCertificate certificate_3615 m

/-- Checked base and every prefix for input 3617. -/
theorem certificate_3617 : classCertificateB 2 3617 = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_3617 (m : Nat) : stoppingTime (2 ^ 2 * m + 3617) 2 :=
  stoppingTime_of_classCertificate certificate_3617 m

/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange 3551 3619 := by
  intro n hlo hhi hodd
  have hn : n = 3551 ∨ n = 3553 ∨ n = 3555 ∨ n = 3557 ∨ n = 3559 ∨ n = 3561 ∨ n = 3563 ∨ n = 3565 ∨ n = 3567 ∨ n = 3569 ∨ n = 3571 ∨ n = 3573 ∨ n = 3575 ∨ n = 3577 ∨ n = 3579 ∨ n = 3581 ∨ n = 3583 ∨ n = 3585 ∨ n = 3587 ∨ n = 3589 ∨ n = 3591 ∨ n = 3593 ∨ n = 3595 ∨ n = 3597 ∨ n = 3599 ∨ n = 3601 ∨ n = 3603 ∨ n = 3605 ∨ n = 3607 ∨ n = 3609 ∨ n = 3611 ∨ n = 3613 ∨ n = 3615 ∨ n = 3617 := by omega
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst n
    exact ⟨13, witness_of_certificate certificate_3551⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3553⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_3555⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3557⟩
  · subst n
    exact ⟨12, witness_of_certificate certificate_3559⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3561⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_3563⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3565⟩
  · subst n
    exact ⟨35, witness_of_certificate certificate_3567⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3569⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_3571⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3573⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_3575⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3577⟩
  · subst n
    exact ⟨10, witness_of_certificate certificate_3579⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3581⟩
  · subst n
    exact ⟨18, witness_of_certificate certificate_3583⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3585⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_3587⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3589⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_3591⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3593⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_3595⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3597⟩
  · subst n
    exact ⟨7, witness_of_certificate certificate_3599⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3601⟩
  · subst n
    exact ⟨4, witness_of_certificate certificate_3603⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3605⟩
  · subst n
    exact ⟨5, witness_of_certificate certificate_3607⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3609⟩
  · subst n
    exact ⟨15, witness_of_certificate certificate_3611⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3613⟩
  · subst n
    exact ⟨18, witness_of_certificate certificate_3615⟩
  · subst n
    exact ⟨2, witness_of_certificate certificate_3617⟩

end Collatz.Research.CoefficientDescent.Batch054
