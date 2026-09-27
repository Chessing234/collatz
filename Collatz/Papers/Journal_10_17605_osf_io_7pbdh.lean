import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Hamaguchi, Motohiro, "Mechanism of Singularity Formation in the Collatz Tree: The Structural Necessity of Peak 9232 and the 1822-Hub Hypothesis コラッツ樹形図における特異点形成のメカニズム ―最大値 9232 の正体と 1822 ハブ説―", 2026.

Title: Mechanism of Singularity Formation in the Collatz Tree: The Structural Necessity of Peak 9232 and the 1822-Hub Hypothesis コラッツ樹形図における特異点形成のメカニズム ―最大値 9232 の正体と 1822 ハブ説―

Abstract (from harvested metadata, truncated):
This project investigates the convergence mechanism of the Collatz sequence for initial values under 10,000. It proposes the "1822-Hub Hypothesis," identifying the value 1822 as a critical statistical singularity (junction) that captures approximately 16% of all trajectories in this range. By analyzing the structural necessity of the peak value 9232 and introducing the original "8m + alpha" index, this study demonstrates that convergence is not chaotic, but a highly designed system returning to the preceding routes established by the smallest odd numbers. 本プロジェクトは、初期値10,000以下のコラッツ数列における収束メカニズムを調査したものです。この範囲の軌跡の約16%を回収する重要な統計的特異点（結節点）として「1822」を特定し、「1822ハブ説」を提唱します。最大値9232の構造的必然性の分析と、独自指標「8m +...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.17605/osf.io/7pbdh
-/

namespace Collatz.Papers.Journal_10_17605_osf_io_7pbdh

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Hamaguchi, Motohiro, \"Mechanism of Singularity Formation in the Collatz Tree: The Structural Necessity of Peak 9232 and the 1822-Hub Hypothesis コラッツ樹形図における特異点形成のメカニズム ―最大値 9232 の正体と 1822 ハブ説―\", OSF Registries, DOI:10.17605/osf.io/7pbdh [2026]."

/-- Recorded main claim shell (structural); the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Journal_10_17605_osf_io_7pbdh
