import Collatz.Basic

/-! A registry for paper-derived lemma drafts. -/

namespace Collatz

/-- The first registry entry: the project goal itself. -/
def seedDraft : LemmaDraft where
  name := "collatz_conjecture_shell"
  source := "project seed"
  statement := "Every positive orbit reaches 1."
  status := "open"

/-- Lagarias (1985): the standard and accelerated formulations are equivalent. -/
def lagarias1985Draft : LemmaDraft where
  name := "lagarias_1985_equivalence_of_formulations"
  source := "Jeffrey C. Lagarias, The 3x+1 problem and its generalizations, Amer. Math. Monthly 92 (1985), 3--23."
  statement := "The standard Collatz conjecture (every positive orbit under C(n) = n/2 even, 3n+1 odd reaches 1) is equivalent to the accelerated conjecture (every n > 1 under T(n) = n/2 even, (3n+1)/2 odd reaches 1)."
  status := "proved: equivalence of standard and accelerated formulations"

/-- Lagarias (2003): the accelerated 3x+1 conjecture. -/
def lagarias2003BibliographyDraft : LemmaDraft where
  name := "lagarias_2003_three_x_plus_one_conjecture"
  source := "Jeffrey C. Lagarias, The 3x+1 problem: An annotated bibliography (1963--1999) (sorted by author), arXiv:math/0309224 [math.NT]."
  statement := "For every positive integer n > 1, the forward orbit under T(n) = (3n+1)/2 for odd n and T(n) = n/2 for even n includes 1."
  status := "open"

/-- Everett (1977): probabilistic analysis of the accelerated map. -/
def everett1977Draft : LemmaDraft where
  name := "everett_1977_stopping_time_density"
  source := "C. J. Everett, Iteration of the number-theoretic function f(2n)=n, f(2n+1)=3n+2, Adv. Math. 25 (1977), 42--45."
  statement := "The set of positive integers with a finite stopping time under the accelerated map has natural density 1."
  status := "partial: parity-vector congruence and equidistribution lemmas proved; main density theorem recorded"

/-- Terras (1976): stopping-time density theorem. -/
def terras1976Draft : LemmaDraft where
  name := "terras_1976_finite_stopping_time_density_one"
  source := "Riho Terras, A stopping time problem on the positive integers, Acta Arith. 30 (1976), 241--252."
  statement := "The set of positive integers n with a finite stopping time σ(n) = min{k ≥ 1 : T^k(n) < n} has natural density 1, where T(n) = (3n+1)/2 for odd n and T(n) = n/2 for even n."
  status := "partial: stopping-time closure lemmas, finite computations, and parity-vector equidistribution proved; main density-1 theorem recorded"

/-- Tao (2022): almost all orbits attain almost bounded values. -/
def tao2022Draft : LemmaDraft where
  name := "tao_2022_almost_bounded_orbits"
  source := "Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, Forum Math. Pi 10 (2022), e12."
  statement := "For every function f : ℕ⁺ → ℝ tending to +∞, the infimum of the Collatz orbit of n is at most f(n) for almost all n in the sense of logarithmic density."
  status := "open"

/-- Krasikov--Lagarias (2003): lower bound on the number of convergent values. -/
def krasikovLagarias2003Draft : LemmaDraft where
  name := "krasikov_lagarias_2003_lower_bound"
  source := "Ilia Krasikov and Jeffrey C. Lagarias, Bounds for the 3x+1 problem using difference inequalities, Acta Arith. 109 (2003), 237--258."
  statement := "There is an explicit positive rational constant c such that at least N^c positive integers ≤ N have finite total stopping time under the accelerated 3x+1 map."
  status := "open"

/-- Conway (1972): undecidability for generalized Collatz maps. -/
def conway1972Draft : LemmaDraft where
  name := "conway_1972_generalized_maps_undecidable"
  source := "John H. Conway, Unpredictable iterations, Proc. 1972 Number Theory Conference, Univ. Colorado, Boulder, pp. 49--52."
  statement := "For the family of generalized 3x+1 maps g with g(n) = (a_i n + b_i)/m on each residue class n ≡ i (mod m), the question whether a forward orbit reaches 1 is algorithmically undecidable."
  status := "open"

/-- Registry entries known to Lean. -/
def registry : List LemmaDraft :=
  [ seedDraft
  , lagarias1985Draft
  , lagarias2003BibliographyDraft
  , everett1977Draft
  , terras1976Draft
  , tao2022Draft
  , krasikovLagarias2003Draft
  , conway1972Draft
  ]

/-- The registry is nonempty. -/
theorem registry_nonempty : registry ≠ [] := by
  decide

end Collatz
