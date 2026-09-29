import Mathlib

/-!
# Sum–difference bounds

This module states the two-set inequality, the transfer to the small-sumset
exponent, the resulting bounds, and the finite multiscale inequality.
The definitions are concrete. The Challenge uses only Mathlib; the Solution
uses the accompanying proof development. See the proof paper for the argument.
-/

open Finset Pointwise

namespace SumDifferenceResults

def Admissible (t : ℝ) : Prop :=
  1 < t ∧ ∀ K : ℝ, 1 < K → ∃ c : ℝ, 0 < c ∧ ∀ n₀ : ℕ, ∃ A B : Finset ℤ,
    n₀ ≤ #A ∧ B.Nonempty ∧ (#(A + B) : ℝ) ≤ K * #A ∧
      c * (#(A + B) : ℝ) ^ t ≤ (#(A - B) : ℝ)

noncomputable def theta : ℝ := sSup {t : ℝ | Admissible t}

def pairCeilingExponents : Set ℝ :=
  {lam : ℝ | ∀ X Y : Finset ℤ, (#(X - Y) : ℝ) ≤ (#(X + Y) : ℝ) ^ lam}

noncomputable def pairExponent : ℝ := sInf pairCeilingExponents

/-- Theorem 2.1: the constant-free inequality in every abelian group. -/
theorem pair_bound {G : Type*} [AddCommGroup G] [DecidableEq G] (X Y : Finset G) :
    (#(X - Y) : ℝ) ≤
      (#(X + Y) : ℝ) ^ ((9451 * Real.exp 1 - 3286) / (5378 * Real.exp 1 + 787)) := by
  sorry

/-- Theorem 2.2, first assertion: transfer of any universal integer exponent. -/
theorem transfer_bound {lam : ℝ}
    (hpair : ∀ X Y : Finset ℤ, (#(X - Y) : ℝ) ≤ (#(X + Y) : ℝ) ^ lam) :
    theta ≤ 2 - 1 / lam := by
  sorry

/-- Theorem 2.2, second assertion: transfer at the infimum of the exponents. -/
theorem transfer_pair_exponent : theta ≤ 2 - 1 / pairExponent := by
  sorry

/-- The integer pair exponent is at most the universal abelian-group bound. -/
theorem pair_exponent_bound :
    pairExponent ≤ (9451 * Real.exp 1 - 3286) / (5378 * Real.exp 1 + 787) := by
  sorry

/-- Corollary 2.3: the explicit upper bound for the admissibility exponent. -/
theorem theta_bound :
    theta ≤ (13524 * Real.exp 1 - 7359) / (9451 * Real.exp 1 - 3286) := by
  sorry

/-- Proposition 3.5: the finite estimate valid at each fixed doubling constant. -/
theorem multiscale_bound {G : Type*} [AddCommGroup G] [DecidableEq G]
    {A B : Finset G} {K lam : ℝ} (hA : A.Nonempty) (hB : B.Nonempty)
    (hK : (#(A + B) : ℝ) ≤ K * #A) (hlam : 1 ≤ lam)
    (hpair : ∀ X ⊆ A, (#(X - B) : ℝ) ≤ (#(X + B) : ℝ) ^ lam) (J : ℕ) :
    (#(A - B) : ℝ) ^ J ≤
      (#(A + B) : ℝ) ^ J * (K ^ (2 * 4 ^ J) * #A) ^ (1 + J * (1 - 1 / lam)) := by
  sorry

end SumDifferenceResults
