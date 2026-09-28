module

public import Mathlib

/-!
# The exponent `θ` of Gyarmati, Hennecart and Ruzsa

The admissibility definition in the proof paper: admissible exponents and their supremum
`θ*` (the exponent of equation (5) of K. Gyarmati, F. Hennecart, I. Z. Ruzsa, *Sums and
differences of finite sets*).
-/

@[expose] public section

open Finset Pointwise

namespace SumsDifferences

/-- `θ` is *admissible* if `θ > 1` and for every `K > 1` there is a constant `c(K) > 0` such that
for every `n₀` there are finite sets of integers `A`, `B` with `B` nonempty, `|A| ≥ n₀`,
`|A + B| ≤ K |A|` and `|A - B| ≥ c(K) |A + B|^θ` (the admissibility definition in the proof paper). -/
def Admissible (θ : ℝ) : Prop :=
  1 < θ ∧ ∀ K : ℝ, 1 < K → ∃ c : ℝ, 0 < c ∧ ∀ n₀ : ℕ, ∃ A B : Finset ℤ,
    n₀ ≤ #A ∧ B.Nonempty ∧ (#(A + B) : ℝ) ≤ K * #A ∧
      c * (#(A + B) : ℝ) ^ θ ≤ (#(A - B) : ℝ)

/-- The exponent `θ*`: the supremum of all admissible exponents (`sSup ∅ = 0`). -/
noncomputable def theta : ℝ := sSup {t : ℝ | Admissible t}

end SumsDifferences
