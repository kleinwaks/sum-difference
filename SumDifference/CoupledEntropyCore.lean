/-
# The coupled pair and the grid `h(i, j)` (§4.2 of the proof paper)

`P μ ν i j = μ^i ν^j` (the law of `i` copies of `μ` plus `j` copies of `ν`, so that
`h(i, j) = ent (P μ ν i j)`), the choice of one pair per difference (`exists_coupling`,
Lemma 4.1), the coupled Ruzsa triangle inequality on the grid (`link`, Lemma 4.2) and the grid
concavity lemma (`grid_concave`, Lemma 4.3).  The general Madiman and monotonicity rows for
arbitrary count vectors (`mad`, `mono`) are also recorded; the proof of the paper uses only their
unit-step cases, through `grid_concave`.
-/
import Mathlib
import SumDifference.EntropySumsetCalculus

open Finset Real Pointwise

namespace SumsDifferences

namespace CoupledEntropy


variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The law of `i` copies of `μ` plus `j` copies of `ν`. -/
noncomputable def P (μ ν : AddMonoidAlgebra ℝ G) (i j : ℕ) : AddMonoidAlgebra ℝ G :=
  μ ^ i * ν ^ j

omit [DecidableEq G] in
theorem P_mul (μ ν : AddMonoidAlgebra ℝ G) (i j k l : ℕ) :
    P μ ν i j * P μ ν k l = P μ ν (i + k) (j + l) := by
  simp only [P, pow_add]; ring

theorem isLaw_P {μ ν : AddMonoidAlgebra ℝ G} (hμ : IsLaw μ) (hν : IsLaw ν) (i j : ℕ) :
    IsLaw (P μ ν i j) :=
  (hμ.pow i).mul (hν.pow j)

/-- Madiman's inequality for count vectors `u = (i₁, j₁)`, `w = (i₂, j₂)`, `v = (i₃, j₃)`:
`h(u + w + v) + h(w) ≤ h(u + w) + h(w + v)`. -/
theorem mad {μ ν : AddMonoidAlgebra ℝ G} (hμ : IsLaw μ) (hν : IsLaw ν)
    (i₁ j₁ i₂ j₂ i₃ j₃ : ℕ) :
    ent (P μ ν (i₁ + i₂ + i₃) (j₁ + j₂ + j₃)) + ent (P μ ν i₂ j₂)
      ≤ ent (P μ ν (i₁ + i₂) (j₁ + j₂)) + ent (P μ ν (i₂ + i₃) (j₂ + j₃)) := by
  have h := ent_madiman (isLaw_P hμ hν i₁ j₁) (isLaw_P hμ hν i₂ j₂) (isLaw_P hμ hν i₃ j₃)
  rwa [P_mul, P_mul, P_mul] at h

/-- Monotonicity for count vectors. -/
theorem mono {μ ν : AddMonoidAlgebra ℝ G} (hμ : IsLaw μ) (hν : IsLaw ν) (i j k l : ℕ) :
    ent (P μ ν i j) ≤ ent (P μ ν (i + k) (j + l)) := by
  have h := ent_le_ent_mul (isLaw_P hμ hν i j) (isLaw_P hμ hν k l)
  rwa [P_mul] at h

/-- **Unit-step concavity**: adding one more independent copy of `α` to `β`
increases the entropy by at most as much as the previous copy did,
`H(α * α * β) + H(β) ≤ 2 H(α * β)`.  This is Madiman's inequality with `U, W` two copies of `α`. -/
theorem ent_concave_step {α β : AddMonoidAlgebra ℝ G} (hα : IsLaw α) (hβ : IsLaw β) :
    ent (α * α * β) + ent β ≤ 2 * ent (α * β) := by
  have h := ent_madiman hα hβ hα
  rw [show α * β * α = α * α * β by ring, show β * α = α * β by ring] at h
  linarith

/-- **Grid concavity lemma** (Lemma 4.3).  The array `h(i, j) = H(μ^i ν^j)` is discretely
concave and nondecreasing along each axis.  These are the only properties of `h` used by the grid
lemma (Proposition 5.1), besides the links and the two-copy inequality. -/
theorem grid_concave {μ ν : AddMonoidAlgebra ℝ G} (hμ : IsLaw μ) (hν : IsLaw ν) (i j : ℕ) :
    (ent (P μ ν (i + 2) j) + ent (P μ ν i j) ≤ 2 * ent (P μ ν (i + 1) j)) ∧
    (ent (P μ ν i (j + 2)) + ent (P μ ν i j) ≤ 2 * ent (P μ ν i (j + 1))) ∧
    ent (P μ ν i j) ≤ ent (P μ ν (i + 1) j) ∧ ent (P μ ν i j) ≤ ent (P μ ν i (j + 1)) := by
  have hP := isLaw_P hμ hν i j
  have e1 : μ * μ * P μ ν i j = P μ ν (i + 2) j := by simp only [P, pow_succ]; ring
  have e2 : μ * P μ ν i j = P μ ν (i + 1) j := by simp only [P, pow_succ]; ring
  have e3 : ν * ν * P μ ν i j = P μ ν i (j + 2) := by simp only [P, pow_succ]; ring
  have e4 : ν * P μ ν i j = P μ ν i (j + 1) := by simp only [P, pow_succ]; ring
  have c1 := ent_concave_step hμ hP
  have c2 := ent_concave_step hν hP
  have m1 := ent_le_ent_mul hP hμ
  have m2 := ent_le_ent_mul hP hν
  rw [e1, e2] at c1
  rw [e3, e4] at c2
  rw [mul_comm, e2] at m1
  rw [mul_comm, e4] at m2
  exact ⟨c1, c2, m1, m2⟩

/-- The coupled Ruzsa triangle inequality on the grid (Lemma 4.2):
`L + h(i, j) ≤ h(i + 1, j) + h(i, j + 1)`. -/
theorem link {Γ : Finset (G × G)} (hΓ : Γ.Nonempty)
    (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') (i j : ℕ) :
    Real.log #Γ + ent (P (margFst Γ) (margSnd Γ) i j)
      ≤ ent (P (margFst Γ) (margSnd Γ) (i + 1) j)
        + ent (P (margFst Γ) (margSnd Γ) i (j + 1)) := by
  have h := coupled_link hΓ hinj (isLaw_P (isLaw_margFst hΓ) (isLaw_margSnd hΓ) i j)
  have e1 : margFst Γ * P (margFst Γ) (margSnd Γ) i j = P (margFst Γ) (margSnd Γ) (i + 1) j := by
    simp only [P, pow_succ]; ring
  have e2 : margSnd Γ * P (margFst Γ) (margSnd Γ) i j = P (margFst Γ) (margSnd Γ) i (j + 1) := by
    simp only [P, pow_succ]; ring
  rwa [e1, e2] at h

/-- One representative pair for every difference (Lemma 4.1). -/
theorem exists_coupling (X Y : Finset G) :
    ∃ Γ : Finset (G × G), Γ ⊆ X ×ˢ Y ∧ #Γ = #(X - Y) ∧
      ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q' := by
  classical
  have hrep : ∀ z ∈ X - Y, ∃ q ∈ X ×ˢ Y, q.1 - q.2 = z := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_sub.mp hz
    exact ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩
  let r : G → G × G := fun z => if h : ∃ q ∈ X ×ˢ Y, q.1 - q.2 = z then h.choose else 0
  have hr : ∀ z ∈ X - Y, r z ∈ X ×ˢ Y ∧ (r z).1 - (r z).2 = z := by
    intro z hz
    have h := hrep z hz
    simp only [r, dif_pos h]
    exact h.choose_spec
  have hinj : Set.InjOn r ((X - Y : Finset G) : Set G) := by
    intro z hz z' hz' e
    rw [Finset.mem_coe] at hz hz'
    rw [← (hr z hz).2, ← (hr z' hz').2, e]
  refine ⟨(X - Y).image r, ?_, Finset.card_image_of_injOn hinj, ?_⟩
  · intro q hq
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq
    exact (hr z hz).1
  · intro q hq q' hq' e
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hq'
    rw [(hr z hz).2, (hr z' hz').2] at e
    rw [e]

end CoupledEntropy

end SumsDifferences
