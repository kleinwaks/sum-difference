/-
# Product laws: independence and additivity of entropy

The product `p ⊗ r` of two laws (`productLaw`), the product formula for the law of
`(f(ω), g(λ))` (`pushWeight_productLaw_pair`) and **additivity** `H(f ⊗ g) = H(f) + H(g)`
(`pushEntropy_productLaw_pair`, with the corollaries `pushEntropy_productLaw_fst/snd`).

Used by `EntropySumsetCalculus.lean` for the independence statements of §3 of
the proof paper (fact (E2)).
-/
import Mathlib
import SumDifference.FinEntropy
import SumDifference.JointEntropy
import SumDifference.CondEntropy

open Finset

namespace SumsDifferences

variable {ι ν α β γ : Type*}

/-! ## Product laws -/

/-- The product of two weight functions. -/
noncomputable def productLaw (p : ι → ℝ) (r : ν → ℝ) (z : ι × ν) : ℝ := p z.1 * r z.2

theorem productLaw_nonneg {p : ι → ℝ} {r : ν → ℝ} {Ω : Finset ι} {Λ : Finset ν}
    (hp : ∀ i ∈ Ω, 0 ≤ p i) (hr : ∀ j ∈ Λ, 0 ≤ r j) :
    ∀ z ∈ Ω ×ˢ Λ, 0 ≤ productLaw p r z := by
  intro z hz
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp hz
  exact mul_nonneg (hp _ h1) (hr _ h2)

theorem productLaw_sum {p : ι → ℝ} {r : ν → ℝ} {Ω : Finset ι} {Λ : Finset ν}
    (hp : ∑ i ∈ Ω, p i = 1) (hr : ∑ j ∈ Λ, r j = 1) :
    ∑ z ∈ Ω ×ˢ Λ, productLaw p r z = 1 := by
  rw [Finset.sum_product]
  simp only [productLaw]
  rw [Finset.sum_congr rfl (fun i _ => by rw [← Finset.mul_sum, hr, mul_one])]
  exact hp

/-- The law of `(f(ω), g(λ))` under a product law is the product of the two laws. -/
theorem pushWeight_productLaw_pair [DecidableEq α] [DecidableEq β] (Ω : Finset ι) (Λ : Finset ν)
    (p : ι → ℝ) (r : ν → ℝ) (f : ι → α) (g : ν → β) (a : α) (b : β) :
    pushWeight (Ω ×ˢ Λ) (productLaw p r) (fun z => (f z.1, g z.2)) (a, b)
      = pushWeight Ω p f a * pushWeight Λ r g b := by
  classical
  simp only [pushWeight, productLaw]
  rw [Finset.sum_mul_sum]
  rw [← Finset.sum_product']
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext z
  simp only [Finset.mem_filter, Finset.mem_product, Prod.mk.injEq]
  tauto

/-- The entropy of a product weight function is the sum of the entropies. -/
theorem entropy_product {S : Finset α} {T : Finset β} {a : α → ℝ} {b : β → ℝ}
    (ha : ∀ x ∈ S, 0 ≤ a x) (hb : ∀ y ∈ T, 0 ≤ b y) (hasum : ∑ x ∈ S, a x = 1)
    (hbsum : ∑ y ∈ T, b y = 1) :
    entropy (S ×ˢ T) (fun z => a z.1 * b z.2) = entropy S a + entropy T b := by
  classical
  have key : ∀ z ∈ S ×ˢ T, Real.negMulLog (a z.1 * b z.2)
      = b z.2 * Real.negMulLog (a z.1) + a z.1 * Real.negMulLog (b z.2) := by
    intro z hz
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hz
    rcases eq_or_lt_of_le (ha _ h1) with h | hA
    · simp [Real.negMulLog, ← h]
    · rcases eq_or_lt_of_le (hb _ h2) with h' | hB
      · simp [Real.negMulLog, ← h']
      · simp only [Real.negMulLog, Real.log_mul (ne_of_gt hA) (ne_of_gt hB)]
        ring
  simp only [entropy]
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_product, Finset.sum_product]
  have e1 : ∑ x ∈ S, ∑ y ∈ T, b y * Real.negMulLog (a x) = ∑ x ∈ S, Real.negMulLog (a x) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_mul, hbsum, one_mul]
  have e2 : ∑ x ∈ S, ∑ y ∈ T, a x * Real.negMulLog (b y) = ∑ y ∈ T, Real.negMulLog (b y) := by
    rw [Finset.sum_congr rfl (fun x _ => by rw [← Finset.mul_sum])]
    rw [← Finset.sum_mul, hasum, one_mul]
  rw [e1, e2]

/-- **Additivity of entropy under independence**: on a product law, `H(f, g) = H(f) + H(g)`. -/
theorem pushEntropy_productLaw_pair [DecidableEq α] [DecidableEq β] {Ω : Finset ι} {Λ : Finset ν}
    {p : ι → ℝ} {r : ν → ℝ} (hp : ∀ i ∈ Ω, 0 ≤ p i) (hr : ∀ j ∈ Λ, 0 ≤ r j)
    (hpsum : ∑ i ∈ Ω, p i = 1) (hrsum : ∑ j ∈ Λ, r j = 1) (f : ι → α) (g : ν → β) :
    pushEntropy (Ω ×ˢ Λ) (productLaw p r) (fun z => (f z.1, g z.2))
      = pushEntropy Ω p f + pushEntropy Λ r g := by
  classical
  have himg : (Ω ×ˢ Λ).image (fun z : ι × ν => (f z.1, g z.2)) = (Ω.image f) ×ˢ (Λ.image g) := by
    ext c
    obtain ⟨a, b⟩ := c
    simp only [Finset.mem_image, Finset.mem_product, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨i, j⟩, hz, h1, h2⟩
      exact ⟨⟨i, hz.1, h1⟩, ⟨j, hz.2, h2⟩⟩
    · rintro ⟨⟨i, hi, h1⟩, j, hj, h2⟩
      exact ⟨(i, j), ⟨hi, hj⟩, h1, h2⟩
  have hstep : ∑ c ∈ (Ω.image f) ×ˢ (Λ.image g),
        Real.negMulLog (pushWeight (Ω ×ˢ Λ) (productLaw p r) (fun z => (f z.1, g z.2)) c)
      = ∑ c ∈ (Ω.image f) ×ˢ (Λ.image g),
        Real.negMulLog (pushWeight Ω p f c.1 * pushWeight Λ r g c.2) :=
    Finset.sum_congr rfl fun c _ => congrArg Real.negMulLog
      (pushWeight_productLaw_pair Ω Λ p r f g c.1 c.2)
  simp only [pushEntropy, himg, entropy]
  rw [hstep]
  exact entropy_product (S := Ω.image f) (T := Λ.image g)
    (fun a _ => pushWeight_nonneg hp a) (fun b _ => pushWeight_nonneg hr b)
    (by rw [sum_pushWeight, hpsum]) (by rw [sum_pushWeight, hrsum])

/-- Adding an independent second coordinate does not change the entropy of the first. -/
theorem pushEntropy_productLaw_fst [DecidableEq α] {Ω : Finset ι} {Λ : Finset ν}
    {p : ι → ℝ} {r : ν → ℝ} (hp : ∀ i ∈ Ω, 0 ≤ p i) (hr : ∀ j ∈ Λ, 0 ≤ r j)
    (hpsum : ∑ i ∈ Ω, p i = 1) (hrsum : ∑ j ∈ Λ, r j = 1) (f : ι → α) :
    pushEntropy (Ω ×ˢ Λ) (productLaw p r) (fun z => f z.1) = pushEntropy Ω p f := by
  classical
  have h := pushEntropy_productLaw_pair (β := Unit) hp hr hpsum hrsum f (fun _ => ())
  have h0 : pushEntropy Λ r (fun _ : ν => ()) = 0 := by
    simp only [pushEntropy, entropy]
    rcases Finset.eq_empty_or_nonempty Λ with h' | h'
    · simp [h']
    · have : Λ.image (fun _ : ν => ()) = {()} := by
        ext u; simp [Finset.mem_image, h'.exists_mem]
      rw [this]
      simp only [Finset.sum_singleton]
      have : pushWeight Λ r (fun _ : ν => ()) () = 1 := by
        simpa [pushWeight] using hrsum
      rw [this]
      simp [Real.negMulLog]
  rw [h0, add_zero] at h
  rw [← h]
  refine pushEntropy_eq_of_comp (productLaw_nonneg hp hr) (ψ := fun a : α => (a, ()))
    (χ := fun z : α × Unit => z.1) (fun _ _ => rfl) (fun _ _ => rfl)

/-- Adding an independent first coordinate does not change the entropy of the second. -/
theorem pushEntropy_productLaw_snd [DecidableEq β] {Ω : Finset ι} {Λ : Finset ν}
    {p : ι → ℝ} {r : ν → ℝ} (hp : ∀ i ∈ Ω, 0 ≤ p i) (hr : ∀ j ∈ Λ, 0 ≤ r j)
    (hpsum : ∑ i ∈ Ω, p i = 1) (hrsum : ∑ j ∈ Λ, r j = 1) (g : ν → β) :
    pushEntropy (Ω ×ˢ Λ) (productLaw p r) (fun z => g z.2) = pushEntropy Λ r g := by
  classical
  have h := pushEntropy_productLaw_pair (α := Unit) hp hr hpsum hrsum (fun _ => ()) g
  have h0 : pushEntropy Ω p (fun _ : ι => ()) = 0 := by
    simp only [pushEntropy, entropy]
    rcases Finset.eq_empty_or_nonempty Ω with h' | h'
    · simp [h']
    · have : Ω.image (fun _ : ι => ()) = {()} := by
        ext u; simp [Finset.mem_image, h'.exists_mem]
      rw [this]
      simp only [Finset.sum_singleton]
      have : pushWeight Ω p (fun _ : ι => ()) () = 1 := by
        simpa [pushWeight] using hpsum
      rw [this]
      simp [Real.negMulLog]
  rw [h0, zero_add] at h
  rw [← h]
  refine pushEntropy_eq_of_comp (productLaw_nonneg hp hr) (ψ := fun b : β => ((), b))
    (χ := fun z : Unit × β => z.2) (fun _ _ => rfl) (fun _ _ => rfl)

end SumsDifferences
