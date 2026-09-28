/-
# Computing and combining finite entropies

Structural lemmas about `pushEntropy`; the proof of the proof paper uses the
entropy of a uniform law (`pushWeight_unif`, `pushEntropy_unif_of_injOn`):

* `pushEntropy_image` — transporting a law along an injection of the index set;
* `pushEntropy_relabel` — the entropy of a random variable does not change when its values are
  relabelled injectively;
* `pushEntropy_prod` — **additivity**: for a product law on `s₁ ×ˢ s₂` and a pair of variables
  depending on the two coordinates separately, the joint entropy is the sum of the two
  entropies;

together with the elementary formula

* `pushEntropy_unif_eq` — for a *uniform* law the pushforward weights are the fibre
  cardinalities divided by `#s`, which turns any concrete entropy into a finite sum of
  `negMulLog`s of rational numbers.
-/
import Mathlib
import SumDifference.FinEntropy
import SumDifference.JointEntropy

open Finset

namespace SumsDifferences

variable {ι κ α β γ : Type*} [DecidableEq κ] [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-! ## Transport along an injection of the index set -/

/-- If `φ` is injective on `s`, the law `p` on `s.image φ` and the law `p ∘ φ` on `s` give the
same pushforward weights. -/
theorem pushWeight_image {s : Finset ι} {φ : ι → κ} (hinj : Set.InjOn φ s) (p : κ → ℝ)
    (f : κ → α) (a : α) :
    pushWeight (s.image φ) p f a = pushWeight s (fun i => p (φ i)) (fun i => f (φ i)) a := by
  classical
  rw [pushWeight, pushWeight, Finset.filter_image]
  refine Finset.sum_image ?_
  intro x hx y hy hxy
  exact hinj (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hxy

/-- **Transport along an injection.**  Relabelling the index set injectively does not change the
entropy of a random variable. -/
theorem pushEntropy_image {s : Finset ι} {φ : ι → κ} (hinj : Set.InjOn φ s) (p : κ → ℝ)
    (f : κ → α) :
    pushEntropy (s.image φ) p f = pushEntropy s (fun i => p (φ i)) (fun i => f (φ i)) := by
  classical
  rw [pushEntropy, pushEntropy, Finset.image_image]
  exact Finset.sum_congr rfl fun a _ => by rw [pushWeight_image hinj]

/-! ## Injective relabelling of the values -/

omit [DecidableEq κ] in
/-- If `ψ` is injective on the range of `f`, then `ψ ∘ f` has the same law as `f` up to
relabelling, hence the same entropy. -/
theorem pushEntropy_relabel {s : Finset ι} {p : ι → ℝ} {f : ι → α} {ψ : α → γ}
    (hψ : Set.InjOn ψ (s.image f)) :
    pushEntropy s p (fun i => ψ (f i)) = pushEntropy s p f := by
  classical
  have hkey : ∀ a ∈ s.image f, pushWeight s p (fun i => ψ (f i)) (ψ a) = pushWeight s p f a := by
    intro a ha
    rw [pushWeight, pushWeight]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext i
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro hi
    exact ⟨fun h => hψ (Finset.mem_image_of_mem f hi) ha h, fun h => by rw [h]⟩
  calc pushEntropy s p (fun i => ψ (f i))
      = ∑ c ∈ (s.image f).image ψ, Real.negMulLog (pushWeight s p (fun i => ψ (f i)) c) := by
        rw [pushEntropy, entropy, Finset.image_image]; rfl
    _ = ∑ a ∈ s.image f, Real.negMulLog (pushWeight s p (fun i => ψ (f i)) (ψ a)) :=
        Finset.sum_image (fun x hx y hy h => hψ hx hy h)
    _ = ∑ a ∈ s.image f, Real.negMulLog (pushWeight s p f a) :=
        Finset.sum_congr rfl fun a ha => by rw [hkey a ha]
    _ = pushEntropy s p f := rfl

/-! ## Additivity for product laws -/

omit [DecidableEq κ] in
private theorem negMulLog_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.negMulLog (x * y) = y * Real.negMulLog x + x * Real.negMulLog y := by
  rcases eq_or_lt_of_le hx with hx0 | hx0
  · simp [Real.negMulLog, ← hx0]
  rcases eq_or_lt_of_le hy with hy0 | hy0
  · simp [Real.negMulLog, ← hy0]
  · rw [Real.negMulLog, Real.negMulLog, Real.negMulLog,
      Real.log_mul (ne_of_gt hx0) (ne_of_gt hy0)]
    ring

omit [DecidableEq κ] in
/-- The pushforward weight of a product law along a pair of coordinatewise variables is the
product of the two pushforward weights. -/
theorem pushWeight_prod {s₁ : Finset ι} {s₂ : Finset κ} {p₁ : ι → ℝ} {p₂ : κ → ℝ}
    {f₁ : ι → α} {f₂ : κ → β} (a : α) (b : β) :
    pushWeight (s₁ ×ˢ s₂) (fun z => p₁ z.1 * p₂ z.2) (fun z => (f₁ z.1, f₂ z.2)) (a, b)
      = pushWeight s₁ p₁ f₁ a * pushWeight s₂ p₂ f₂ b := by
  classical
  rw [pushWeight, pushWeight, pushWeight, Finset.sum_mul_sum]
  rw [show (s₁ ×ˢ s₂).filter (fun z => (f₁ z.1, f₂ z.2) = (a, b))
      = (s₁.filter fun i => f₁ i = a) ×ˢ (s₂.filter fun j => f₂ j = b) from ?_]
  · rw [Finset.sum_product]
  · ext z
    simp only [Finset.mem_filter, Finset.mem_product, Prod.mk.injEq]
    tauto

omit [DecidableEq κ] in
/-- **Additivity of entropy for independent coordinates.** -/
theorem pushEntropy_prod {s₁ : Finset ι} {s₂ : Finset κ} {p₁ : ι → ℝ} {p₂ : κ → ℝ}
    (h₁ : ∀ i ∈ s₁, 0 ≤ p₁ i) (h₂ : ∀ j ∈ s₂, 0 ≤ p₂ j)
    (hs₁ : ∑ i ∈ s₁, p₁ i = 1) (hs₂ : ∑ j ∈ s₂, p₂ j = 1) (f₁ : ι → α) (f₂ : κ → β) :
    pushEntropy (s₁ ×ˢ s₂) (fun z => p₁ z.1 * p₂ z.2) (fun z => (f₁ z.1, f₂ z.2))
      = pushEntropy s₁ p₁ f₁ + pushEntropy s₂ p₂ f₂ := by
  classical
  have himg : (s₁ ×ˢ s₂).image (fun z => (f₁ z.1, f₂ z.2)) = (s₁.image f₁) ×ˢ (s₂.image f₂) := by
    ext w
    simp only [Finset.mem_image, Finset.mem_product, Prod.ext_iff]
    constructor
    · rintro ⟨z, hz, h1, h2⟩
      exact ⟨⟨z.1, hz.1, h1⟩, ⟨z.2, hz.2, h2⟩⟩
    · rintro ⟨⟨i, hi, h1⟩, ⟨j, hj, h2⟩⟩
      exact ⟨(i, j), ⟨hi, hj⟩, h1, h2⟩
  have hw₁ : ∀ a, 0 ≤ pushWeight s₁ p₁ f₁ a := fun a => pushWeight_nonneg h₁ a
  have hw₂ : ∀ b, 0 ≤ pushWeight s₂ p₂ f₂ b := fun b => pushWeight_nonneg h₂ b
  have hm₁ : ∑ a ∈ s₁.image f₁, pushWeight s₁ p₁ f₁ a = 1 := by rw [sum_pushWeight, hs₁]
  have hm₂ : ∑ b ∈ s₂.image f₂, pushWeight s₂ p₂ f₂ b = 1 := by rw [sum_pushWeight, hs₂]
  rw [pushEntropy, himg, entropy, Finset.sum_product]
  have : ∀ a ∈ s₁.image f₁, ∑ b ∈ s₂.image f₂,
      Real.negMulLog (pushWeight (s₁ ×ˢ s₂) (fun z => p₁ z.1 * p₂ z.2)
        (fun z => (f₁ z.1, f₂ z.2)) (a, b))
      = Real.negMulLog (pushWeight s₁ p₁ f₁ a)
        + pushWeight s₁ p₁ f₁ a * entropy (s₂.image f₂) (pushWeight s₂ p₂ f₂) := by
    intro a _
    have : ∀ b ∈ s₂.image f₂, Real.negMulLog (pushWeight (s₁ ×ˢ s₂)
        (fun z => p₁ z.1 * p₂ z.2) (fun z => (f₁ z.1, f₂ z.2)) (a, b))
        = pushWeight s₂ p₂ f₂ b * Real.negMulLog (pushWeight s₁ p₁ f₁ a)
          + pushWeight s₁ p₁ f₁ a * Real.negMulLog (pushWeight s₂ p₂ f₂ b) := by
      intro b _
      rw [pushWeight_prod, negMulLog_mul (hw₁ a) (hw₂ b)]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.sum_mul, hm₂, one_mul,
      ← Finset.mul_sum]
    rfl
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.sum_mul, hm₁, one_mul]
  rfl

/-! ## Uniform laws: entropies as sums over fibre cardinalities -/

omit [DecidableEq κ] in
/-- For a uniform law the pushforward weight of `a` is the size of the fibre over `a`. -/
theorem pushWeight_unif {s : Finset ι} (f : ι → α) (a : α) :
    pushWeight s (fun _ => (#s : ℝ)⁻¹) f a = (#(s.filter fun i => f i = a) : ℝ) / #s := by
  rw [pushWeight, Finset.sum_const, nsmul_eq_mul]
  ring

omit [DecidableEq κ] in
/-- The entropy of a random variable under the uniform law, as an explicit finite sum. -/
theorem pushEntropy_unif_eq {s : Finset ι} (f : ι → α) :
    pushEntropy s (fun _ => (#s : ℝ)⁻¹) f
      = ∑ a ∈ s.image f, Real.negMulLog ((#(s.filter fun i => f i = a) : ℝ) / #s) := by
  rw [pushEntropy, entropy]
  exact Finset.sum_congr rfl fun a _ => by rw [pushWeight_unif]

omit [DecidableEq κ] in
/-- An injective random variable under the uniform law has the full entropy `log #s`. -/
theorem pushEntropy_unif_of_injOn {s : Finset ι} {f : ι → α} (hinj : Set.InjOn f s) :
    pushEntropy s (fun _ => (#s : ℝ)⁻¹) f = Real.log #s := by
  classical
  refine pushEntropy_eq_log_card_of_uniform (t := s.image f) rfl ?_ |>.trans ?_
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    rw [pushWeight_unif, Finset.card_image_of_injOn hinj]
    rw [show s.filter (fun j => f j = f i) = {i} from ?_]
    · simp
    · ext j
      simp only [Finset.mem_filter, Finset.mem_singleton]
      exact ⟨fun h => hinj h.1 hi h.2, fun h => ⟨h ▸ hi, by rw [h]⟩⟩
  · rw [Finset.card_image_of_injOn hinj]

omit [DecidableEq κ] in
/-- `negMulLog` of a ratio of positive reals. -/
theorem negMulLog_div {k n : ℝ} (hk : 0 < k) (hn : 0 < n) :
    Real.negMulLog (k / n) = (k / n) * (Real.log n - Real.log k) := by
  rw [Real.negMulLog, Real.log_div (ne_of_gt hk) (ne_of_gt hn)]
  ring

end SumsDifferences
