/-
# Entropy of convolutions of finitely supported laws

Laws on an abelian group `G` are represented as elements `f` of `AddMonoidAlgebra ℝ G` with
nonnegative coefficients summing to `1` (`IsLaw`); multiplication in `AddMonoidAlgebra` is
convolution, i.e. the law of the sum of two *independent* random variables.  `ent f` is the
Shannon entropy (natural logarithm) of `f`.

Main results:

* `ent_le_ent_mul` — `H(X) ≤ H(X + Y)` for independent `X, Y` (fact (E4) of §4.1 of
  the proof paper);
* `ent_madiman` — **Madiman's submodularity** `H(X + Y + Z) + H(Y) ≤ H(X + Y) + H(Y + Z)`
  for independent `X, Y, Z` (fact (E5));
* `ent_mul_le_log_card` — the law of `X + Y` is supported in `supp X + supp Y` (with (E1));
* `coupled_link`, `coupled_link0` — for a set `Γ` of pairs with pairwise distinct differences
  and `(X₁, Y₁)` uniform on `Γ` with marginals `μX, μY`:
  `log #Γ + H(W) ≤ H(μX * W) + H(μY * W)` for every law `W` (Lemma 3.2), and
  `log #Γ ≤ H(μX) + H(μY)`.

The entropy toolkit is that of `FinEntropy.lean`, `JointEntropy.lean`, `CondEntropy.lean` and
`ProductLaw.lean` (product laws and additivity of entropy).
-/
import Mathlib
import SumDifference.FinEntropy
import SumDifference.JointEntropy
import SumDifference.CondEntropy
import SumDifference.ProductLaw

open Finset Real Pointwise

namespace SumsDifferences

namespace CoupledEntropy

section general

variable {ι ι' α : Type*}

/-- Reindexing a law along an injective map does not change the entropy of any random
variable. -/
theorem pushEntropy_reindex [DecidableEq ι'] [DecidableEq α] {Ω : Finset ι} {p : ι → ℝ}
    {p' : ι' → ℝ} (e : ι → ι') (he : Set.InjOn e Ω) (hp : ∀ i ∈ Ω, p' (e i) = p i)
    (φ : ι' → α) :
    pushEntropy Ω p (fun i => φ (e i)) = pushEntropy (Ω.image e) p' φ := by
  have hw : ∀ a, pushWeight Ω p (fun i => φ (e i)) a = pushWeight (Ω.image e) p' φ a := by
    intro a
    simp only [pushWeight]
    rw [Finset.filter_image, Finset.sum_image (fun x hx y hy hxy =>
      he (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hxy)]
    exact Finset.sum_congr rfl fun i hi => (hp i (Finset.mem_filter.mp hi).1).symm
  have himg : Ω.image (fun i => φ (e i)) = (Ω.image e).image φ := by
    rw [Finset.image_image]; rfl
  simp only [pushEntropy, himg]
  exact Finset.sum_congr rfl fun a _ => by rw [hw a]

/-- The entropy of an injective random variable is the entropy of the law. -/
theorem pushEntropy_eq_entropy_of_injOn [DecidableEq α] {Ω : Finset ι} {p : ι → ℝ}
    {F : ι → α} (hF : Set.InjOn F Ω) : pushEntropy Ω p F = entropy Ω p := by
  classical
  have hw : ∀ i ∈ Ω, pushWeight Ω p F (F i) = p i := by
    intro i hi
    simp only [pushWeight]
    rw [Finset.sum_eq_single i
      (fun j hj hji => absurd (hF (Finset.mem_filter.mp hj).1 hi (Finset.mem_filter.mp hj).2) hji)
      (fun hi' => (hi' (Finset.mem_filter.mpr ⟨hi, rfl⟩)).elim)]
  simp only [pushEntropy, entropy]
  rw [Finset.sum_image (fun x hx y hy hxy => hF hx hy hxy)]
  exact Finset.sum_congr rfl fun i hi => by rw [hw i hi]

end general

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A law on `G`: nonnegative coefficients with total mass `1`. -/
def IsLaw (f : AddMonoidAlgebra ℝ G) : Prop :=
  (∀ x, 0 ≤ f x) ∧ ∑ x ∈ f.support, f x = 1

/-- Shannon entropy of a law. -/
noncomputable def ent (f : AddMonoidAlgebra ℝ G) : ℝ :=
  entropy f.support (⇑f)

omit [AddCommGroup G] [DecidableEq G] in
/-- The entropy can be computed over any finite superset of the support. -/
theorem entropy_eq_ent_of_subset {f : AddMonoidAlgebra ℝ G} {S : Finset G}
    (h : f.support ⊆ S) : entropy S (⇑f) = ent f := by
  simp only [ent, entropy]
  refine (Finset.sum_subset h fun x _ hx => ?_).symm
  rw [Finsupp.notMem_support_iff.mp hx, Real.negMulLog_zero]

omit [AddCommGroup G] in
/-- A random variable whose law is `h` has entropy `ent h`. -/
theorem pushEntropy_eq_ent {ι : Type*} {Ω : Finset ι} {p : ι → ℝ} {F : ι → G}
    {h : AddMonoidAlgebra ℝ G} (hw : ∀ z, pushWeight Ω p F z = h z) :
    pushEntropy Ω p F = ent h := by
  have hsub : h.support ⊆ Ω.image F := by
    intro z hz
    rw [Finsupp.mem_support_iff, ← hw z] at hz
    obtain ⟨i, hi, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
    obtain ⟨hiΩ, hiz⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_image.mpr ⟨i, hiΩ, hiz⟩
  rw [← entropy_eq_ent_of_subset hsub]
  simp only [pushEntropy, entropy]
  exact Finset.sum_congr rfl fun z _ => by rw [hw z]

omit [AddCommGroup G] [DecidableEq G] in
theorem IsLaw.nonneg {f : AddMonoidAlgebra ℝ G} (hf : IsLaw f) (x : G) : 0 ≤ f x := hf.1 x

omit [AddCommGroup G] in
/-- The identity random variable on the support of a law has the law itself. -/
theorem pushWeight_support_id (f : AddMonoidAlgebra ℝ G) (z : G) :
    pushWeight f.support (⇑f) id z = f z := by
  simp only [pushWeight, id]
  by_cases hz : z ∈ f.support
  · rw [Finset.sum_eq_single z (fun j hj hjz => absurd (Finset.mem_filter.mp hj).2 hjz)
      (fun hz' => (hz' (Finset.mem_filter.mpr ⟨hz, rfl⟩)).elim)]
  · rw [Finsupp.notMem_support_iff.mp hz]
    refine Finset.sum_eq_zero fun j hj => ?_
    obtain ⟨hj1, hj2⟩ := Finset.mem_filter.mp hj
    exact absurd (hj2 ▸ hj1) hz

omit [AddCommGroup G] in
theorem ent_eq_pushEntropy_id (f : AddMonoidAlgebra ℝ G) :
    ent f = pushEntropy f.support (⇑f) id :=
  (pushEntropy_eq_ent (pushWeight_support_id f)).symm

omit [AddCommGroup G] in
/-- A law with the same weights as a pushforward is supported in the image. -/
theorem support_subset_image_of_pushWeight {ι : Type*} {Ω : Finset ι} {p : ι → ℝ} {F : ι → G}
    {h : AddMonoidAlgebra ℝ G} (hw : ∀ z, pushWeight Ω p F z = h z) :
    h.support ⊆ Ω.image F := by
  intro z hz
  rw [Finsupp.mem_support_iff, ← hw z] at hz
  obtain ⟨i, hi, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  obtain ⟨hiΩ, hiz⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_image.mpr ⟨i, hiΩ, hiz⟩

omit [AddCommGroup G] in
/-- The pushforward of a probability law is a law. -/
theorem isLaw_of_pushWeight {ι : Type*} {Ω : Finset ι} {p : ι → ℝ} {F : ι → G}
    {h : AddMonoidAlgebra ℝ G} (hp : ∀ i ∈ Ω, 0 ≤ p i) (hsum : ∑ i ∈ Ω, p i = 1)
    (hw : ∀ z, pushWeight Ω p F z = h z) : IsLaw h := by
  refine ⟨fun x => hw x ▸ pushWeight_nonneg hp x, ?_⟩
  rw [Finset.sum_subset (support_subset_image_of_pushWeight hw)
    (fun x _ hx => Finsupp.notMem_support_iff.mp hx), ← hsum, ← sum_pushWeight Ω p F]
  exact Finset.sum_congr rfl fun x _ => (hw x).symm

omit [AddCommGroup G] [DecidableEq G] in
theorem IsLaw.nonneg_on {f : AddMonoidAlgebra ℝ G} (hf : IsLaw f) :
    ∀ x ∈ f.support, 0 ≤ f x := fun x _ => hf.1 x

/-- **Convolution as a pushforward.**  If `F₁` has law `h₁` and `F₂` has law `h₂` (on two
independent coordinates), then `F₁ + F₂` has law `h₁ * h₂`. -/
theorem pushWeight_add_eq_mul {α β : Type*} {Ω₁ : Finset α} {Ω₂ : Finset β}
    {w₁ : α → ℝ} {w₂ : β → ℝ} {F₁ : α → G} {F₂ : β → G} {h₁ h₂ : AddMonoidAlgebra ℝ G}
    (hw₁ : ∀ u, pushWeight Ω₁ w₁ F₁ u = h₁ u) (hw₂ : ∀ v, pushWeight Ω₂ w₂ F₂ v = h₂ v)
    (z : G) :
    pushWeight (Ω₁ ×ˢ Ω₂) (productLaw w₁ w₂) (fun ω => F₁ ω.1 + F₂ ω.2) z = (h₁ * h₂) z := by
  classical
  rw [AddMonoidAlgebra.mul_apply_left, Finsupp.sum]
  have step1 : pushWeight (Ω₁ ×ˢ Ω₂) (productLaw w₁ w₂) (fun ω => F₁ ω.1 + F₂ ω.2) z
      = ∑ i ∈ Ω₁, w₁ i * h₂ (-F₁ i + z) := by
    simp only [pushWeight, productLaw]
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hw₂, pushWeight, Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : F₁ i + F₂ j = z
    · have hc' : F₂ j = -F₁ i + z := by rw [← hc]; abel
      simp [hc']
    · have hc' : ¬ F₂ j = -F₁ i + z := fun h => hc (by rw [h]; abel)
      simp [hc, hc']
  have step2 : ∑ i ∈ Ω₁, w₁ i * h₂ (-F₁ i + z) = ∑ u ∈ Ω₁.image F₁, h₁ u * h₂ (-u + z) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := F₁) (t := Ω₁.image F₁)
      (fun i hi => Finset.mem_image_of_mem F₁ hi)]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← hw₁ u, pushWeight, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.mp hi).2]
  rw [step1, step2]
  refine (Finset.sum_subset (support_subset_image_of_pushWeight hw₁) fun u _ hu => ?_).symm
  rw [Finsupp.notMem_support_iff.mp hu, zero_mul]

omit [AddCommGroup G] in
/-- The law of a pair of independent random variables with laws `h₁`, `h₂` has entropy
`ent h₁ + ent h₂`. -/
theorem pushEntropy_pair_eq {β : Type*} [DecidableEq β] {Ω : Finset β} {p : β → ℝ}
    {F : β → G × G} {h₁ h₂ : AddMonoidAlgebra ℝ G} (hh₁ : IsLaw h₁) (hh₂ : IsLaw h₂)
    (hw : ∀ u v, pushWeight Ω p F (u, v) = h₁ u * h₂ v) :
    pushEntropy Ω p F = ent h₁ + ent h₂ := by
  classical
  have hout : ∀ c ∉ Ω.image F, pushWeight Ω p F c = 0 := by
    intro c hc
    refine Finset.sum_eq_zero fun i hi => ?_
    obtain ⟨hiΩ, hic⟩ := Finset.mem_filter.mp hi
    exact absurd (Finset.mem_image.mpr ⟨i, hiΩ, hic⟩) hc
  have e1 : pushEntropy Ω p F
      = ∑ c ∈ Ω.image F ∪ h₁.support ×ˢ h₂.support, Real.negMulLog (h₁ c.1 * h₂ c.2) := by
    have hw' : ∀ c, pushWeight Ω p F c = h₁ c.1 * h₂ c.2 := fun c => hw c.1 c.2
    simp only [pushEntropy, entropy, hw']
    refine Finset.sum_subset Finset.subset_union_left fun c _ hc => ?_
    rw [← hw' c, hout _ hc, Real.negMulLog_zero]
  have e2 : ∑ c ∈ Ω.image F ∪ h₁.support ×ˢ h₂.support, Real.negMulLog (h₁ c.1 * h₂ c.2)
      = entropy (h₁.support ×ˢ h₂.support) (fun c => h₁ c.1 * h₂ c.2) := by
    refine (Finset.sum_subset Finset.subset_union_right fun c _ hc => ?_).symm
    rw [Finset.mem_product, not_and_or] at hc
    rcases hc with hc | hc
    · rw [Finsupp.notMem_support_iff.mp hc, zero_mul, Real.negMulLog_zero]
    · rw [Finsupp.notMem_support_iff.mp hc, mul_zero, Real.negMulLog_zero]
  rw [e1, e2]
  exact entropy_product hh₁.nonneg_on hh₂.nonneg_on hh₁.2 hh₂.2

/-- `f * g` is the law of `x + y` under the product of `f` and `g`. -/
theorem pushWeight_mul (f g : AddMonoidAlgebra ℝ G) (z : G) :
    pushWeight (f.support ×ˢ g.support) (productLaw (⇑f) (⇑g))
      (fun ω => ω.1 + ω.2) z = (f * g) z :=
  pushWeight_add_eq_mul (F₁ := id) (F₂ := id) (pushWeight_support_id f)
    (pushWeight_support_id g) z

theorem IsLaw.mul {f g : AddMonoidAlgebra ℝ G} (hf : IsLaw f) (hg : IsLaw g) :
    IsLaw (f * g) :=
  isLaw_of_pushWeight (productLaw_nonneg hf.nonneg_on hg.nonneg_on)
    (productLaw_sum hf.2 hg.2) (pushWeight_mul f g)

theorem isLaw_one : IsLaw (1 : AddMonoidAlgebra ℝ G) := by
  refine ⟨fun x => ?_, ?_⟩
  · rw [AddMonoidAlgebra.one_def, Finsupp.single_apply]
    split_ifs <;> norm_num
  · rw [AddMonoidAlgebra.one_def, Finsupp.support_single_ne_zero _ one_ne_zero]
    simp

theorem IsLaw.pow {f : AddMonoidAlgebra ℝ G} (hf : IsLaw f) (n : ℕ) : IsLaw (f ^ n) := by
  induction n with
  | zero => simpa using (isLaw_one (G := G))
  | succ n ih => rw [pow_succ]; exact ih.mul hf

theorem ent_mul_eq_pushEntropy (f g : AddMonoidAlgebra ℝ G) :
    ent (f * g) = pushEntropy (f.support ×ˢ g.support)
      (productLaw (⇑f) (⇑g)) (fun ω => ω.1 + ω.2) :=
  (pushEntropy_eq_ent (pushWeight_mul f g)).symm

/-- **Adding an independent summand does not decrease entropy**: `H(X) ≤ H(X + Y)`. -/
theorem ent_le_ent_mul {f g : AddMonoidAlgebra ℝ G} (hf : IsLaw f) (hg : IsLaw g) :
    ent f ≤ ent (f * g) := by
  classical
  have hp := productLaw_nonneg hf.nonneg_on hg.nonneg_on
  have hs := productLaw_sum hf.2 hg.2
  -- `H(X + Y, Y) = H(X, Y) = H(X) + H(Y)`
  have h1 : pushEntropy (f.support ×ˢ g.support) (productLaw (⇑f) (⇑g))
      (fun ω => (ω.1 + ω.2, ω.2))
      = pushEntropy (f.support ×ˢ g.support) (productLaw (⇑f) (⇑g))
      (fun ω => (id ω.1, id ω.2)) :=
    pushEntropy_eq_of_comp hp (fun c : G × G => (c.1 - c.2, c.2))
      (fun c : G × G => (c.1 + c.2, c.2)) (fun ω _ => by simp) (fun ω _ => rfl)
  rw [pushEntropy_productLaw_pair hf.nonneg_on hg.nonneg_on hf.2 hg.2, ← ent_eq_pushEntropy_id,
    ← ent_eq_pushEntropy_id] at h1
  have h2 := pushEntropy_pair_le hp hs (fun ω : G × G => ω.1 + ω.2) (fun ω : G × G => ω.2)
  have h3 : pushEntropy (f.support ×ˢ g.support) (productLaw (⇑f) (⇑g))
      (fun ω => ω.2) = ent g := by
    exact (pushEntropy_productLaw_snd hf.nonneg_on hg.nonneg_on hf.2 hg.2 (id : G → G)).trans
      (ent_eq_pushEntropy_id g).symm
  rw [h1, h3, ← ent_mul_eq_pushEntropy] at h2
  linarith

/-- **Madiman's submodularity** for independent `X, Y, Z`:
`H(X + Y + Z) + H(Y) ≤ H(X + Y) + H(Y + Z)`. -/
theorem ent_madiman {f g k : AddMonoidAlgebra ℝ G} (hf : IsLaw f) (hg : IsLaw g)
    (hk : IsLaw k) : ent (f * g * k) + ent g ≤ ent (f * g) + ent (g * k) := by
  classical
  set S := f.support
  set T := g.support
  set U := k.support
  set r : G × G → ℝ := productLaw (⇑g) (⇑k) with hr
  set P : G × G × G → ℝ := productLaw (⇑f) r with hP
  set Ω := S ×ˢ (T ×ˢ U) with hΩ
  have hr0 : ∀ j ∈ T ×ˢ U, 0 ≤ r j := productLaw_nonneg hg.nonneg_on hk.nonneg_on
  have hrs : ∑ j ∈ T ×ˢ U, r j = 1 := productLaw_sum hg.2 hk.2
  have hP0 : ∀ i ∈ Ω, 0 ≤ P i := productLaw_nonneg hf.nonneg_on hr0
  have hPs : ∑ i ∈ Ω, P i = 1 := productLaw_sum hf.2 hrs
  -- the random variables
  have hsub := pushEntropy_submodular hP0 hPs (fun ω : G × G × G => ω.1)
    (fun ω : G × G × G => ω.1 + (ω.2.1 + ω.2.2)) (fun ω : G × G × G => ω.2.2)
  -- `H(X, S, Z) = H(X) + H(Y) + H(Z)`
  have eXSZ : pushEntropy Ω P (fun ω : G × G × G => (ω.1, ω.1 + (ω.2.1 + ω.2.2), ω.2.2))
      = ent f + ent g + ent k := by
    have e : pushEntropy Ω P (fun ω : G × G × G => (ω.1, ω.1 + (ω.2.1 + ω.2.2), ω.2.2))
        = pushEntropy Ω P (fun ω : G × G × G => (id ω.1, id ω.2)) :=
      pushEntropy_eq_of_comp hP0 (fun c : G × G × G => (c.1, c.2.1 - c.1 - c.2.2, c.2.2))
        (fun c : G × G × G => (c.1, c.1 + (c.2.1 + c.2.2), c.2.2))
        (fun ω _ => by simp) (fun ω _ => rfl)
    rw [e, pushEntropy_productLaw_pair hf.nonneg_on hr0 hf.2 hrs, ← ent_eq_pushEntropy_id]
    have e2 : pushEntropy (T ×ˢ U) r id = pushEntropy (T ×ˢ U) r (fun ω => (id ω.1, id ω.2)) :=
      rfl
    rw [e2, pushEntropy_productLaw_pair hg.nonneg_on hk.nonneg_on hg.2 hk.2,
      ← ent_eq_pushEntropy_id, ← ent_eq_pushEntropy_id]
    ring
  -- `H(S) = H(f * g * k)`
  have eS : pushEntropy Ω P (fun ω : G × G × G => ω.1 + (ω.2.1 + ω.2.2)) = ent (f * g * k) := by
    rw [mul_assoc]
    exact pushEntropy_eq_ent (pushWeight_add_eq_mul (F₁ := id) (pushWeight_support_id f)
      (pushWeight_mul g k))
  -- `H(X, S) = H(X) + H(Y + Z)`
  have eXS : pushEntropy Ω P (fun ω : G × G × G => (ω.1, ω.1 + (ω.2.1 + ω.2.2)))
      = ent f + ent (g * k) := by
    have e : pushEntropy Ω P (fun ω : G × G × G => (ω.1, ω.1 + (ω.2.1 + ω.2.2)))
        = pushEntropy Ω P (fun ω : G × G × G => (id ω.1, ω.2.1 + ω.2.2)) :=
      pushEntropy_eq_of_comp hP0 (fun c : G × G => (c.1, c.2 - c.1))
        (fun c : G × G => (c.1, c.1 + c.2)) (fun ω _ => by simp) (fun ω _ => rfl)
    rw [e, pushEntropy_productLaw_pair hf.nonneg_on hr0 hf.2 hrs (id : G → G)
      (fun ω : G × G => ω.1 + ω.2), ← ent_eq_pushEntropy_id, ← ent_mul_eq_pushEntropy]
  -- `H(S, Z) = H(X + Y) + H(Z)`
  have eSZ : pushEntropy Ω P (fun ω : G × G × G => (ω.1 + (ω.2.1 + ω.2.2), ω.2.2))
      = ent (f * g) + ent k := by
    have e : pushEntropy Ω P (fun ω : G × G × G => (ω.1 + (ω.2.1 + ω.2.2), ω.2.2))
        = pushEntropy Ω P (fun ω : G × G × G => ((fun c : (G × G) × G => (c.1.1 + c.1.2, c.2))
          ((fun ω : G × G × G => ((ω.1, ω.2.1), ω.2.2)) ω))) :=
      pushEntropy_eq_of_comp hP0 (fun c : G × G => (c.1 - c.2, c.2))
        (fun c : G × G => (c.1 + c.2, c.2)) (fun ω _ => by simp; abel)
        (fun ω _ => Prod.ext (add_assoc _ _ _) rfl)
    rw [e]
    refine Eq.trans (pushEntropy_reindex (p' := productLaw (productLaw (⇑f) (⇑g))
      (⇑k)) (fun ω : G × G × G => ((ω.1, ω.2.1), ω.2.2))
      (fun a _ b _ hab => by
        simp only [Prod.mk.injEq] at hab
        exact Prod.ext hab.1.1 (Prod.ext hab.1.2 hab.2))
      (fun ω _ => by simp only [hP, hr, productLaw]; ring)
      (fun c : (G × G) × G => (c.1.1 + c.1.2, c.2))) ?_
    have himg : Ω.image (fun ω : G × G × G => ((ω.1, ω.2.1), ω.2.2)) = (S ×ˢ T) ×ˢ U := by
      ext ⟨⟨a, b⟩, c⟩
      simp only [hΩ, Finset.mem_image, Finset.mem_product, Prod.exists, Prod.mk.injEq]
      constructor
      · rintro ⟨a', b', c', ⟨h1, h2, h3⟩, ⟨rfl, rfl⟩, rfl⟩; exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨a, b, c, ⟨h1, h2, h3⟩, ⟨rfl, rfl⟩, rfl⟩
    rw [himg]
    exact (pushEntropy_productLaw_pair (productLaw_nonneg hf.nonneg_on hg.nonneg_on)
      hk.nonneg_on (productLaw_sum hf.2 hg.2) hk.2 (fun ω : G × G => ω.1 + ω.2) (id : G → G)).trans
      (congrArg₂ (· + ·) (ent_mul_eq_pushEntropy f g).symm (ent_eq_pushEntropy_id k).symm)
  rw [eXSZ, eS, eXS, eSZ] at hsub
  linarith

/-- The law of `X + Y` lives on `supp X + supp Y`. -/
theorem ent_mul_le_log_card {f g : AddMonoidAlgebra ℝ G} (hf : IsLaw f) (hg : IsLaw g)
    {X Y : Finset G} (hX : f.support ⊆ X) (hY : g.support ⊆ Y) :
    ent (f * g) ≤ Real.log #(X + Y) := by
  rw [ent_mul_eq_pushEntropy]
  refine pushEntropy_le_log_card (productLaw_nonneg hf.nonneg_on hg.nonneg_on)
    (productLaw_sum hf.2 hg.2) fun ω hω => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp hω
  exact Finset.add_mem_add (hX h1) (hY h2)

/-! ## The coupled pair -/

/-- First marginal of the uniform law on a finite set of pairs. -/
noncomputable def margFst (Γ : Finset (G × G)) : AddMonoidAlgebra ℝ G :=
  ∑ q ∈ Γ, AddMonoidAlgebra.single q.1 ((#Γ : ℝ)⁻¹)

/-- Second marginal of the uniform law on a finite set of pairs. -/
noncomputable def margSnd (Γ : Finset (G × G)) : AddMonoidAlgebra ℝ G :=
  ∑ q ∈ Γ, AddMonoidAlgebra.single q.2 ((#Γ : ℝ)⁻¹)

omit [AddCommGroup G] in
theorem pushWeight_fst_eq_margFst (Γ : Finset (G × G)) (z : G) :
    pushWeight Γ (fun _ => (#Γ : ℝ)⁻¹) Prod.fst z = margFst Γ z := by
  simp only [pushWeight, margFst, Finset.sum_filter]
  rw [Finsupp.finset_sum_apply]
  simp [AddMonoidAlgebra.single_apply]

omit [AddCommGroup G] in
theorem pushWeight_snd_eq_margSnd (Γ : Finset (G × G)) (z : G) :
    pushWeight Γ (fun _ => (#Γ : ℝ)⁻¹) Prod.snd z = margSnd Γ z := by
  simp only [pushWeight, margSnd, Finset.sum_filter]
  rw [Finsupp.finset_sum_apply]
  simp [AddMonoidAlgebra.single_apply]

omit [AddCommGroup G] [DecidableEq G] in
theorem uniform_sum {ι : Type*} {Γ : Finset ι} (hΓ : Γ.Nonempty) :
    ∑ _q ∈ Γ, (#Γ : ℝ)⁻¹ = 1 := by
  have : (0 : ℝ) < #Γ := by exact_mod_cast hΓ.card_pos
  rw [Finset.sum_const, nsmul_eq_mul]
  field_simp

omit [AddCommGroup G] in
theorem isLaw_margFst {Γ : Finset (G × G)} (hΓ : Γ.Nonempty) : IsLaw (margFst Γ) :=
  isLaw_of_pushWeight (fun _ _ => by positivity) (uniform_sum hΓ) (pushWeight_fst_eq_margFst Γ)

omit [AddCommGroup G] in
theorem isLaw_margSnd {Γ : Finset (G × G)} (hΓ : Γ.Nonempty) : IsLaw (margSnd Γ) :=
  isLaw_of_pushWeight (fun _ _ => by positivity) (uniform_sum hΓ) (pushWeight_snd_eq_margSnd Γ)

omit [AddCommGroup G] in
theorem support_margFst_subset {Γ : Finset (G × G)} {X Y : Finset G} (h : Γ ⊆ X ×ˢ Y) :
    (margFst Γ).support ⊆ X := by
  intro z hz
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp
    (support_subset_image_of_pushWeight (pushWeight_fst_eq_margFst Γ) hz)
  exact (Finset.mem_product.mp (h hq)).1

omit [AddCommGroup G] in
theorem support_margSnd_subset {Γ : Finset (G × G)} {X Y : Finset G} (h : Γ ⊆ X ×ˢ Y) :
    (margSnd Γ).support ⊆ Y := by
  intro z hz
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp
    (support_subset_image_of_pushWeight (pushWeight_snd_eq_margSnd Γ) hz)
  exact (Finset.mem_product.mp (h hq)).2

omit [AddCommGroup G] in
/-- `log #Γ ≤ H(X₁) + H(Y₁)` (subadditivity). -/
theorem coupled_link0 {Γ : Finset (G × G)} (hΓ : Γ.Nonempty) :
    Real.log #Γ ≤ ent (margFst Γ) + ent (margSnd Γ) := by
  classical
  have h := pushEntropy_pair_le (fun _ _ => by positivity) (uniform_sum hΓ)
    (Prod.fst : G × G → G) (Prod.snd : G × G → G)
  rw [pushEntropy_eq_ent (pushWeight_fst_eq_margFst Γ),
    pushEntropy_eq_ent (pushWeight_snd_eq_margSnd Γ),
    pushEntropy_eq_entropy_of_injOn (fun a _ b _ hab => by
      simp only [Prod.mk.injEq] at hab; exact Prod.ext hab.1 hab.2), entropy_uniform] at h
  exact h

/-- **The coupled Ruzsa triangle inequality** (Lemma 4.2).  If the pairs in `Γ` have pairwise distinct differences, then for
every law `W`: `log #Γ + H(W) ≤ H(X₁ + W) + H(Y₁ + W)`, because
`(X₁, Y₁, W) ↦ (X₁ + W, Y₁ + W)` is injective. -/
theorem coupled_link {Γ : Finset (G × G)} (hΓ : Γ.Nonempty)
    (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q')
    {w : AddMonoidAlgebra ℝ G} (hw : IsLaw w) :
    Real.log #Γ + ent w ≤ ent (margFst Γ * w) + ent (margSnd Γ * w) := by
  classical
  have hu0 : ∀ q ∈ Γ, 0 ≤ (fun _ => (#Γ : ℝ)⁻¹) q := fun _ _ => by positivity
  have hp := productLaw_nonneg hu0 hw.nonneg_on
  have hs := productLaw_sum (uniform_sum hΓ) hw.2
  have h := pushEntropy_pair_le hp hs (fun ω : (G × G) × G => ω.1.1 + ω.2)
    (fun ω : (G × G) × G => ω.1.2 + ω.2)
  have hΦ : Set.InjOn (fun ω : (G × G) × G => (ω.1.1 + ω.2, ω.1.2 + ω.2))
      ↑(Γ ×ˢ w.support) := by
    intro a ha b hb hab
    simp only [Prod.mk.injEq] at hab
    have ha' := Finset.mem_product.mp ha
    have hb' := Finset.mem_product.mp hb
    have hq : a.1 = b.1 := hinj _ ha'.1 _ hb'.1 (by
      have e1 : a.1.1 - a.1.2 = (a.1.1 + a.2) - (a.1.2 + a.2) := by abel
      have e2 : b.1.1 - b.1.2 = (b.1.1 + b.2) - (b.1.2 + b.2) := by abel
      rw [e1, e2, hab.1, hab.2])
    have ht : a.2 = b.2 := by
      have := hab.1
      rw [hq] at this
      exact add_left_cancel this
    exact Prod.ext hq ht
  rw [pushEntropy_eq_entropy_of_injOn hΦ] at h
  have hent : entropy (Γ ×ˢ w.support) (productLaw (fun _ => (#Γ : ℝ)⁻¹) (⇑w))
      = Real.log #Γ + ent w := by
    rw [show productLaw (fun _ => (#Γ : ℝ)⁻¹) (⇑w)
        = fun z : (G × G) × G => (fun _ => (#Γ : ℝ)⁻¹) z.1 * (⇑w) z.2 from rfl,
      entropy_product hu0 hw.nonneg_on (uniform_sum hΓ) hw.2, entropy_uniform]
    rfl
  have e1 : pushEntropy (Γ ×ˢ w.support) (productLaw (fun _ => (#Γ : ℝ)⁻¹) (⇑w))
      (fun ω : (G × G) × G => ω.1.1 + ω.2) = ent (margFst Γ * w) :=
    pushEntropy_eq_ent (pushWeight_add_eq_mul (F₂ := id) (pushWeight_fst_eq_margFst Γ)
      (pushWeight_support_id w))
  have e2 : pushEntropy (Γ ×ˢ w.support) (productLaw (fun _ => (#Γ : ℝ)⁻¹) (⇑w))
      (fun ω : (G × G) × G => ω.1.2 + ω.2) = ent (margSnd Γ * w) :=
    pushEntropy_eq_ent (pushWeight_add_eq_mul (F₂ := id) (pushWeight_snd_eq_margSnd Γ)
      (pushWeight_support_id w))
  rw [hent, e1, e2] at h
  exact h

end CoupledEntropy

end SumsDifferences
