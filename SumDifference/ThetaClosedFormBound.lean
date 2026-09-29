module

/-
# Theorem 1.1 and Corollary 1.3 of the proof paper

1. **Proposition 4.1** (`CoupledForms.two_copy_ineq`, `SumDifference/ThetaTwoCopyLemma.lean`) for the
   coupling `Γ` and for its mirror image `Γ' = {(−y, −x)}` (a coupling for `(−Y, −X)`, with the same
   `L` and `log |X+Y|` and with `h'(i,j) = h(j,i)`); their average is the symmetric two-copy
   inequality (Corollary 4.3, `two_copy_ineq_sym`)
   `22882 L ≤ 5820 log s + 8694 h(1,1) + 11645 (h(1,0)+h(0,1)) + 685 (h(2,0)+h(0,2))`.
2. The grid lemma (Proposition 5.1, `GridClosedForm.grid_closed_form`) gives
   `(21512 e + 3148) L ≤ (37804 e − 13144) log s` (`ClosedForm.log_card_le_of_coupling_closed`),
   hence **Theorem 1.1** (`pair_ceiling_entropic`): `|X − Y| ≤ |X + Y|^{λ∞}` for finite sets in
   *any* abelian group, `λ∞ = (9451 e − 3286)/(5378 e + 787)`, with no constant.
3. With `G = ℤ` this gives `λ_* ≤ λ∞` (`lamSup_le_closed_form`), and Theorem 1.2
   (`theta_le_two_sub_inv_lamSup`, `SumDifference/ThetaMultiScaleCore.lean`) gives
   **Corollary 1.3** (`theta_le_closed_form`):
   `θ ≤ 2 − 1/λ∞ = (13524 e − 7359)/(9451 e − 3286) ≈ 1.3123733021151`.
-/
public import Mathlib
public import SumDifference.ThetaTwoCopyLemma
public import SumDifference.ThetaGridClosedForm
public import SumDifference.ThetaMultiScaleCore

@[expose] public section

open Finset Real Pointwise

namespace SumsDifferences

namespace CoupledForms

open CoupledEntropy

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-! ### The mirror image of a coupled pair -/

/-- The reflected set of pairs `{(−y, −x) : (x, y) ∈ Γ}`. -/
def mirror (Γ : Finset (G × G)) : Finset (G × G) := Γ.image (fun q => (-q.2, -q.1))

omit [DecidableEq G] in
lemma mirror_injective : Function.Injective (fun q : G × G => (-q.2, -q.1)) := by
  intro a b h
  simp only [Prod.mk.injEq, neg_inj] at h
  exact Prod.ext h.2 h.1

lemma card_mirror (Γ : Finset (G × G)) : #(mirror Γ) = #Γ :=
  card_image_of_injective _ mirror_injective

/-- Reflection `x ↦ −x` on laws. -/
noncomputable def negMap : AddMonoidAlgebra ℝ G →+* AddMonoidAlgebra ℝ G :=
  AddMonoidAlgebra.mapDomainRingHom ℝ (negAddMonoidHom : G →+ G)

omit [DecidableEq G] in
lemma negMap_apply_neg (f : AddMonoidAlgebra ℝ G) (y : G) : (negMap f).coeff (-y) = f.coeff y := by
  show Finsupp.mapDomain (fun x : G => -x) f.coeff (-y) = f.coeff y
  exact Finsupp.mapDomain_apply_of_injective neg_injective f.coeff y

omit [DecidableEq G] in
lemma negMap_single (a : G) (r : ℝ) :
    negMap (AddMonoidAlgebra.single a r) = AddMonoidAlgebra.single (-a) r := by
  show AddMonoidAlgebra.mapDomain (fun x : G => -x) (AddMonoidAlgebra.single a r) = AddMonoidAlgebra.single (-a) r
  exact AddMonoidAlgebra.mapDomain_single

lemma ent_negMap (f : AddMonoidAlgebra ℝ G) : ent (negMap f) = ent f := by
  have hsub : (negMap f).coeff.support ⊆ f.coeff.support.image (fun x => -x) := by
    intro z hz
    rw [Finsupp.mem_support_iff] at hz
    refine Finset.mem_image.mpr ⟨-z, ?_, neg_neg z⟩
    rw [Finsupp.mem_support_iff, ← negMap_apply_neg f (-z), neg_neg]
    exact hz
  rw [← entropy_eq_ent_of_subset hsub]
  unfold ent entropy
  rw [Finset.sum_image (fun a _ b _ h => neg_injective h)]
  exact Finset.sum_congr rfl fun y _ => by rw [negMap_apply_neg]

lemma margFst_mirror (Γ : Finset (G × G)) : margFst (mirror Γ) = negMap (margSnd Γ) := by
  unfold margFst margSnd mirror
  rw [card_image_of_injective _ mirror_injective,
    Finset.sum_image (fun a _ b _ h => mirror_injective h), map_sum]
  exact Finset.sum_congr rfl fun q _ => (negMap_single _ _).symm

lemma margSnd_mirror (Γ : Finset (G × G)) : margSnd (mirror Γ) = negMap (margFst Γ) := by
  unfold margFst margSnd mirror
  rw [card_image_of_injective _ mirror_injective,
    Finset.sum_image (fun a _ b _ h => mirror_injective h), map_sum]
  exact Finset.sum_congr rfl fun q _ => (negMap_single _ _).symm

lemma ent_P_mirror (Γ : Finset (G × G)) (i j : ℕ) :
    ent (P (margFst (mirror Γ)) (margSnd (mirror Γ)) i j) = ent (P (margFst Γ) (margSnd Γ) j i) := by
  rw [margFst_mirror, margSnd_mirror]
  unfold P
  rw [← map_pow, ← map_pow, ← map_mul, ent_negMap, mul_comm]

/-- **Symmetric two-copy inequality** (Corollary 4.3): the average of Proposition 4.1 for `Γ` and
for its mirror image. -/
theorem two_copy_ineq_sym {Γ : Finset (G × G)} (hΓ : Γ.Nonempty)
    (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') {X Y : Finset G}
    (hXY : Γ ⊆ X ×ˢ Y) :
    22882 * Real.log #Γ ≤ 5820 * Real.log #(X + Y)
      + 8694 * ent (P (margFst Γ) (margSnd Γ) 1 1)
      + 11645 * (ent (P (margFst Γ) (margSnd Γ) 1 0) + ent (P (margFst Γ) (margSnd Γ) 0 1))
      + 685 * (ent (P (margFst Γ) (margSnd Γ) 2 0) + ent (P (margFst Γ) (margSnd Γ) 0 2)) := by
  have h1 := two_copy_ineq hΓ hinj hXY
  have hΓ' : (mirror Γ).Nonempty := hΓ.image _
  have hinj' : ∀ q ∈ mirror Γ, ∀ q' ∈ mirror Γ, q.1 - q.2 = q'.1 - q'.2 → q = q' := by
    intro q hq q' hq' hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq'
    have : a = b := hinj a ha b hb (by simp only [neg_sub_neg] at hd; exact hd)
    rw [this]
  have hXY' : mirror Γ ⊆ (-Y) ×ˢ (-X) := by
    intro q hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    have := hXY ha
    rw [Finset.mem_product] at this ⊢
    exact ⟨Finset.neg_mem_neg this.2, Finset.neg_mem_neg this.1⟩
  have h2 := two_copy_ineq hΓ' hinj' hXY'
  have hc : #((-Y) + (-X)) = #(X + Y) := by
    rw [← neg_add, Finset.card_neg, add_comm]
  rw [hc, card_mirror, ent_P_mirror, ent_P_mirror, ent_P_mirror, ent_P_mirror, ent_P_mirror] at h2
  linarith

end CoupledForms

namespace ClosedForm

open CoupledEntropy CoupledForms

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [AddCommGroup G] [DecidableEq G] in
lemma ent_nonneg_of_isLaw {f : AddMonoidAlgebra ℝ G} (hf : IsLaw f) : 0 ≤ ent f := by
  unfold ent entropy
  refine Finset.sum_nonneg fun x hx => Real.negMulLog_nonneg (hf.1 x) ?_
  rw [← hf.2]
  exact Finset.single_le_sum (fun y _ => hf.1 y) hx

/-- **Entropic pair inequality** (proof of Theorem 1.1): Lemmas 3.2, 3.3, Corollary 4.3 and
Proposition 5.1 give `(21512 e + 3148) log #Γ ≤ (37804 e − 13144) log #(X + Y)`. -/
theorem log_card_le_of_coupling_closed {Γ : Finset (G × G)} (hΓ : Γ.Nonempty)
    (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') {X Y : Finset G}
    (hXY : Γ ⊆ X ×ˢ Y) :
    (21512 * exp 1 + 3148) * Real.log #Γ ≤ (37804 * exp 1 - 13144) * Real.log #(X + Y) := by
  have hμ : IsLaw (margFst Γ) := isLaw_margFst hΓ
  have hν : IsLaw (margSnd Γ) := isLaw_margSnd hΓ
  refine GridClosedForm.grid_closed_form (fun i j => ent (P (margFst Γ) (margSnd Γ) i j)) _ _
    (fun i j => (grid_concave hμ hν i j).1) (fun i j => (grid_concave hμ hν i j).2.1)
    (fun i j => (grid_concave hμ hν i j).2.2.1) (fun i j => (grid_concave hμ hν i j).2.2.2)
    (fun i j => ent_nonneg_of_isLaw (isLaw_P hμ hν i j)) (fun i j => link hΓ hinj i j)
    ?_ (two_copy_ineq_sym hΓ hinj hXY)
  have := ent_mul_le_log_card hμ hν (support_margFst_subset hXY) (support_margSnd_subset hXY)
  simpa [P] using this

/-- The exponent `λ∞ = (37804 e − 13144)/(21512 e + 3148) ≈ 1.4542774489` of Theorem 1.1. -/
noncomputable def lamInf : ℝ := (37804 * exp 1 - 13144) / (21512 * exp 1 + 3148)

lemma one_le_lamInf : 1 ≤ lamInf := by
  have := Real.exp_one_gt_d9
  unfold lamInf
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- **`|X − Y| ≤ |X + Y|^{λ∞}`** for all finite sets in an abelian group. -/
theorem card_sub_le_rpow_closed (X Y : Finset G) :
    (#(X - Y) : ℝ) ≤ (#(X + Y) : ℝ) ^ lamInf := by
  have hE := Real.exp_one_gt_d9
  rcases X.eq_empty_or_nonempty with rfl | hX
  · simp only [Finset.empty_sub, Finset.card_empty, Nat.cast_zero]; positivity
  rcases Y.eq_empty_or_nonempty with rfl | hY
  · simp only [Finset.sub_empty, Finset.card_empty, Nat.cast_zero]; positivity
  have hd : (0 : ℝ) < #(X - Y) := by exact_mod_cast (hX.sub hY).card_pos
  have hs : (0 : ℝ) < #(X + Y) := by exact_mod_cast (hX.add hY).card_pos
  rw [Real.le_rpow_iff_log_le hd hs]
  obtain ⟨Γ, hΓXY, hcard, hinj⟩ := exists_coupling X Y
  have hΓ : Γ.Nonempty := by
    rw [← Finset.card_pos, hcard, Finset.card_pos]
    exact hX.sub hY
  have key := log_card_le_of_coupling_closed hΓ hinj hΓXY
  rw [hcard] at key
  unfold lamInf
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  linarith

lemma lamInf_eq : lamInf = (9451 * exp 1 - 3286) / (5378 * exp 1 + 787) := by
  unfold lamInf
  rw [div_eq_div_iff (by linarith [Real.exp_one_gt_d9]) (by linarith [Real.exp_one_gt_d9])]
  ring

end ClosedForm

/-- **Theorem 1.1: the entropic pair ceiling.**  In *every* abelian group, for all finite sets `X`,
`Y`, with no constant:
`|X − Y| ≤ |X + Y|^{λ∞}`, `λ∞ = (9451 e − 3286)/(5378 e + 787) ≈ 1.4542774489`. -/
theorem pair_ceiling_entropic {G : Type*} [AddCommGroup G] [DecidableEq G] (X Y : Finset G) :
    (#(X - Y) : ℝ) ≤ (#(X + Y) : ℝ) ^ ((9451 * exp 1 - 3286) / (5378 * exp 1 + 787)) := by
  rw [← ClosedForm.lamInf_eq]
  exact ClosedForm.card_sub_le_rpow_closed X Y

/-- **`λ_* ≤ λ∞`** (proof of Corollary 1.3): the pair exponent is at most the entropic
exponent. -/
theorem lamSup_le_closed_form : lamSup ≤ (9451 * exp 1 - 3286) / (5378 * exp 1 + 787) :=
  lamSup_le_of_pair_ceiling pair_ceiling_entropic

/-- **Corollary 1.3: `θ ≤ (13524 e − 7359)/(9451 e − 3286) ≈ 1.3123733021151`**, from
`θ ≤ 2 − 1/λ_*` (Theorem 1.2, `theta_le_two_sub_inv_lamSup`) and `λ_* ≤ λ∞`
(`lamSup_le_closed_form`); standard axioms only. -/
theorem theta_le_closed_form : theta ≤ (13524 * exp 1 - 7359) / (9451 * exp 1 - 3286) := by
  have hE := Real.exp_one_gt_d9
  have h1 := theta_le_two_sub_inv_lamSup
  have h2 := lamSup_le_closed_form
  have h0 : (0 : ℝ) < lamSup := lt_of_lt_of_le one_pos one_le_lamSup
  have h3 : 1 / ((9451 * exp 1 - 3286) / (5378 * exp 1 + 787)) ≤ 1 / lamSup :=
    one_div_le_one_div_of_le h0 h2
  have e : 2 - 1 / ((9451 * exp 1 - 3286) / (5378 * exp 1 + 787))
      = (13524 * exp 1 - 7359) / (9451 * exp 1 - 3286) := by
    have h4 : (9451 * exp 1 - 3286) ≠ 0 := by linarith
    have h5 : (5378 * exp 1 + 787) ≠ 0 := by linarith
    field_simp
    ring
  linarith

/-- The bound of Corollary 1.3 is smaller than `2 − 1/λ₂₁ = 50808459084/38714944141`, where
`λ₂₁ = 38714944141/26621429198`; the difference is about `1.2·10⁻¹¹`. -/
theorem closed_form_lt_degree21 :
    (13524 * exp 1 - 7359) / (9451 * exp 1 - 3286) < 50808459084 / 38714944141 := by
  have hE := Real.exp_one_lt_d9
  have hE' := Real.exp_one_gt_d9
  rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
  linarith

end SumsDifferences
