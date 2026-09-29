module

public import Mathlib
public import SumDifference.ThetaDefs

/-!
# Localisation and Plünnecke–Ruzsa for the transfer (Part I)

§2 of the proof paper: the reduction to the window `|A+B| ≤ 2|A|`
(`admissible_le_of_rpow_bound`, Lemma 2.1), the maximal translate packing
(`exists_translate_packing`, Lemma 2.2), the localisation inequality
(`card_sub_mul_card_le_localized_const`, Lemma 2.3, stated with an optional constant `C`) and the
Plünnecke–Ruzsa inequality in real form (`card_nsmul_sub_nsmul_le_real`).
-/

@[expose] public section

open Finset Pointwise

namespace SumsDifferences

/-- **Reduction to `K = 2`** (Lemma 2.1): an inequality `|A-B| ≤ C |A+B|^r` valid on the whole
window `|A+B| ≤ 2|A|` forces every admissible exponent to be at most `r`. -/
theorem admissible_le_of_rpow_bound {θ r C : ℝ} (hC : 0 < C)
    (hbound : ∀ A B : Finset ℤ, A.Nonempty → B.Nonempty → (#(A + B) : ℝ) ≤ 2 * #A →
      (#(A - B) : ℝ) ≤ C * (#(A + B) : ℝ) ^ r)
    (h : Admissible θ) : θ ≤ r := by
  obtain ⟨-, hfam⟩ := h
  obtain ⟨c, hc, hAB⟩ := hfam 2 one_lt_two
  by_contra hlt
  push_neg at hlt
  set δ : ℝ := θ - r with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set M : ℝ := C / c with hMdef
  have hMpos : 0 < M := by rw [hMdef]; positivity
  set N : ℕ := ⌈M ^ (1 / δ)⌉₊ + 1 with hNdef
  obtain ⟨A, B, hcard, hBne, hsmall, hlow⟩ := hAB (max N 1)
  have hAne : A.Nonempty := by
    rw [← card_pos]
    have : 1 ≤ #A := le_trans (le_max_right N 1) hcard
    omega
  have hs : (0 : ℝ) < #(A + B) := by exact_mod_cast (hAne.add hBne).card_pos
  have hsN : (N : ℝ) ≤ (#(A + B) : ℝ) := by
    have h1 : #A ≤ #(A + B) := card_le_card_add_right hBne
    have h2 : N ≤ #A := le_trans (le_max_left N 1) hcard
    exact_mod_cast le_trans h2 h1
  have hbig : M ^ (1 / δ) < (#(A + B) : ℝ) := by
    have h1 := Nat.le_ceil (M ^ (1 / δ))
    have hN : (N : ℝ) = (⌈M ^ (1 / δ)⌉₊ : ℝ) + 1 := by rw [hNdef]; push_cast; ring
    rw [hN] at hsN
    linarith
  have hupper := hbound A B hAne hBne hsmall
  have hsplit : (#(A + B) : ℝ) ^ θ = (#(A + B) : ℝ) ^ δ * (#(A + B) : ℝ) ^ r := by
    rw [← Real.rpow_add hs, hδdef]; ring_nf
  have hrpos : (0 : ℝ) < (#(A + B) : ℝ) ^ r := Real.rpow_pos_of_pos hs r
  have hcontr : c * (#(A + B) : ℝ) ^ δ ≤ C := by
    have hchain : c * (#(A + B) : ℝ) ^ θ ≤ C * (#(A + B) : ℝ) ^ r := le_trans hlow hupper
    rw [hsplit] at hchain
    have : (c * (#(A + B) : ℝ) ^ δ) * (#(A + B) : ℝ) ^ r ≤ C * (#(A + B) : ℝ) ^ r := by
      nlinarith
    exact le_of_mul_le_mul_right this hrpos
  have hgt : M < (#(A + B) : ℝ) ^ δ := by
    have h2 : (M ^ (1 / δ)) ^ δ < ((#(A + B) : ℝ)) ^ δ :=
      Real.rpow_lt_rpow (by positivity) hbig hδ
    rwa [← Real.rpow_mul hMpos.le, one_div, inv_mul_cancel₀ (ne_of_gt hδ), Real.rpow_one] at h2
  rw [hMdef, div_lt_iff₀ hc] at hgt
  nlinarith

namespace ConverseAmplification

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

/-- **Maximal translate packing** (Lemma 2.2).  For finite `A` and nonempty `D` there is `T ⊆ A` whose
translates `t + D` are pairwise disjoint and such that every `a ∈ A` satisfies
`a − t ∈ D − D` for some `t ∈ T`. -/
theorem exists_translate_packing (A D : Finset G) (hD : D.Nonempty) :
    ∃ T ⊆ A, (∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → Disjoint (t +ᵥ D) (t' +ᵥ D)) ∧
      ∀ a ∈ A, ∃ t ∈ T, a - t ∈ D - D := by
  classical
  let P : Finset (Finset G) := A.powerset.filter
    (fun T => ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → Disjoint (t +ᵥ D) (t' +ᵥ D))
  have hne : P.Nonempty := ⟨∅, by simp [P]⟩
  obtain ⟨T, hT, hmax⟩ := P.exists_max_image Finset.card hne
  simp only [P, mem_filter, mem_powerset] at hT
  refine ⟨T, hT.1, hT.2, fun a ha => ?_⟩
  by_cases haT : a ∈ T
  · obtain ⟨d, hd⟩ := hD
    exact ⟨a, haT, by simpa using sub_mem_sub hd hd⟩
  · by_contra hcon
    push_neg at hcon
    have hmem : insert a T ∈ P := by
      simp only [P, mem_filter, mem_powerset]
      refine ⟨insert_subset ha hT.1, ?_⟩
      have key : ∀ t ∈ T, Disjoint (a +ᵥ D) (t +ᵥ D) := by
        intro t ht
        rw [Finset.disjoint_left]
        intro x hx hx'
        obtain ⟨d, hd, rfl⟩ := Finset.mem_vadd_finset.1 hx
        obtain ⟨d', hd', hdd⟩ := Finset.mem_vadd_finset.1 hx'
        apply hcon t ht
        have : a - t = d' - d := by
          simp only [vadd_eq_add] at hdd
          rw [sub_eq_sub_iff_add_eq_add, ← hdd]; abel
        rw [this]; exact sub_mem_sub hd' hd
      intro t ht t' ht' hne
      rw [mem_insert] at ht ht'
      rcases ht with rfl | ht <;> rcases ht' with rfl | ht'
      · exact absurd rfl hne
      · exact key t' ht'
      · exact (key t ht).symm
      · exact hT.2 t ht t' ht' hne
    have := hmax _ hmem
    rw [card_insert_of_notMem haT] at this
    omega

/-- `x ≤ U` and `x ≤ v^λ` give `x ≤ U^{1−1/λ} v` (for `λ ≥ 1`). -/
theorem le_rpow_mul_of_le_of_le_rpow {x U v lam : ℝ} (hx : 0 ≤ x) (hlam : 1 ≤ lam)
    (hU : x ≤ U) (hv0 : 0 ≤ v) (hv : x ≤ v ^ lam) : x ≤ U ^ (1 - 1 / lam) * v := by
  have hl0 : 0 < lam := by linarith
  have h1 : x = x ^ (1 - 1 / lam) * x ^ (1 / lam) := by
    rw [← Real.rpow_add' hx (by norm_num)]; simp
  have ha : 0 ≤ 1 - 1 / lam := by
    rw [sub_nonneg, div_le_one hl0]; exact hlam
  have h2 : x ^ (1 - 1 / lam) ≤ U ^ (1 - 1 / lam) := Real.rpow_le_rpow hx hU ha
  have h3 : x ^ (1 / lam) ≤ v := by
    calc x ^ (1 / lam) ≤ (v ^ lam) ^ (1 / lam) :=
          Real.rpow_le_rpow hx hv (one_div_pos.2 hl0).le
      _ = v := by rw [one_div, Real.rpow_rpow_inv hv0 hl0.ne']
  rw [h1]
  exact mul_le_mul h2 h3 (Real.rpow_nonneg hx _) (Real.rpow_nonneg (hx.trans hU) _)

/-- **The localisation inequality with a constant** (Lemma 2.3 with a constant `C`).  If every subset `X ⊆ A` lying in a
translate of `D − D` satisfies `|X − B| ≤ C|X + B|^λ` (`C > 0`, `λ ≥ 1`), then for every nonempty
`D`, `|A − B| · |D| ≤ C^{1/λ} |D − D − B|^{1−1/λ} · |A + B| · |D − D + D − B|`. -/
theorem card_sub_mul_card_le_localized_const (A B D : Finset G) (hD : D.Nonempty) {lam C : ℝ}
    (hlam : 1 ≤ lam) (hC : 0 < C)
    (hpair : ∀ X ⊆ A, ∀ t : G, X ⊆ t +ᵥ (D - D) →
      (#(X - B) : ℝ) ≤ C * (#(X + B) : ℝ) ^ lam) :
    (#(A - B) : ℝ) * #D ≤
      C ^ (1 / lam) * ((#(D - D - B) : ℝ) ^ (1 - 1 / lam) * #(A + B) * #(D - D + D - B)) := by
  have hlam0 : 0 < lam := by linarith
  classical
  obtain ⟨T, -, hdisj, hcov⟩ := exists_translate_packing A D hD
  let f : G → G := fun a => if h : a ∈ A then Classical.choose (hcov a h) else 0
  have hfT : ∀ a ∈ A, f a ∈ T := fun a ha => by
    simp only [f, dif_pos ha]; exact (Classical.choose_spec (hcov a ha)).1
  have hfD : ∀ a ∈ A, a - f a ∈ D - D := fun a ha => by
    simp only [f, dif_pos ha]; exact (Classical.choose_spec (hcov a ha)).2
  let P : G → Finset G := fun t => A.filter (fun a => f a = t)
  have hPA : ∀ t, P t ⊆ A := fun t => filter_subset _ _
  set U : ℝ := (#(D - D - B) : ℝ) with hUdef
  -- the pieces cover the difference set
  have hcover : A - B ⊆ T.biUnion (fun t => P t - B) := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sub.1 hx
    exact mem_biUnion.2 ⟨f a, hfT a ha, sub_mem_sub (mem_filter.2 ⟨ha, rfl⟩) hb⟩
  have hstep2 : (#(A - B) : ℝ) ≤ ∑ t ∈ T, (#(P t - B) : ℝ) := by
    have := (card_le_card hcover).trans card_biUnion_le
    exact_mod_cast this
  -- each piece: capacity bound and pair ceiling
  have hpiece : ∀ t ∈ T, (#(P t - B) : ℝ) ≤
      U ^ (1 - 1 / lam) * (C ^ (1 / lam) * #(P t + B)) := by
    intro t _
    have hloc : P t ⊆ t +ᵥ (D - D) := by
      intro a ha
      obtain ⟨haA, hat⟩ := mem_filter.1 ha
      refine mem_vadd_finset.2 ⟨a - t, hat ▸ hfD a haA, ?_⟩
      simp only [vadd_eq_add]; abel
    have hCv : (#(P t - B) : ℝ) ≤ (C ^ (1 / lam) * #(P t + B)) ^ lam := by
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hC.le,
        one_div, inv_mul_cancel₀ hlam0.ne', Real.rpow_one]
      exact hpair _ (hPA t) t hloc
    apply le_rpow_mul_of_le_of_le_rpow (by positivity) hlam _ (by positivity) hCv
    have hsub : P t - B ⊆ t +ᵥ (D - D - B) := by
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_sub.1 hx
      obtain ⟨haA, hat⟩ := mem_filter.1 ha
      have h1 : a - t ∈ D - D := hat ▸ hfD a haA
      refine mem_vadd_finset.2 ⟨(a - t) - b, sub_mem_sub h1 hb, ?_⟩
      simp only [vadd_eq_add]; abel
    have := card_le_card hsub
    rw [card_vadd_finset] at this
    rw [hUdef]
    exact_mod_cast this
  -- bounded overlap of the pieces' sumsets
  have hmult : ∀ w, (#(T.filter (fun t => w ∈ P t + B)) : ℝ) * #D ≤ #(D - D + D - B) := by
    intro w
    set S := T.filter (fun t => w ∈ P t + B)
    have hsub : S.biUnion (fun t => t +ᵥ D) ⊆ w +ᵥ (D - D + D - B) := by
      intro x hx
      obtain ⟨t, htS, hx⟩ := mem_biUnion.1 hx
      obtain ⟨-, hw⟩ := mem_filter.1 htS
      obtain ⟨a, ha, b, hb, hab⟩ := mem_add.1 hw
      obtain ⟨haA, hat⟩ := mem_filter.1 ha
      have h1 : a - t ∈ D - D := hat ▸ hfD a haA
      obtain ⟨y, hy, z, hz, hyz⟩ := mem_sub.1 h1
      obtain ⟨d, hd, rfl⟩ := mem_vadd_finset.1 hx
      refine mem_vadd_finset.2 ⟨(z - y) + d - b,
        sub_mem_sub (add_mem_add (sub_mem_sub hz hy) hd) hb, ?_⟩
      simp only [vadd_eq_add]
      rw [← hab]
      have : t = a - (y - z) := by rw [hyz]; abel
      rw [this]; abel
    have hcard : #(S.biUnion (fun t => t +ᵥ D)) = #S * #D := by
      rw [card_biUnion]
      · simp [card_vadd_finset]
      · intro t ht t' ht' hne
        exact hdisj t (mem_filter.1 ht).1 t' (mem_filter.1 ht').1 hne
    have := card_le_card hsub
    rw [card_vadd_finset, hcard] at this
    exact_mod_cast this
  have hsum : (∑ t ∈ T, (#(P t + B) : ℝ)) * #D ≤ #(A + B) * #(D - D + D - B) := by
    have hdc : ∑ t ∈ T, (#(P t + B) : ℝ) =
        ∑ w ∈ A + B, (#(T.filter (fun t => w ∈ P t + B)) : ℝ) := by
      have h1 : ∀ t, (#(P t + B) : ℝ) = ∑ w ∈ A + B, if w ∈ P t + B then (1:ℝ) else 0 := by
        intro t
        rw [sum_boole]
        congr 2
        ext w
        simp only [mem_filter]
        constructor
        · intro hw; exact ⟨add_subset_add_right (hPA t) hw, hw⟩
        · intro hw; exact hw.2
      simp_rw [h1]
      rw [sum_comm]
      congr 1; ext w
      rw [sum_boole]
    rw [hdc, sum_mul]
    calc ∑ w ∈ A + B, (#(T.filter (fun t => w ∈ P t + B)) : ℝ) * #D
        ≤ ∑ w ∈ A + B, (#(D - D + D - B) : ℝ) := sum_le_sum fun w _ => hmult w
      _ = #(A + B) * #(D - D + D - B) := by rw [sum_const, nsmul_eq_mul]
  calc (#(A - B) : ℝ) * #D ≤ (∑ t ∈ T, (#(P t - B) : ℝ)) * #D :=
        mul_le_mul_of_nonneg_right hstep2 (by positivity)
    _ ≤ (∑ t ∈ T, U ^ (1 - 1 / lam) * (C ^ (1 / lam) * (#(P t + B) : ℝ))) * #D :=
        mul_le_mul_of_nonneg_right (sum_le_sum hpiece) (by positivity)
    _ = C ^ (1 / lam) * U ^ (1 - 1 / lam) * ((∑ t ∈ T, (#(P t + B) : ℝ)) * #D) := by
        rw [sum_mul, sum_mul, mul_sum]
        exact sum_congr rfl fun _ _ => by ring
    _ ≤ C ^ (1 / lam) * U ^ (1 - 1 / lam) * (#(A + B) * #(D - D + D - B)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- **The localisation inequality** (Lemma 2.3, `C = 1`).  If every subset `X ⊆ A` lying in a translate of `D − D`
satisfies the pair ceiling `|X − B| ≤ |X + B|^λ`, then for every nonempty `D`
`|A − B| · |D| ≤ |D − D − B|^{1−1/λ} · |A + B| · |D − D + D − B|`. -/
theorem card_sub_mul_card_le_localized (A B D : Finset G) (hD : D.Nonempty) {lam : ℝ}
    (hlam : 1 ≤ lam)
    (hpair : ∀ X ⊆ A, ∀ t : G, X ⊆ t +ᵥ (D - D) → (#(X - B) : ℝ) ≤ (#(X + B) : ℝ) ^ lam) :
    (#(A - B) : ℝ) * #D ≤
      (#(D - D - B) : ℝ) ^ (1 - 1 / lam) * #(A + B) * #(D - D + D - B) := by
  have := card_sub_mul_card_le_localized_const A B D hD hlam one_pos
    (fun X hX t ht => by rw [one_mul]; exact hpair X hX t ht)
  rwa [Real.one_rpow, one_mul] at this

/-- Plünnecke–Ruzsa in real form: `|A + B| ≤ K|A| ⟹ |mB − nB| ≤ K^{m+n}|A|` (from Mathlib's
`pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add`). -/
theorem card_nsmul_sub_nsmul_le_real {A B : Finset G} {K : ℝ} (hA : A.Nonempty)
    (hK : (#(A + B) : ℝ) ≤ K * #A) (m n : ℕ) :
    (#(m • B - n • B) : ℝ) ≤ K ^ (m + n) * #A := by
  have hm : (0 : ℝ) < #A := by exact_mod_cast hA.card_pos
  have hplu : (#(m • B - n • B) : ℝ) ≤ ((#(A + B) : ℝ) / (#A : ℝ)) ^ (m + n) * (#A : ℝ) := by
    have h := pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add hA B m n
    have := (NNRat.cast_le (K := ℝ)).mpr h
    push_cast at this
    exact this
  refine hplu.trans (mul_le_mul_of_nonneg_right ?_ hm.le)
  have h0 : 0 ≤ (#(A + B) : ℝ) / #A := by positivity
  have h1 : (#(A + B) : ℝ) / #A ≤ K := by rw [div_le_iff₀ hm]; exact hK
  exact pow_le_pow_left₀ h0 h1 _

end ConverseAmplification

end SumsDifferences
