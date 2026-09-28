/-
# The copy lemma for finitely supported laws

For a law `p` on a finite set `s` and a "key" random variable `K : ι → κ`, the *conditionally
independent copy over `K`* is the law on pairs

  `copySet s K = {(i, j) ∈ s × s : K i = K j}`,   `copyW s p K (i, j) = p i · p j / P(K = K i)`.

Its two marginals are `p` again (`copy_sum_fst`, `copy_sum_snd`), so every random variable that
only looks at the first (or only at the second) coordinate keeps its entropy
(`pushEntropy_copy_fst`, `pushEntropy_copy_snd`), and the two coordinates are conditionally
independent given the (common) key:

  `H(F ∘ fst, G ∘ snd, K ∘ fst) + H(K) = H(F, K) + H(G, K)`       (`pushEntropy_copy_ci`).

This is the Zhang–Yeung copy lemma (Lemma 3.6 of the proof paper, in the form
`copy_step` of `SumDifference/MatusInequality.lean`), the source of all non-Shannon entropy
inequalities used in the proof.
-/
import Mathlib
import SumDifference.CondEntropy

open Finset

namespace SumsDifferences

namespace NonShannon

variable {ι κ α β : Type*} [DecidableEq κ]

/-- The support of the conditionally independent copy over `K`. -/
def copySet (s : Finset ι) (K : ι → κ) : Finset (ι × ι) :=
  (s ×ˢ s).filter (fun q => K q.1 = K q.2)

/-- The weights of the conditionally independent copy over `K`. -/
noncomputable def copyW (s : Finset ι) (p : ι → ℝ) (K : ι → κ) (q : ι × ι) : ℝ :=
  p q.1 * p q.2 / pushWeight s p K (K q.1)

theorem mem_copySet {s : Finset ι} {K : ι → κ} {q : ι × ι} :
    q ∈ copySet s K ↔ q.1 ∈ s ∧ q.2 ∈ s ∧ K q.1 = K q.2 := by
  simp [copySet, and_assoc]

theorem copyW_nonneg {s : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i) (K : ι → κ)
    {q : ι × ι} (hq : q ∈ copySet s K) : 0 ≤ copyW s p K q := by
  rw [mem_copySet] at hq
  exact div_nonneg (mul_nonneg (hp _ hq.1) (hp _ hq.2.1)) (pushWeight_nonneg hp _)

/-- A point of positive mass has positive key weight. -/
theorem pushWeight_pos_of_pos {s : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i)
    {γ : Type*} [DecidableEq γ] (F : ι → γ) {i : ι} (hi : i ∈ s) (hpi : 0 < p i) :
    0 < pushWeight s p F (F i) := by
  unfold pushWeight
  have hmem : i ∈ s.filter (fun j => F j = F i) := by simp [hi]
  calc 0 < p i := hpi
    _ ≤ ∑ j ∈ s with F j = F i, p j :=
      Finset.single_le_sum (f := p) (fun j hj => hp j (Finset.mem_filter.mp hj).1) hmem

/-- The key weight is the sum of the weights with the same key. -/
theorem pushWeight_eq_sum_ite {s : Finset ι} {p : ι → ℝ} {γ : Type*} [DecidableEq γ]
    (F : ι → γ) (a : γ) : pushWeight s p F a = ∑ j ∈ s, p j * (if F j = a then 1 else 0) := by
  unfold pushWeight
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp

/-- **First marginal of the copy.** -/
theorem copy_sum_fst {s : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i) (K : ι → κ)
    (φ : ι → ℝ) :
    ∑ q ∈ copySet s K, copyW s p K q * φ q.1 = ∑ i ∈ s, p i * φ i := by
  classical
  have h1 : ∑ q ∈ copySet s K, copyW s p K q * φ q.1
      = ∑ i ∈ s, ∑ j ∈ s, (if K i = K j then copyW s p K (i, j) * φ i else 0) := by
    rw [copySet, Finset.sum_filter, Finset.sum_product]
  rw [h1]
  refine Finset.sum_congr rfl fun i hi => ?_
  rcases (hp i hi).lt_or_eq with hpi | hpi
  · have hc := pushWeight_pos_of_pos hp K hi hpi
    have hsum : ∑ j ∈ s, (if K i = K j then copyW s p K (i, j) * φ i else 0)
        = p i * φ i / pushWeight s p K (K i) * ∑ j ∈ s, p j * (if K j = K i then 1 else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : K i = K j
      · rw [if_pos h, if_pos h.symm]; simp only [copyW]; field_simp
      · rw [if_neg h, if_neg (Ne.symm h)]; ring
    rw [hsum, ← pushWeight_eq_sum_ite]
    field_simp
  · rw [← hpi]
    simp only [copyW, zero_mul]
    exact Finset.sum_eq_zero fun j _ => by rw [← hpi]; simp

/-- **Second marginal of the copy.** -/
theorem copy_sum_snd {s : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i) (K : ι → κ)
    (φ : ι → ℝ) :
    ∑ q ∈ copySet s K, copyW s p K q * φ q.2 = ∑ i ∈ s, p i * φ i := by
  classical
  have hswap : ∑ q ∈ copySet s K, copyW s p K q * φ q.2
      = ∑ q ∈ copySet s K, copyW s p K q * φ q.1 := by
    refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
    · intro q hq
      rw [mem_copySet] at hq ⊢
      exact ⟨hq.2.1, hq.1, hq.2.2.symm⟩
    · intro q hq
      rw [mem_copySet] at hq ⊢
      exact ⟨hq.2.1, hq.1, hq.2.2.symm⟩
    · intro q _; simp
    · intro q _; simp
    · intro q hq
      rw [mem_copySet] at hq
      simp only [copyW, Prod.fst_swap, Prod.snd_swap, hq.2.2]
      ring
  rw [hswap, copy_sum_fst hp K φ]

theorem pushWeight_copy_fst {s : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i) (K : ι → κ)
    [DecidableEq α] (F : ι → α) (a : α) :
    pushWeight (copySet s K) (copyW s p K) (fun q => F q.1) a = pushWeight s p F a := by
  rw [pushWeight_eq_sum_ite, pushWeight_eq_sum_ite]
  exact copy_sum_fst hp K (fun i => if F i = a then 1 else 0)

theorem pushWeight_copy_snd {s : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i) (K : ι → κ)
    [DecidableEq α] (F : ι → α) (a : α) :
    pushWeight (copySet s K) (copyW s p K) (fun q => F q.2) a = pushWeight s p F a := by
  rw [pushWeight_eq_sum_ite, pushWeight_eq_sum_ite]
  exact copy_sum_snd hp K (fun i => if F i = a then 1 else 0)

/-- Random variables of the first coordinate keep their entropy. -/
theorem pushEntropy_copy_fst {s : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i) (K : ι → κ)
    [DecidableEq α] (F : ι → α) :
    pushEntropy (copySet s K) (copyW s p K) (fun q => F q.1) = pushEntropy s p F := by
  rw [← sum_negMulLog_pushWeight, ← sum_negMulLog_pushWeight]
  have : ∀ q ∈ copySet s K,
      -(copyW s p K q * Real.log (pushWeight (copySet s K) (copyW s p K) (fun q => F q.1) (F q.1)))
        = copyW s p K q * (-(Real.log (pushWeight s p F (F q.1)))) := by
    intro q _; rw [pushWeight_copy_fst hp K F]; ring
  rw [Finset.sum_congr rfl this, copy_sum_fst hp K (fun i => -(Real.log (pushWeight s p F (F i))))]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Random variables of the second coordinate keep their entropy. -/
theorem pushEntropy_copy_snd {s : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i) (K : ι → κ)
    [DecidableEq α] (F : ι → α) :
    pushEntropy (copySet s K) (copyW s p K) (fun q => F q.2) = pushEntropy s p F := by
  rw [← sum_negMulLog_pushWeight, ← sum_negMulLog_pushWeight]
  have : ∀ q ∈ copySet s K,
      -(copyW s p K q * Real.log (pushWeight (copySet s K) (copyW s p K) (fun q => F q.2) (F q.2)))
        = copyW s p K q * (-(Real.log (pushWeight s p F (F q.2)))) := by
    intro q _; rw [pushWeight_copy_snd hp K F]; ring
  rw [Finset.sum_congr rfl this, copy_sum_snd hp K (fun i => -(Real.log (pushWeight s p F (F i))))]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The joint weight of the copy factorises. -/
theorem pushWeight_copy_ci {s : Finset ι} {p : ι → ℝ} (K : ι → κ) [DecidableEq α] [DecidableEq β]
    (F : ι → α) (G : ι → β) (f : α) (g : β) (k : κ) :
    pushWeight (copySet s K) (copyW s p K) (fun q => (F q.1, G q.2, K q.1)) (f, g, k)
      = pushWeight s p (fun i => (F i, K i)) (f, k) * pushWeight s p (fun i => (G i, K i)) (g, k)
          / pushWeight s p K k := by
  classical
  rw [pushWeight_eq_sum_ite, pushWeight_eq_sum_ite, pushWeight_eq_sum_ite, copySet,
    Finset.sum_filter, Finset.sum_product, Finset.sum_mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [copyW, Prod.mk.injEq]
  by_cases hk : K i = K j
  · rw [if_pos hk]
    by_cases h1 : F i = f ∧ K i = k
    · by_cases h2 : G j = g ∧ K j = k
      · rw [if_pos ⟨h1.1, h2.1, h1.2⟩, if_pos h1, if_pos h2, h1.2]; ring
      · rw [if_neg (fun h => h2 ⟨h.2.1, hk ▸ h.2.2⟩), if_neg h2]; ring
    · rw [if_neg (fun h => h1 ⟨h.1, h.2.2⟩), if_neg h1]; ring
  · rw [if_neg hk]
    by_cases h1 : F i = f ∧ K i = k
    · by_cases h2 : G j = g ∧ K j = k
      · exact absurd (h1.2.trans h2.2.symm) hk
      · rw [if_neg h2]; ring
    · rw [if_neg h1]; ring

/-- **Conditional independence of the copy**:
`H(F ∘ fst, G ∘ snd, K ∘ fst) + H(K) = H(F, K) + H(G, K)`. -/
theorem pushEntropy_copy_ci {s : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i) (K : ι → κ)
    [DecidableEq α] [DecidableEq β] (F : ι → α) (G : ι → β) :
    pushEntropy (copySet s K) (copyW s p K) (fun q => (F q.1, G q.2, K q.1)) + pushEntropy s p K
      = pushEntropy s p (fun i => (F i, K i)) + pushEntropy s p (fun i => (G i, K i)) := by
  classical
  set a := pushWeight s p (fun i => (F i, K i))
  set b := pushWeight s p (fun i => (G i, K i))
  set c := pushWeight s p K
  rw [← sum_negMulLog_pushWeight (copySet s K), ← sum_negMulLog_pushWeight s p K,
    ← sum_negMulLog_pushWeight s p (fun i => (F i, K i)),
    ← sum_negMulLog_pushWeight s p (fun i => (G i, K i))]
  have hterm : ∀ q ∈ copySet s K,
      -(copyW s p K q * Real.log (pushWeight (copySet s K) (copyW s p K)
          (fun q => (F q.1, G q.2, K q.1)) (F q.1, G q.2, K q.1)))
        = copyW s p K q * (-(Real.log (a (F q.1, K q.1))))
          + copyW s p K q * (-(Real.log (b (G q.2, K q.2))))
          - copyW s p K q * (-(Real.log (c (K q.1)))) := by
    intro q hq
    have hq' := mem_copySet.mp hq
    rw [pushWeight_copy_ci K F G]
    rcases (copyW_nonneg hp K hq).lt_or_eq with hw | hw
    · have hp1 : 0 < p q.1 := by
        rcases (hp _ hq'.1).lt_or_eq with h | h
        · exact h
        · exfalso; simp only [copyW, ← h, zero_mul, zero_div] at hw; exact lt_irrefl _ hw
      have hp2 : 0 < p q.2 := by
        rcases (hp _ hq'.2.1).lt_or_eq with h | h
        · exact h
        · exfalso; simp only [copyW, ← h, mul_zero, zero_div] at hw; exact lt_irrefl _ hw
      have ha : 0 < a (F q.1, K q.1) := pushWeight_pos_of_pos hp (fun i => (F i, K i)) hq'.1 hp1
      have hb : 0 < b (G q.2, K q.2) := pushWeight_pos_of_pos hp (fun i => (G i, K i)) hq'.2.1 hp2
      have hc : 0 < c (K q.1) := pushWeight_pos_of_pos hp K hq'.1 hp1
      rw [← hq'.2.2] at hb
      rw [Real.log_div (mul_pos ha hb).ne' hc.ne', Real.log_mul ha.ne' hb.ne', hq'.2.2]
      ring
    · rw [← hw]; ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    copy_sum_fst hp K (fun i => -(Real.log (a (F i, K i)))),
    copy_sum_snd hp K (fun i => -(Real.log (b (G i, K i)))),
    copy_sum_fst hp K (fun i => -(Real.log (c (K i))))]
  have e : ∀ (w : ι → ℝ), ∑ i ∈ s, p i * -(Real.log (w i)) = ∑ i ∈ s, -(p i * Real.log (w i)) :=
    fun w => Finset.sum_congr rfl fun i _ => by ring
  rw [e, e, e]
  ring

end NonShannon

end SumsDifferences
