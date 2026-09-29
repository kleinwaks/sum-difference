/-
# Joint entropy, data processing and subadditivity for finitely supported laws

`SumDifference/FinEntropy.lean` provides `entropy` and `pushEntropy` together with the
maximum-entropy bound.  This file adds the three structural facts needed to run an entropy
argument with several random variables defined on the same finite probability space:

* `pushWeight_comp` / `pushEntropy_comp` — the chain rule for pushforwards: the law of `ψ ∘ f`
  is the pushforward along `ψ` of the law of `f`;
* `pushEntropy_le_entropy` and `pushEntropy_comp_le` — **data processing**: coarsening a random
  variable cannot increase its entropy;
* `pushEntropy_pair_le` — **subadditivity**: `H(f, g) ≤ H(f) + H(g)`.

The first two are proved from the monotonicity of `log`, the third from Gibbs' inequality
(`entropy_le_of_gibbs`).
-/
import Mathlib
import SumDifference.FinEntropy

open Finset

namespace SumsDifferences

variable {ι α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-! ## Chain rule for pushforwards -/

/-- The pushforward of a pushforward: `pushWeight` composes. -/
theorem pushWeight_comp (s : Finset ι) (p : ι → ℝ) (f : ι → α) (ψ : α → γ) (c : γ) :
    pushWeight (s.image f) (pushWeight s p f) ψ c = pushWeight s p (fun i => ψ (f i)) c := by
  classical
  simp only [pushWeight]
  have h1 : ∀ a ∈ (s.image f).filter (fun a => ψ a = c),
      ∑ i ∈ s with f i = a, p i
        = ∑ i ∈ (s.filter (fun i => ψ (f i) = c)) with f i = a, p i := by
    intro a ha
    simp only [Finset.mem_filter] at ha
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hi, rfl⟩; exact ⟨⟨hi, ha.2⟩, rfl⟩
    · rintro ⟨⟨hi, _⟩, rfl⟩; exact ⟨hi, rfl⟩
  rw [Finset.sum_congr rfl h1]
  refine Finset.sum_fiberwise_of_maps_to (fun i hi => ?_) p
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨Finset.mem_image_of_mem f hi.1, hi.2⟩

/-- `H(ψ ∘ f)` may be computed on the law of `f`. -/
theorem pushEntropy_comp (s : Finset ι) (p : ι → ℝ) (f : ι → α) (ψ : α → γ) :
    pushEntropy s p (fun i => ψ (f i)) = pushEntropy (s.image f) (pushWeight s p f) ψ := by
  classical
  simp only [pushEntropy]
  rw [Finset.image_image]
  exact Finset.sum_congr rfl fun c _ => by rw [pushWeight_comp]

/-! ## Data processing -/

/-- **Merging atoms decreases entropy.** -/
theorem pushEntropy_le_entropy {t : Finset ι} {ν : ι → ℝ} (hν : ∀ i ∈ t, 0 ≤ ν i) (ψ : ι → α) :
    pushEntropy t ν ψ ≤ entropy t ν := by
  classical
  have key : ∀ a ∈ t.image ψ, Real.negMulLog (pushWeight t ν ψ a)
      ≤ ∑ i ∈ t with ψ i = a, Real.negMulLog (ν i) := by
    intro a _
    set F := t.filter (fun i => ψ i = a) with hF
    have hsub : F ⊆ t := Finset.filter_subset _ _
    have hnn : ∀ i ∈ F, 0 ≤ ν i := fun i hi => hν i (hsub hi)
    have hle : ∀ i ∈ F, ν i ≤ ∑ j ∈ F, ν j := fun i hi => Finset.single_le_sum hnn hi
    have hstep : ∀ i ∈ F, -(ν i * Real.log (∑ j ∈ F, ν j)) ≤ Real.negMulLog (ν i) := by
      intro i hi
      rcases eq_or_lt_of_le (hnn i hi) with h | h
      · simp [Real.negMulLog, ← h]
      · have hlog : Real.log (ν i) ≤ Real.log (∑ j ∈ F, ν j) := Real.log_le_log h (hle i hi)
        simp only [Real.negMulLog]
        nlinarith
    calc Real.negMulLog (pushWeight t ν ψ a)
        = -((∑ i ∈ F, ν i) * Real.log (∑ j ∈ F, ν j)) := by
          simp [pushWeight, Real.negMulLog, hF]
      _ = ∑ i ∈ F, -(ν i * Real.log (∑ j ∈ F, ν j)) := by rw [Finset.sum_mul]; simp
      _ ≤ ∑ i ∈ F, Real.negMulLog (ν i) := Finset.sum_le_sum hstep
  calc pushEntropy t ν ψ = ∑ a ∈ t.image ψ, Real.negMulLog (pushWeight t ν ψ a) := rfl
    _ ≤ ∑ a ∈ t.image ψ, ∑ i ∈ t with ψ i = a, Real.negMulLog (ν i) := Finset.sum_le_sum key
    _ = entropy t ν :=
        Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem ψ hi) _

/-- **Data processing**: a function of a random variable has no more entropy. -/
theorem pushEntropy_comp_le {s : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i)
    (f : ι → α) (ψ : α → γ) :
    pushEntropy s p (fun i => ψ (f i)) ≤ pushEntropy s p f := by
  rw [pushEntropy_comp]
  exact pushEntropy_le_entropy (fun a _ => pushWeight_nonneg hp a) ψ

/-! ## Subadditivity -/

/-- **Subadditivity of entropy, abstract form**: a law on a finite set of pairs has entropy at
most the sum of the entropies of its two marginals. -/
theorem entropy_le_pushEntropy_fst_add_snd {K : Finset (α × β)} {P : α × β → ℝ}
    (hP : ∀ z ∈ K, 0 ≤ P z) (hsum : ∑ z ∈ K, P z = 1) :
    entropy K P ≤ pushEntropy K P Prod.fst + pushEntropy K P Prod.snd := by
  classical
  set pf := pushWeight K P Prod.fst with hpf
  set pg := pushWeight K P Prod.snd with hpg
  have hpf0 : ∀ a, 0 ≤ pf a := fun a => pushWeight_nonneg hP a
  have hpg0 : ∀ b, 0 ≤ pg b := fun b => pushWeight_nonneg hP b
  -- each marginal dominates the joint weight
  have hdom1 : ∀ z ∈ K, P z ≤ pf z.1 := by
    intro z hz
    refine Finset.single_le_sum (f := P) (fun i hi => hP i (Finset.mem_filter.mp hi).1) ?_
    exact Finset.mem_filter.mpr ⟨hz, rfl⟩
  have hdom2 : ∀ z ∈ K, P z ≤ pg z.2 := by
    intro z hz
    refine Finset.single_le_sum (f := P) (fun i hi => hP i (Finset.mem_filter.mp hi).1) ?_
    exact Finset.mem_filter.mpr ⟨hz, rfl⟩
  -- Gibbs against the product of the marginals
  have hKsub : K ⊆ (K.image Prod.fst) ×ˢ (K.image Prod.snd) := by
    intro z hz
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hz, Finset.mem_image_of_mem _ hz⟩
  have hqsum : ∑ z ∈ K, pf z.1 * pg z.2 ≤ ∑ z ∈ K, P z := by
    rw [hsum]
    calc ∑ z ∈ K, pf z.1 * pg z.2
        ≤ ∑ z ∈ (K.image Prod.fst) ×ˢ (K.image Prod.snd), pf z.1 * pg z.2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hKsub
            (fun z _ _ => mul_nonneg (hpf0 _) (hpg0 _))
      _ = (∑ a ∈ K.image Prod.fst, pf a) * (∑ b ∈ K.image Prod.snd, pg b) := by
          rw [Finset.sum_product, ← Finset.sum_mul_sum]
      _ = 1 := by
          rw [hpf, hpg, sum_pushWeight, sum_pushWeight, hsum, mul_one]
  have hgibbs := entropy_le_of_gibbs (s := K) (p := P) (q := fun z => pf z.1 * pg z.2)
    hP (fun z _ => mul_nonneg (hpf0 _) (hpg0 _))
    (fun z hz hpos => mul_pos (lt_of_lt_of_le hpos (hdom1 z hz))
      (lt_of_lt_of_le hpos (hdom2 z hz))) hqsum
  -- split the cross entropy into the two marginal cross entropies
  have hsplit : ∀ z ∈ K, -(P z * Real.log (pf z.1 * pg z.2))
      = -(P z * Real.log (pf z.1)) + -(P z * Real.log (pg z.2)) := by
    intro z hz
    rcases eq_or_lt_of_le (hP z hz) with h | h
    · simp [← h]
    · rw [Real.log_mul (ne_of_gt (lt_of_lt_of_le h (hdom1 z hz)))
        (ne_of_gt (lt_of_lt_of_le h (hdom2 z hz)))]
      ring
  have hm1 : ∑ z ∈ K, -(P z * Real.log (pf z.1)) = pushEntropy K P Prod.fst := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (g := fun z : α × β => z.1) (t := K.image Prod.fst)
      (fun z hz => Finset.mem_image_of_mem _ hz)
      (fun z => -(P z * Real.log (pf z.1)))]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hc : ∀ z ∈ K.filter (fun z : α × β => z.1 = a),
        -(P z * Real.log (pf z.1)) = -(P z * Real.log (pf a)) := by
      intro z hz; rw [(Finset.mem_filter.mp hz).2]
    rw [Finset.sum_congr rfl hc]
    have hfac : ∑ z ∈ K.filter (fun z : α × β => z.1 = a), -(P z * Real.log (pf a))
        = -((∑ z ∈ K.filter (fun z : α × β => z.1 = a), P z) * Real.log (pf a)) := by
      rw [Finset.sum_mul]; simp
    rw [hfac]
    simp [Real.negMulLog, hpf, pushWeight]
  have hm2 : ∑ z ∈ K, -(P z * Real.log (pg z.2)) = pushEntropy K P Prod.snd := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (g := fun z : α × β => z.2) (t := K.image Prod.snd)
      (fun z hz => Finset.mem_image_of_mem _ hz)
      (fun z => -(P z * Real.log (pg z.2)))]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hc : ∀ z ∈ K.filter (fun z : α × β => z.2 = b),
        -(P z * Real.log (pg z.2)) = -(P z * Real.log (pg b)) := by
      intro z hz; rw [(Finset.mem_filter.mp hz).2]
    rw [Finset.sum_congr rfl hc]
    have hfac : ∑ z ∈ K.filter (fun z : α × β => z.2 = b), -(P z * Real.log (pg b))
        = -((∑ z ∈ K.filter (fun z : α × β => z.2 = b), P z) * Real.log (pg b)) := by
      rw [Finset.sum_mul]; simp
    rw [hfac]
    simp [Real.negMulLog, hpg, pushWeight]
  refine hgibbs.trans (le_of_eq ?_)
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, hm1, hm2]

/-- **Subadditivity of entropy**: `H(f, g) ≤ H(f) + H(g)`. -/
theorem pushEntropy_pair_le {s : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i)
    (hsum : ∑ i ∈ s, p i = 1) (f : ι → α) (g : ι → β) :
    pushEntropy s p (fun i => (f i, g i)) ≤ pushEntropy s p f + pushEntropy s p g := by
  classical
  set F : ι → α × β := fun i => (f i, g i) with hF
  set K := s.image F with hK
  set P := pushWeight s p F with hP
  have hP0 : ∀ z ∈ K, 0 ≤ P z := fun z _ => pushWeight_nonneg hp z
  have hPsum : ∑ z ∈ K, P z = 1 := by rw [hK, hP, sum_pushWeight, hsum]
  have h := entropy_le_pushEntropy_fst_add_snd hP0 hPsum
  have h1 : pushEntropy K P Prod.fst = pushEntropy s p f := by
    rw [hK, hP, ← pushEntropy_comp]
  have h2 : pushEntropy K P Prod.snd = pushEntropy s p g := by
    rw [hK, hP, ← pushEntropy_comp]
  rw [h1, h2] at h
  exact h

end SumsDifferences
