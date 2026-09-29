module

/-
# Equality cases of the finite-entropy inequalities

`SumDifference/FinEntropy.lean` and `SumDifference/JointEntropy.lean` prove Gibbs' inequality,
subadditivity `H(f,g) ≤ H(f) + H(g)` and data processing `H(ψ ∘ f) ≤ H(f)`.  This file supplies
the corresponding **equality cases**:

* `eq_of_gibbs_eq` — equality in Gibbs forces `q = p` pointwise;
* `pushWeight_pair_eq_mul_of_entropy_eq` — equality in subadditivity forces the joint law of
  `(f,g)` to be the product of its marginals (independence);
* `injOn_of_pushEntropy_le_entropy_eq` and `pushEntropy_comp_eq_injective` — equality in data
  processing forces the coarsening map to be injective on the support.

All three are proved by re-running the original proofs and observing that each of the pointwise
inequalities they sum must then be an equality; the strictness input is
`Real.log_lt_sub_one_of_pos`.  The proof of the proof paper uses only the
last section (`pushWeight_le_one`, `pushEntropy_nonneg`: entropy is nonnegative).
-/
public import Mathlib
public import SumDifference.FinEntropy
public import SumDifference.JointEntropy

@[expose] public section

open Finset Real

namespace SumsDifferences

variable {ι α β γ : Type*}

/-! ## Equality in Gibbs' inequality -/

/-- **Equality case of Gibbs' inequality.**  Under the hypotheses of `entropy_le_of_gibbs`,
equality forces `q` to agree with `p` on all of `s`. -/
theorem eq_of_gibbs_eq {s : Finset ι} {p q : ι → ℝ}
    (hp : ∀ i ∈ s, 0 ≤ p i) (hq0 : ∀ i ∈ s, 0 ≤ q i) (hq : ∀ i ∈ s, 0 < p i → 0 < q i)
    (hsum : ∑ i ∈ s, q i ≤ ∑ i ∈ s, p i)
    (heq : entropy s p = ∑ i ∈ s, -(p i * Real.log (q i))) :
    ∀ i ∈ s, q i = p i := by
  classical
  -- the pointwise slack of the proof of `entropy_le_of_gibbs`
  set g : ι → ℝ := fun i =>
    (q i - p i) - (Real.negMulLog (p i) - -(p i * Real.log (q i))) with hg
  have hgnn : ∀ i ∈ s, 0 ≤ g i := by
    intro i hi
    rcases eq_or_lt_of_le (hp i hi) with h | h
    · have hp0 : p i = 0 := h.symm
      simp only [hg, hp0]
      simpa using hq0 i hi
    · have hqi := hq i hi h
      have hlog : Real.log (q i / p i) ≤ q i / p i - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div (ne_of_gt hqi) (ne_of_gt h)] at hlog
      have hmul : p i * (Real.log (q i) - Real.log (p i)) ≤ p i * (q i / p i - 1) :=
        mul_le_mul_of_nonneg_left hlog h.le
      have h2 : p i * (q i / p i - 1) = q i - p i := by field_simp
      simp only [hg, Real.negMulLog]
      nlinarith
  have hgsum : ∑ i ∈ s, g i = ∑ i ∈ s, q i - ∑ i ∈ s, p i := by
    simp only [hg]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    have : ∑ i ∈ s, Real.negMulLog (p i) = entropy s p := rfl
    rw [this, heq]
    ring
  have hle : ∑ i ∈ s, g i ≤ 0 := by rw [hgsum]; linarith
  have hge : 0 ≤ ∑ i ∈ s, g i := Finset.sum_nonneg hgnn
  have hzero : ∀ i ∈ s, g i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hgnn).mp (le_antisymm hle hge)
  intro i hi
  have hi0 := hzero i hi
  rcases eq_or_lt_of_le (hp i hi) with h | h
  · have hp0 : p i = 0 := h.symm
    rw [hp0]
    simp only [hg, hp0] at hi0
    simpa using hi0
  · have hqi := hq i hi h
    have hpne : p i ≠ 0 := ne_of_gt h
    by_contra hne
    -- strict Gibbs at the index `i`
    have hne1 : q i / p i ≠ 1 := by
      intro hone
      rw [div_eq_one_iff_eq hpne] at hone
      exact hne hone
    have hlog : Real.log (q i / p i) < q i / p i - 1 :=
      Real.log_lt_sub_one_of_pos (by positivity) hne1
    rw [Real.log_div (ne_of_gt hqi) (ne_of_gt h)] at hlog
    have hmul : p i * (Real.log (q i) - Real.log (p i)) < p i * (q i / p i - 1) :=
      mul_lt_mul_of_pos_left hlog h
    have h2 : p i * (q i / p i - 1) = q i - p i := by field_simp
    simp only [hg, Real.negMulLog] at hi0
    nlinarith

/-! ## Equality in subadditivity: independence -/

section Pair

variable [DecidableEq α] [DecidableEq β]

/-- The cross entropy of a law of pairs against the product of its marginals splits as the sum
of the two marginal entropies.  (This is the equality step hidden inside the proof of
`entropy_le_pushEntropy_fst_add_snd`.) -/
theorem sum_cross_entropy_marginals {K : Finset (α × β)} {P : α × β → ℝ}
    (hP : ∀ z ∈ K, 0 ≤ P z) :
    ∑ z ∈ K, -(P z *
        Real.log (pushWeight K P Prod.fst z.1 * pushWeight K P Prod.snd z.2))
      = pushEntropy K P Prod.fst + pushEntropy K P Prod.snd := by
  classical
  set pf := pushWeight K P Prod.fst with hpf
  set pg := pushWeight K P Prod.snd with hpg
  have hdom1 : ∀ z ∈ K, P z ≤ pf z.1 := by
    intro z hz
    refine Finset.single_le_sum (f := P) (fun i hi => hP i (Finset.mem_filter.mp hi).1) ?_
    exact Finset.mem_filter.mpr ⟨hz, rfl⟩
  have hdom2 : ∀ z ∈ K, P z ≤ pg z.2 := by
    intro z hz
    refine Finset.single_le_sum (f := P) (fun i hi => hP i (Finset.mem_filter.mp hi).1) ?_
    exact Finset.mem_filter.mpr ⟨hz, rfl⟩
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
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, hm1, hm2]

/-- **Equality case of subadditivity, abstract form.**  If a law on a finite set of pairs has
entropy equal to the sum of its marginal entropies, then it *is* the product of its
marginals. -/
theorem eq_mul_of_entropy_eq_of_pair {K : Finset (α × β)} {P : α × β → ℝ}
    (hP : ∀ z ∈ K, 0 ≤ P z) (hsum : ∑ z ∈ K, P z = 1)
    (heq : entropy K P = pushEntropy K P Prod.fst + pushEntropy K P Prod.snd) :
    ∀ z ∈ K, pushWeight K P Prod.fst z.1 * pushWeight K P Prod.snd z.2 = P z := by
  classical
  set pf := pushWeight K P Prod.fst with hpf
  set pg := pushWeight K P Prod.snd with hpg
  have hpf0 : ∀ a, 0 ≤ pf a := fun a => pushWeight_nonneg hP a
  have hpg0 : ∀ b, 0 ≤ pg b := fun b => pushWeight_nonneg hP b
  have hdom1 : ∀ z ∈ K, P z ≤ pf z.1 := by
    intro z hz
    refine Finset.single_le_sum (f := P) (fun i hi => hP i (Finset.mem_filter.mp hi).1) ?_
    exact Finset.mem_filter.mpr ⟨hz, rfl⟩
  have hdom2 : ∀ z ∈ K, P z ≤ pg z.2 := by
    intro z hz
    refine Finset.single_le_sum (f := P) (fun i hi => hP i (Finset.mem_filter.mp hi).1) ?_
    exact Finset.mem_filter.mpr ⟨hz, rfl⟩
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
  refine eq_of_gibbs_eq (s := K) (p := P) (q := fun z => pf z.1 * pg z.2)
    hP (fun z _ => mul_nonneg (hpf0 _) (hpg0 _))
    (fun z hz hpos => mul_pos (lt_of_lt_of_le hpos (hdom1 z hz))
      (lt_of_lt_of_le hpos (hdom2 z hz))) hqsum ?_
  rw [heq, ← sum_cross_entropy_marginals hP]

end Pair

/-! ## Equality in data processing: injectivity on the support -/

section DataProcessing

variable [DecidableEq α] [DecidableEq γ]

/-- **Equality case of `pushEntropy_le_entropy`.**  If merging the atoms of `ν` along `ψ` does
not decrease the entropy, then every fibre of `ψ` contains at most one atom of positive mass. -/
theorem eq_of_pushEntropy_eq_entropy {t : Finset ι} {ν : ι → ℝ}
    (hν : ∀ i ∈ t, 0 ≤ ν i) {ψ : ι → α} (heq : pushEntropy t ν ψ = entropy t ν) :
    ∀ i ∈ t, ∀ j ∈ t, ψ i = ψ j → 0 < ν i → 0 < ν j → i = j := by
  classical
  -- the pointwise inequality of `pushEntropy_le_entropy`, together with its inner
  -- fibrewise inequality
  have hstep : ∀ a : α, ∀ i ∈ t.filter (fun i => ψ i = a),
      -(ν i * Real.log (∑ j ∈ t.filter (fun i => ψ i = a), ν j)) ≤ Real.negMulLog (ν i) := by
    intro a i hi
    have hsub : t.filter (fun i => ψ i = a) ⊆ t := Finset.filter_subset _ _
    have hnn : ∀ j ∈ t.filter (fun i => ψ i = a), 0 ≤ ν j := fun j hj => hν j (hsub hj)
    have hle : ν i ≤ ∑ j ∈ t.filter (fun i => ψ i = a), ν j := Finset.single_le_sum hnn hi
    rcases eq_or_lt_of_le (hnn i hi) with h | h
    · simp [Real.negMulLog, ← h]
    · have hlog : Real.log (ν i) ≤ Real.log (∑ j ∈ t.filter (fun i => ψ i = a), ν j) :=
        Real.log_le_log h hle
      simp only [Real.negMulLog]
      nlinarith
  have hinner : ∀ a : α, Real.negMulLog (pushWeight t ν ψ a)
      = ∑ i ∈ t.filter (fun i => ψ i = a),
          -(ν i * Real.log (∑ j ∈ t.filter (fun i => ψ i = a), ν j)) := by
    intro a
    have : Real.negMulLog (pushWeight t ν ψ a)
        = -((∑ i ∈ t.filter (fun i => ψ i = a), ν i)
            * Real.log (∑ j ∈ t.filter (fun i => ψ i = a), ν j)) := by
      simp [pushWeight, Real.negMulLog]
    rw [this, Finset.sum_mul]
    simp
  have key : ∀ a ∈ t.image ψ, Real.negMulLog (pushWeight t ν ψ a)
      ≤ ∑ i ∈ t.filter (fun i => ψ i = a), Real.negMulLog (ν i) := by
    intro a _
    rw [hinner a]
    exact Finset.sum_le_sum (hstep a)
  have hfib : ∑ a ∈ t.image ψ, ∑ i ∈ t.filter (fun i => ψ i = a), Real.negMulLog (ν i)
      = entropy t ν :=
    Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem ψ hi) _
  have hsum : ∑ a ∈ t.image ψ, Real.negMulLog (pushWeight t ν ψ a)
      = ∑ a ∈ t.image ψ, ∑ i ∈ t.filter (fun i => ψ i = a), Real.negMulLog (ν i) := by
    rw [hfib]; exact heq
  have heach := (Finset.sum_eq_sum_iff_of_le key).mp hsum
  -- every positive atom in a fibre carries the whole mass of the fibre
  have hfull : ∀ i ∈ t, 0 < ν i → ν i = ∑ j ∈ t.filter (fun k => ψ k = ψ i), ν j := by
    intro i hi hpos
    set a := ψ i with ha
    have hamem : a ∈ t.image ψ := Finset.mem_image_of_mem ψ hi
    have hE := heach a hamem
    rw [hinner a] at hE
    have hpt := (Finset.sum_eq_sum_iff_of_le (hstep a)).mp hE
    have himem : i ∈ t.filter (fun k => ψ k = a) := Finset.mem_filter.mpr ⟨hi, rfl⟩
    have h0 := hpt i himem
    set S := ∑ j ∈ t.filter (fun k => ψ k = a), ν j with hS
    have hSpos : 0 < S := lt_of_lt_of_le hpos
      (Finset.single_le_sum (fun j hj => hν j (Finset.filter_subset _ _ hj)) himem)
    have hlogeq : Real.log (ν i) = Real.log S := by
      simp only [Real.negMulLog] at h0
      have : ν i * Real.log S = ν i * Real.log (ν i) := by linarith
      exact (mul_left_cancel₀ (ne_of_gt hpos) this).symm
    have := Real.log_injOn_pos (Set.mem_Ioi.mpr hpos) (Set.mem_Ioi.mpr hSpos) hlogeq
    exact this
  intro i hi j hj hij hpi hpj
  by_contra hne
  have hfi := hfull i hi hpi
  have hsub : ({i, j} : Finset ι) ⊆ t.filter (fun k => ψ k = ψ i) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hi, rfl⟩
    · exact Finset.mem_filter.mpr ⟨hj, hij.symm⟩
  have hpair : ν i + ν j ≤ ∑ k ∈ t.filter (fun k => ψ k = ψ i), ν k := by
    have h2 : ∑ k ∈ ({i, j} : Finset ι), ν k ≤ ∑ k ∈ t.filter (fun k => ψ k = ψ i), ν k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun k hk _ => hν k (Finset.filter_subset _ _ hk))
    rwa [Finset.sum_pair hne] at h2
  linarith

/-- **Equality case of data processing.**  If `ψ ∘ f` has the same entropy as `f`, then `ψ` is
injective on the support of the law of `f`. -/
theorem injOn_of_pushEntropy_comp_eq {s : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i)
    {f : ι → α} {ψ : α → γ}
    (heq : pushEntropy s p (fun i => ψ (f i)) = pushEntropy s p f) :
    ∀ a ∈ s.image f, ∀ b ∈ s.image f, ψ a = ψ b →
      0 < pushWeight s p f a → 0 < pushWeight s p f b → a = b := by
  classical
  have h := eq_of_pushEntropy_eq_entropy
    (t := s.image f) (ν := pushWeight s p f) (fun a _ => pushWeight_nonneg hp a)
    (ψ := ψ) (by rw [← pushEntropy_comp]; exact heq)
  exact h

/-- **Converse of the equality case.**  If every fibre of `ψ` carries at most one atom of
positive mass, then merging along `ψ` does not change the entropy. -/
theorem pushEntropy_eq_entropy_of_injOn {t : Finset ι} {ν : ι → ℝ}
    (hν : ∀ i ∈ t, 0 ≤ ν i) {ψ : ι → α}
    (hinj : ∀ i ∈ t, ∀ j ∈ t, ψ i = ψ j → 0 < ν i → 0 < ν j → i = j) :
    pushEntropy t ν ψ = entropy t ν := by
  classical
  have hfib : ∑ a ∈ t.image ψ, ∑ i ∈ t.filter (fun i => ψ i = a), Real.negMulLog (ν i)
      = entropy t ν :=
    Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem ψ hi) _
  rw [← hfib]
  refine Finset.sum_congr rfl fun a _ => ?_
  set F := t.filter (fun i => ψ i = a) with hF
  have hFsub : F ⊆ t := Finset.filter_subset _ _
  by_cases hpos : ∃ i ∈ F, 0 < ν i
  · obtain ⟨i0, hi0, hi0pos⟩ := hpos
    have hvanish : ∀ j ∈ F, j ≠ i0 → ν j = 0 := by
      intro j hj hne
      rcases eq_or_lt_of_le (hν j (hFsub hj)) with h | h
      · exact h.symm
      · exact absurd (hinj j (hFsub hj) i0 (hFsub hi0)
          (by rw [(Finset.mem_filter.mp hj).2, (Finset.mem_filter.mp hi0).2]) h hi0pos) hne
    have h1 : pushWeight t ν ψ a = ν i0 := by
      rw [show pushWeight t ν ψ a = ∑ j ∈ F, ν j from rfl]
      exact Finset.sum_eq_single_of_mem i0 hi0 (fun j hj hne => hvanish j hj hne)
    have h2 : ∑ j ∈ F, Real.negMulLog (ν j) = Real.negMulLog (ν i0) :=
      Finset.sum_eq_single_of_mem i0 hi0
        (fun j hj hne => by rw [hvanish j hj hne]; simp)
    rw [h1, h2]
  · push_neg at hpos
    have hzero : ∀ j ∈ F, ν j = 0 := fun j hj =>
      le_antisymm (hpos j hj) (hν j (hFsub hj))
    have h1 : pushWeight t ν ψ a = 0 := by
      rw [show pushWeight t ν ψ a = ∑ j ∈ F, ν j from rfl]
      exact Finset.sum_eq_zero hzero
    rw [h1]
    rw [Finset.sum_congr rfl (fun j hj => by rw [hzero j hj])]
    simp

/-- The entropy of the law of the identity is the entropy of the law. -/
theorem pushEntropy_id_eq_entropy [DecidableEq ι] (t : Finset ι) (ν : ι → ℝ) :
    pushEntropy t ν (fun x => x) = entropy t ν := by
  classical
  simp only [pushEntropy, Finset.image_id']
  refine Finset.sum_congr rfl fun a ha => ?_
  congr 1
  simp only [pushWeight, Finset.filter_eq' t a, ha, if_true]
  simp

/-! ## Non-negativity of entropy -/

/-- The pushforward weight of a law is at most `1`. -/
theorem pushWeight_le_one {s : Finset ι} {p : ι → ℝ} {f : ι → α}
    (hp : ∀ i ∈ s, 0 ≤ p i) (hsum : ∑ i ∈ s, p i = 1) (a : α) :
    pushWeight s p f a ≤ 1 := by
  classical
  rw [← hsum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun i hi _ => hp i hi)

/-- The entropy of the law of a random variable is non-negative. -/
theorem pushEntropy_nonneg {s : Finset ι} {p : ι → ℝ} {f : ι → α}
    (hp : ∀ i ∈ s, 0 ≤ p i) (hsum : ∑ i ∈ s, p i = 1) :
    0 ≤ pushEntropy s p f :=
  Finset.sum_nonneg fun a _ =>
    Real.negMulLog_nonneg (pushWeight_nonneg hp a) (pushWeight_le_one hp hsum a)

end DataProcessing

end SumsDifferences

#print axioms SumsDifferences.eq_of_gibbs_eq
#print axioms SumsDifferences.eq_mul_of_entropy_eq_of_pair
#print axioms SumsDifferences.eq_of_pushEntropy_eq_entropy
#print axioms SumsDifferences.pushEntropy_eq_entropy_of_injOn
