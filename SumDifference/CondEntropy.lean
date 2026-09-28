/-
# Conditional entropy, submodularity and Shearer's inequality for finitely supported laws

`SumDifference/FinEntropy.lean` gives `entropy`/`pushEntropy` and the maximum-entropy bound;
`SumDifference/JointEntropy.lean` adds the chain rule for pushforwards, data processing and
subadditivity.  This file develops, from scratch, submodularity (fact (E3) of §4.1 of
the proof paper) and a Shearer-type inequality; only submodularity and the
auxiliary tools listed below are used in the proof of the paper:

* `pushEntropy_submodular` — **submodularity** `H(f,g,h) + H(g) ≤ H(f,g) + H(g,h)`,
  equivalently "conditioning on more variables reduces entropy",
  `H(f | g, h) ≤ H(f | g)`;
* `shearer_four` — the four-variable **Shearer inequality relative to a conditioning
  variable** `V`, for the fractional cover of `{1,2,3,4}` by its four `3`-element subsets:
  `3·H(Y₁,Y₂,Y₃,Y₄ | V) ≤ ∑_{i} H(Y_{-i} | V)`.

Auxiliary tools proved on the way:

* `sum_negMulLog_pushWeight` — the "grouping" identity
  `∑_{i ∈ s} -(p i · log (pushWeight s p φ (φ i))) = pushEntropy s p φ`;
* `pushEntropy_congr` — `pushEntropy` only depends on the values of the variable on `s`;
* `pushEntropy_eq_of_comp` — two random variables that determine each other have equal
  entropy (used to permute the coordinates of a tuple).

Everything is proved from Gibbs' inequality (`entropy_le_of_gibbs`).
-/
import Mathlib
import SumDifference.FinEntropy
import SumDifference.JointEntropy

open Finset

namespace SumsDifferences

variable {ι α β γ δ : Type*}

/-! ## Grouping identity -/

/-- The cross-entropy of a law against the law of one of its random variables is the entropy of
that random variable. -/
theorem sum_negMulLog_pushWeight [DecidableEq δ] (s : Finset ι) (p : ι → ℝ) (φ : ι → δ) :
    ∑ i ∈ s, -(p i * Real.log (pushWeight s p φ (φ i))) = pushEntropy s p φ := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := φ) (t := s.image φ)
      (fun i hi => Finset.mem_image_of_mem _ hi)
      (fun i => -(p i * Real.log (pushWeight s p φ (φ i))))]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hc : ∀ i ∈ s.filter (fun i => φ i = a),
      -(p i * Real.log (pushWeight s p φ (φ i))) = -(p i * Real.log (pushWeight s p φ a)) := by
    intro i hi; rw [(Finset.mem_filter.mp hi).2]
  rw [Finset.sum_congr rfl hc]
  have hfac : ∑ i ∈ s.filter (fun i => φ i = a), -(p i * Real.log (pushWeight s p φ a))
      = -((∑ i ∈ s.filter (fun i => φ i = a), p i) * Real.log (pushWeight s p φ a)) := by
    rw [Finset.sum_mul]; simp
  rw [hfac]
  simp [Real.negMulLog, pushWeight]

/-! ## Congruence and relabelling -/

theorem pushWeight_congr [DecidableEq α] {s : Finset ι} {p : ι → ℝ} {f g : ι → α}
    (h : ∀ i ∈ s, f i = g i) (a : α) : pushWeight s p f a = pushWeight s p g a := by
  classical
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext i
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hi, hfi⟩; exact ⟨hi, by rw [← h i hi]; exact hfi⟩
  · rintro ⟨hi, hgi⟩; exact ⟨hi, by rw [h i hi]; exact hgi⟩

/-- `pushEntropy` depends only on the values of the random variable on `s`. -/
theorem pushEntropy_congr [DecidableEq α] {s : Finset ι} {p : ι → ℝ} {f g : ι → α}
    (h : ∀ i ∈ s, f i = g i) : pushEntropy s p f = pushEntropy s p g := by
  classical
  have himg : s.image f = s.image g := by
    ext a
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, (h i hi).symm⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, h i hi⟩
  simp only [pushEntropy, himg]
  exact Finset.sum_congr rfl fun a _ => by rw [pushWeight_congr h a]

/-- Two random variables that determine each other have the same entropy. -/
theorem pushEntropy_eq_of_comp [DecidableEq α] [DecidableEq γ] {s : Finset ι} {p : ι → ℝ}
    (hp : ∀ i ∈ s, 0 ≤ p i) {f : ι → α} {g : ι → γ} (ψ : α → γ) (χ : γ → α)
    (h1 : ∀ i ∈ s, ψ (f i) = g i) (h2 : ∀ i ∈ s, χ (g i) = f i) :
    pushEntropy s p f = pushEntropy s p g := by
  refine le_antisymm ?_ ?_
  · calc pushEntropy s p f = pushEntropy s p (fun i => χ (g i)) := pushEntropy_congr
          (fun i hi => (h2 i hi).symm)
      _ ≤ pushEntropy s p g := pushEntropy_comp_le hp g χ
  · calc pushEntropy s p g = pushEntropy s p (fun i => ψ (f i)) := pushEntropy_congr
          (fun i hi => (h1 i hi).symm)
      _ ≤ pushEntropy s p f := pushEntropy_comp_le hp f ψ

/-! ## Submodularity -/

section Submodular

variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- **Submodularity, abstract form.**  For a law `P` on a finite set of triples,
`H(XYZ) + H(Y) ≤ H(XY) + H(YZ)`. -/
theorem entropy_add_pushEntropy_mid_le {K : Finset (α × β × γ)} {P : α × β × γ → ℝ}
    (hP : ∀ z ∈ K, 0 ≤ P z) (hsum : ∑ z ∈ K, P z = 1) :
    entropy K P + pushEntropy K P (fun z => z.2.1)
      ≤ pushEntropy K P (fun z => (z.1, z.2.1)) + pushEntropy K P (fun z => (z.2.1, z.2.2)) := by
  classical
  set p12 := pushWeight K P (fun z : α × β × γ => (z.1, z.2.1)) with hp12
  set p23 := pushWeight K P (fun z : α × β × γ => (z.2.1, z.2.2)) with hp23
  set p2 := pushWeight K P (fun z : α × β × γ => z.2.1) with hp2
  have hp12n : ∀ a, 0 ≤ p12 a := fun a => pushWeight_nonneg hP a
  have hp23n : ∀ a, 0 ≤ p23 a := fun a => pushWeight_nonneg hP a
  have hp2n : ∀ a, 0 ≤ p2 a := fun a => pushWeight_nonneg hP a
  have hdom12 : ∀ z ∈ K, P z ≤ p12 (z.1, z.2.1) := by
    intro z hz
    refine Finset.single_le_sum (f := P) (fun i hi => hP i (Finset.mem_filter.mp hi).1) ?_
    exact Finset.mem_filter.mpr ⟨hz, rfl⟩
  have hdom23 : ∀ z ∈ K, P z ≤ p23 (z.2.1, z.2.2) := by
    intro z hz
    refine Finset.single_le_sum (f := P) (fun i hi => hP i (Finset.mem_filter.mp hi).1) ?_
    exact Finset.mem_filter.mpr ⟨hz, rfl⟩
  have hdom2 : ∀ z ∈ K, P z ≤ p2 z.2.1 := by
    intro z hz
    refine Finset.single_le_sum (f := P) (fun i hi => hP i (Finset.mem_filter.mp hi).1) ?_
    exact Finset.mem_filter.mpr ⟨hz, rfl⟩
  set q : α × β × γ → ℝ := fun z => p12 (z.1, z.2.1) * p23 (z.2.1, z.2.2) / p2 z.2.1 with hq
  have hqn : ∀ z, 0 ≤ q z := by
    intro z; rw [hq]
    exact div_nonneg (mul_nonneg (hp12n _) (hp23n _)) (hp2n _)
  -- the total mass of `q` is at most `1`
  have hqsum : ∑ z ∈ K, q z ≤ ∑ z ∈ K, P z := by
    rw [hsum]
    have hfib : ∑ z ∈ K, q z
        = ∑ y ∈ K.image (fun z : α × β × γ => z.2.1),
            ∑ z ∈ K.filter (fun z : α × β × γ => z.2.1 = y), q z :=
      (Finset.sum_fiberwise_of_maps_to (fun z hz => Finset.mem_image_of_mem _ hz) q).symm
    have hinner : ∀ y ∈ K.image (fun z : α × β × γ => z.2.1),
        ∑ z ∈ K.filter (fun z : α × β × γ => z.2.1 = y), q z ≤ p2 y := by
      intro y _
      set Ky := K.filter (fun z : α × β × γ => z.2.1 = y) with hKy
      have hp2y : p2 y = ∑ z ∈ Ky, P z := rfl
      rcases eq_or_lt_of_le (hp2n y) with h0 | hpos
      · -- `p2 y = 0`: every term of `q` on the fibre has denominator `0`, hence vanishes
        have : ∀ z ∈ Ky, q z = 0 := by
          intro z hz
          have hz2 : z.2.1 = y := (Finset.mem_filter.mp hz).2
          rw [hq]
          simp only [hz2, ← h0, div_zero]
        rw [Finset.sum_congr rfl this]
        simp [← h0]
      · set X := Ky.image (fun z : α × β × γ => z.1) with hX
        set W := Ky.image (fun z : α × β × γ => z.2.2) with hW
        have hXsum : ∑ x ∈ X, p12 (x, y) = p2 y := by
          have : ∀ x ∈ X, p12 (x, y) = ∑ z ∈ Ky.filter (fun z : α × β × γ => z.1 = x), P z := by
            intro x _
            rw [hp12, pushWeight]
            refine Finset.sum_congr ?_ (fun _ _ => rfl)
            ext z
            simp only [hKy, Finset.mem_filter, Prod.mk.injEq]
            tauto
          rw [Finset.sum_congr rfl this, hp2y]
          exact Finset.sum_fiberwise_of_maps_to (fun z hz => Finset.mem_image_of_mem _ hz) P
        have hWsum : ∑ w ∈ W, p23 (y, w) = p2 y := by
          have : ∀ w ∈ W, p23 (y, w) = ∑ z ∈ Ky.filter (fun z : α × β × γ => z.2.2 = w), P z := by
            intro w _
            rw [hp23, pushWeight]
            refine Finset.sum_congr ?_ (fun _ _ => rfl)
            ext z
            simp only [hKy, Finset.mem_filter, Prod.mk.injEq]
            tauto
          rw [Finset.sum_congr rfl this, hp2y]
          exact Finset.sum_fiberwise_of_maps_to (fun z hz => Finset.mem_image_of_mem _ hz) P
        have hstep : ∑ z ∈ Ky, q z
            = ∑ z ∈ Ky, p12 (z.1, y) * p23 (y, z.2.2) / p2 y := by
          refine Finset.sum_congr rfl fun z hz => ?_
          have hz2 : z.2.1 = y := (Finset.mem_filter.mp hz).2
          rw [hq]; simp only [hz2]
        have hinj : ∀ z ∈ Ky, ∀ z' ∈ Ky,
            (z.1, z.2.2) = ((z'.1, z'.2.2) : α × γ) → z = z' := by
          rintro ⟨a, b, c⟩ hz ⟨a', b', c'⟩ hz' heq
          have hb : b = y := (Finset.mem_filter.mp hz).2
          have hb' : b' = y := (Finset.mem_filter.mp hz').2
          simp only [Prod.mk.injEq] at heq ⊢
          exact ⟨heq.1, hb.trans hb'.symm, heq.2⟩
        have himg : ∑ u ∈ Ky.image (fun z : α × β × γ => (z.1, z.2.2)),
              p12 (u.1, y) * p23 (y, u.2) / p2 y
            = ∑ z ∈ Ky, p12 (z.1, y) * p23 (y, z.2.2) / p2 y :=
          Finset.sum_image hinj
        have hsub : Ky.image (fun z : α × β × γ => (z.1, z.2.2)) ⊆ X ×ˢ W := by
          intro u hu
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hu
          exact Finset.mem_product.mpr
            ⟨Finset.mem_image_of_mem _ hz, Finset.mem_image_of_mem _ hz⟩
        calc ∑ z ∈ Ky, q z
            = ∑ u ∈ Ky.image (fun z : α × β × γ => (z.1, z.2.2)),
                p12 (u.1, y) * p23 (y, u.2) / p2 y := by rw [himg, hstep]
          _ ≤ ∑ u ∈ X ×ˢ W, p12 (u.1, y) * p23 (y, u.2) / p2 y :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub
                (fun u _ _ => div_nonneg (mul_nonneg (hp12n _) (hp23n _)) (hp2n _))
          _ = (∑ x ∈ X, p12 (x, y)) * (∑ w ∈ W, p23 (y, w)) / p2 y := by
              rw [Finset.sum_mul_sum, Finset.sum_div, Finset.sum_product]
              refine Finset.sum_congr rfl fun x _ => ?_
              rw [Finset.sum_div]
          _ = p2 y := by rw [hXsum, hWsum]; field_simp
    calc ∑ z ∈ K, q z
        = ∑ y ∈ K.image (fun z : α × β × γ => z.2.1),
            ∑ z ∈ K.filter (fun z : α × β × γ => z.2.1 = y), q z := hfib
      _ ≤ ∑ y ∈ K.image (fun z : α × β × γ => z.2.1), p2 y := Finset.sum_le_sum hinner
      _ = ∑ z ∈ K, P z := by rw [hp2, sum_pushWeight]
      _ = 1 := hsum
  -- Gibbs' inequality against `q`
  have hgibbs := entropy_le_of_gibbs (s := K) (p := P) (q := q) hP (fun z _ => hqn z)
    (fun z hz hpos => by
      rw [hq]
      have h1 : 0 < p12 (z.1, z.2.1) := lt_of_lt_of_le hpos (hdom12 z hz)
      have h2 : 0 < p23 (z.2.1, z.2.2) := lt_of_lt_of_le hpos (hdom23 z hz)
      have h3 : 0 < p2 z.2.1 := lt_of_lt_of_le hpos (hdom2 z hz)
      positivity) hqsum
  -- split the cross entropy
  have hsplit : ∀ z ∈ K, -(P z * Real.log (q z))
      = -(P z * Real.log (p12 (z.1, z.2.1))) + -(P z * Real.log (p23 (z.2.1, z.2.2)))
        + P z * Real.log (p2 z.2.1) := by
    intro z hz
    rcases eq_or_lt_of_le (hP z hz) with h | h
    · simp [← h]
    · have h1 : 0 < p12 (z.1, z.2.1) := lt_of_lt_of_le h (hdom12 z hz)
      have h2 : 0 < p23 (z.2.1, z.2.2) := lt_of_lt_of_le h (hdom23 z hz)
      have h3 : 0 < p2 z.2.1 := lt_of_lt_of_le h (hdom2 z hz)
      rw [hq, Real.log_div (by positivity) (ne_of_gt h3), Real.log_mul (ne_of_gt h1)
        (ne_of_gt h2)]
      ring
  have e1 : ∑ z ∈ K, -(P z * Real.log (p12 (z.1, z.2.1)))
      = pushEntropy K P (fun z : α × β × γ => (z.1, z.2.1)) :=
    sum_negMulLog_pushWeight K P _
  have e2 : ∑ z ∈ K, -(P z * Real.log (p23 (z.2.1, z.2.2)))
      = pushEntropy K P (fun z : α × β × γ => (z.2.1, z.2.2)) :=
    sum_negMulLog_pushWeight K P _
  have e3 : ∑ z ∈ K, P z * Real.log (p2 z.2.1)
      = -pushEntropy K P (fun z : α × β × γ => z.2.1) := by
    have := sum_negMulLog_pushWeight K P (fun z : α × β × γ => z.2.1)
    rw [← this, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [Finset.sum_congr rfl hsplit] at hgibbs
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, e1, e2, e3] at hgibbs
  linarith

/-- **Submodularity** of joint entropy: `H(f,g,h) + H(g) ≤ H(f,g) + H(g,h)`. -/
theorem pushEntropy_submodular {s : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i)
    (hsum : ∑ i ∈ s, p i = 1) (f : ι → α) (g : ι → β) (h : ι → γ) :
    pushEntropy s p (fun i => (f i, g i, h i)) + pushEntropy s p g
      ≤ pushEntropy s p (fun i => (f i, g i)) + pushEntropy s p (fun i => (g i, h i)) := by
  classical
  set F : ι → α × β × γ := fun i => (f i, g i, h i) with hF
  set K := s.image F with hK
  set P := pushWeight s p F with hP
  have hP0 : ∀ z ∈ K, 0 ≤ P z := fun z _ => pushWeight_nonneg hp z
  have hPsum : ∑ z ∈ K, P z = 1 := by rw [hK, hP, sum_pushWeight, hsum]
  have key := entropy_add_pushEntropy_mid_le hP0 hPsum
  have h0 : pushEntropy s p F = entropy K P := rfl
  have h2 : pushEntropy K P (fun z : α × β × γ => z.2.1) = pushEntropy s p g := by
    rw [hK, hP, ← pushEntropy_comp]
  have h12 : pushEntropy K P (fun z : α × β × γ => (z.1, z.2.1))
      = pushEntropy s p (fun i => (f i, g i)) := by
    rw [hK, hP, ← pushEntropy_comp]
  have h23 : pushEntropy K P (fun z : α × β × γ => (z.2.1, z.2.2))
      = pushEntropy s p (fun i => (g i, h i)) := by
    rw [hK, hP, ← pushEntropy_comp]
  rw [h2, h12, h23, ← h0] at key
  exact key

end Submodular

/-! ## Conditional entropy -/

/-- Conditional entropy `H(f | g) = H(f, g) - H(g)`. -/
noncomputable def condEntropy [DecidableEq α] [DecidableEq β] (s : Finset ι) (p : ι → ℝ)
    (f : ι → α) (g : ι → β) : ℝ :=
  pushEntropy s p (fun i => (f i, g i)) - pushEntropy s p g

section Cond

variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- Conditional entropy is nonnegative. -/
theorem condEntropy_nonneg {s : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i)
    (f : ι → α) (g : ι → β) : 0 ≤ condEntropy s p f g := by
  have := pushEntropy_comp_le hp (fun i => (f i, g i)) (fun z : α × β => z.2)
  simp only [condEntropy]
  linarith [this]

/-- Conditioning reduces entropy: `H(f | g) ≤ H(f)`. -/
theorem condEntropy_le {s : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i)
    (hsum : ∑ i ∈ s, p i = 1) (f : ι → α) (g : ι → β) :
    condEntropy s p f g ≤ pushEntropy s p f := by
  have := pushEntropy_pair_le hp hsum f g
  simp only [condEntropy]
  linarith

/-- **Conditioning on more reduces entropy**: `H(f | g, h) ≤ H(f | g)`. -/
theorem condEntropy_pair_le {s : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i)
    (hsum : ∑ i ∈ s, p i = 1) (f : ι → α) (g : ι → β) (h : ι → γ) :
    condEntropy s p f (fun i => (g i, h i)) ≤ condEntropy s p f g := by
  have hsub := pushEntropy_submodular hp hsum f g h
  simp only [condEntropy]
  linarith

end Cond

/-! ## Shearer's inequality for four variables, relative to a conditioning variable -/

section Shearer

variable {ζ κ : Type*} [DecidableEq ζ] [DecidableEq κ]

/-- **Shearer's inequality for the four `3`-subsets of `{1,2,3,4}`, relative to `V`.**

`3·H(Y₁,Y₂,Y₃,Y₄ | V) ≤ H(Y₁Y₂Y₃|V) + H(Y₁Y₂Y₄|V) + H(Y₁Y₃Y₄|V) + H(Y₂Y₃Y₄|V)`,
written out in joint entropies.  The proof is the standard chain-rule telescoping, each step
being one instance of `pushEntropy_submodular`. -/
theorem shearer_four_joint {s : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i)
    (hsum : ∑ i ∈ s, p i = 1) (Y₁ Y₂ Y₃ Y₄ : ι → ζ) (V : ι → κ) :
    3 * pushEntropy s p (fun i => (Y₁ i, Y₂ i, Y₃ i, Y₄ i, V i)) + pushEntropy s p V
      ≤ pushEntropy s p (fun i => (Y₁ i, Y₂ i, Y₃ i, V i))
        + pushEntropy s p (fun i => (Y₁ i, Y₂ i, Y₄ i, V i))
        + pushEntropy s p (fun i => (Y₁ i, Y₃ i, Y₄ i, V i))
        + pushEntropy s p (fun i => (Y₂ i, Y₃ i, Y₄ i, V i)) := by
  classical
  -- (A′)  H(1,2,4,V) + H(1,2,3,V) ≥ H(1,2,3,4,V) + H(1,2,V)
  have hA := pushEntropy_submodular hp hsum Y₄ (fun i => (Y₁ i, Y₂ i, V i)) Y₃
  have hA1 : pushEntropy s p (fun i => (Y₄ i, (Y₁ i, Y₂ i, V i), Y₃ i))
      = pushEntropy s p (fun i => (Y₁ i, Y₂ i, Y₃ i, Y₄ i, V i)) :=
    pushEntropy_eq_of_comp hp
      (fun z : ζ × (ζ × ζ × κ) × ζ => (z.2.1.1, z.2.1.2.1, z.2.2, z.1, z.2.1.2.2))
      (fun z : ζ × ζ × ζ × ζ × κ => (z.2.2.2.1, (z.1, z.2.1, z.2.2.2.2), z.2.2.1))
      (fun _ _ => rfl) (fun _ _ => rfl)
  have hA2 : pushEntropy s p (fun i => (Y₄ i, (Y₁ i, Y₂ i, V i)))
      = pushEntropy s p (fun i => (Y₁ i, Y₂ i, Y₄ i, V i)) :=
    pushEntropy_eq_of_comp hp
      (fun z : ζ × ζ × ζ × κ => (z.2.1, z.2.2.1, z.1, z.2.2.2))
      (fun z : ζ × ζ × ζ × κ => (z.2.2.1, z.1, z.2.1, z.2.2.2))
      (fun _ _ => rfl) (fun _ _ => rfl)
  have hA3 : pushEntropy s p (fun i => ((Y₁ i, Y₂ i, V i), Y₃ i))
      = pushEntropy s p (fun i => (Y₁ i, Y₂ i, Y₃ i, V i)) :=
    pushEntropy_eq_of_comp hp
      (fun z : (ζ × ζ × κ) × ζ => (z.1.1, z.1.2.1, z.2, z.1.2.2))
      (fun z : ζ × ζ × ζ × κ => ((z.1, z.2.1, z.2.2.2), z.2.2.1))
      (fun _ _ => rfl) (fun _ _ => rfl)
  rw [hA1, hA2, hA3] at hA
  -- (B1)  H(1,3,V) + H(1,2,V) ≥ H(1,2,3,V) + H(1,V)
  have hB1 := pushEntropy_submodular hp hsum Y₃ (fun i => (Y₁ i, V i)) Y₂
  have hB11 : pushEntropy s p (fun i => (Y₃ i, (Y₁ i, V i), Y₂ i))
      = pushEntropy s p (fun i => (Y₁ i, Y₂ i, Y₃ i, V i)) :=
    pushEntropy_eq_of_comp hp
      (fun z : ζ × (ζ × κ) × ζ => (z.2.1.1, z.2.2, z.1, z.2.1.2))
      (fun z : ζ × ζ × ζ × κ => (z.2.2.1, (z.1, z.2.2.2), z.2.1))
      (fun _ _ => rfl) (fun _ _ => rfl)
  have hB12 : pushEntropy s p (fun i => (Y₃ i, (Y₁ i, V i)))
      = pushEntropy s p (fun i => (Y₁ i, Y₃ i, V i)) :=
    pushEntropy_eq_of_comp hp
      (fun z : ζ × ζ × κ => (z.2.1, z.1, z.2.2))
      (fun z : ζ × ζ × κ => (z.2.1, z.1, z.2.2))
      (fun _ _ => rfl) (fun _ _ => rfl)
  have hB13 : pushEntropy s p (fun i => ((Y₁ i, V i), Y₂ i))
      = pushEntropy s p (fun i => (Y₁ i, Y₂ i, V i)) :=
    pushEntropy_eq_of_comp hp
      (fun z : (ζ × κ) × ζ => (z.1.1, z.2, z.1.2))
      (fun z : ζ × ζ × κ => ((z.1, z.2.2), z.2.1))
      (fun _ _ => rfl) (fun _ _ => rfl)
  rw [hB11, hB12, hB13] at hB1
  -- (B2)  H(1,3,4,V) + H(1,2,3,V) ≥ H(1,2,3,4,V) + H(1,3,V)
  have hB2 := pushEntropy_submodular hp hsum Y₄ (fun i => (Y₁ i, Y₃ i, V i)) Y₂
  have hB21 : pushEntropy s p (fun i => (Y₄ i, (Y₁ i, Y₃ i, V i), Y₂ i))
      = pushEntropy s p (fun i => (Y₁ i, Y₂ i, Y₃ i, Y₄ i, V i)) :=
    pushEntropy_eq_of_comp hp
      (fun z : ζ × (ζ × ζ × κ) × ζ => (z.2.1.1, z.2.2, z.2.1.2.1, z.1, z.2.1.2.2))
      (fun z : ζ × ζ × ζ × ζ × κ => (z.2.2.2.1, (z.1, z.2.2.1, z.2.2.2.2), z.2.1))
      (fun _ _ => rfl) (fun _ _ => rfl)
  have hB22 : pushEntropy s p (fun i => (Y₄ i, (Y₁ i, Y₃ i, V i)))
      = pushEntropy s p (fun i => (Y₁ i, Y₃ i, Y₄ i, V i)) :=
    pushEntropy_eq_of_comp hp
      (fun z : ζ × ζ × ζ × κ => (z.2.1, z.2.2.1, z.1, z.2.2.2))
      (fun z : ζ × ζ × ζ × κ => (z.2.2.1, z.1, z.2.1, z.2.2.2))
      (fun _ _ => rfl) (fun _ _ => rfl)
  have hB23 : pushEntropy s p (fun i => ((Y₁ i, Y₃ i, V i), Y₂ i))
      = pushEntropy s p (fun i => (Y₁ i, Y₂ i, Y₃ i, V i)) :=
    pushEntropy_eq_of_comp hp
      (fun z : (ζ × ζ × κ) × ζ => (z.1.1, z.2, z.1.2.1, z.1.2.2))
      (fun z : ζ × ζ × ζ × κ => ((z.1, z.2.2.1, z.2.2.2), z.2.1))
      (fun _ _ => rfl) (fun _ _ => rfl)
  rw [hB21, hB22, hB23] at hB2
  -- (step 1)  H(2,V) + H(1,V) ≥ H(1,2,V) + H(V)
  have hC1 := pushEntropy_submodular hp hsum Y₂ V Y₁
  have hC11 : pushEntropy s p (fun i => (Y₂ i, V i, Y₁ i))
      = pushEntropy s p (fun i => (Y₁ i, Y₂ i, V i)) :=
    pushEntropy_eq_of_comp hp
      (fun z : ζ × κ × ζ => (z.2.2, z.1, z.2.1))
      (fun z : ζ × ζ × κ => (z.2.1, z.2.2, z.1))
      (fun _ _ => rfl) (fun _ _ => rfl)
  have hC12 : pushEntropy s p (fun i => (V i, Y₁ i))
      = pushEntropy s p (fun i => (Y₁ i, V i)) :=
    pushEntropy_eq_of_comp hp
      (fun z : κ × ζ => (z.2, z.1)) (fun z : ζ × κ => (z.2, z.1))
      (fun _ _ => rfl) (fun _ _ => rfl)
  rw [hC11, hC12] at hC1
  -- (step 2)  H(2,3,V) + H(1,2,V) ≥ H(1,2,3,V) + H(2,V)
  have hC2 := pushEntropy_submodular hp hsum Y₃ (fun i => (Y₂ i, V i)) Y₁
  have hC21 : pushEntropy s p (fun i => (Y₃ i, (Y₂ i, V i), Y₁ i))
      = pushEntropy s p (fun i => (Y₁ i, Y₂ i, Y₃ i, V i)) :=
    pushEntropy_eq_of_comp hp
      (fun z : ζ × (ζ × κ) × ζ => (z.2.2, z.2.1.1, z.1, z.2.1.2))
      (fun z : ζ × ζ × ζ × κ => (z.2.2.1, (z.2.1, z.2.2.2), z.1))
      (fun _ _ => rfl) (fun _ _ => rfl)
  have hC22 : pushEntropy s p (fun i => (Y₃ i, (Y₂ i, V i)))
      = pushEntropy s p (fun i => (Y₂ i, Y₃ i, V i)) :=
    pushEntropy_eq_of_comp hp
      (fun z : ζ × ζ × κ => (z.2.1, z.1, z.2.2))
      (fun z : ζ × ζ × κ => (z.2.1, z.1, z.2.2))
      (fun _ _ => rfl) (fun _ _ => rfl)
  have hC23 : pushEntropy s p (fun i => ((Y₂ i, V i), Y₁ i))
      = pushEntropy s p (fun i => (Y₁ i, Y₂ i, V i)) :=
    pushEntropy_eq_of_comp hp
      (fun z : (ζ × κ) × ζ => (z.2, z.1.1, z.1.2))
      (fun z : ζ × ζ × κ => ((z.2.1, z.2.2), z.1))
      (fun _ _ => rfl) (fun _ _ => rfl)
  rw [hC21, hC22, hC23] at hC2
  -- (step 3)  H(2,3,4,V) + H(1,2,3,V) ≥ H(1,2,3,4,V) + H(2,3,V)
  have hC3 := pushEntropy_submodular hp hsum Y₄ (fun i => (Y₂ i, Y₃ i, V i)) Y₁
  have hC31 : pushEntropy s p (fun i => (Y₄ i, (Y₂ i, Y₃ i, V i), Y₁ i))
      = pushEntropy s p (fun i => (Y₁ i, Y₂ i, Y₃ i, Y₄ i, V i)) :=
    pushEntropy_eq_of_comp hp
      (fun z : ζ × (ζ × ζ × κ) × ζ => (z.2.2, z.2.1.1, z.2.1.2.1, z.1, z.2.1.2.2))
      (fun z : ζ × ζ × ζ × ζ × κ => (z.2.2.2.1, (z.2.1, z.2.2.1, z.2.2.2.2), z.1))
      (fun _ _ => rfl) (fun _ _ => rfl)
  have hC32 : pushEntropy s p (fun i => (Y₄ i, (Y₂ i, Y₃ i, V i)))
      = pushEntropy s p (fun i => (Y₂ i, Y₃ i, Y₄ i, V i)) :=
    pushEntropy_eq_of_comp hp
      (fun z : ζ × ζ × ζ × κ => (z.2.1, z.2.2.1, z.1, z.2.2.2))
      (fun z : ζ × ζ × ζ × κ => (z.2.2.1, z.1, z.2.1, z.2.2.2))
      (fun _ _ => rfl) (fun _ _ => rfl)
  have hC33 : pushEntropy s p (fun i => ((Y₂ i, Y₃ i, V i), Y₁ i))
      = pushEntropy s p (fun i => (Y₁ i, Y₂ i, Y₃ i, V i)) :=
    pushEntropy_eq_of_comp hp
      (fun z : (ζ × ζ × κ) × ζ => (z.2, z.1.1, z.1.2.1, z.1.2.2))
      (fun z : ζ × ζ × ζ × κ => ((z.2.1, z.2.2.1, z.2.2.2), z.1))
      (fun _ _ => rfl) (fun _ _ => rfl)
  rw [hC31, hC32, hC33] at hC3
  linarith

/-- The conditional-entropy form of `shearer_four_joint`. -/
theorem shearer_four_cond {s : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i)
    (hsum : ∑ i ∈ s, p i = 1) (Y₁ Y₂ Y₃ Y₄ : ι → ζ) (V : ι → κ) :
    3 * condEntropy s p (fun i => (Y₁ i, Y₂ i, Y₃ i, Y₄ i)) V
      ≤ condEntropy s p (fun i => (Y₁ i, Y₂ i, Y₃ i)) V
        + condEntropy s p (fun i => (Y₁ i, Y₂ i, Y₄ i)) V
        + condEntropy s p (fun i => (Y₁ i, Y₃ i, Y₄ i)) V
        + condEntropy s p (fun i => (Y₂ i, Y₃ i, Y₄ i)) V := by
  classical
  have key := shearer_four_joint hp hsum Y₁ Y₂ Y₃ Y₄ V
  have e4 : pushEntropy s p (fun i => ((Y₁ i, Y₂ i, Y₃ i, Y₄ i), V i))
      = pushEntropy s p (fun i => (Y₁ i, Y₂ i, Y₃ i, Y₄ i, V i)) :=
    pushEntropy_eq_of_comp hp
      (fun z : (ζ × ζ × ζ × ζ) × κ => (z.1.1, z.1.2.1, z.1.2.2.1, z.1.2.2.2, z.2))
      (fun z : ζ × ζ × ζ × ζ × κ => ((z.1, z.2.1, z.2.2.1, z.2.2.2.1), z.2.2.2.2))
      (fun _ _ => rfl) (fun _ _ => rfl)
  have e123 : pushEntropy s p (fun i => ((Y₁ i, Y₂ i, Y₃ i), V i))
      = pushEntropy s p (fun i => (Y₁ i, Y₂ i, Y₃ i, V i)) :=
    pushEntropy_eq_of_comp hp
      (fun z : (ζ × ζ × ζ) × κ => (z.1.1, z.1.2.1, z.1.2.2, z.2))
      (fun z : ζ × ζ × ζ × κ => ((z.1, z.2.1, z.2.2.1), z.2.2.2))
      (fun _ _ => rfl) (fun _ _ => rfl)
  have e124 : pushEntropy s p (fun i => ((Y₁ i, Y₂ i, Y₄ i), V i))
      = pushEntropy s p (fun i => (Y₁ i, Y₂ i, Y₄ i, V i)) :=
    pushEntropy_eq_of_comp hp
      (fun z : (ζ × ζ × ζ) × κ => (z.1.1, z.1.2.1, z.1.2.2, z.2))
      (fun z : ζ × ζ × ζ × κ => ((z.1, z.2.1, z.2.2.1), z.2.2.2))
      (fun _ _ => rfl) (fun _ _ => rfl)
  have e134 : pushEntropy s p (fun i => ((Y₁ i, Y₃ i, Y₄ i), V i))
      = pushEntropy s p (fun i => (Y₁ i, Y₃ i, Y₄ i, V i)) :=
    pushEntropy_eq_of_comp hp
      (fun z : (ζ × ζ × ζ) × κ => (z.1.1, z.1.2.1, z.1.2.2, z.2))
      (fun z : ζ × ζ × ζ × κ => ((z.1, z.2.1, z.2.2.1), z.2.2.2))
      (fun _ _ => rfl) (fun _ _ => rfl)
  have e234 : pushEntropy s p (fun i => ((Y₂ i, Y₃ i, Y₄ i), V i))
      = pushEntropy s p (fun i => (Y₂ i, Y₃ i, Y₄ i, V i)) :=
    pushEntropy_eq_of_comp hp
      (fun z : (ζ × ζ × ζ) × κ => (z.1.1, z.1.2.1, z.1.2.2, z.2))
      (fun z : ζ × ζ × ζ × κ => ((z.1, z.2.1, z.2.2.1), z.2.2.2))
      (fun _ _ => rfl) (fun _ _ => rfl)
  simp only [condEntropy, e4, e123, e124, e134, e234]
  linarith

end Shearer

end SumsDifferences

#print axioms SumsDifferences.pushEntropy_submodular
#print axioms SumsDifferences.shearer_four_joint
#print axioms SumsDifferences.shearer_four_cond
