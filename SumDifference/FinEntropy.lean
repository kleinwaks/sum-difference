/-
# Shannon entropy of a finitely supported law

A minimal, self-contained finite-entropy toolkit (the entropy facts (E1)–(E3) of §3.1 of
the proof paper rest on it).  The required finite-law entropy calculus is developed here from elementary real inequalities:

* `entropy s p = ∑_{i ∈ s} -p i * log (p i)`, the entropy of a weight function;
* `pushEntropy s p f`, the entropy of the law of the "random variable" `f`;
* the maximum-entropy bound `entropy ≤ log #s` and its pushforward form
  `pushEntropy s p f ≤ log #t` whenever `f` takes its values in `t`;
* the entropy of a uniform law, `entropy s (fun _ => (#s)⁻¹) = log #s`, and its pushforward
  form `pushEntropy_eq_log_card_of_uniform` (the law of `f` is uniform on its range).

Everything is proved from the elementary inequality `log t ≤ t - 1`, i.e. from Gibbs'
inequality; no convexity API is needed.
-/
import Mathlib

open Finset Real

namespace SumsDifferences

variable {ι α : Type*}

/-- Shannon entropy (natural logarithm) of the weight function `p` on the finite set `s`. -/
noncomputable def entropy (s : Finset ι) (p : ι → ℝ) : ℝ :=
  ∑ i ∈ s, Real.negMulLog (p i)

/-- The weight that the law `p` on `s` gives to the fibre `f ⁻¹ {a}`. -/
noncomputable def pushWeight [DecidableEq α] (s : Finset ι) (p : ι → ℝ) (f : ι → α) (a : α) : ℝ :=
  ∑ i ∈ s with f i = a, p i

/-- The entropy of the law of the random variable `f` under `p`. -/
noncomputable def pushEntropy [DecidableEq α] (s : Finset ι) (p : ι → ℝ) (f : ι → α) : ℝ :=
  entropy (s.image f) (pushWeight s p f)

/-! ## Gibbs' inequality and the maximum-entropy bound -/

/-- **Gibbs' inequality**, in the form needed here: if `p` is a law on `s` and `q` is a
nonnegative weight function on `s` of total mass at most that of `p`, and `q` is nonzero
wherever `p` is, then `∑ -p log p ≤ ∑ -p log q`. -/
theorem entropy_le_of_gibbs {s : Finset ι} {p q : ι → ℝ}
    (hp : ∀ i ∈ s, 0 ≤ p i) (hq0 : ∀ i ∈ s, 0 ≤ q i) (hq : ∀ i ∈ s, 0 < p i → 0 < q i)
    (hsum : ∑ i ∈ s, q i ≤ ∑ i ∈ s, p i) :
    entropy s p ≤ ∑ i ∈ s, -(p i * Real.log (q i)) := by
  have key : ∀ i ∈ s, Real.negMulLog (p i) - -(p i * Real.log (q i)) ≤ q i - p i := by
    intro i hi
    rcases eq_or_lt_of_le (hp i hi) with h | h
    · simp only [Real.negMulLog, ← h]
      simpa using hq0 i hi
    · have hqi := hq i hi h
      have hlog : Real.log (q i / p i) ≤ q i / p i - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div (ne_of_gt hqi) (ne_of_gt h)] at hlog
      have hmul : p i * (Real.log (q i) - Real.log (p i)) ≤ p i * (q i / p i - 1) :=
        mul_le_mul_of_nonneg_left hlog h.le
      have h2 : p i * (q i / p i - 1) = q i - p i := by field_simp
      simp only [Real.negMulLog]
      nlinarith
  have hsub := Finset.sum_le_sum key
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hsub
  simp only [entropy]
  linarith

theorem pushWeight_nonneg [DecidableEq α] {s : Finset ι} {p : ι → ℝ} {f : ι → α}
    (hp : ∀ i ∈ s, 0 ≤ p i) (a : α) : 0 ≤ pushWeight s p f a :=
  Finset.sum_nonneg fun i hi => hp i (Finset.mem_filter.mp hi).1

/-- The pushforward of a law is a law. -/
theorem sum_pushWeight [DecidableEq α] (s : Finset ι) (p : ι → ℝ) (f : ι → α) :
    ∑ a ∈ s.image f, pushWeight s p f a = ∑ i ∈ s, p i :=
  Finset.sum_fiberwise_of_maps_to (fun _ hi => Finset.mem_image_of_mem f hi) p

/-- **Maximum entropy.**  A law on a finite set has entropy at most the logarithm of the size of
the set. -/
theorem entropy_le_log_card {s : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i)
    (hsum : ∑ i ∈ s, p i = 1) : entropy s p ≤ Real.log #s := by
  have hne : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with h | h
    · rw [h] at hsum; simp at hsum
    · exact h
  have hcard : (0 : ℝ) < #s := by exact_mod_cast hne.card_pos
  have hq : ∑ _i ∈ s, ((#s : ℝ))⁻¹ ≤ ∑ i ∈ s, p i := by
    rw [Finset.sum_const, nsmul_eq_mul, hsum]
    simp [mul_inv_cancel₀ hcard.ne']
  have h := entropy_le_of_gibbs (q := fun _ => ((#s : ℝ))⁻¹) hp
    (fun _ _ => by positivity) (fun _ _ _ => by positivity) hq
  refine h.trans_eq ?_
  have : ∀ i ∈ s, -(p i * Real.log ((#s : ℝ))⁻¹) = p i * Real.log #s := by
    intro i _
    rw [Real.log_inv]; ring
  rw [Finset.sum_congr rfl this, ← Finset.sum_mul, hsum, one_mul]

/-- **Maximum entropy for a random variable.**  If `f` takes its values in `t`, then the entropy
of the law of `f` is at most `log #t`. -/
theorem pushEntropy_le_log_card [DecidableEq α] {s : Finset ι} {p : ι → ℝ} {f : ι → α}
    {t : Finset α} (hp : ∀ i ∈ s, 0 ≤ p i) (hsum : ∑ i ∈ s, p i = 1)
    (hf : ∀ i ∈ s, f i ∈ t) : pushEntropy s p f ≤ Real.log #t := by
  have h1 : entropy (s.image f) (pushWeight s p f) ≤ Real.log #(s.image f) :=
    entropy_le_log_card (fun a _ => pushWeight_nonneg hp a)
      (by rw [sum_pushWeight, hsum])
  refine h1.trans ?_
  have hsub : s.image f ⊆ t := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact hf i hi
  have : (#(s.image f) : ℝ) ≤ #t := by exact_mod_cast Finset.card_le_card hsub
  have hne : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with h | h
    · rw [h] at hsum; simp at hsum
    · exact h
  exact Real.log_le_log (by exact_mod_cast (hne.image f).card_pos) this

/-- The entropy of the uniform law on a finite set. -/
theorem entropy_uniform (s : Finset ι) :
    entropy s (fun _ => (#s : ℝ)⁻¹) = Real.log #s := by
  rcases Finset.eq_empty_or_nonempty s with h | h
  · simp [entropy, h]
  · have hcard : (0 : ℝ) < #s := by exact_mod_cast h.card_pos
    simp only [entropy, Finset.sum_const, nsmul_eq_mul, Real.negMulLog, Real.log_inv]
    field_simp

/-- The entropy of a random variable whose law is uniform on its (nonempty) range.  Note that
this does *not* require the underlying law `p` to be uniform. -/
theorem pushEntropy_eq_log_card_of_uniform [DecidableEq α] {s : Finset ι} {p : ι → ℝ}
    {f : ι → α} {t : Finset α} (himg : s.image f = t)
    (hunif : ∀ a ∈ t, pushWeight s p f a = (#t : ℝ)⁻¹) :
    pushEntropy s p f = Real.log #t := by
  rw [pushEntropy, himg]
  rw [show entropy t (pushWeight s p f) = entropy t (fun _ => (#t : ℝ)⁻¹) from
    Finset.sum_congr rfl fun a ha => by rw [hunif a ha]]
  exact entropy_uniform t

end SumsDifferences
