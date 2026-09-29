module

/-
# The companion family of five-variable non-Shannon inequalities

The family of E. P. Csirmaz and L. Csirmaz (*Information inequalities for five random
variables*, arXiv:2512.23316v2, equation (31); Theorem 3.5 of the proof paper, where the left-hand side is written
`C_k[abcd]`, resp. `C_k[acbd]`): for every `k ≥ 0`,

  `(a,b‖z) + k·(slb + (a,z‖b) + (b,z‖a)) + k(k-1)/2·((a,c‖b) + (b,c‖a)) ≥ 0`,

with `slb = [abcd]` or `[acbd]` (`companion_ineq`).  Proof by induction on `k`, following the
second proof of Csirmaz–Csirmaz: by the copy lemma replace `z` by a copy `z'` over `(a, b)`; the
inequality for `k` applied to the joint variables `(az', bz', cz', dz', cz')` (`HS_joint`) plus
finitely many Shannon inequalities give the inequality for `k + 1`.
-/
public import Mathlib
public import SumDifference.MatusInequality

@[expose] public section

open Finset

namespace SumsDifferences

namespace NonShannon

universe u v

variable {ι G : Type*} [DecidableEq G] [Zero G]

/-- Index map `(a, b, c, d, z) ↦ (a, b, c, d, c)`. -/
def jidx : Fin 5 → Fin 5 := ![0, 1, 2, 3, 2]

/-- The joint family `((a, z), (b, z), (c, z), (d, z), (c, z))`. -/
def jointFam (v : Fin 5 → ι → G) : Fin 5 → ι → G × G := fun j i => (v (jidx j) i, v 4 i)

theorem HS_joint {s : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i) (v : Fin 5 → ι → G)
    {S T : Finset (Fin 5)} {j₀ : Fin 5} (hj₀ : j₀ ∈ S) (hT : S.image jidx ∪ {4} = T) :
    HS s p (jointFam v) S = HS s p v T := by
  classical
  have h4 : ∀ j, jidx j ≠ 4 := by decide
  have h4T : (4 : Fin 5) ∈ T := hT ▸ Finset.mem_union_right _ (Finset.mem_singleton_self _)
  unfold HS
  refine pushEntropy_eq_of_comp hp
    (fun y t => if t = 4 then (y j₀).2 else if h : ∃ j ∈ S, jidx j = t then (y h.choose).1 else 0)
    (fun x j => if j ∈ S then (x (jidx j), x 4) else 0) ?_ ?_
  · intro i _
    funext t
    by_cases ht : t = 4
    · subst ht; simp [hj₀, h4T, jointFam]
    · by_cases hex : ∃ j ∈ S, jidx j = t
      · have hc := hex.choose_spec
        have htT : t ∈ T := hT ▸ Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, hc.1, hc.2⟩)
        simp only [ht, if_false, dif_pos hex, hc.1, if_true, htT, jointFam]
        rw [hc.2]
      · have htT : t ∉ T := by
          rw [← hT]
          simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton, not_or]
          exact ⟨hex, ht⟩
        simp [ht, hex, htT]
  · intro i _
    funext j
    by_cases hj : j ∈ S
    · have hjT : jidx j ∈ T := hT ▸ Finset.mem_union_left _ (Finset.mem_image_of_mem _ hj)
      simp [hj, hjT, h4T, jointFam]
    · simp [hj]

/-- The expression `C_k` of Theorem 3.5, written out on the subsets of
`{a, b, c, d, z} = {0, 1, 2, 3, 4}`:
`(a,b‖z) + k·(slb + (a,z‖b) + (b,z‖a)) + k(k-1)/2·((a,c‖b) + (b,c‖a))`, where
`slb = [abcd]` (`sw = false`) or `slb = [acbd]` (`sw = true`). -/
noncomputable def compL (h : Finset (Fin 5) → ℝ) (k : ℝ) (sw : Bool) : ℝ :=
  (- h {4} + h {0, 4} + h {1, 4} - h {0, 1, 4})
    + k * (if sw then (- 2 * h {0} - h {1} - h {2} + 3 * h {0, 1} + h {0, 2} + h {0, 3} + h {0, 4} + h {1, 2} - h {1, 3} + h {1, 4} + h {2, 3} - h {0, 1, 2} - 2 * h {0, 1, 4} - h {0, 2, 3})
      else (- 2 * h {0} - 2 * h {1} + 3 * h {0, 1} + h {0, 2} + h {0, 3} + h {0, 4} + h {1, 2} + h {1, 3} + h {1, 4} - h {2, 3} - h {0, 1, 2} - h {0, 1, 3} - 2 * h {0, 1, 4}))
    + (k * (k - 1) / 2) * (- h {0} - h {1} + 2 * h {0, 1} + h {0, 2} + h {1, 2} - 2 * h {0, 1, 2})

set_option maxHeartbeats 4000000 in
/-- **The Csirmaz–Csirmaz family of non-Shannon inequalities** (Theorem 3.5): for five random
variables `a, b, c, d, z`
(here `v 0, …, v 4`) on a finite probability space and every `k ∈ ℕ`,
`(a,b‖z) + k·([abcd] + (a,z‖b) + (b,z‖a)) + k(k-1)/2·((a,c‖b) + (b,c‖a)) ≥ 0`, and the same with
`[acbd]`.  Proof by induction on `k` (the second proof of Csirmaz–Csirmaz): replace `z` by a copy
over `(a, b)` and apply the inequality for `k` to the joint variables `(az, bz, cz, dz, cz)`. -/
theorem companion_ineq (k : ℕ) : ∀ (sw : Bool) {G : Type u} [DecidableEq G] [Zero G] {ι : Type v}
    (s : Finset ι) (p : ι → ℝ) (_hp : ∀ i ∈ s, 0 ≤ p i) (_hsum : ∑ i ∈ s, p i = 1)
    (v : Fin 5 → ι → G), 0 ≤ compL (HS s p v) k sw := by
  induction k with
  | zero =>
    intro sw G _ _ ι s p hp hsum v
    have := HS_submod_lit hp hsum v (S := {0, 4}) (T := {1, 4}) (U := {0, 1, 4}) (V := {4})
      (by decide) (by decide)
    simp only [compL, Nat.cast_zero, zero_mul, add_zero, zero_sub, mul_neg, mul_one,
      neg_zero, zero_div]
    linarith
  | succ k ih =>
    intro sw G _ _ ι s p hp hsum v
    obtain ⟨s', p', v', hp', hsum', Hfst, Hsnd, CI⟩ := copy_step hp hsum v
    set w := jointFam v'
    have IH := ih sw s' p' hp' hsum' w
    have J0 : HS s' p' w {0} = HS s' p' v' {0, 4} := HS_joint hp' v' (j₀ := 0) (by decide) (by decide)
    have J1 : HS s' p' w {1} = HS s' p' v' {1, 4} := HS_joint hp' v' (j₀ := 1) (by decide) (by decide)
    have J2 : HS s' p' w {2} = HS s' p' v' {2, 4} := HS_joint hp' v' (j₀ := 2) (by decide) (by decide)
    have J4 : HS s' p' w {4} = HS s' p' v' {2, 4} := HS_joint hp' v' (j₀ := 4) (by decide) (by decide)
    have J01 : HS s' p' w {0, 1} = HS s' p' v' {0, 1, 4} := HS_joint hp' v' (j₀ := 0) (by decide) (by decide)
    have J02 : HS s' p' w {0, 2} = HS s' p' v' {0, 2, 4} := HS_joint hp' v' (j₀ := 0) (by decide) (by decide)
    have J03 : HS s' p' w {0, 3} = HS s' p' v' {0, 3, 4} := HS_joint hp' v' (j₀ := 0) (by decide) (by decide)
    have J04 : HS s' p' w {0, 4} = HS s' p' v' {0, 2, 4} := HS_joint hp' v' (j₀ := 0) (by decide) (by decide)
    have J12 : HS s' p' w {1, 2} = HS s' p' v' {1, 2, 4} := HS_joint hp' v' (j₀ := 1) (by decide) (by decide)
    have J13 : HS s' p' w {1, 3} = HS s' p' v' {1, 3, 4} := HS_joint hp' v' (j₀ := 1) (by decide) (by decide)
    have J14 : HS s' p' w {1, 4} = HS s' p' v' {1, 2, 4} := HS_joint hp' v' (j₀ := 1) (by decide) (by decide)
    have J23 : HS s' p' w {2, 3} = HS s' p' v' {2, 3, 4} := HS_joint hp' v' (j₀ := 2) (by decide) (by decide)
    have J012 : HS s' p' w {0, 1, 2} = HS s' p' v' {0, 1, 2, 4} := HS_joint hp' v' (j₀ := 0) (by decide) (by decide)
    have J013 : HS s' p' w {0, 1, 3} = HS s' p' v' {0, 1, 3, 4} := HS_joint hp' v' (j₀ := 0) (by decide) (by decide)
    have J014 : HS s' p' w {0, 1, 4} = HS s' p' v' {0, 1, 2, 4} := HS_joint hp' v' (j₀ := 0) (by decide) (by decide)
    have J023 : HS s' p' w {0, 2, 3} = HS s' p' v' {0, 2, 3, 4} := HS_joint hp' v' (j₀ := 0) (by decide) (by decide)
    have F0 : HS s' p' v' {0} = HS s p v {0} := Hfst _ (by decide)
    have F1 : HS s' p' v' {1} = HS s p v {1} := Hfst _ (by decide)
    have F2 : HS s' p' v' {2} = HS s p v {2} := Hfst _ (by decide)
    have F4 : HS s' p' v' {4} = HS s p v {4} := Hsnd _ (by decide)
    have F01 : HS s' p' v' {0, 1} = HS s p v {0, 1} := Hfst _ (by decide)
    have F02 : HS s' p' v' {0, 2} = HS s p v {0, 2} := Hfst _ (by decide)
    have F03 : HS s' p' v' {0, 3} = HS s p v {0, 3} := Hfst _ (by decide)
    have F04 : HS s' p' v' {0, 4} = HS s p v {0, 4} := Hsnd _ (by decide)
    have F12 : HS s' p' v' {1, 2} = HS s p v {1, 2} := Hfst _ (by decide)
    have F13 : HS s' p' v' {1, 3} = HS s p v {1, 3} := Hfst _ (by decide)
    have F14 : HS s' p' v' {1, 4} = HS s p v {1, 4} := Hsnd _ (by decide)
    have F23 : HS s' p' v' {2, 3} = HS s p v {2, 3} := Hfst _ (by decide)
    have F012 : HS s' p' v' {0, 1, 2} = HS s p v {0, 1, 2} := Hfst _ (by decide)
    have F013 : HS s' p' v' {0, 1, 3} = HS s p v {0, 1, 3} := Hfst _ (by decide)
    have F014 : HS s' p' v' {0, 1, 4} = HS s p v {0, 1, 4} := Hsnd _ (by decide)
    have F023 : HS s' p' v' {0, 2, 3} = HS s p v {0, 2, 3} := Hfst _ (by decide)
    have S0123_0124 := HS_submod_lit hp' hsum' v' (S := {0, 1, 2, 3}) (T := {0, 1, 2, 4}) (U := {0, 1, 2, 3, 4}) (V := {0, 1, 2}) (by decide) (by decide)
    have S0123_0134 := HS_submod_lit hp' hsum' v' (S := {0, 1, 2, 3}) (T := {0, 1, 3, 4}) (U := {0, 1, 2, 3, 4}) (V := {0, 1, 3}) (by decide) (by decide)
    have S0123_0234 := HS_submod_lit hp' hsum' v' (S := {0, 1, 2, 3}) (T := {0, 2, 3, 4}) (U := {0, 1, 2, 3, 4}) (V := {0, 2, 3}) (by decide) (by decide)
    have S013_134 := HS_submod_lit hp' hsum' v' (S := {0, 1, 3}) (T := {1, 3, 4}) (U := {0, 1, 3, 4}) (V := {1, 3}) (by decide) (by decide)
    have S023_234 := HS_submod_lit hp' hsum' v' (S := {0, 2, 3}) (T := {2, 3, 4}) (U := {0, 2, 3, 4}) (V := {2, 3}) (by decide) (by decide)
    have S02_04 := HS_submod_lit hp' hsum' v' (S := {0, 2}) (T := {0, 4}) (U := {0, 2, 4}) (V := {0}) (by decide) (by decide)
    have S034_134 := HS_submod_lit hp' hsum' v' (S := {0, 3, 4}) (T := {1, 3, 4}) (U := {0, 1, 3, 4}) (V := {3, 4}) (by decide) (by decide)
    have S034_234 := HS_submod_lit hp' hsum' v' (S := {0, 3, 4}) (T := {2, 3, 4}) (U := {0, 2, 3, 4}) (V := {3, 4}) (by decide) (by decide)
    have S03_04 := HS_submod_lit hp' hsum' v' (S := {0, 3}) (T := {0, 4}) (U := {0, 3, 4}) (V := {0}) (by decide) (by decide)
    have S12_14 := HS_submod_lit hp' hsum' v' (S := {1, 2}) (T := {1, 4}) (U := {1, 2, 4}) (V := {1}) (by decide) (by decide)
    have S13_14 := HS_submod_lit hp' hsum' v' (S := {1, 3}) (T := {1, 4}) (U := {1, 3, 4}) (V := {1}) (by decide) (by decide)
    have S14_34 := HS_submod_lit hp' hsum' v' (S := {1, 4}) (T := {3, 4}) (U := {1, 3, 4}) (V := {4}) (by decide) (by decide)
    have S23_24 := HS_submod_lit hp' hsum' v' (S := {2, 3}) (T := {2, 4}) (U := {2, 3, 4}) (V := {2}) (by decide) (by decide)
    have S24_34 := HS_submod_lit hp' hsum' v' (S := {2, 4}) (T := {3, 4}) (U := {2, 3, 4}) (V := {4}) (by decide) (by decide)
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hkk : (0 : ℝ) ≤ (k : ℝ) * ((k : ℝ) - 1) / 2 := by
      rcases Nat.eq_zero_or_pos k with h0 | h1
      · simp [h0]
      · have : (1 : ℝ) ≤ k := by exact_mod_cast h1
        have : 0 ≤ (k : ℝ) * ((k : ℝ) - 1) := mul_nonneg hk (by linarith)
        linarith
    unfold compL at IH ⊢
    simp only [J0, J1, J2, J4, J01, J02, J03, J04, J12, J13, J14, J23, J012, J013, J014, J023] at IH
    cases sw
    · simp only [Bool.false_eq_true, if_false] at IH ⊢
      have hc : 0 ≤ (- 2 * HS s' p' v' {0} - 2 * HS s' p' v' {1} - HS s' p' v' {4} + 3 * HS s' p' v' {0, 1} + HS s' p' v' {0, 2} + HS s' p' v' {0, 3} + 2 * HS s' p' v' {0, 4} + HS s' p' v' {1, 2} + HS s' p' v' {1, 3} + 2 * HS s' p' v' {1, 4} - HS s' p' v' {2, 3} + HS s' p' v' {2, 4} - HS s' p' v' {0, 1, 2} - HS s' p' v' {0, 1, 3} - 3 * HS s' p' v' {0, 1, 4} - HS s' p' v' {0, 2, 4} - HS s' p' v' {1, 2, 4} + HS s' p' v' {0, 1, 2, 4}) := by linarith [CI, S034_134, S023_234, S0123_0234, S24_34, S02_04, S12_14, S0123_0134, S03_04, S13_14, S0123_0124]
      have hl : 0 ≤ (- 3 * HS s' p' v' {0} - 3 * HS s' p' v' {1} + 5 * HS s' p' v' {0, 1} + 2 * HS s' p' v' {0, 2} + HS s' p' v' {0, 3} + 3 * HS s' p' v' {0, 4} + 2 * HS s' p' v' {1, 2} + HS s' p' v' {1, 3} + 3 * HS s' p' v' {1, 4} - HS s' p' v' {2, 3} - 3 * HS s' p' v' {0, 1, 2} - HS s' p' v' {0, 1, 3} - 5 * HS s' p' v' {0, 1, 4} - 2 * HS s' p' v' {0, 2, 4} - HS s' p' v' {0, 3, 4} - 2 * HS s' p' v' {1, 2, 4} - HS s' p' v' {1, 3, 4} + HS s' p' v' {2, 3, 4} + 3 * HS s' p' v' {0, 1, 2, 4} + HS s' p' v' {0, 1, 3, 4}) := by linarith [CI, S023_234, S0123_0234, S02_04, S12_14, S0123_0134, S03_04, S13_14, S0123_0124]
      have hq : 0 ≤ (- HS s' p' v' {0} - HS s' p' v' {1} + 2 * HS s' p' v' {0, 1} + HS s' p' v' {0, 2} + HS s' p' v' {0, 4} + HS s' p' v' {1, 2} + HS s' p' v' {1, 4} - 2 * HS s' p' v' {0, 1, 2} - 2 * HS s' p' v' {0, 1, 4} - HS s' p' v' {0, 2, 4} - HS s' p' v' {1, 2, 4} + 2 * HS s' p' v' {0, 1, 2, 4}) := by linarith [CI, S02_04, S12_14, S0123_0124]
      have hkl := mul_nonneg hk hl
      have hkq := mul_nonneg hkk hq
      simp only [F0, F1, F4, F01, F02, F03, F04, F12, F13, F14, F23, F012, F013, F014] at IH hc hkl hkq
      push_cast
      linarith only [IH, hc, hkl, hkq]
    · simp only [if_true] at IH ⊢
      have hc : 0 ≤ (- 2 * HS s' p' v' {0} - HS s' p' v' {1} - HS s' p' v' {2} - HS s' p' v' {4} + 3 * HS s' p' v' {0, 1} + HS s' p' v' {0, 2} + HS s' p' v' {0, 3} + 2 * HS s' p' v' {0, 4} + HS s' p' v' {1, 2} - HS s' p' v' {1, 3} + 2 * HS s' p' v' {1, 4} + HS s' p' v' {2, 3} + HS s' p' v' {2, 4} - HS s' p' v' {0, 1, 2} - 3 * HS s' p' v' {0, 1, 4} - HS s' p' v' {0, 2, 3} - HS s' p' v' {0, 2, 4} - HS s' p' v' {1, 2, 4} + HS s' p' v' {0, 1, 2, 4}) := by linarith [CI, S034_234, S013_134, S14_34, S0123_0234, S02_04, S12_14, S0123_0134, S03_04, S23_24, S0123_0124]
      have hl : 0 ≤ (- 3 * HS s' p' v' {0} - 2 * HS s' p' v' {1} - HS s' p' v' {2} + 5 * HS s' p' v' {0, 1} + 2 * HS s' p' v' {0, 2} + HS s' p' v' {0, 3} + 3 * HS s' p' v' {0, 4} + 2 * HS s' p' v' {1, 2} - HS s' p' v' {1, 3} + 2 * HS s' p' v' {1, 4} + HS s' p' v' {2, 3} + HS s' p' v' {2, 4} - 3 * HS s' p' v' {0, 1, 2} - 5 * HS s' p' v' {0, 1, 4} - HS s' p' v' {0, 2, 3} - 2 * HS s' p' v' {0, 2, 4} - HS s' p' v' {0, 3, 4} - 2 * HS s' p' v' {1, 2, 4} + HS s' p' v' {1, 3, 4} - HS s' p' v' {2, 3, 4} + 3 * HS s' p' v' {0, 1, 2, 4} + HS s' p' v' {0, 2, 3, 4}) := by linarith [CI, S013_134, S0123_0234, S02_04, S12_14, S0123_0134, S03_04, S23_24, S0123_0124]
      have hq : 0 ≤ (- HS s' p' v' {0} - HS s' p' v' {1} + 2 * HS s' p' v' {0, 1} + HS s' p' v' {0, 2} + HS s' p' v' {0, 4} + HS s' p' v' {1, 2} + HS s' p' v' {1, 4} - 2 * HS s' p' v' {0, 1, 2} - 2 * HS s' p' v' {0, 1, 4} - HS s' p' v' {0, 2, 4} - HS s' p' v' {1, 2, 4} + 2 * HS s' p' v' {0, 1, 2, 4}) := by linarith [CI, S02_04, S12_14, S0123_0124]
      have hkl := mul_nonneg hk hl
      have hkq := mul_nonneg hkk hq
      simp only [F0, F1, F2, F4, F01, F02, F03, F04, F12, F13, F14, F23, F012, F014, F023] at IH hc hkl hkq
      push_cast
      linarith only [IH, hc, hkl, hkq]

end NonShannon

end SumsDifferences
