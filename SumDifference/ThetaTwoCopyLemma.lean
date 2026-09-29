/-
# The two-copy inequality (Proposition 4.1 of the paper)

For a coupled pair (the uniform law on `Γ ⊆ X × Y`, differences pairwise distinct) with marginals
`μ, ν`, write `L = log |Γ|` and `h(i,j) = H(μ^{*i} * ν^{*j})`. This file proves
(`two_copy_ineq`)

  `194497 L ≤ 49470 log|X+Y| + 73899 h(1,1) + 99532 h(1,0) + 98433 h(0,1) + 4986 h(2,0) + 6659 h(0,2)`.

It is the sum, with positive integer weights, of the following rows, all stated for joint
entropies `HL Γ F` of lists `F` of integer linear forms in two independent copies `(X₁,Y₁)`,
`(X₂,Y₂)` of the coupled pair:

* 27 Shannon inequalities (Table 1 of the paper, rows `s116`–`s142`) and the support inequality
  `H(X₁+Y₁) ≤ log |X+Y|` (row `r143`);
* the ten non-Shannon inequalities of Table 2 (rows `cut144`–`cut153`): instances of Matúš's
  family and of its companion in which each of the five variables is a single form or a pair of
  forms;
* identities between joint entropies (rows `e154`–`e190`): the identifications (R4)–(R6) of single
  forms with `L` and with the `h(i,j)`, and instances of the exchange rule (R3);
* `HL Γ [] = 0` (row `e0`).

Layout. Every row that needs only `Γ`, `hΓ`, `hinj` is a separate private lemma
`two_copy_row_…`. Every identity between two joint entropies is one application
`HL_eq_norm hinj (by decide)` of the normal-form lemma of `SumDifference/LinearFormsNormalForm.lean`.
The final step is a `linear_combination` with the integer weights of Tables 1 and 2.
The complete certificate is contained in this file; no external data or generator is needed
to check it. The certificate was found computationally and is verified by the proof below.
-/
import Mathlib
import SumDifference.LinearFormsEntropy
import SumDifference.LinearFormsNormalForm
import SumDifference.CoupledEntropyCore
import SumDifference.CompanionInequality
import SumDifference.LinearFormsPairs

open Finset Real Pointwise

namespace SumsDifferences

namespace CoupledForms

open CoupledEntropy NonShannon

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-! ### The rows of Proposition 4.1, one lemma each (they need only `Γ`, `hΓ`, `hinj`) -/

private theorem two_copy_row_s116 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(0, 1, 1, 0), (0, 0, 0, 1)] + HL Γ [] ≤ HL Γ [(0, 0, 0, 1)] + HL Γ [(0, 1, 1, 0)] := by
  have h0 := HL_submod hΓ [(0, 0, 0, 1)] [] [(0, 1, 1, 0)]
  simp only [List.cons_append, List.nil_append, List.append_nil] at h0
  have h1 : HL Γ [(0, 0, 0, 1), (0, 1, 1, 0)] = HL Γ [(0, 1, 1, 0), (0, 0, 0, 1)] :=
    HL_eq_norm hinj (by decide)
  linarith

private theorem two_copy_row_s117 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 0, -1, 0), (0, 0, 0, 1)] + HL Γ [] ≤ HL Γ [(0, 0, 0, 1)] + HL Γ [(1, 0, -1, 0)] := by
  have h0 := HL_submod hΓ [(0, 0, 0, 1)] [] [(1, 0, -1, 0)]
  simp only [List.cons_append, List.nil_append, List.append_nil] at h0
  have h1 : HL Γ [(0, 0, 0, 1), (1, 0, -1, 0)] = HL Γ [(1, 0, -1, 0), (0, 0, 0, 1)] :=
    HL_eq_norm hinj (by decide)
  linarith

private theorem two_copy_row_s118 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 0, 0, 0), (0, 0, 0, 1)] + HL Γ [] ≤ HL Γ [(0, 0, 0, 1)] + HL Γ [(1, 0, 0, 0)] := by
  have h0 := HL_submod hΓ [(0, 0, 0, 1)] [] [(1, 0, 0, 0)]
  simp only [List.cons_append, List.nil_append, List.append_nil] at h0
  have h1 : HL Γ [(0, 0, 0, 1), (1, 0, 0, 0)] = HL Γ [(1, 0, 0, 0), (0, 0, 0, 1)] :=
    HL_eq_norm hinj (by decide)
  linarith

private theorem two_copy_row_s119 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 0, 1, 0), (0, 0, 0, 1)] + HL Γ [] ≤ HL Γ [(0, 0, 0, 1)] + HL Γ [(1, 0, 1, 0)] := by
  have h0 := HL_submod hΓ [(0, 0, 0, 1)] [] [(1, 0, 1, 0)]
  simp only [List.cons_append, List.nil_append, List.append_nil] at h0
  have h1 : HL Γ [(0, 0, 0, 1), (1, 0, 1, 0)] = HL Γ [(1, 0, 1, 0), (0, 0, 0, 1)] :=
    HL_eq_norm hinj (by decide)
  linarith

private theorem two_copy_row_s120 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 1, 0, 0), (0, 0, 0, 1)] + HL Γ [] ≤ HL Γ [(0, 0, 0, 1)] + HL Γ [(1, 1, 0, 0)] := by
  have h0 := HL_submod hΓ [(0, 0, 0, 1)] [] [(1, 1, 0, 0)]
  simp only [List.cons_append, List.nil_append, List.append_nil] at h0
  have h1 : HL Γ [(0, 0, 0, 1), (1, 1, 0, 0)] = HL Γ [(1, 1, 0, 0), (0, 0, 0, 1)] :=
    HL_eq_norm hinj (by decide)
  linarith

private theorem two_copy_row_s121 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] + HL Γ [] ≤ HL Γ [(0, 0, 1, 0), (0, 0, 0, 1)] + HL Γ [(1, -1, -1, 0)] := by
  have h0 := HL_submod hΓ [(0, 0, 1, 0), (0, 0, 0, 1)] [] [(1, -1, -1, 0)]
  simp only [List.cons_append, List.nil_append, List.append_nil] at h0
  have h1 : HL Γ [(0, 0, 1, 0), (0, 0, 0, 1), (1, -1, -1, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] :=
    HL_eq_norm hinj (by decide)
  linarith

private theorem two_copy_row_s122 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] + HL Γ [] ≤ HL Γ [(0, 0, 1, 0), (0, 0, 0, 1)] + HL Γ [(1, -1, 0, 1)] := by
  have h0 := HL_submod hΓ [(0, 0, 1, 0), (0, 0, 0, 1)] [] [(1, -1, 0, 1)]
  simp only [List.cons_append, List.nil_append, List.append_nil] at h0
  have h1 : HL Γ [(0, 0, 1, 0), (0, 0, 0, 1), (1, -1, 0, 1)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] :=
    HL_eq_norm hinj (by decide)
  linarith

private theorem two_copy_row_s123 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 0, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] + HL Γ [] ≤ HL Γ [(0, 0, 1, 0), (0, 0, 0, 1)] + HL Γ [(1, 0, 0, 0)] := by
  have h0 := HL_submod hΓ [(0, 0, 1, 0), (0, 0, 0, 1)] [] [(1, 0, 0, 0)]
  simp only [List.cons_append, List.nil_append, List.append_nil] at h0
  have h1 : HL Γ [(0, 0, 1, 0), (0, 0, 0, 1), (1, 0, 0, 0)] = HL Γ [(1, 0, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] :=
    HL_eq_norm hinj (by decide)
  linarith

private theorem two_copy_row_s124 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] + HL Γ [(0, 0, 0, 1)] ≤ HL Γ [(0, 0, 1, 0), (0, 0, 0, 1)] + HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 1)] := by
  have h0 := HL_submod hΓ [(0, 0, 1, 0), (0, 0, 0, 1)] [(0, 0, 0, 1)] [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 1)]
  simp only [List.cons_append, List.nil_append] at h0
  have h1 : HL Γ [(0, 0, 1, 0), (0, 0, 0, 1), (0, 0, 0, 1), (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 1)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] :=
    HL_eq_norm hinj (by decide)
  have h2 : HL Γ [(0, 0, 1, 0), (0, 0, 0, 1), (0, 0, 0, 1)] = HL Γ [(0, 0, 1, 0), (0, 0, 0, 1)] :=
    HL_eq_norm hinj (by decide)
  have h3 : HL Γ [(0, 0, 0, 1), (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 1)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 1)] :=
    HL_eq_norm hinj (by decide)
  linarith

private theorem two_copy_row_s125 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] + HL Γ [(0, 0, 1, 0)] ≤ HL Γ [(0, 0, 1, 0), (0, 0, 0, 1)] + HL Γ [(1, 1, 0, 0), (0, 0, 1, 0)] := by
  have h0 := HL_submod hΓ [(0, 0, 1, 0), (0, 0, 0, 1)] [(0, 0, 1, 0)] [(1, 1, 0, 0), (0, 0, 1, 0)]
  simp only [List.cons_append, List.nil_append] at h0
  have h1 : HL Γ [(0, 0, 1, 0), (0, 0, 0, 1), (0, 0, 1, 0), (1, 1, 0, 0), (0, 0, 1, 0)] = HL Γ [(1, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] :=
    HL_eq_norm hinj (by decide)
  have h2 : HL Γ [(0, 0, 1, 0), (0, 0, 0, 1), (0, 0, 1, 0)] = HL Γ [(0, 0, 1, 0), (0, 0, 0, 1)] :=
    HL_eq_norm hinj (by decide)
  have h3 : HL Γ [(0, 0, 1, 0), (1, 1, 0, 0), (0, 0, 1, 0)] = HL Γ [(1, 1, 0, 0), (0, 0, 1, 0)] :=
    HL_eq_norm hinj (by decide)
  linarith

private theorem two_copy_row_s126 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(0, 1, 0, -1), (0, 0, 1, 0)] + HL Γ [] ≤ HL Γ [(0, 0, 1, 0)] + HL Γ [(0, 1, 0, -1)] := by
  have h0 := HL_submod hΓ [(0, 0, 1, 0)] [] [(0, 1, 0, -1)]
  simp only [List.cons_append, List.nil_append, List.append_nil] at h0
  have h1 : HL Γ [(0, 0, 1, 0), (0, 1, 0, -1)] = HL Γ [(0, 1, 0, -1), (0, 0, 1, 0)] :=
    HL_eq_norm hinj (by decide)
  linarith

private theorem two_copy_row_s127 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(0, 1, 0, 1), (0, 0, 1, 0)] + HL Γ [] ≤ HL Γ [(0, 0, 1, 0)] + HL Γ [(0, 1, 0, 1)] := by
  have h0 := HL_submod hΓ [(0, 0, 1, 0)] [] [(0, 1, 0, 1)]
  simp only [List.cons_append, List.nil_append, List.append_nil] at h0
  have h1 : HL Γ [(0, 0, 1, 0), (0, 1, 0, 1)] = HL Γ [(0, 1, 0, 1), (0, 0, 1, 0)] :=
    HL_eq_norm hinj (by decide)
  linarith

private theorem two_copy_row_s128 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 0, 0, 1), (0, 0, 1, 0)] + HL Γ [] ≤ HL Γ [(0, 0, 1, 0)] + HL Γ [(1, 0, 0, 1)] := by
  have h0 := HL_submod hΓ [(0, 0, 1, 0)] [] [(1, 0, 0, 1)]
  simp only [List.cons_append, List.nil_append, List.append_nil] at h0
  have h1 : HL Γ [(0, 0, 1, 0), (1, 0, 0, 1)] = HL Γ [(1, 0, 0, 1), (0, 0, 1, 0)] :=
    HL_eq_norm hinj (by decide)
  linarith

private theorem two_copy_row_s129 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 1, 0, 0), (0, 0, 1, 0)] + HL Γ [] ≤ HL Γ [(0, 0, 1, 0)] + HL Γ [(1, 1, 0, 0)] := by
  have h0 := HL_submod hΓ [(0, 0, 1, 0)] [] [(1, 1, 0, 0)]
  simp only [List.cons_append, List.nil_append, List.append_nil] at h0
  have h1 : HL Γ [(0, 0, 1, 0), (1, 1, 0, 0)] = HL Γ [(1, 1, 0, 0), (0, 0, 1, 0)] :=
    HL_eq_norm hinj (by decide)
  linarith

private theorem two_copy_row_s130 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 0, 0, 0), (0, 1, 0, -1), (0, 0, 1, 0)] + HL Γ [] ≤ HL Γ [(0, 1, 0, -1)] + HL Γ [(1, 0, 0, 0), (0, 0, 1, 0)] := by
  have h0 := HL_submod hΓ [(0, 1, 0, -1)] [] [(1, 0, 0, 0), (0, 0, 1, 0)]
  simp only [List.cons_append, List.nil_append, List.append_nil] at h0
  have h1 : HL Γ [(0, 1, 0, -1), (1, 0, 0, 0), (0, 0, 1, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, -1), (0, 0, 1, 0)] :=
    HL_eq_norm hinj (by decide)
  linarith

private theorem two_copy_row_s131 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 0, 1, 1), (0, 1, 1, 0)] + HL Γ [] ≤ HL Γ [(0, 1, 1, 0)] + HL Γ [(1, 0, 1, 1)] := by
  have h0 := HL_submod hΓ [(0, 1, 1, 0)] [] [(1, 0, 1, 1)]
  simp only [List.cons_append, List.nil_append, List.append_nil] at h0
  have h1 : HL Γ [(0, 1, 1, 0), (1, 0, 1, 1)] = HL Γ [(1, 0, 1, 1), (0, 1, 1, 0)] :=
    HL_eq_norm hinj (by decide)
  linarith

private theorem two_copy_row_s132 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 0, -1, 1), (0, 1, 1, 0)] + HL Γ [] ≤ HL Γ [(0, 1, 1, 0)] + HL Γ [(1, 1, 0, 1)] := by
  have h0 := HL_submod hΓ [(0, 1, 1, 0)] [] [(1, 1, 0, 1)]
  simp only [List.cons_append, List.nil_append, List.append_nil] at h0
  have h1 : HL Γ [(0, 1, 1, 0), (1, 1, 0, 1)] = HL Γ [(1, 0, -1, 1), (0, 1, 1, 0)] :=
    HL_eq_norm hinj (by decide)
  linarith

private theorem two_copy_row_s133 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) :
    HL Γ [(1, 0, -1, 0), (0, 1, 0, 0), (0, 0, 0, 1)] + HL Γ [] ≤ HL Γ [(1, 0, -1, 0)] + HL Γ [(0, 1, 0, 0), (0, 0, 0, 1)] := by
  have h0 := HL_submod hΓ [(1, 0, -1, 0)] [] [(0, 1, 0, 0), (0, 0, 0, 1)]
  simp only [List.cons_append, List.nil_append, List.append_nil] at h0
  linarith

private theorem two_copy_row_s134 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 0, 1, 0), (0, 1, 0, 0), (0, 0, 0, 1)] + HL Γ [(0, 1, 0, -1)] ≤ HL Γ [(0, 1, 0, 0), (0, 0, 0, 1)] + HL Γ [(1, 0, 1, 1), (0, 1, 0, -1)] := by
  have h0 := HL_submod hΓ [(0, 1, 0, 0), (0, 0, 0, 1)] [(0, 1, 0, -1)] [(1, 0, 1, 1), (0, 1, 0, -1)]
  simp only [List.cons_append, List.nil_append] at h0
  have h1 : HL Γ [(0, 1, 0, 0), (0, 0, 0, 1), (0, 1, 0, -1), (1, 0, 1, 1), (0, 1, 0, -1)] = HL Γ [(1, 0, 1, 0), (0, 1, 0, 0), (0, 0, 0, 1)] :=
    HL_eq_norm hinj (by decide)
  have h2 : HL Γ [(0, 1, 0, 0), (0, 0, 0, 1), (0, 1, 0, -1)] = HL Γ [(0, 1, 0, 0), (0, 0, 0, 1)] :=
    HL_eq_norm hinj (by decide)
  have h3 : HL Γ [(0, 1, 0, -1), (1, 0, 1, 1), (0, 1, 0, -1)] = HL Γ [(1, 0, 1, 1), (0, 1, 0, -1)] :=
    HL_eq_norm hinj (by decide)
  linarith

private theorem two_copy_row_s135 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] + HL Γ [(0, 1, 1, -1)] ≤ HL Γ [(0, 1, 1, 0), (0, 0, 0, 1)] + HL Γ [(1, 0, 1, 0), (0, 1, 1, -1)] := by
  have h0 := HL_submod hΓ [(0, 1, 1, 0), (0, 0, 0, 1)] [(0, 1, 1, -1)] [(1, 0, 1, 0), (0, 1, 1, -1)]
  simp only [List.cons_append, List.nil_append] at h0
  have h1 : HL Γ [(0, 1, 1, 0), (0, 0, 0, 1), (0, 1, 1, -1), (1, 0, 1, 0), (0, 1, 1, -1)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] :=
    HL_eq_norm hinj (by decide)
  have h2 : HL Γ [(0, 1, 1, 0), (0, 0, 0, 1), (0, 1, 1, -1)] = HL Γ [(0, 1, 1, 0), (0, 0, 0, 1)] :=
    HL_eq_norm hinj (by decide)
  have h3 : HL Γ [(0, 1, 1, -1), (1, 0, 1, 0), (0, 1, 1, -1)] = HL Γ [(1, 0, 1, 0), (0, 1, 1, -1)] :=
    HL_eq_norm hinj (by decide)
  linarith

private theorem two_copy_row_s136 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 0, 0, 0), (0, 1, 1, 0), (0, 0, 0, 1)] + HL Γ [(0, 1, 1, 1)] ≤ HL Γ [(0, 1, 1, 0), (0, 0, 0, 1)] + HL Γ [(1, 0, 0, 0), (0, 1, 1, 1)] := by
  have h0 := HL_submod hΓ [(0, 1, 1, 0), (0, 0, 0, 1)] [(0, 1, 1, 1)] [(1, 0, 0, 0), (0, 1, 1, 1)]
  simp only [List.cons_append, List.nil_append] at h0
  have h1 : HL Γ [(0, 1, 1, 0), (0, 0, 0, 1), (0, 1, 1, 1), (1, 0, 0, 0), (0, 1, 1, 1)] = HL Γ [(1, 0, 0, 0), (0, 1, 1, 0), (0, 0, 0, 1)] :=
    HL_eq_norm hinj (by decide)
  have h2 : HL Γ [(0, 1, 1, 0), (0, 0, 0, 1), (0, 1, 1, 1)] = HL Γ [(0, 1, 1, 0), (0, 0, 0, 1)] :=
    HL_eq_norm hinj (by decide)
  have h3 : HL Γ [(0, 1, 1, 1), (1, 0, 0, 0), (0, 1, 1, 1)] = HL Γ [(1, 0, 0, 0), (0, 1, 1, 1)] :=
    HL_eq_norm hinj (by decide)
  linarith

private theorem two_copy_row_s137 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] + HL Γ [(1, 0, 0, 0), (0, 1, 0, 1)] ≤ HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 1)] + HL Γ [(1, 0, 0, 0), (0, 1, 0, 1), (0, 0, 1, 0)] := by
  have h0 := HL_submod hΓ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 1)] [(1, 0, 0, 0), (0, 1, 0, 1)] [(1, 0, 0, 0), (0, 1, 0, 1), (0, 0, 1, 0)]
  simp only [List.cons_append, List.nil_append] at h0
  have h1 : HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 1), (1, 0, 0, 0), (0, 1, 0, 1), (1, 0, 0, 0), (0, 1, 0, 1), (0, 0, 1, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] :=
    HL_eq_norm hinj (by decide)
  have h2 : HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 1), (1, 0, 0, 0), (0, 1, 0, 1)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 1)] :=
    HL_eq_norm hinj (by decide)
  have h3 : HL Γ [(1, 0, 0, 0), (0, 1, 0, 1), (1, 0, 0, 0), (0, 1, 0, 1), (0, 0, 1, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 1), (0, 0, 1, 0)] :=
    HL_eq_norm hinj (by decide)
  linarith

private theorem two_copy_row_s138 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 0, 0, 0), (0, 1, 1, 0), (0, 0, 0, 1)] + HL Γ [(1, 1, 1, 0)] ≤ HL Γ [(1, 1, 1, 0), (0, 0, 0, 1)] + HL Γ [(1, 0, 0, 0), (0, 1, 1, 0)] := by
  have h0 := HL_submod hΓ [(1, 1, 1, 0), (0, 0, 0, 1)] [(1, 1, 1, 0)] [(1, 0, 0, 0), (0, 1, 1, 0)]
  simp only [List.cons_append, List.nil_append] at h0
  have h1 : HL Γ [(1, 1, 1, 0), (0, 0, 0, 1), (1, 1, 1, 0), (1, 0, 0, 0), (0, 1, 1, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 1, 0), (0, 0, 0, 1)] :=
    HL_eq_norm hinj (by decide)
  have h2 : HL Γ [(1, 1, 1, 0), (0, 0, 0, 1), (1, 1, 1, 0)] = HL Γ [(1, 1, 1, 0), (0, 0, 0, 1)] :=
    HL_eq_norm hinj (by decide)
  have h3 : HL Γ [(1, 1, 1, 0), (1, 0, 0, 0), (0, 1, 1, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 1, 0)] :=
    HL_eq_norm hinj (by decide)
  linarith

private theorem two_copy_row_s139 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 0, 0, 0), (0, 1, 0, 1), (0, 0, 1, 0)] + HL Γ [(1, 0, -1, 0)] ≤ HL Γ [(1, 0, 0, 0), (0, 0, 1, 0)] + HL Γ [(1, 0, -1, 0), (0, 1, 1, 1)] := by
  have h0 := HL_submod hΓ [(1, 0, 0, 0), (0, 0, 1, 0)] [(1, 0, -1, 0)] [(1, 0, -1, 0), (0, 1, 1, 1)]
  simp only [List.cons_append, List.nil_append] at h0
  have h1 : HL Γ [(1, 0, 0, 0), (0, 0, 1, 0), (1, 0, -1, 0), (1, 0, -1, 0), (0, 1, 1, 1)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 1), (0, 0, 1, 0)] :=
    HL_eq_norm hinj (by decide)
  have h2 : HL Γ [(1, 0, 0, 0), (0, 0, 1, 0), (1, 0, -1, 0)] = HL Γ [(1, 0, 0, 0), (0, 0, 1, 0)] :=
    HL_eq_norm hinj (by decide)
  have h3 : HL Γ [(1, 0, -1, 0), (1, 0, -1, 0), (0, 1, 1, 1)] = HL Γ [(1, 0, -1, 0), (0, 1, 1, 1)] :=
    HL_eq_norm hinj (by decide)
  linarith

private theorem two_copy_row_s140 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] + HL Γ [(1, 0, -1, 1)] ≤ HL Γ [(1, 0, 0, 1), (0, 0, 1, 0)] + HL Γ [(1, 0, -1, 1), (0, 1, 0, 1)] := by
  have h0 := HL_submod hΓ [(1, 0, 0, 1), (0, 0, 1, 0)] [(1, 0, -1, 1)] [(1, 0, -1, 1), (0, 1, 0, 1)]
  simp only [List.cons_append, List.nil_append] at h0
  have h1 : HL Γ [(1, 0, 0, 1), (0, 0, 1, 0), (1, 0, -1, 1), (1, 0, -1, 1), (0, 1, 0, 1)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] :=
    HL_eq_norm hinj (by decide)
  have h2 : HL Γ [(1, 0, 0, 1), (0, 0, 1, 0), (1, 0, -1, 1)] = HL Γ [(1, 0, 0, 1), (0, 0, 1, 0)] :=
    HL_eq_norm hinj (by decide)
  have h3 : HL Γ [(1, 0, -1, 1), (1, 0, -1, 1), (0, 1, 0, 1)] = HL Γ [(1, 0, -1, 1), (0, 1, 0, 1)] :=
    HL_eq_norm hinj (by decide)
  linarith

private theorem two_copy_row_s141 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 0, 0, 1), (0, 1, 0, -1), (0, 0, 1, 1)] + HL Γ [(0, 1, 0, -1)] ≤ HL Γ [(0, 1, 0, -1), (0, 0, 1, 1)] + HL Γ [(1, 0, 0, 1), (0, 1, 0, -1)] := by
  have h0 := HL_submod hΓ [(0, 1, 0, -1), (0, 0, 1, 1)] [(0, 1, 0, -1)] [(1, 0, 0, 1), (0, 1, 0, -1)]
  simp only [List.cons_append, List.nil_append] at h0
  have h1 : HL Γ [(0, 1, 0, -1), (0, 0, 1, 1), (0, 1, 0, -1), (1, 0, 0, 1), (0, 1, 0, -1)] = HL Γ [(1, 0, 0, 1), (0, 1, 0, -1), (0, 0, 1, 1)] :=
    HL_eq_norm hinj (by decide)
  have h2 : HL Γ [(0, 1, 0, -1), (0, 0, 1, 1), (0, 1, 0, -1)] = HL Γ [(0, 1, 0, -1), (0, 0, 1, 1)] :=
    HL_eq_norm hinj (by decide)
  have h3 : HL Γ [(0, 1, 0, -1), (1, 0, 0, 1), (0, 1, 0, -1)] = HL Γ [(1, 0, 0, 1), (0, 1, 0, -1)] :=
    HL_eq_norm hinj (by decide)
  linarith

private theorem two_copy_row_s142 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 0, 0, 1), (0, 1, 0, -1), (0, 0, 1, 1)] + HL Γ [(1, 0, -1, 0)] ≤ HL Γ [(1, 0, 0, 1), (0, 0, 1, 1)] + HL Γ [(1, 0, -1, 0), (0, 1, 1, 0)] := by
  have h0 := HL_submod hΓ [(1, 0, 0, 1), (0, 0, 1, 1)] [(1, 0, -1, 0)] [(1, 0, -1, 0), (0, 1, 1, 0)]
  simp only [List.cons_append, List.nil_append] at h0
  have h1 : HL Γ [(1, 0, 0, 1), (0, 0, 1, 1), (1, 0, -1, 0), (1, 0, -1, 0), (0, 1, 1, 0)] = HL Γ [(1, 0, 0, 1), (0, 1, 0, -1), (0, 0, 1, 1)] :=
    HL_eq_norm hinj (by decide)
  have h2 : HL Γ [(1, 0, 0, 1), (0, 0, 1, 1), (1, 0, -1, 0)] = HL Γ [(1, 0, 0, 1), (0, 0, 1, 1)] :=
    HL_eq_norm hinj (by decide)
  have h3 : HL Γ [(1, 0, -1, 0), (1, 0, -1, 0), (0, 1, 1, 0)] = HL Γ [(1, 0, -1, 0), (0, 1, 1, 0)] :=
    HL_eq_norm hinj (by decide)
  linarith

private theorem two_copy_row_cut144 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    0 ≤ (-1) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 0)] + (3) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 1)] + (-6) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] + (3) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0)] + (-2) * HL Γ [(1, 0, 0, 1), (0, 1, 0, -1)] + (-2) * HL Γ [(1, 0, -1, 0), (0, 1, 1, 0)] + (1) * HL Γ [(1, 0, -1, 0), (0, 1, 1, 0), (0, 0, 0, 1)] + (1) * HL Γ [(1, 0, 0, 1), (0, 1, 0, -1), (0, 0, 1, 0)] + (3) * HL Γ [(1, 0, 0, 1), (0, 1, 0, -1), (0, 0, 1, 1)] := by
  -- Matúš instance on joint variables, k = 1, [abcd], (a,b,c,d,z) = [(1, 0, 0, 1), (0, 1, 0, -1)] ; [(1, 0, -1, 0), (0, 1, 1, 0)] ; [(1, 0, -1, 1), (0, 1, 1, -1)] ; [(1, 0, 0, 0), (0, 1, 0, 0)] ; [(1, 0, 0, 0), (0, 1, 0, 0)]
  have cut144 := matus_ineq (G := G × G) 1 false (Γ ×ˢ Γ) (pw Γ) (pw_nonneg Γ) (pw_sum hΓ)
    (fun j q => (form (![(1, 0, 0, 1), (1, 0, -1, 0), (1, 0, -1, 1), (1, 0, 0, 0), (1, 0, 0, 0)] j) q, form (![(0, 1, 0, -1), (0, 1, 1, 0), (0, 1, 1, -1), (0, 1, 0, 0), (0, 1, 0, 0)] j) q))
  simp only [matusL, Bool.false_eq_true, ↓reduceIte] at cut144
  have cut144_0 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 1), (1, 0, -1, 0), (1, 0, -1, 1), (1, 0, 0, 0), (1, 0, 0, 0)] j) q, form (![(0, 1, 0, -1), (0, 1, 1, 0), (0, 1, 1, -1), (0, 1, 0, 0), (0, 1, 0, 0)] j) q)) {0} = HL Γ [(1, 0, 0, 1), (0, 1, 0, -1)] := by
    rw [show ({0} : Finset (Fin 5)) = ([0] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 1), (0, 1, 0, -1)] = HL Γ [(1, 0, 0, 1), (0, 1, 0, -1)]
    exact rfl
  have cut144_1 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 1), (1, 0, -1, 0), (1, 0, -1, 1), (1, 0, 0, 0), (1, 0, 0, 0)] j) q, form (![(0, 1, 0, -1), (0, 1, 1, 0), (0, 1, 1, -1), (0, 1, 0, 0), (0, 1, 0, 0)] j) q)) {1} = HL Γ [(1, 0, -1, 0), (0, 1, 1, 0)] := by
    rw [show ({1} : Finset (Fin 5)) = ([1] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, -1, 0), (0, 1, 1, 0)] = HL Γ [(1, 0, -1, 0), (0, 1, 1, 0)]
    exact rfl
  have cut144_2 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 1), (1, 0, -1, 0), (1, 0, -1, 1), (1, 0, 0, 0), (1, 0, 0, 0)] j) q, form (![(0, 1, 0, -1), (0, 1, 1, 0), (0, 1, 1, -1), (0, 1, 0, 0), (0, 1, 0, 0)] j) q)) {2} = HL Γ [(1, 0, -1, 1), (0, 1, 1, -1)] := by
    rw [show ({2} : Finset (Fin 5)) = ([2] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, -1, 1), (0, 1, 1, -1)] = HL Γ [(1, 0, -1, 1), (0, 1, 1, -1)]
    exact rfl
  have cut144_4 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 1), (1, 0, -1, 0), (1, 0, -1, 1), (1, 0, 0, 0), (1, 0, 0, 0)] j) q, form (![(0, 1, 0, -1), (0, 1, 1, 0), (0, 1, 1, -1), (0, 1, 0, 0), (0, 1, 0, 0)] j) q)) {4} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0)] := by
    rw [show ({4} : Finset (Fin 5)) = ([4] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 0), (0, 1, 0, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0)]
    exact rfl
  have cut144_01 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 1), (1, 0, -1, 0), (1, 0, -1, 1), (1, 0, 0, 0), (1, 0, 0, 0)] j) q, form (![(0, 1, 0, -1), (0, 1, 1, 0), (0, 1, 1, -1), (0, 1, 0, 0), (0, 1, 0, 0)] j) q)) {0, 1} = HL Γ [(1, 0, 0, 1), (0, 1, 0, -1), (0, 0, 1, 1)] := by
    rw [show ({0, 1} : Finset (Fin 5)) = ([0, 1] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 1), (1, 0, -1, 0), (0, 1, 0, -1), (0, 1, 1, 0)] = HL Γ [(1, 0, 0, 1), (0, 1, 0, -1), (0, 0, 1, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut144_02 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 1), (1, 0, -1, 0), (1, 0, -1, 1), (1, 0, 0, 0), (1, 0, 0, 0)] j) q, form (![(0, 1, 0, -1), (0, 1, 1, 0), (0, 1, 1, -1), (0, 1, 0, 0), (0, 1, 0, 0)] j) q)) {0, 2} = HL Γ [(1, 0, 0, 1), (0, 1, 0, -1), (0, 0, 1, 0)] := by
    rw [show ({0, 2} : Finset (Fin 5)) = ([0, 2] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 1), (1, 0, -1, 1), (0, 1, 0, -1), (0, 1, 1, -1)] = HL Γ [(1, 0, 0, 1), (0, 1, 0, -1), (0, 0, 1, 0)]
    exact HL_eq_norm hinj (by decide)
  have cut144_03 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 1), (1, 0, -1, 0), (1, 0, -1, 1), (1, 0, 0, 0), (1, 0, 0, 0)] j) q, form (![(0, 1, 0, -1), (0, 1, 1, 0), (0, 1, 1, -1), (0, 1, 0, 0), (0, 1, 0, 0)] j) q)) {0, 3} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 3} : Finset (Fin 5)) = ([0, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 1), (1, 0, 0, 0), (0, 1, 0, -1), (0, 1, 0, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut144_04 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 1), (1, 0, -1, 0), (1, 0, -1, 1), (1, 0, 0, 0), (1, 0, 0, 0)] j) q, form (![(0, 1, 0, -1), (0, 1, 1, 0), (0, 1, 1, -1), (0, 1, 0, 0), (0, 1, 0, 0)] j) q)) {0, 4} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 4} : Finset (Fin 5)) = ([0, 4] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 1), (1, 0, 0, 0), (0, 1, 0, -1), (0, 1, 0, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut144_12 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 1), (1, 0, -1, 0), (1, 0, -1, 1), (1, 0, 0, 0), (1, 0, 0, 0)] j) q, form (![(0, 1, 0, -1), (0, 1, 1, 0), (0, 1, 1, -1), (0, 1, 0, 0), (0, 1, 0, 0)] j) q)) {1, 2} = HL Γ [(1, 0, -1, 0), (0, 1, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({1, 2} : Finset (Fin 5)) = ([1, 2] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, -1, 0), (1, 0, -1, 1), (0, 1, 1, 0), (0, 1, 1, -1)] = HL Γ [(1, 0, -1, 0), (0, 1, 1, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut144_13 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 1), (1, 0, -1, 0), (1, 0, -1, 1), (1, 0, 0, 0), (1, 0, 0, 0)] j) q, form (![(0, 1, 0, -1), (0, 1, 1, 0), (0, 1, 1, -1), (0, 1, 0, 0), (0, 1, 0, 0)] j) q)) {1, 3} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0)] := by
    rw [show ({1, 3} : Finset (Fin 5)) = ([1, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, -1, 0), (1, 0, 0, 0), (0, 1, 1, 0), (0, 1, 0, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0)]
    exact HL_eq_norm hinj (by decide)
  have cut144_14 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 1), (1, 0, -1, 0), (1, 0, -1, 1), (1, 0, 0, 0), (1, 0, 0, 0)] j) q, form (![(0, 1, 0, -1), (0, 1, 1, 0), (0, 1, 1, -1), (0, 1, 0, 0), (0, 1, 0, 0)] j) q)) {1, 4} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0)] := by
    rw [show ({1, 4} : Finset (Fin 5)) = ([1, 4] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, -1, 0), (1, 0, 0, 0), (0, 1, 1, 0), (0, 1, 0, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0)]
    exact HL_eq_norm hinj (by decide)
  have cut144_23 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 1), (1, 0, -1, 0), (1, 0, -1, 1), (1, 0, 0, 0), (1, 0, 0, 0)] j) q, form (![(0, 1, 0, -1), (0, 1, 1, 0), (0, 1, 1, -1), (0, 1, 0, 0), (0, 1, 0, 0)] j) q)) {2, 3} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({2, 3} : Finset (Fin 5)) = ([2, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, -1, 1), (1, 0, 0, 0), (0, 1, 1, -1), (0, 1, 0, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut144_012 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 1), (1, 0, -1, 0), (1, 0, -1, 1), (1, 0, 0, 0), (1, 0, 0, 0)] j) q, form (![(0, 1, 0, -1), (0, 1, 1, 0), (0, 1, 1, -1), (0, 1, 0, 0), (0, 1, 0, 0)] j) q)) {0, 1, 2} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 1, 2} : Finset (Fin 5)) = ([0, 1, 2] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 1), (1, 0, -1, 0), (1, 0, -1, 1), (0, 1, 0, -1), (0, 1, 1, 0), (0, 1, 1, -1)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut144_013 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 1), (1, 0, -1, 0), (1, 0, -1, 1), (1, 0, 0, 0), (1, 0, 0, 0)] j) q, form (![(0, 1, 0, -1), (0, 1, 1, 0), (0, 1, 1, -1), (0, 1, 0, 0), (0, 1, 0, 0)] j) q)) {0, 1, 3} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 1, 3} : Finset (Fin 5)) = ([0, 1, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 1), (1, 0, -1, 0), (1, 0, 0, 0), (0, 1, 0, -1), (0, 1, 1, 0), (0, 1, 0, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut144_014 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 1), (1, 0, -1, 0), (1, 0, -1, 1), (1, 0, 0, 0), (1, 0, 0, 0)] j) q, form (![(0, 1, 0, -1), (0, 1, 1, 0), (0, 1, 1, -1), (0, 1, 0, 0), (0, 1, 0, 0)] j) q)) {0, 1, 4} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 1, 4} : Finset (Fin 5)) = ([0, 1, 4] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 1), (1, 0, -1, 0), (1, 0, 0, 0), (0, 1, 0, -1), (0, 1, 1, 0), (0, 1, 0, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut144_023 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 1), (1, 0, -1, 0), (1, 0, -1, 1), (1, 0, 0, 0), (1, 0, 0, 0)] j) q, form (![(0, 1, 0, -1), (0, 1, 1, 0), (0, 1, 1, -1), (0, 1, 0, 0), (0, 1, 0, 0)] j) q)) {0, 2, 3} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 2, 3} : Finset (Fin 5)) = ([0, 2, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 1), (1, 0, -1, 1), (1, 0, 0, 0), (0, 1, 0, -1), (0, 1, 1, -1), (0, 1, 0, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut144_row : 0 ≤ (-1) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 0)] + (3) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 1)] + (-6) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] + (3) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0)] + (-2) * HL Γ [(1, 0, 0, 1), (0, 1, 0, -1)] + (-2) * HL Γ [(1, 0, -1, 0), (0, 1, 1, 0)] + (1) * HL Γ [(1, 0, -1, 0), (0, 1, 1, 0), (0, 0, 0, 1)] + (1) * HL Γ [(1, 0, 0, 1), (0, 1, 0, -1), (0, 0, 1, 0)] + (3) * HL Γ [(1, 0, 0, 1), (0, 1, 0, -1), (0, 0, 1, 1)] := by
    norm_num at cut144
    linarith only [cut144, cut144_0, cut144_1, cut144_2, cut144_4, cut144_01, cut144_02, cut144_03, cut144_04, cut144_12, cut144_13, cut144_14, cut144_23, cut144_012, cut144_013, cut144_014, cut144_023]
  exact cut144_row

private theorem two_copy_row_cut145 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    0 ≤ (8) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 1)] + (-13) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] + (-5) * HL Γ [(1, 0, 0, 0), (0, 1, 0, -1)] + (-3) * HL Γ [(1, 0, 0, 1), (0, 1, 0, -1)] + (-3) * HL Γ [(1, 0, 1, 1), (0, 1, 0, -1)] + (2) * HL Γ [(1, 0, 1, 0), (0, 1, 0, 0), (0, 0, 0, 1)] + (2) * HL Γ [(1, 0, 0, 0), (0, 1, 0, -1), (0, 0, 1, 0)] + (6) * HL Γ [(1, 0, 0, 1), (0, 1, 0, -1), (0, 0, 1, 0)] + (6) * HL Γ [(1, 0, 0, 0), (0, 1, 0, -1), (0, 0, 1, 1)] := by
  -- companion instance on joint variables, k = 2, [acbd], (a,b,c,d,z) = [(1, 0, 0, 0), (0, 1, 0, -1)] ; [(1, 0, 0, 1), (0, 1, 0, -1)] ; [(1, 0, 1, 1), (0, 1, 0, -1)] ; [(1, 1, 1, -1)] ; [(1, 0, 1, 1), (0, 1, 0, -1)]
  have cut145 := companion_ineq (G := G × G) 2 true (Γ ×ˢ Γ) (pw Γ) (pw_nonneg Γ) (pw_sum hΓ)
    (fun j q => (form (![(1, 0, 0, 0), (1, 0, 0, 1), (1, 0, 1, 1), (1, 1, 1, -1), (1, 0, 1, 1)] j) q, form (![(0, 1, 0, -1), (0, 1, 0, -1), (0, 1, 0, -1), (0, 0, 0, 0), (0, 1, 0, -1)] j) q))
  simp only [compL, ↓reduceIte] at cut145
  have cut145_0 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 0), (1, 0, 0, 1), (1, 0, 1, 1), (1, 1, 1, -1), (1, 0, 1, 1)] j) q, form (![(0, 1, 0, -1), (0, 1, 0, -1), (0, 1, 0, -1), (0, 0, 0, 0), (0, 1, 0, -1)] j) q)) {0} = HL Γ [(1, 0, 0, 0), (0, 1, 0, -1)] := by
    rw [show ({0} : Finset (Fin 5)) = ([0] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 0), (0, 1, 0, -1)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, -1)]
    exact rfl
  have cut145_1 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 0), (1, 0, 0, 1), (1, 0, 1, 1), (1, 1, 1, -1), (1, 0, 1, 1)] j) q, form (![(0, 1, 0, -1), (0, 1, 0, -1), (0, 1, 0, -1), (0, 0, 0, 0), (0, 1, 0, -1)] j) q)) {1} = HL Γ [(1, 0, 0, 1), (0, 1, 0, -1)] := by
    rw [show ({1} : Finset (Fin 5)) = ([1] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 1), (0, 1, 0, -1)] = HL Γ [(1, 0, 0, 1), (0, 1, 0, -1)]
    exact rfl
  have cut145_2 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 0), (1, 0, 0, 1), (1, 0, 1, 1), (1, 1, 1, -1), (1, 0, 1, 1)] j) q, form (![(0, 1, 0, -1), (0, 1, 0, -1), (0, 1, 0, -1), (0, 0, 0, 0), (0, 1, 0, -1)] j) q)) {2} = HL Γ [(1, 0, 1, 1), (0, 1, 0, -1)] := by
    rw [show ({2} : Finset (Fin 5)) = ([2] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 1, 1), (0, 1, 0, -1)] = HL Γ [(1, 0, 1, 1), (0, 1, 0, -1)]
    exact rfl
  have cut145_4 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 0), (1, 0, 0, 1), (1, 0, 1, 1), (1, 1, 1, -1), (1, 0, 1, 1)] j) q, form (![(0, 1, 0, -1), (0, 1, 0, -1), (0, 1, 0, -1), (0, 0, 0, 0), (0, 1, 0, -1)] j) q)) {4} = HL Γ [(1, 0, 1, 1), (0, 1, 0, -1)] := by
    rw [show ({4} : Finset (Fin 5)) = ([4] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 1, 1), (0, 1, 0, -1)] = HL Γ [(1, 0, 1, 1), (0, 1, 0, -1)]
    exact rfl
  have cut145_01 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 0), (1, 0, 0, 1), (1, 0, 1, 1), (1, 1, 1, -1), (1, 0, 1, 1)] j) q, form (![(0, 1, 0, -1), (0, 1, 0, -1), (0, 1, 0, -1), (0, 0, 0, 0), (0, 1, 0, -1)] j) q)) {0, 1} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 1} : Finset (Fin 5)) = ([0, 1] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 0), (1, 0, 0, 1), (0, 1, 0, -1), (0, 1, 0, -1)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut145_02 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 0), (1, 0, 0, 1), (1, 0, 1, 1), (1, 1, 1, -1), (1, 0, 1, 1)] j) q, form (![(0, 1, 0, -1), (0, 1, 0, -1), (0, 1, 0, -1), (0, 0, 0, 0), (0, 1, 0, -1)] j) q)) {0, 2} = HL Γ [(1, 0, 0, 0), (0, 1, 0, -1), (0, 0, 1, 1)] := by
    rw [show ({0, 2} : Finset (Fin 5)) = ([0, 2] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 0), (1, 0, 1, 1), (0, 1, 0, -1), (0, 1, 0, -1)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, -1), (0, 0, 1, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut145_03 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 0), (1, 0, 0, 1), (1, 0, 1, 1), (1, 1, 1, -1), (1, 0, 1, 1)] j) q, form (![(0, 1, 0, -1), (0, 1, 0, -1), (0, 1, 0, -1), (0, 0, 0, 0), (0, 1, 0, -1)] j) q)) {0, 3} = HL Γ [(1, 0, 0, 0), (0, 1, 0, -1), (0, 0, 1, 0)] := by
    rw [show ({0, 3} : Finset (Fin 5)) = ([0, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 0), (1, 1, 1, -1), (0, 1, 0, -1), (0, 0, 0, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, -1), (0, 0, 1, 0)]
    exact HL_eq_norm hinj (by decide)
  have cut145_04 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 0), (1, 0, 0, 1), (1, 0, 1, 1), (1, 1, 1, -1), (1, 0, 1, 1)] j) q, form (![(0, 1, 0, -1), (0, 1, 0, -1), (0, 1, 0, -1), (0, 0, 0, 0), (0, 1, 0, -1)] j) q)) {0, 4} = HL Γ [(1, 0, 0, 0), (0, 1, 0, -1), (0, 0, 1, 1)] := by
    rw [show ({0, 4} : Finset (Fin 5)) = ([0, 4] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 0), (1, 0, 1, 1), (0, 1, 0, -1), (0, 1, 0, -1)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, -1), (0, 0, 1, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut145_12 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 0), (1, 0, 0, 1), (1, 0, 1, 1), (1, 1, 1, -1), (1, 0, 1, 1)] j) q, form (![(0, 1, 0, -1), (0, 1, 0, -1), (0, 1, 0, -1), (0, 0, 0, 0), (0, 1, 0, -1)] j) q)) {1, 2} = HL Γ [(1, 0, 0, 1), (0, 1, 0, -1), (0, 0, 1, 0)] := by
    rw [show ({1, 2} : Finset (Fin 5)) = ([1, 2] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 1), (1, 0, 1, 1), (0, 1, 0, -1), (0, 1, 0, -1)] = HL Γ [(1, 0, 0, 1), (0, 1, 0, -1), (0, 0, 1, 0)]
    exact HL_eq_norm hinj (by decide)
  have cut145_13 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 0), (1, 0, 0, 1), (1, 0, 1, 1), (1, 1, 1, -1), (1, 0, 1, 1)] j) q, form (![(0, 1, 0, -1), (0, 1, 0, -1), (0, 1, 0, -1), (0, 0, 0, 0), (0, 1, 0, -1)] j) q)) {1, 3} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({1, 3} : Finset (Fin 5)) = ([1, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 1), (1, 1, 1, -1), (0, 1, 0, -1), (0, 0, 0, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut145_14 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 0), (1, 0, 0, 1), (1, 0, 1, 1), (1, 1, 1, -1), (1, 0, 1, 1)] j) q, form (![(0, 1, 0, -1), (0, 1, 0, -1), (0, 1, 0, -1), (0, 0, 0, 0), (0, 1, 0, -1)] j) q)) {1, 4} = HL Γ [(1, 0, 0, 1), (0, 1, 0, -1), (0, 0, 1, 0)] := by
    rw [show ({1, 4} : Finset (Fin 5)) = ([1, 4] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 1), (1, 0, 1, 1), (0, 1, 0, -1), (0, 1, 0, -1)] = HL Γ [(1, 0, 0, 1), (0, 1, 0, -1), (0, 0, 1, 0)]
    exact HL_eq_norm hinj (by decide)
  have cut145_23 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 0), (1, 0, 0, 1), (1, 0, 1, 1), (1, 1, 1, -1), (1, 0, 1, 1)] j) q, form (![(0, 1, 0, -1), (0, 1, 0, -1), (0, 1, 0, -1), (0, 0, 0, 0), (0, 1, 0, -1)] j) q)) {2, 3} = HL Γ [(1, 0, 1, 0), (0, 1, 0, 0), (0, 0, 0, 1)] := by
    rw [show ({2, 3} : Finset (Fin 5)) = ([2, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 1, 1), (1, 1, 1, -1), (0, 1, 0, -1), (0, 0, 0, 0)] = HL Γ [(1, 0, 1, 0), (0, 1, 0, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut145_012 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 0), (1, 0, 0, 1), (1, 0, 1, 1), (1, 1, 1, -1), (1, 0, 1, 1)] j) q, form (![(0, 1, 0, -1), (0, 1, 0, -1), (0, 1, 0, -1), (0, 0, 0, 0), (0, 1, 0, -1)] j) q)) {0, 1, 2} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 1, 2} : Finset (Fin 5)) = ([0, 1, 2] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 0), (1, 0, 0, 1), (1, 0, 1, 1), (0, 1, 0, -1), (0, 1, 0, -1), (0, 1, 0, -1)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut145_013 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 0), (1, 0, 0, 1), (1, 0, 1, 1), (1, 1, 1, -1), (1, 0, 1, 1)] j) q, form (![(0, 1, 0, -1), (0, 1, 0, -1), (0, 1, 0, -1), (0, 0, 0, 0), (0, 1, 0, -1)] j) q)) {0, 1, 3} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 1, 3} : Finset (Fin 5)) = ([0, 1, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 0), (1, 0, 0, 1), (1, 1, 1, -1), (0, 1, 0, -1), (0, 1, 0, -1), (0, 0, 0, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut145_014 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 0), (1, 0, 0, 1), (1, 0, 1, 1), (1, 1, 1, -1), (1, 0, 1, 1)] j) q, form (![(0, 1, 0, -1), (0, 1, 0, -1), (0, 1, 0, -1), (0, 0, 0, 0), (0, 1, 0, -1)] j) q)) {0, 1, 4} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 1, 4} : Finset (Fin 5)) = ([0, 1, 4] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 0), (1, 0, 0, 1), (1, 0, 1, 1), (0, 1, 0, -1), (0, 1, 0, -1), (0, 1, 0, -1)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut145_023 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 0), (1, 0, 0, 1), (1, 0, 1, 1), (1, 1, 1, -1), (1, 0, 1, 1)] j) q, form (![(0, 1, 0, -1), (0, 1, 0, -1), (0, 1, 0, -1), (0, 0, 0, 0), (0, 1, 0, -1)] j) q)) {0, 2, 3} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 2, 3} : Finset (Fin 5)) = ([0, 2, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 0), (1, 0, 1, 1), (1, 1, 1, -1), (0, 1, 0, -1), (0, 1, 0, -1), (0, 0, 0, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut145_row : 0 ≤ (8) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 1)] + (-13) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] + (-5) * HL Γ [(1, 0, 0, 0), (0, 1, 0, -1)] + (-3) * HL Γ [(1, 0, 0, 1), (0, 1, 0, -1)] + (-3) * HL Γ [(1, 0, 1, 1), (0, 1, 0, -1)] + (2) * HL Γ [(1, 0, 1, 0), (0, 1, 0, 0), (0, 0, 0, 1)] + (2) * HL Γ [(1, 0, 0, 0), (0, 1, 0, -1), (0, 0, 1, 0)] + (6) * HL Γ [(1, 0, 0, 1), (0, 1, 0, -1), (0, 0, 1, 0)] + (6) * HL Γ [(1, 0, 0, 0), (0, 1, 0, -1), (0, 0, 1, 1)] := by
    norm_num at cut145
    linarith only [cut145, cut145_0, cut145_1, cut145_2, cut145_4, cut145_01, cut145_02, cut145_03, cut145_04, cut145_12, cut145_13, cut145_14, cut145_23, cut145_012, cut145_013, cut145_014, cut145_023]
  exact cut145_row

private theorem two_copy_row_cut146 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    0 ≤ (-4) * HL Γ [(0, 0, 1, 0)] + (-3) * HL Γ [(0, 1, 1, -1)] + (-3) * HL Γ [(0, 1, 1, 0)] + (-9) * HL Γ [(1, 1, 1, 0)] + (4) * HL Γ [(0, 1, 0, -1), (0, 0, 1, 0)] + (6) * HL Γ [(0, 1, 0, 0), (0, 0, 1, 0)] + (-15) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0)] + (3) * HL Γ [(1, 0, 0, 0), (0, 0, 1, 0)] + (10) * HL Γ [(1, 1, 0, 0), (0, 0, 1, 0)] + (3) * HL Γ [(1, 0, 1, 0), (0, 1, 0, 0)] + (6) * HL Γ [(1, 0, 0, 1), (0, 1, 1, -1)] + (9) * HL Γ [(1, 0, 0, 0), (0, 1, 1, 0)] + (-7) * HL Γ [(1, 0, 0, 1), (0, 1, 0, -1), (0, 0, 1, 0)] := by
  -- Matúš instance k = 3, [abcd], (a,b,c,d,z) = (0, 0, 1, 0), (1, 1, 1, 0), (0, 1, 1, 0), (1, 0, 1, 0), (0, 1, 1, -1)
  have cut146 := matus_ineq (G := G) 3 false (Γ ×ˢ Γ) (pw Γ) (pw_nonneg Γ) (pw_sum hΓ)
    (fun j q => form (![(0, 0, 1, 0), (1, 1, 1, 0), (0, 1, 1, 0), (1, 0, 1, 0), (0, 1, 1, -1)] j) q)
  simp only [matusL, Bool.false_eq_true, ↓reduceIte] at cut146
  have cut146_0 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 0, 1, 0), (1, 1, 1, 0), (0, 1, 1, 0), (1, 0, 1, 0), (0, 1, 1, -1)] j) q) {0} = HL Γ [(0, 0, 1, 0)] := by
    rw [show ({0} : Finset (Fin 5)) = ([0] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact rfl
  have cut146_1 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 0, 1, 0), (1, 1, 1, 0), (0, 1, 1, 0), (1, 0, 1, 0), (0, 1, 1, -1)] j) q) {1} = HL Γ [(1, 1, 1, 0)] := by
    rw [show ({1} : Finset (Fin 5)) = ([1] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact rfl
  have cut146_2 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 0, 1, 0), (1, 1, 1, 0), (0, 1, 1, 0), (1, 0, 1, 0), (0, 1, 1, -1)] j) q) {2} = HL Γ [(0, 1, 1, 0)] := by
    rw [show ({2} : Finset (Fin 5)) = ([2] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact rfl
  have cut146_4 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 0, 1, 0), (1, 1, 1, 0), (0, 1, 1, 0), (1, 0, 1, 0), (0, 1, 1, -1)] j) q) {4} = HL Γ [(0, 1, 1, -1)] := by
    rw [show ({4} : Finset (Fin 5)) = ([4] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact rfl
  have cut146_01 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 0, 1, 0), (1, 1, 1, 0), (0, 1, 1, 0), (1, 0, 1, 0), (0, 1, 1, -1)] j) q) {0, 1} = HL Γ [(1, 1, 0, 0), (0, 0, 1, 0)] := by
    rw [show ({0, 1} : Finset (Fin 5)) = ([0, 1] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut146_02 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 0, 1, 0), (1, 1, 1, 0), (0, 1, 1, 0), (1, 0, 1, 0), (0, 1, 1, -1)] j) q) {0, 2} = HL Γ [(0, 1, 0, 0), (0, 0, 1, 0)] := by
    rw [show ({0, 2} : Finset (Fin 5)) = ([0, 2] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut146_03 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 0, 1, 0), (1, 1, 1, 0), (0, 1, 1, 0), (1, 0, 1, 0), (0, 1, 1, -1)] j) q) {0, 3} = HL Γ [(1, 0, 0, 0), (0, 0, 1, 0)] := by
    rw [show ({0, 3} : Finset (Fin 5)) = ([0, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut146_04 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 0, 1, 0), (1, 1, 1, 0), (0, 1, 1, 0), (1, 0, 1, 0), (0, 1, 1, -1)] j) q) {0, 4} = HL Γ [(0, 1, 0, -1), (0, 0, 1, 0)] := by
    rw [show ({0, 4} : Finset (Fin 5)) = ([0, 4] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut146_12 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 0, 1, 0), (1, 1, 1, 0), (0, 1, 1, 0), (1, 0, 1, 0), (0, 1, 1, -1)] j) q) {1, 2} = HL Γ [(1, 0, 0, 0), (0, 1, 1, 0)] := by
    rw [show ({1, 2} : Finset (Fin 5)) = ([1, 2] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut146_13 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 0, 1, 0), (1, 1, 1, 0), (0, 1, 1, 0), (1, 0, 1, 0), (0, 1, 1, -1)] j) q) {1, 3} = HL Γ [(1, 0, 1, 0), (0, 1, 0, 0)] := by
    rw [show ({1, 3} : Finset (Fin 5)) = ([1, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut146_14 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 0, 1, 0), (1, 1, 1, 0), (0, 1, 1, 0), (1, 0, 1, 0), (0, 1, 1, -1)] j) q) {1, 4} = HL Γ [(1, 0, 0, 1), (0, 1, 1, -1)] := by
    rw [show ({1, 4} : Finset (Fin 5)) = ([1, 4] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut146_23 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 0, 1, 0), (1, 1, 1, 0), (0, 1, 1, 0), (1, 0, 1, 0), (0, 1, 1, -1)] j) q) {2, 3} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0)] := by
    rw [show ({2, 3} : Finset (Fin 5)) = ([2, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut146_012 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 0, 1, 0), (1, 1, 1, 0), (0, 1, 1, 0), (1, 0, 1, 0), (0, 1, 1, -1)] j) q) {0, 1, 2} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0)] := by
    rw [show ({0, 1, 2} : Finset (Fin 5)) = ([0, 1, 2] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut146_013 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 0, 1, 0), (1, 1, 1, 0), (0, 1, 1, 0), (1, 0, 1, 0), (0, 1, 1, -1)] j) q) {0, 1, 3} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0)] := by
    rw [show ({0, 1, 3} : Finset (Fin 5)) = ([0, 1, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut146_014 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 0, 1, 0), (1, 1, 1, 0), (0, 1, 1, 0), (1, 0, 1, 0), (0, 1, 1, -1)] j) q) {0, 1, 4} = HL Γ [(1, 0, 0, 1), (0, 1, 0, -1), (0, 0, 1, 0)] := by
    rw [show ({0, 1, 4} : Finset (Fin 5)) = ([0, 1, 4] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut146_023 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 0, 1, 0), (1, 1, 1, 0), (0, 1, 1, 0), (1, 0, 1, 0), (0, 1, 1, -1)] j) q) {0, 2, 3} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0)] := by
    rw [show ({0, 2, 3} : Finset (Fin 5)) = ([0, 2, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut146_row : 0 ≤ (-4) * HL Γ [(0, 0, 1, 0)] + (-3) * HL Γ [(0, 1, 1, -1)] + (-3) * HL Γ [(0, 1, 1, 0)] + (-9) * HL Γ [(1, 1, 1, 0)] + (4) * HL Γ [(0, 1, 0, -1), (0, 0, 1, 0)] + (6) * HL Γ [(0, 1, 0, 0), (0, 0, 1, 0)] + (-15) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0)] + (3) * HL Γ [(1, 0, 0, 0), (0, 0, 1, 0)] + (10) * HL Γ [(1, 1, 0, 0), (0, 0, 1, 0)] + (3) * HL Γ [(1, 0, 1, 0), (0, 1, 0, 0)] + (6) * HL Γ [(1, 0, 0, 1), (0, 1, 1, -1)] + (9) * HL Γ [(1, 0, 0, 0), (0, 1, 1, 0)] + (-7) * HL Γ [(1, 0, 0, 1), (0, 1, 0, -1), (0, 0, 1, 0)] := by
    norm_num at cut146
    linarith only [cut146, cut146_0, cut146_1, cut146_2, cut146_4, cut146_01, cut146_02, cut146_03, cut146_04, cut146_12, cut146_13, cut146_14, cut146_23, cut146_012, cut146_013, cut146_014, cut146_023]
  exact cut146_row

private theorem two_copy_row_cut147 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    0 ≤ (-13) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] + (8) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0)] + (-5) * HL Γ [(1, 0, -1, 0), (0, 1, 0, 0)] + (-3) * HL Γ [(1, 0, -1, 0), (0, 1, 1, 0)] + (-3) * HL Γ [(1, 0, -1, 0), (0, 1, 1, 1)] + (2) * HL Γ [(1, 0, -1, 0), (0, 1, 0, 0), (0, 0, 0, 1)] + (6) * HL Γ [(1, 0, -1, 0), (0, 1, 1, 0), (0, 0, 0, 1)] + (2) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 1), (0, 0, 1, 0)] + (6) * HL Γ [(1, 0, 0, 1), (0, 1, 0, 0), (0, 0, 1, 1)] := by
  -- companion instance on joint variables, k = 2, [acbd], (a,b,c,d,z) = [(1, 0, -1, 0), (0, 1, 0, 0)] ; [(1, 0, -1, 0), (0, 1, 1, 0)] ; [(1, 0, -1, 0), (0, 1, 1, 1)] ; [(1, 1, -1, 1)] ; [(1, 0, -1, 0), (0, 1, 1, 1)]
  have cut147 := companion_ineq (G := G × G) 2 true (Γ ×ˢ Γ) (pw Γ) (pw_nonneg Γ) (pw_sum hΓ)
    (fun j q => (form (![(1, 0, -1, 0), (1, 0, -1, 0), (1, 0, -1, 0), (1, 1, -1, 1), (1, 0, -1, 0)] j) q, form (![(0, 1, 0, 0), (0, 1, 1, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 1, 1, 1)] j) q))
  simp only [compL, ↓reduceIte] at cut147
  have cut147_0 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, -1, 0), (1, 0, -1, 0), (1, 0, -1, 0), (1, 1, -1, 1), (1, 0, -1, 0)] j) q, form (![(0, 1, 0, 0), (0, 1, 1, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 1, 1, 1)] j) q)) {0} = HL Γ [(1, 0, -1, 0), (0, 1, 0, 0)] := by
    rw [show ({0} : Finset (Fin 5)) = ([0] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, -1, 0), (0, 1, 0, 0)] = HL Γ [(1, 0, -1, 0), (0, 1, 0, 0)]
    exact rfl
  have cut147_1 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, -1, 0), (1, 0, -1, 0), (1, 0, -1, 0), (1, 1, -1, 1), (1, 0, -1, 0)] j) q, form (![(0, 1, 0, 0), (0, 1, 1, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 1, 1, 1)] j) q)) {1} = HL Γ [(1, 0, -1, 0), (0, 1, 1, 0)] := by
    rw [show ({1} : Finset (Fin 5)) = ([1] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, -1, 0), (0, 1, 1, 0)] = HL Γ [(1, 0, -1, 0), (0, 1, 1, 0)]
    exact rfl
  have cut147_2 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, -1, 0), (1, 0, -1, 0), (1, 0, -1, 0), (1, 1, -1, 1), (1, 0, -1, 0)] j) q, form (![(0, 1, 0, 0), (0, 1, 1, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 1, 1, 1)] j) q)) {2} = HL Γ [(1, 0, -1, 0), (0, 1, 1, 1)] := by
    rw [show ({2} : Finset (Fin 5)) = ([2] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, -1, 0), (0, 1, 1, 1)] = HL Γ [(1, 0, -1, 0), (0, 1, 1, 1)]
    exact rfl
  have cut147_4 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, -1, 0), (1, 0, -1, 0), (1, 0, -1, 0), (1, 1, -1, 1), (1, 0, -1, 0)] j) q, form (![(0, 1, 0, 0), (0, 1, 1, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 1, 1, 1)] j) q)) {4} = HL Γ [(1, 0, -1, 0), (0, 1, 1, 1)] := by
    rw [show ({4} : Finset (Fin 5)) = ([4] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, -1, 0), (0, 1, 1, 1)] = HL Γ [(1, 0, -1, 0), (0, 1, 1, 1)]
    exact rfl
  have cut147_01 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, -1, 0), (1, 0, -1, 0), (1, 0, -1, 0), (1, 1, -1, 1), (1, 0, -1, 0)] j) q, form (![(0, 1, 0, 0), (0, 1, 1, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 1, 1, 1)] j) q)) {0, 1} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0)] := by
    rw [show ({0, 1} : Finset (Fin 5)) = ([0, 1] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, -1, 0), (1, 0, -1, 0), (0, 1, 0, 0), (0, 1, 1, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0)]
    exact HL_eq_norm hinj (by decide)
  have cut147_02 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, -1, 0), (1, 0, -1, 0), (1, 0, -1, 0), (1, 1, -1, 1), (1, 0, -1, 0)] j) q, form (![(0, 1, 0, 0), (0, 1, 1, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 1, 1, 1)] j) q)) {0, 2} = HL Γ [(1, 0, 0, 1), (0, 1, 0, 0), (0, 0, 1, 1)] := by
    rw [show ({0, 2} : Finset (Fin 5)) = ([0, 2] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, -1, 0), (1, 0, -1, 0), (0, 1, 0, 0), (0, 1, 1, 1)] = HL Γ [(1, 0, 0, 1), (0, 1, 0, 0), (0, 0, 1, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut147_03 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, -1, 0), (1, 0, -1, 0), (1, 0, -1, 0), (1, 1, -1, 1), (1, 0, -1, 0)] j) q, form (![(0, 1, 0, 0), (0, 1, 1, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 1, 1, 1)] j) q)) {0, 3} = HL Γ [(1, 0, -1, 0), (0, 1, 0, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 3} : Finset (Fin 5)) = ([0, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, -1, 0), (1, 1, -1, 1), (0, 1, 0, 0), (0, 0, 0, 0)] = HL Γ [(1, 0, -1, 0), (0, 1, 0, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut147_04 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, -1, 0), (1, 0, -1, 0), (1, 0, -1, 0), (1, 1, -1, 1), (1, 0, -1, 0)] j) q, form (![(0, 1, 0, 0), (0, 1, 1, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 1, 1, 1)] j) q)) {0, 4} = HL Γ [(1, 0, 0, 1), (0, 1, 0, 0), (0, 0, 1, 1)] := by
    rw [show ({0, 4} : Finset (Fin 5)) = ([0, 4] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, -1, 0), (1, 0, -1, 0), (0, 1, 0, 0), (0, 1, 1, 1)] = HL Γ [(1, 0, 0, 1), (0, 1, 0, 0), (0, 0, 1, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut147_12 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, -1, 0), (1, 0, -1, 0), (1, 0, -1, 0), (1, 1, -1, 1), (1, 0, -1, 0)] j) q, form (![(0, 1, 0, 0), (0, 1, 1, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 1, 1, 1)] j) q)) {1, 2} = HL Γ [(1, 0, -1, 0), (0, 1, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({1, 2} : Finset (Fin 5)) = ([1, 2] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, -1, 0), (1, 0, -1, 0), (0, 1, 1, 0), (0, 1, 1, 1)] = HL Γ [(1, 0, -1, 0), (0, 1, 1, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut147_13 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, -1, 0), (1, 0, -1, 0), (1, 0, -1, 0), (1, 1, -1, 1), (1, 0, -1, 0)] j) q, form (![(0, 1, 0, 0), (0, 1, 1, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 1, 1, 1)] j) q)) {1, 3} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({1, 3} : Finset (Fin 5)) = ([1, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, -1, 0), (1, 1, -1, 1), (0, 1, 1, 0), (0, 0, 0, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut147_14 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, -1, 0), (1, 0, -1, 0), (1, 0, -1, 0), (1, 1, -1, 1), (1, 0, -1, 0)] j) q, form (![(0, 1, 0, 0), (0, 1, 1, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 1, 1, 1)] j) q)) {1, 4} = HL Γ [(1, 0, -1, 0), (0, 1, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({1, 4} : Finset (Fin 5)) = ([1, 4] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, -1, 0), (1, 0, -1, 0), (0, 1, 1, 0), (0, 1, 1, 1)] = HL Γ [(1, 0, -1, 0), (0, 1, 1, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut147_23 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, -1, 0), (1, 0, -1, 0), (1, 0, -1, 0), (1, 1, -1, 1), (1, 0, -1, 0)] j) q, form (![(0, 1, 0, 0), (0, 1, 1, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 1, 1, 1)] j) q)) {2, 3} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 1), (0, 0, 1, 0)] := by
    rw [show ({2, 3} : Finset (Fin 5)) = ([2, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, -1, 0), (1, 1, -1, 1), (0, 1, 1, 1), (0, 0, 0, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 1), (0, 0, 1, 0)]
    exact HL_eq_norm hinj (by decide)
  have cut147_012 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, -1, 0), (1, 0, -1, 0), (1, 0, -1, 0), (1, 1, -1, 1), (1, 0, -1, 0)] j) q, form (![(0, 1, 0, 0), (0, 1, 1, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 1, 1, 1)] j) q)) {0, 1, 2} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 1, 2} : Finset (Fin 5)) = ([0, 1, 2] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, -1, 0), (1, 0, -1, 0), (1, 0, -1, 0), (0, 1, 0, 0), (0, 1, 1, 0), (0, 1, 1, 1)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut147_013 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, -1, 0), (1, 0, -1, 0), (1, 0, -1, 0), (1, 1, -1, 1), (1, 0, -1, 0)] j) q, form (![(0, 1, 0, 0), (0, 1, 1, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 1, 1, 1)] j) q)) {0, 1, 3} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 1, 3} : Finset (Fin 5)) = ([0, 1, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, -1, 0), (1, 0, -1, 0), (1, 1, -1, 1), (0, 1, 0, 0), (0, 1, 1, 0), (0, 0, 0, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut147_014 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, -1, 0), (1, 0, -1, 0), (1, 0, -1, 0), (1, 1, -1, 1), (1, 0, -1, 0)] j) q, form (![(0, 1, 0, 0), (0, 1, 1, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 1, 1, 1)] j) q)) {0, 1, 4} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 1, 4} : Finset (Fin 5)) = ([0, 1, 4] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, -1, 0), (1, 0, -1, 0), (1, 0, -1, 0), (0, 1, 0, 0), (0, 1, 1, 0), (0, 1, 1, 1)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut147_023 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, -1, 0), (1, 0, -1, 0), (1, 0, -1, 0), (1, 1, -1, 1), (1, 0, -1, 0)] j) q, form (![(0, 1, 0, 0), (0, 1, 1, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 1, 1, 1)] j) q)) {0, 2, 3} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 2, 3} : Finset (Fin 5)) = ([0, 2, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, -1, 0), (1, 0, -1, 0), (1, 1, -1, 1), (0, 1, 0, 0), (0, 1, 1, 1), (0, 0, 0, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut147_row : 0 ≤ (-13) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] + (8) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0)] + (-5) * HL Γ [(1, 0, -1, 0), (0, 1, 0, 0)] + (-3) * HL Γ [(1, 0, -1, 0), (0, 1, 1, 0)] + (-3) * HL Γ [(1, 0, -1, 0), (0, 1, 1, 1)] + (2) * HL Γ [(1, 0, -1, 0), (0, 1, 0, 0), (0, 0, 0, 1)] + (6) * HL Γ [(1, 0, -1, 0), (0, 1, 1, 0), (0, 0, 0, 1)] + (2) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 1), (0, 0, 1, 0)] + (6) * HL Γ [(1, 0, 0, 1), (0, 1, 0, 0), (0, 0, 1, 1)] := by
    norm_num at cut147
    linarith only [cut147, cut147_0, cut147_1, cut147_2, cut147_4, cut147_01, cut147_02, cut147_03, cut147_04, cut147_12, cut147_13, cut147_14, cut147_23, cut147_012, cut147_013, cut147_014, cut147_023]
  exact cut147_row

private theorem two_copy_row_cut148 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    0 ≤ (-4) * HL Γ [(0, 0, 1, 0)] + (-6) * HL Γ [(0, 1, 1, -1)] + (-9) * HL Γ [(1, 1, 1, 0)] + (10) * HL Γ [(0, 1, 0, -1), (0, 0, 1, 0)] + (-3) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0)] + (3) * HL Γ [(1, 0, 0, 0), (0, 0, 1, 0)] + (10) * HL Γ [(1, 1, 0, 0), (0, 0, 1, 0)] + (3) * HL Γ [(1, 0, 1, 0), (0, 1, 0, 0)] + (-3) * HL Γ [(1, 0, 1, 0), (0, 1, 1, -1)] + (15) * HL Γ [(1, 0, 0, 1), (0, 1, 1, -1)] + (-16) * HL Γ [(1, 0, 0, 1), (0, 1, 0, -1), (0, 0, 1, 0)] := by
  -- companion instance k = 3, [acbd], (a,b,c,d,z) = (1, 1, 1, 0), (0, 1, 1, -1), (0, 0, 1, 0), (1, 0, 1, 0), (0, 0, 1, 0)
  have cut148 := companion_ineq (G := G) 3 true (Γ ×ˢ Γ) (pw Γ) (pw_nonneg Γ) (pw_sum hΓ)
    (fun j q => form (![(1, 1, 1, 0), (0, 1, 1, -1), (0, 0, 1, 0), (1, 0, 1, 0), (0, 0, 1, 0)] j) q)
  simp only [compL, ↓reduceIte] at cut148
  have cut148_0 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(1, 1, 1, 0), (0, 1, 1, -1), (0, 0, 1, 0), (1, 0, 1, 0), (0, 0, 1, 0)] j) q) {0} = HL Γ [(1, 1, 1, 0)] := by
    rw [show ({0} : Finset (Fin 5)) = ([0] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact rfl
  have cut148_1 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(1, 1, 1, 0), (0, 1, 1, -1), (0, 0, 1, 0), (1, 0, 1, 0), (0, 0, 1, 0)] j) q) {1} = HL Γ [(0, 1, 1, -1)] := by
    rw [show ({1} : Finset (Fin 5)) = ([1] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact rfl
  have cut148_2 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(1, 1, 1, 0), (0, 1, 1, -1), (0, 0, 1, 0), (1, 0, 1, 0), (0, 0, 1, 0)] j) q) {2} = HL Γ [(0, 0, 1, 0)] := by
    rw [show ({2} : Finset (Fin 5)) = ([2] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact rfl
  have cut148_4 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(1, 1, 1, 0), (0, 1, 1, -1), (0, 0, 1, 0), (1, 0, 1, 0), (0, 0, 1, 0)] j) q) {4} = HL Γ [(0, 0, 1, 0)] := by
    rw [show ({4} : Finset (Fin 5)) = ([4] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact rfl
  have cut148_01 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(1, 1, 1, 0), (0, 1, 1, -1), (0, 0, 1, 0), (1, 0, 1, 0), (0, 0, 1, 0)] j) q) {0, 1} = HL Γ [(1, 0, 0, 1), (0, 1, 1, -1)] := by
    rw [show ({0, 1} : Finset (Fin 5)) = ([0, 1] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut148_02 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(1, 1, 1, 0), (0, 1, 1, -1), (0, 0, 1, 0), (1, 0, 1, 0), (0, 0, 1, 0)] j) q) {0, 2} = HL Γ [(1, 1, 0, 0), (0, 0, 1, 0)] := by
    rw [show ({0, 2} : Finset (Fin 5)) = ([0, 2] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut148_03 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(1, 1, 1, 0), (0, 1, 1, -1), (0, 0, 1, 0), (1, 0, 1, 0), (0, 0, 1, 0)] j) q) {0, 3} = HL Γ [(1, 0, 1, 0), (0, 1, 0, 0)] := by
    rw [show ({0, 3} : Finset (Fin 5)) = ([0, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut148_04 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(1, 1, 1, 0), (0, 1, 1, -1), (0, 0, 1, 0), (1, 0, 1, 0), (0, 0, 1, 0)] j) q) {0, 4} = HL Γ [(1, 1, 0, 0), (0, 0, 1, 0)] := by
    rw [show ({0, 4} : Finset (Fin 5)) = ([0, 4] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut148_12 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(1, 1, 1, 0), (0, 1, 1, -1), (0, 0, 1, 0), (1, 0, 1, 0), (0, 0, 1, 0)] j) q) {1, 2} = HL Γ [(0, 1, 0, -1), (0, 0, 1, 0)] := by
    rw [show ({1, 2} : Finset (Fin 5)) = ([1, 2] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut148_13 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(1, 1, 1, 0), (0, 1, 1, -1), (0, 0, 1, 0), (1, 0, 1, 0), (0, 0, 1, 0)] j) q) {1, 3} = HL Γ [(1, 0, 1, 0), (0, 1, 1, -1)] := by
    rw [show ({1, 3} : Finset (Fin 5)) = ([1, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut148_14 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(1, 1, 1, 0), (0, 1, 1, -1), (0, 0, 1, 0), (1, 0, 1, 0), (0, 0, 1, 0)] j) q) {1, 4} = HL Γ [(0, 1, 0, -1), (0, 0, 1, 0)] := by
    rw [show ({1, 4} : Finset (Fin 5)) = ([1, 4] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut148_23 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(1, 1, 1, 0), (0, 1, 1, -1), (0, 0, 1, 0), (1, 0, 1, 0), (0, 0, 1, 0)] j) q) {2, 3} = HL Γ [(1, 0, 0, 0), (0, 0, 1, 0)] := by
    rw [show ({2, 3} : Finset (Fin 5)) = ([2, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut148_012 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(1, 1, 1, 0), (0, 1, 1, -1), (0, 0, 1, 0), (1, 0, 1, 0), (0, 0, 1, 0)] j) q) {0, 1, 2} = HL Γ [(1, 0, 0, 1), (0, 1, 0, -1), (0, 0, 1, 0)] := by
    rw [show ({0, 1, 2} : Finset (Fin 5)) = ([0, 1, 2] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut148_013 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(1, 1, 1, 0), (0, 1, 1, -1), (0, 0, 1, 0), (1, 0, 1, 0), (0, 0, 1, 0)] j) q) {0, 1, 3} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 1, 3} : Finset (Fin 5)) = ([0, 1, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut148_014 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(1, 1, 1, 0), (0, 1, 1, -1), (0, 0, 1, 0), (1, 0, 1, 0), (0, 0, 1, 0)] j) q) {0, 1, 4} = HL Γ [(1, 0, 0, 1), (0, 1, 0, -1), (0, 0, 1, 0)] := by
    rw [show ({0, 1, 4} : Finset (Fin 5)) = ([0, 1, 4] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut148_023 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(1, 1, 1, 0), (0, 1, 1, -1), (0, 0, 1, 0), (1, 0, 1, 0), (0, 0, 1, 0)] j) q) {0, 2, 3} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0)] := by
    rw [show ({0, 2, 3} : Finset (Fin 5)) = ([0, 2, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut148_row : 0 ≤ (-4) * HL Γ [(0, 0, 1, 0)] + (-6) * HL Γ [(0, 1, 1, -1)] + (-9) * HL Γ [(1, 1, 1, 0)] + (10) * HL Γ [(0, 1, 0, -1), (0, 0, 1, 0)] + (-3) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0)] + (3) * HL Γ [(1, 0, 0, 0), (0, 0, 1, 0)] + (10) * HL Γ [(1, 1, 0, 0), (0, 0, 1, 0)] + (3) * HL Γ [(1, 0, 1, 0), (0, 1, 0, 0)] + (-3) * HL Γ [(1, 0, 1, 0), (0, 1, 1, -1)] + (15) * HL Γ [(1, 0, 0, 1), (0, 1, 1, -1)] + (-16) * HL Γ [(1, 0, 0, 1), (0, 1, 0, -1), (0, 0, 1, 0)] := by
    norm_num at cut148
    linarith only [cut148, cut148_0, cut148_1, cut148_2, cut148_4, cut148_01, cut148_02, cut148_03, cut148_04, cut148_12, cut148_13, cut148_14, cut148_23, cut148_012, cut148_013, cut148_014, cut148_023]
  exact cut148_row

private theorem two_copy_row_cut149 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    0 ≤ (-4) * HL Γ [(0, 1, 0, 0)] + (-3) * HL Γ [(0, 1, 1, 0)] + (-9) * HL Γ [(0, 1, 1, 1)] + (-3) * HL Γ [(1, -1, -1, 0)] + (3) * HL Γ [(0, 1, 0, 0), (0, 0, 0, 1)] + (9) * HL Γ [(0, 1, 1, 0), (0, 0, 0, 1)] + (-15) * HL Γ [(0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] + (6) * HL Γ [(0, 1, 0, 0), (0, 0, 1, 0)] + (3) * HL Γ [(0, 1, 0, 1), (0, 0, 1, 0)] + (10) * HL Γ [(0, 1, 0, 0), (0, 0, 1, 1)] + (4) * HL Γ [(1, 0, -1, 0), (0, 1, 0, 0)] + (6) * HL Γ [(1, 0, 0, 1), (0, 1, 1, 1)] + (-7) * HL Γ [(1, 0, 0, 1), (0, 1, 0, 0), (0, 0, 1, 1)] := by
  -- Matúš instance k = 3, [abcd], (a,b,c,d,z) = (0, 1, 0, 0), (0, 1, 1, 1), (0, 1, 1, 0), (0, 1, 0, 1), (1, -1, -1, 0)
  have cut149 := matus_ineq (G := G) 3 false (Γ ×ˢ Γ) (pw Γ) (pw_nonneg Γ) (pw_sum hΓ)
    (fun j q => form (![(0, 1, 0, 0), (0, 1, 1, 1), (0, 1, 1, 0), (0, 1, 0, 1), (1, -1, -1, 0)] j) q)
  simp only [matusL, Bool.false_eq_true, ↓reduceIte] at cut149
  have cut149_0 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 1, 0, 0), (0, 1, 1, 1), (0, 1, 1, 0), (0, 1, 0, 1), (1, -1, -1, 0)] j) q) {0} = HL Γ [(0, 1, 0, 0)] := by
    rw [show ({0} : Finset (Fin 5)) = ([0] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact rfl
  have cut149_1 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 1, 0, 0), (0, 1, 1, 1), (0, 1, 1, 0), (0, 1, 0, 1), (1, -1, -1, 0)] j) q) {1} = HL Γ [(0, 1, 1, 1)] := by
    rw [show ({1} : Finset (Fin 5)) = ([1] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact rfl
  have cut149_2 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 1, 0, 0), (0, 1, 1, 1), (0, 1, 1, 0), (0, 1, 0, 1), (1, -1, -1, 0)] j) q) {2} = HL Γ [(0, 1, 1, 0)] := by
    rw [show ({2} : Finset (Fin 5)) = ([2] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact rfl
  have cut149_4 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 1, 0, 0), (0, 1, 1, 1), (0, 1, 1, 0), (0, 1, 0, 1), (1, -1, -1, 0)] j) q) {4} = HL Γ [(1, -1, -1, 0)] := by
    rw [show ({4} : Finset (Fin 5)) = ([4] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact rfl
  have cut149_01 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 1, 0, 0), (0, 1, 1, 1), (0, 1, 1, 0), (0, 1, 0, 1), (1, -1, -1, 0)] j) q) {0, 1} = HL Γ [(0, 1, 0, 0), (0, 0, 1, 1)] := by
    rw [show ({0, 1} : Finset (Fin 5)) = ([0, 1] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut149_02 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 1, 0, 0), (0, 1, 1, 1), (0, 1, 1, 0), (0, 1, 0, 1), (1, -1, -1, 0)] j) q) {0, 2} = HL Γ [(0, 1, 0, 0), (0, 0, 1, 0)] := by
    rw [show ({0, 2} : Finset (Fin 5)) = ([0, 2] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut149_03 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 1, 0, 0), (0, 1, 1, 1), (0, 1, 1, 0), (0, 1, 0, 1), (1, -1, -1, 0)] j) q) {0, 3} = HL Γ [(0, 1, 0, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 3} : Finset (Fin 5)) = ([0, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut149_04 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 1, 0, 0), (0, 1, 1, 1), (0, 1, 1, 0), (0, 1, 0, 1), (1, -1, -1, 0)] j) q) {0, 4} = HL Γ [(1, 0, -1, 0), (0, 1, 0, 0)] := by
    rw [show ({0, 4} : Finset (Fin 5)) = ([0, 4] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut149_12 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 1, 0, 0), (0, 1, 1, 1), (0, 1, 1, 0), (0, 1, 0, 1), (1, -1, -1, 0)] j) q) {1, 2} = HL Γ [(0, 1, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({1, 2} : Finset (Fin 5)) = ([1, 2] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut149_13 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 1, 0, 0), (0, 1, 1, 1), (0, 1, 1, 0), (0, 1, 0, 1), (1, -1, -1, 0)] j) q) {1, 3} = HL Γ [(0, 1, 0, 1), (0, 0, 1, 0)] := by
    rw [show ({1, 3} : Finset (Fin 5)) = ([1, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut149_14 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 1, 0, 0), (0, 1, 1, 1), (0, 1, 1, 0), (0, 1, 0, 1), (1, -1, -1, 0)] j) q) {1, 4} = HL Γ [(1, 0, 0, 1), (0, 1, 1, 1)] := by
    rw [show ({1, 4} : Finset (Fin 5)) = ([1, 4] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut149_23 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 1, 0, 0), (0, 1, 1, 1), (0, 1, 1, 0), (0, 1, 0, 1), (1, -1, -1, 0)] j) q) {2, 3} = HL Γ [(0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({2, 3} : Finset (Fin 5)) = ([2, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut149_012 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 1, 0, 0), (0, 1, 1, 1), (0, 1, 1, 0), (0, 1, 0, 1), (1, -1, -1, 0)] j) q) {0, 1, 2} = HL Γ [(0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 1, 2} : Finset (Fin 5)) = ([0, 1, 2] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut149_013 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 1, 0, 0), (0, 1, 1, 1), (0, 1, 1, 0), (0, 1, 0, 1), (1, -1, -1, 0)] j) q) {0, 1, 3} = HL Γ [(0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 1, 3} : Finset (Fin 5)) = ([0, 1, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut149_014 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 1, 0, 0), (0, 1, 1, 1), (0, 1, 1, 0), (0, 1, 0, 1), (1, -1, -1, 0)] j) q) {0, 1, 4} = HL Γ [(1, 0, 0, 1), (0, 1, 0, 0), (0, 0, 1, 1)] := by
    rw [show ({0, 1, 4} : Finset (Fin 5)) = ([0, 1, 4] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut149_023 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 1, 0, 0), (0, 1, 1, 1), (0, 1, 1, 0), (0, 1, 0, 1), (1, -1, -1, 0)] j) q) {0, 2, 3} = HL Γ [(0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 2, 3} : Finset (Fin 5)) = ([0, 2, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut149_row : 0 ≤ (-4) * HL Γ [(0, 1, 0, 0)] + (-3) * HL Γ [(0, 1, 1, 0)] + (-9) * HL Γ [(0, 1, 1, 1)] + (-3) * HL Γ [(1, -1, -1, 0)] + (3) * HL Γ [(0, 1, 0, 0), (0, 0, 0, 1)] + (9) * HL Γ [(0, 1, 1, 0), (0, 0, 0, 1)] + (-15) * HL Γ [(0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] + (6) * HL Γ [(0, 1, 0, 0), (0, 0, 1, 0)] + (3) * HL Γ [(0, 1, 0, 1), (0, 0, 1, 0)] + (10) * HL Γ [(0, 1, 0, 0), (0, 0, 1, 1)] + (4) * HL Γ [(1, 0, -1, 0), (0, 1, 0, 0)] + (6) * HL Γ [(1, 0, 0, 1), (0, 1, 1, 1)] + (-7) * HL Γ [(1, 0, 0, 1), (0, 1, 0, 0), (0, 0, 1, 1)] := by
    norm_num at cut149
    linarith only [cut149, cut149_0, cut149_1, cut149_2, cut149_4, cut149_01, cut149_02, cut149_03, cut149_04, cut149_12, cut149_13, cut149_14, cut149_23, cut149_012, cut149_013, cut149_014, cut149_023]
  exact cut149_row

private theorem two_copy_row_cut150 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    0 ≤ (-4) * HL Γ [(0, 0, 0, 1)] + (-6) * HL Γ [(1, 0, -1, 1)] + (-9) * HL Γ [(1, 1, 0, 1)] + (3) * HL Γ [(0, 1, 0, 0), (0, 0, 0, 1)] + (-3) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 1)] + (10) * HL Γ [(1, 0, -1, 0), (0, 0, 0, 1)] + (10) * HL Γ [(1, 1, 0, 0), (0, 0, 0, 1)] + (-3) * HL Γ [(1, 0, -1, 1), (0, 1, 0, 1)] + (3) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 1)] + (15) * HL Γ [(1, 0, -1, 1), (0, 1, 1, 0)] + (-16) * HL Γ [(1, 0, -1, 0), (0, 1, 1, 0), (0, 0, 0, 1)] := by
  -- Matúš instance k = 3, [abcd], (a,b,c,d,z) = (0, 0, 0, 1), (1, 1, 0, 1), (1, 0, -1, 1), (0, 1, 0, 1), (1, 0, -1, 1)
  have cut150 := matus_ineq (G := G) 3 false (Γ ×ˢ Γ) (pw Γ) (pw_nonneg Γ) (pw_sum hΓ)
    (fun j q => form (![(0, 0, 0, 1), (1, 1, 0, 1), (1, 0, -1, 1), (0, 1, 0, 1), (1, 0, -1, 1)] j) q)
  simp only [matusL, Bool.false_eq_true, ↓reduceIte] at cut150
  have cut150_0 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 0, 0, 1), (1, 1, 0, 1), (1, 0, -1, 1), (0, 1, 0, 1), (1, 0, -1, 1)] j) q) {0} = HL Γ [(0, 0, 0, 1)] := by
    rw [show ({0} : Finset (Fin 5)) = ([0] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact rfl
  have cut150_1 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 0, 0, 1), (1, 1, 0, 1), (1, 0, -1, 1), (0, 1, 0, 1), (1, 0, -1, 1)] j) q) {1} = HL Γ [(1, 1, 0, 1)] := by
    rw [show ({1} : Finset (Fin 5)) = ([1] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact rfl
  have cut150_2 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 0, 0, 1), (1, 1, 0, 1), (1, 0, -1, 1), (0, 1, 0, 1), (1, 0, -1, 1)] j) q) {2} = HL Γ [(1, 0, -1, 1)] := by
    rw [show ({2} : Finset (Fin 5)) = ([2] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact rfl
  have cut150_4 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 0, 0, 1), (1, 1, 0, 1), (1, 0, -1, 1), (0, 1, 0, 1), (1, 0, -1, 1)] j) q) {4} = HL Γ [(1, 0, -1, 1)] := by
    rw [show ({4} : Finset (Fin 5)) = ([4] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact rfl
  have cut150_01 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 0, 0, 1), (1, 1, 0, 1), (1, 0, -1, 1), (0, 1, 0, 1), (1, 0, -1, 1)] j) q) {0, 1} = HL Γ [(1, 1, 0, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 1} : Finset (Fin 5)) = ([0, 1] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut150_02 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 0, 0, 1), (1, 1, 0, 1), (1, 0, -1, 1), (0, 1, 0, 1), (1, 0, -1, 1)] j) q) {0, 2} = HL Γ [(1, 0, -1, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 2} : Finset (Fin 5)) = ([0, 2] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut150_03 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 0, 0, 1), (1, 1, 0, 1), (1, 0, -1, 1), (0, 1, 0, 1), (1, 0, -1, 1)] j) q) {0, 3} = HL Γ [(0, 1, 0, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 3} : Finset (Fin 5)) = ([0, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut150_04 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 0, 0, 1), (1, 1, 0, 1), (1, 0, -1, 1), (0, 1, 0, 1), (1, 0, -1, 1)] j) q) {0, 4} = HL Γ [(1, 0, -1, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 4} : Finset (Fin 5)) = ([0, 4] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut150_12 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 0, 0, 1), (1, 1, 0, 1), (1, 0, -1, 1), (0, 1, 0, 1), (1, 0, -1, 1)] j) q) {1, 2} = HL Γ [(1, 0, -1, 1), (0, 1, 1, 0)] := by
    rw [show ({1, 2} : Finset (Fin 5)) = ([1, 2] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut150_13 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 0, 0, 1), (1, 1, 0, 1), (1, 0, -1, 1), (0, 1, 0, 1), (1, 0, -1, 1)] j) q) {1, 3} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 1)] := by
    rw [show ({1, 3} : Finset (Fin 5)) = ([1, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut150_14 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 0, 0, 1), (1, 1, 0, 1), (1, 0, -1, 1), (0, 1, 0, 1), (1, 0, -1, 1)] j) q) {1, 4} = HL Γ [(1, 0, -1, 1), (0, 1, 1, 0)] := by
    rw [show ({1, 4} : Finset (Fin 5)) = ([1, 4] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut150_23 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 0, 0, 1), (1, 1, 0, 1), (1, 0, -1, 1), (0, 1, 0, 1), (1, 0, -1, 1)] j) q) {2, 3} = HL Γ [(1, 0, -1, 1), (0, 1, 0, 1)] := by
    rw [show ({2, 3} : Finset (Fin 5)) = ([2, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact rfl
  have cut150_012 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 0, 0, 1), (1, 1, 0, 1), (1, 0, -1, 1), (0, 1, 0, 1), (1, 0, -1, 1)] j) q) {0, 1, 2} = HL Γ [(1, 0, -1, 0), (0, 1, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 1, 2} : Finset (Fin 5)) = ([0, 1, 2] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut150_013 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 0, 0, 1), (1, 1, 0, 1), (1, 0, -1, 1), (0, 1, 0, 1), (1, 0, -1, 1)] j) q) {0, 1, 3} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 1, 3} : Finset (Fin 5)) = ([0, 1, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut150_014 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 0, 0, 1), (1, 1, 0, 1), (1, 0, -1, 1), (0, 1, 0, 1), (1, 0, -1, 1)] j) q) {0, 1, 4} = HL Γ [(1, 0, -1, 0), (0, 1, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 1, 4} : Finset (Fin 5)) = ([0, 1, 4] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut150_023 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 0, 0, 1), (1, 1, 0, 1), (1, 0, -1, 1), (0, 1, 0, 1), (1, 0, -1, 1)] j) q) {0, 2, 3} = HL Γ [(1, 0, -1, 0), (0, 1, 0, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 2, 3} : Finset (Fin 5)) = ([0, 2, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    exact HL_eq_norm hinj (by decide)
  have cut150_row : 0 ≤ (-4) * HL Γ [(0, 0, 0, 1)] + (-6) * HL Γ [(1, 0, -1, 1)] + (-9) * HL Γ [(1, 1, 0, 1)] + (3) * HL Γ [(0, 1, 0, 0), (0, 0, 0, 1)] + (-3) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 1)] + (10) * HL Γ [(1, 0, -1, 0), (0, 0, 0, 1)] + (10) * HL Γ [(1, 1, 0, 0), (0, 0, 0, 1)] + (-3) * HL Γ [(1, 0, -1, 1), (0, 1, 0, 1)] + (3) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 1)] + (15) * HL Γ [(1, 0, -1, 1), (0, 1, 1, 0)] + (-16) * HL Γ [(1, 0, -1, 0), (0, 1, 1, 0), (0, 0, 0, 1)] := by
    norm_num at cut150
    linarith only [cut150, cut150_0, cut150_1, cut150_2, cut150_4, cut150_01, cut150_02, cut150_03, cut150_04, cut150_12, cut150_13, cut150_14, cut150_23, cut150_012, cut150_013, cut150_014, cut150_023]
  exact cut150_row

private theorem two_copy_row_cut151 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    0 ≤ (-6) * HL Γ [(1, -1, 0, 1)] + (-4) * HL Γ [(1, 0, 0, 0)] + (-3) * HL Γ [(1, 0, 1, 1)] + (-12) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] + (3) * HL Γ [(1, 0, 0, 0), (0, 0, 1, 0)] + (6) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 1)] + (4) * HL Γ [(1, 0, 0, 0), (0, 0, 1, 1)] + (10) * HL Γ [(1, 0, 0, 0), (0, 1, 0, -1)] + (-6) * HL Γ [(1, 0, 1, 1), (0, 1, 0, 0)] + (-3) * HL Γ [(1, 0, 1, 0), (0, 1, 1, -1)] + (6) * HL Γ [(1, 0, 1, 1), (0, 1, 1, 0)] + (3) * HL Γ [(1, 0, 1, 0), (0, 1, 0, 0), (0, 0, 0, 1)] + (9) * HL Γ [(1, 0, 0, 1), (0, 1, 0, 0), (0, 0, 1, 0)] + (-7) * HL Γ [(1, 0, 0, 0), (0, 1, 0, -1), (0, 0, 1, 1)] := by
  -- Matúš instance on joint variables, k = 3, [acbd], (a,b,c,d,z) = [(1, 0, 0, 0)] ; [(1, -1, 0, 1)] ; [(1, 0, 1, 1), (0, 1, 0, 0)] ; [(1, 0, 1, 0)] ; [(1, 0, 1, 1)]
  have cut151 := matus_ineq (G := G × G) 3 true (Γ ×ˢ Γ) (pw Γ) (pw_nonneg Γ) (pw_sum hΓ)
    (fun j q => (form (![(1, 0, 0, 0), (1, -1, 0, 1), (1, 0, 1, 1), (1, 0, 1, 0), (1, 0, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)] j) q))
  simp only [matusL, ↓reduceIte] at cut151
  have cut151_0 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 0), (1, -1, 0, 1), (1, 0, 1, 1), (1, 0, 1, 0), (1, 0, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)] j) q)) {0} = HL Γ [(1, 0, 0, 0)] := by
    rw [show ({0} : Finset (Fin 5)) = ([0] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 0), (0, 0, 0, 0)] = HL Γ [(1, 0, 0, 0)]
    exact HL_eq_norm hinj (by decide)
  have cut151_1 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 0), (1, -1, 0, 1), (1, 0, 1, 1), (1, 0, 1, 0), (1, 0, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)] j) q)) {1} = HL Γ [(1, -1, 0, 1)] := by
    rw [show ({1} : Finset (Fin 5)) = ([1] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, -1, 0, 1), (0, 0, 0, 0)] = HL Γ [(1, -1, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut151_2 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 0), (1, -1, 0, 1), (1, 0, 1, 1), (1, 0, 1, 0), (1, 0, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)] j) q)) {2} = HL Γ [(1, 0, 1, 1), (0, 1, 0, 0)] := by
    rw [show ({2} : Finset (Fin 5)) = ([2] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 1, 1), (0, 1, 0, 0)] = HL Γ [(1, 0, 1, 1), (0, 1, 0, 0)]
    exact rfl
  have cut151_4 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 0), (1, -1, 0, 1), (1, 0, 1, 1), (1, 0, 1, 0), (1, 0, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)] j) q)) {4} = HL Γ [(1, 0, 1, 1)] := by
    rw [show ({4} : Finset (Fin 5)) = ([4] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 1, 1), (0, 0, 0, 0)] = HL Γ [(1, 0, 1, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut151_01 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 0), (1, -1, 0, 1), (1, 0, 1, 1), (1, 0, 1, 0), (1, 0, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)] j) q)) {0, 1} = HL Γ [(1, 0, 0, 0), (0, 1, 0, -1)] := by
    rw [show ({0, 1} : Finset (Fin 5)) = ([0, 1] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 0), (1, -1, 0, 1), (0, 0, 0, 0), (0, 0, 0, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, -1)]
    exact HL_eq_norm hinj (by decide)
  have cut151_02 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 0), (1, -1, 0, 1), (1, 0, 1, 1), (1, 0, 1, 0), (1, 0, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)] j) q)) {0, 2} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 1)] := by
    rw [show ({0, 2} : Finset (Fin 5)) = ([0, 2] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 0), (1, 0, 1, 1), (0, 0, 0, 0), (0, 1, 0, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut151_03 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 0), (1, -1, 0, 1), (1, 0, 1, 1), (1, 0, 1, 0), (1, 0, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)] j) q)) {0, 3} = HL Γ [(1, 0, 0, 0), (0, 0, 1, 0)] := by
    rw [show ({0, 3} : Finset (Fin 5)) = ([0, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 0), (1, 0, 1, 0), (0, 0, 0, 0), (0, 0, 0, 0)] = HL Γ [(1, 0, 0, 0), (0, 0, 1, 0)]
    exact HL_eq_norm hinj (by decide)
  have cut151_04 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 0), (1, -1, 0, 1), (1, 0, 1, 1), (1, 0, 1, 0), (1, 0, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)] j) q)) {0, 4} = HL Γ [(1, 0, 0, 0), (0, 0, 1, 1)] := by
    rw [show ({0, 4} : Finset (Fin 5)) = ([0, 4] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 0), (1, 0, 1, 1), (0, 0, 0, 0), (0, 0, 0, 0)] = HL Γ [(1, 0, 0, 0), (0, 0, 1, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut151_12 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 0), (1, -1, 0, 1), (1, 0, 1, 1), (1, 0, 1, 0), (1, 0, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)] j) q)) {1, 2} = HL Γ [(1, 0, 0, 1), (0, 1, 0, 0), (0, 0, 1, 0)] := by
    rw [show ({1, 2} : Finset (Fin 5)) = ([1, 2] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, -1, 0, 1), (1, 0, 1, 1), (0, 0, 0, 0), (0, 1, 0, 0)] = HL Γ [(1, 0, 0, 1), (0, 1, 0, 0), (0, 0, 1, 0)]
    exact HL_eq_norm hinj (by decide)
  have cut151_13 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 0), (1, -1, 0, 1), (1, 0, 1, 1), (1, 0, 1, 0), (1, 0, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)] j) q)) {1, 3} = HL Γ [(1, 0, 1, 0), (0, 1, 1, -1)] := by
    rw [show ({1, 3} : Finset (Fin 5)) = ([1, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, -1, 0, 1), (1, 0, 1, 0), (0, 0, 0, 0), (0, 0, 0, 0)] = HL Γ [(1, 0, 1, 0), (0, 1, 1, -1)]
    exact HL_eq_norm hinj (by decide)
  have cut151_14 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 0), (1, -1, 0, 1), (1, 0, 1, 1), (1, 0, 1, 0), (1, 0, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)] j) q)) {1, 4} = HL Γ [(1, 0, 1, 1), (0, 1, 1, 0)] := by
    rw [show ({1, 4} : Finset (Fin 5)) = ([1, 4] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, -1, 0, 1), (1, 0, 1, 1), (0, 0, 0, 0), (0, 0, 0, 0)] = HL Γ [(1, 0, 1, 1), (0, 1, 1, 0)]
    exact HL_eq_norm hinj (by decide)
  have cut151_23 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 0), (1, -1, 0, 1), (1, 0, 1, 1), (1, 0, 1, 0), (1, 0, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)] j) q)) {2, 3} = HL Γ [(1, 0, 1, 0), (0, 1, 0, 0), (0, 0, 0, 1)] := by
    rw [show ({2, 3} : Finset (Fin 5)) = ([2, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 1, 1), (1, 0, 1, 0), (0, 1, 0, 0), (0, 0, 0, 0)] = HL Γ [(1, 0, 1, 0), (0, 1, 0, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut151_012 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 0), (1, -1, 0, 1), (1, 0, 1, 1), (1, 0, 1, 0), (1, 0, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)] j) q)) {0, 1, 2} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 1, 2} : Finset (Fin 5)) = ([0, 1, 2] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 0), (1, -1, 0, 1), (1, 0, 1, 1), (0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 0, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut151_013 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 0), (1, -1, 0, 1), (1, 0, 1, 1), (1, 0, 1, 0), (1, 0, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)] j) q)) {0, 1, 3} = HL Γ [(1, 0, 0, 0), (0, 1, 0, -1), (0, 0, 1, 0)] := by
    rw [show ({0, 1, 3} : Finset (Fin 5)) = ([0, 1, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 0), (1, -1, 0, 1), (1, 0, 1, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, -1), (0, 0, 1, 0)]
    exact HL_eq_norm hinj (by decide)
  have cut151_014 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 0), (1, -1, 0, 1), (1, 0, 1, 1), (1, 0, 1, 0), (1, 0, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)] j) q)) {0, 1, 4} = HL Γ [(1, 0, 0, 0), (0, 1, 0, -1), (0, 0, 1, 1)] := by
    rw [show ({0, 1, 4} : Finset (Fin 5)) = ([0, 1, 4] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 0), (1, -1, 0, 1), (1, 0, 1, 1), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, -1), (0, 0, 1, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut151_023 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(1, 0, 0, 0), (1, -1, 0, 1), (1, 0, 1, 1), (1, 0, 1, 0), (1, 0, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)] j) q)) {0, 2, 3} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 2, 3} : Finset (Fin 5)) = ([0, 2, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 0), (1, 0, 1, 1), (1, 0, 1, 0), (0, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut151_row : 0 ≤ (-6) * HL Γ [(1, -1, 0, 1)] + (-4) * HL Γ [(1, 0, 0, 0)] + (-3) * HL Γ [(1, 0, 1, 1)] + (-12) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] + (3) * HL Γ [(1, 0, 0, 0), (0, 0, 1, 0)] + (6) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 1)] + (4) * HL Γ [(1, 0, 0, 0), (0, 0, 1, 1)] + (10) * HL Γ [(1, 0, 0, 0), (0, 1, 0, -1)] + (-6) * HL Γ [(1, 0, 1, 1), (0, 1, 0, 0)] + (-3) * HL Γ [(1, 0, 1, 0), (0, 1, 1, -1)] + (6) * HL Γ [(1, 0, 1, 1), (0, 1, 1, 0)] + (3) * HL Γ [(1, 0, 1, 0), (0, 1, 0, 0), (0, 0, 0, 1)] + (9) * HL Γ [(1, 0, 0, 1), (0, 1, 0, 0), (0, 0, 1, 0)] + (-7) * HL Γ [(1, 0, 0, 0), (0, 1, 0, -1), (0, 0, 1, 1)] := by
    norm_num at cut151
    linarith only [cut151, cut151_0, cut151_1, cut151_2, cut151_4, cut151_01, cut151_02, cut151_03, cut151_04, cut151_12, cut151_13, cut151_14, cut151_23, cut151_012, cut151_013, cut151_014, cut151_023]
  exact cut151_row

private theorem two_copy_row_cut152 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    0 ≤ (-4) * HL Γ [(0, 1, 0, 0)] + (-3) * HL Γ [(0, 1, 1, 1)] + (-6) * HL Γ [(1, -1, -1, 0)] + (3) * HL Γ [(0, 1, 0, 0), (0, 0, 0, 1)] + (-12) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] + (4) * HL Γ [(0, 1, 0, 0), (0, 0, 1, 1)] + (6) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 1)] + (10) * HL Γ [(1, 0, -1, 0), (0, 1, 0, 0)] + (-3) * HL Γ [(1, 0, -1, 1), (0, 1, 0, 1)] + (-6) * HL Γ [(1, 0, 0, 0), (0, 1, 1, 1)] + (6) * HL Γ [(1, 0, 0, 1), (0, 1, 1, 1)] + (9) * HL Γ [(1, 0, 0, 0), (0, 1, 1, 0), (0, 0, 0, 1)] + (3) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 1), (0, 0, 1, 0)] + (-7) * HL Γ [(1, 0, 0, 1), (0, 1, 0, 0), (0, 0, 1, 1)] := by
  -- Matúš instance on joint variables, k = 3, [acbd], (a,b,c,d,z) = [(0, 1, 0, 0)] ; [(1, -1, -1, 0)] ; [(1, 0, 0, 0), (0, 1, 1, 1)] ; [(0, 1, 0, 1)] ; [(0, 1, 1, 1)]
  have cut152 := matus_ineq (G := G × G) 3 true (Γ ×ˢ Γ) (pw Γ) (pw_nonneg Γ) (pw_sum hΓ)
    (fun j q => (form (![(0, 1, 0, 0), (1, -1, -1, 0), (1, 0, 0, 0), (0, 1, 0, 1), (0, 1, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 0, 0, 0)] j) q))
  simp only [matusL, ↓reduceIte] at cut152
  have cut152_0 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(0, 1, 0, 0), (1, -1, -1, 0), (1, 0, 0, 0), (0, 1, 0, 1), (0, 1, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 0, 0, 0)] j) q)) {0} = HL Γ [(0, 1, 0, 0)] := by
    rw [show ({0} : Finset (Fin 5)) = ([0] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(0, 1, 0, 0), (0, 0, 0, 0)] = HL Γ [(0, 1, 0, 0)]
    exact HL_eq_norm hinj (by decide)
  have cut152_1 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(0, 1, 0, 0), (1, -1, -1, 0), (1, 0, 0, 0), (0, 1, 0, 1), (0, 1, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 0, 0, 0)] j) q)) {1} = HL Γ [(1, -1, -1, 0)] := by
    rw [show ({1} : Finset (Fin 5)) = ([1] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, -1, -1, 0), (0, 0, 0, 0)] = HL Γ [(1, -1, -1, 0)]
    exact HL_eq_norm hinj (by decide)
  have cut152_2 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(0, 1, 0, 0), (1, -1, -1, 0), (1, 0, 0, 0), (0, 1, 0, 1), (0, 1, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 0, 0, 0)] j) q)) {2} = HL Γ [(1, 0, 0, 0), (0, 1, 1, 1)] := by
    rw [show ({2} : Finset (Fin 5)) = ([2] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 0), (0, 1, 1, 1)] = HL Γ [(1, 0, 0, 0), (0, 1, 1, 1)]
    exact rfl
  have cut152_4 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(0, 1, 0, 0), (1, -1, -1, 0), (1, 0, 0, 0), (0, 1, 0, 1), (0, 1, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 0, 0, 0)] j) q)) {4} = HL Γ [(0, 1, 1, 1)] := by
    rw [show ({4} : Finset (Fin 5)) = ([4] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(0, 1, 1, 1), (0, 0, 0, 0)] = HL Γ [(0, 1, 1, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut152_01 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(0, 1, 0, 0), (1, -1, -1, 0), (1, 0, 0, 0), (0, 1, 0, 1), (0, 1, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 0, 0, 0)] j) q)) {0, 1} = HL Γ [(1, 0, -1, 0), (0, 1, 0, 0)] := by
    rw [show ({0, 1} : Finset (Fin 5)) = ([0, 1] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(0, 1, 0, 0), (1, -1, -1, 0), (0, 0, 0, 0), (0, 0, 0, 0)] = HL Γ [(1, 0, -1, 0), (0, 1, 0, 0)]
    exact HL_eq_norm hinj (by decide)
  have cut152_02 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(0, 1, 0, 0), (1, -1, -1, 0), (1, 0, 0, 0), (0, 1, 0, 1), (0, 1, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 0, 0, 0)] j) q)) {0, 2} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 1)] := by
    rw [show ({0, 2} : Finset (Fin 5)) = ([0, 2] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(0, 1, 0, 0), (1, 0, 0, 0), (0, 0, 0, 0), (0, 1, 1, 1)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut152_03 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(0, 1, 0, 0), (1, -1, -1, 0), (1, 0, 0, 0), (0, 1, 0, 1), (0, 1, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 0, 0, 0)] j) q)) {0, 3} = HL Γ [(0, 1, 0, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 3} : Finset (Fin 5)) = ([0, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(0, 1, 0, 0), (0, 1, 0, 1), (0, 0, 0, 0), (0, 0, 0, 0)] = HL Γ [(0, 1, 0, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut152_04 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(0, 1, 0, 0), (1, -1, -1, 0), (1, 0, 0, 0), (0, 1, 0, 1), (0, 1, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 0, 0, 0)] j) q)) {0, 4} = HL Γ [(0, 1, 0, 0), (0, 0, 1, 1)] := by
    rw [show ({0, 4} : Finset (Fin 5)) = ([0, 4] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(0, 1, 0, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 0, 0, 0)] = HL Γ [(0, 1, 0, 0), (0, 0, 1, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut152_12 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(0, 1, 0, 0), (1, -1, -1, 0), (1, 0, 0, 0), (0, 1, 0, 1), (0, 1, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 0, 0, 0)] j) q)) {1, 2} = HL Γ [(1, 0, 0, 0), (0, 1, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({1, 2} : Finset (Fin 5)) = ([1, 2] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, -1, -1, 0), (1, 0, 0, 0), (0, 0, 0, 0), (0, 1, 1, 1)] = HL Γ [(1, 0, 0, 0), (0, 1, 1, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut152_13 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(0, 1, 0, 0), (1, -1, -1, 0), (1, 0, 0, 0), (0, 1, 0, 1), (0, 1, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 0, 0, 0)] j) q)) {1, 3} = HL Γ [(1, 0, -1, 1), (0, 1, 0, 1)] := by
    rw [show ({1, 3} : Finset (Fin 5)) = ([1, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, -1, -1, 0), (0, 1, 0, 1), (0, 0, 0, 0), (0, 0, 0, 0)] = HL Γ [(1, 0, -1, 1), (0, 1, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut152_14 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(0, 1, 0, 0), (1, -1, -1, 0), (1, 0, 0, 0), (0, 1, 0, 1), (0, 1, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 0, 0, 0)] j) q)) {1, 4} = HL Γ [(1, 0, 0, 1), (0, 1, 1, 1)] := by
    rw [show ({1, 4} : Finset (Fin 5)) = ([1, 4] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, -1, -1, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 0, 0, 0)] = HL Γ [(1, 0, 0, 1), (0, 1, 1, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut152_23 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(0, 1, 0, 0), (1, -1, -1, 0), (1, 0, 0, 0), (0, 1, 0, 1), (0, 1, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 0, 0, 0)] j) q)) {2, 3} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 1), (0, 0, 1, 0)] := by
    rw [show ({2, 3} : Finset (Fin 5)) = ([2, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(1, 0, 0, 0), (0, 1, 0, 1), (0, 1, 1, 1), (0, 0, 0, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 1), (0, 0, 1, 0)]
    exact HL_eq_norm hinj (by decide)
  have cut152_012 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(0, 1, 0, 0), (1, -1, -1, 0), (1, 0, 0, 0), (0, 1, 0, 1), (0, 1, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 0, 0, 0)] j) q)) {0, 1, 2} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 1, 2} : Finset (Fin 5)) = ([0, 1, 2] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(0, 1, 0, 0), (1, -1, -1, 0), (1, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 1, 1)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut152_013 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(0, 1, 0, 0), (1, -1, -1, 0), (1, 0, 0, 0), (0, 1, 0, 1), (0, 1, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 0, 0, 0)] j) q)) {0, 1, 3} = HL Γ [(1, 0, -1, 0), (0, 1, 0, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 1, 3} : Finset (Fin 5)) = ([0, 1, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(0, 1, 0, 0), (1, -1, -1, 0), (0, 1, 0, 1), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)] = HL Γ [(1, 0, -1, 0), (0, 1, 0, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut152_014 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(0, 1, 0, 0), (1, -1, -1, 0), (1, 0, 0, 0), (0, 1, 0, 1), (0, 1, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 0, 0, 0)] j) q)) {0, 1, 4} = HL Γ [(1, 0, 0, 1), (0, 1, 0, 0), (0, 0, 1, 1)] := by
    rw [show ({0, 1, 4} : Finset (Fin 5)) = ([0, 1, 4] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(0, 1, 0, 0), (1, -1, -1, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)] = HL Γ [(1, 0, 0, 1), (0, 1, 0, 0), (0, 0, 1, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut152_023 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (![(0, 1, 0, 0), (1, -1, -1, 0), (1, 0, 0, 0), (0, 1, 0, 1), (0, 1, 1, 1)] j) q, form (![(0, 0, 0, 0), (0, 0, 0, 0), (0, 1, 1, 1), (0, 0, 0, 0), (0, 0, 0, 0)] j) q)) {0, 2, 3} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 2, 3} : Finset (Fin 5)) = ([0, 2, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL2]
    show HL Γ [(0, 1, 0, 0), (1, 0, 0, 0), (0, 1, 0, 1), (0, 0, 0, 0), (0, 1, 1, 1), (0, 0, 0, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut152_row : 0 ≤ (-4) * HL Γ [(0, 1, 0, 0)] + (-3) * HL Γ [(0, 1, 1, 1)] + (-6) * HL Γ [(1, -1, -1, 0)] + (3) * HL Γ [(0, 1, 0, 0), (0, 0, 0, 1)] + (-12) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] + (4) * HL Γ [(0, 1, 0, 0), (0, 0, 1, 1)] + (6) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 1)] + (10) * HL Γ [(1, 0, -1, 0), (0, 1, 0, 0)] + (-3) * HL Γ [(1, 0, -1, 1), (0, 1, 0, 1)] + (-6) * HL Γ [(1, 0, 0, 0), (0, 1, 1, 1)] + (6) * HL Γ [(1, 0, 0, 1), (0, 1, 1, 1)] + (9) * HL Γ [(1, 0, 0, 0), (0, 1, 1, 0), (0, 0, 0, 1)] + (3) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 1), (0, 0, 1, 0)] + (-7) * HL Γ [(1, 0, 0, 1), (0, 1, 0, 0), (0, 0, 1, 1)] := by
    norm_num at cut152
    linarith only [cut152, cut152_0, cut152_1, cut152_2, cut152_4, cut152_01, cut152_02, cut152_03, cut152_04, cut152_12, cut152_13, cut152_14, cut152_23, cut152_012, cut152_013, cut152_014, cut152_023]
  exact cut152_row

private theorem two_copy_row_cut153 (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    0 ≤ (-6) * HL Γ [(0, 1, 0, 0)] + (-4) * HL Γ [(0, 1, 1, 0)] + (-9) * HL Γ [(1, -1, 0, 1)] + (3) * HL Γ [(0, 1, 1, 0), (0, 0, 0, 1)] + (-3) * HL Γ [(0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] + (-3) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] + (10) * HL Γ [(0, 1, 0, 0), (0, 0, 1, 0)] + (15) * HL Γ [(1, 0, 0, 1), (0, 1, 0, 0)] + (3) * HL Γ [(1, 0, 1, 0), (0, 1, 1, -1)] + (10) * HL Γ [(1, 0, 1, 1), (0, 1, 1, 0)] + (-16) * HL Γ [(1, 0, 0, 1), (0, 1, 0, 0), (0, 0, 1, 0)] := by
  -- Matúš instance on joint variables, k = 3, [abcd], (a,b,c,d,z) = [(0, 1, 1, 0)] ; [(1, -1, 0, 1)] ; [(0, 1, 0, 0)] ; [(0, 1, 1, -1)] ; [(0, 1, 0, 0)]
  have cut153 := matus_ineq (G := G) 3 false (Γ ×ˢ Γ) (pw Γ) (pw_nonneg Γ) (pw_sum hΓ)
    (fun j q => form (![(0, 1, 1, 0), (1, -1, 0, 1), (0, 1, 0, 0), (0, 1, 1, -1), (0, 1, 0, 0)] j) q)
  simp only [matusL, Bool.false_eq_true, ↓reduceIte] at cut153
  have cut153_0 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 1, 1, 0), (1, -1, 0, 1), (0, 1, 0, 0), (0, 1, 1, -1), (0, 1, 0, 0)] j) q) {0} = HL Γ [(0, 1, 1, 0)] := by
    rw [show ({0} : Finset (Fin 5)) = ([0] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    show HL Γ [(0, 1, 1, 0)] = HL Γ [(0, 1, 1, 0)]
    exact rfl
  have cut153_1 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 1, 1, 0), (1, -1, 0, 1), (0, 1, 0, 0), (0, 1, 1, -1), (0, 1, 0, 0)] j) q) {1} = HL Γ [(1, -1, 0, 1)] := by
    rw [show ({1} : Finset (Fin 5)) = ([1] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    show HL Γ [(1, -1, 0, 1)] = HL Γ [(1, -1, 0, 1)]
    exact rfl
  have cut153_2 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 1, 1, 0), (1, -1, 0, 1), (0, 1, 0, 0), (0, 1, 1, -1), (0, 1, 0, 0)] j) q) {2} = HL Γ [(0, 1, 0, 0)] := by
    rw [show ({2} : Finset (Fin 5)) = ([2] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    show HL Γ [(0, 1, 0, 0)] = HL Γ [(0, 1, 0, 0)]
    exact rfl
  have cut153_4 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 1, 1, 0), (1, -1, 0, 1), (0, 1, 0, 0), (0, 1, 1, -1), (0, 1, 0, 0)] j) q) {4} = HL Γ [(0, 1, 0, 0)] := by
    rw [show ({4} : Finset (Fin 5)) = ([4] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    show HL Γ [(0, 1, 0, 0)] = HL Γ [(0, 1, 0, 0)]
    exact rfl
  have cut153_01 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 1, 1, 0), (1, -1, 0, 1), (0, 1, 0, 0), (0, 1, 1, -1), (0, 1, 0, 0)] j) q) {0, 1} = HL Γ [(1, 0, 1, 1), (0, 1, 1, 0)] := by
    rw [show ({0, 1} : Finset (Fin 5)) = ([0, 1] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    show HL Γ [(0, 1, 1, 0), (1, -1, 0, 1)] = HL Γ [(1, 0, 1, 1), (0, 1, 1, 0)]
    exact HL_eq_norm hinj (by decide)
  have cut153_02 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 1, 1, 0), (1, -1, 0, 1), (0, 1, 0, 0), (0, 1, 1, -1), (0, 1, 0, 0)] j) q) {0, 2} = HL Γ [(0, 1, 0, 0), (0, 0, 1, 0)] := by
    rw [show ({0, 2} : Finset (Fin 5)) = ([0, 2] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    show HL Γ [(0, 1, 1, 0), (0, 1, 0, 0)] = HL Γ [(0, 1, 0, 0), (0, 0, 1, 0)]
    exact HL_eq_norm hinj (by decide)
  have cut153_03 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 1, 1, 0), (1, -1, 0, 1), (0, 1, 0, 0), (0, 1, 1, -1), (0, 1, 0, 0)] j) q) {0, 3} = HL Γ [(0, 1, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 3} : Finset (Fin 5)) = ([0, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    show HL Γ [(0, 1, 1, 0), (0, 1, 1, -1)] = HL Γ [(0, 1, 1, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut153_04 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 1, 1, 0), (1, -1, 0, 1), (0, 1, 0, 0), (0, 1, 1, -1), (0, 1, 0, 0)] j) q) {0, 4} = HL Γ [(0, 1, 0, 0), (0, 0, 1, 0)] := by
    rw [show ({0, 4} : Finset (Fin 5)) = ([0, 4] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    show HL Γ [(0, 1, 1, 0), (0, 1, 0, 0)] = HL Γ [(0, 1, 0, 0), (0, 0, 1, 0)]
    exact HL_eq_norm hinj (by decide)
  have cut153_12 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 1, 1, 0), (1, -1, 0, 1), (0, 1, 0, 0), (0, 1, 1, -1), (0, 1, 0, 0)] j) q) {1, 2} = HL Γ [(1, 0, 0, 1), (0, 1, 0, 0)] := by
    rw [show ({1, 2} : Finset (Fin 5)) = ([1, 2] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    show HL Γ [(1, -1, 0, 1), (0, 1, 0, 0)] = HL Γ [(1, 0, 0, 1), (0, 1, 0, 0)]
    exact HL_eq_norm hinj (by decide)
  have cut153_13 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 1, 1, 0), (1, -1, 0, 1), (0, 1, 0, 0), (0, 1, 1, -1), (0, 1, 0, 0)] j) q) {1, 3} = HL Γ [(1, 0, 1, 0), (0, 1, 1, -1)] := by
    rw [show ({1, 3} : Finset (Fin 5)) = ([1, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    show HL Γ [(1, -1, 0, 1), (0, 1, 1, -1)] = HL Γ [(1, 0, 1, 0), (0, 1, 1, -1)]
    exact HL_eq_norm hinj (by decide)
  have cut153_14 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 1, 1, 0), (1, -1, 0, 1), (0, 1, 0, 0), (0, 1, 1, -1), (0, 1, 0, 0)] j) q) {1, 4} = HL Γ [(1, 0, 0, 1), (0, 1, 0, 0)] := by
    rw [show ({1, 4} : Finset (Fin 5)) = ([1, 4] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    show HL Γ [(1, -1, 0, 1), (0, 1, 0, 0)] = HL Γ [(1, 0, 0, 1), (0, 1, 0, 0)]
    exact HL_eq_norm hinj (by decide)
  have cut153_23 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 1, 1, 0), (1, -1, 0, 1), (0, 1, 0, 0), (0, 1, 1, -1), (0, 1, 0, 0)] j) q) {2, 3} = HL Γ [(0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({2, 3} : Finset (Fin 5)) = ([2, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    show HL Γ [(0, 1, 0, 0), (0, 1, 1, -1)] = HL Γ [(0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut153_012 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 1, 1, 0), (1, -1, 0, 1), (0, 1, 0, 0), (0, 1, 1, -1), (0, 1, 0, 0)] j) q) {0, 1, 2} = HL Γ [(1, 0, 0, 1), (0, 1, 0, 0), (0, 0, 1, 0)] := by
    rw [show ({0, 1, 2} : Finset (Fin 5)) = ([0, 1, 2] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    show HL Γ [(0, 1, 1, 0), (1, -1, 0, 1), (0, 1, 0, 0)] = HL Γ [(1, 0, 0, 1), (0, 1, 0, 0), (0, 0, 1, 0)]
    exact HL_eq_norm hinj (by decide)
  have cut153_013 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 1, 1, 0), (1, -1, 0, 1), (0, 1, 0, 0), (0, 1, 1, -1), (0, 1, 0, 0)] j) q) {0, 1, 3} = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 1, 3} : Finset (Fin 5)) = ([0, 1, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    show HL Γ [(0, 1, 1, 0), (1, -1, 0, 1), (0, 1, 1, -1)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut153_014 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 1, 1, 0), (1, -1, 0, 1), (0, 1, 0, 0), (0, 1, 1, -1), (0, 1, 0, 0)] j) q) {0, 1, 4} = HL Γ [(1, 0, 0, 1), (0, 1, 0, 0), (0, 0, 1, 0)] := by
    rw [show ({0, 1, 4} : Finset (Fin 5)) = ([0, 1, 4] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    show HL Γ [(0, 1, 1, 0), (1, -1, 0, 1), (0, 1, 0, 0)] = HL Γ [(1, 0, 0, 1), (0, 1, 0, 0), (0, 0, 1, 0)]
    exact HL_eq_norm hinj (by decide)
  have cut153_023 : HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (![(0, 1, 1, 0), (1, -1, 0, 1), (0, 1, 0, 0), (0, 1, 1, -1), (0, 1, 0, 0)] j) q) {0, 2, 3} = HL Γ [(0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] := by
    rw [show ({0, 2, 3} : Finset (Fin 5)) = ([0, 2, 3] : List (Fin 5)).toFinset from by decide, HS_eq_HL]
    show HL Γ [(0, 1, 1, 0), (0, 1, 0, 0), (0, 1, 1, -1)] = HL Γ [(0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
    exact HL_eq_norm hinj (by decide)
  have cut153_row : 0 ≤ (-6) * HL Γ [(0, 1, 0, 0)] + (-4) * HL Γ [(0, 1, 1, 0)] + (-9) * HL Γ [(1, -1, 0, 1)] + (3) * HL Γ [(0, 1, 1, 0), (0, 0, 0, 1)] + (-3) * HL Γ [(0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] + (-3) * HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] + (10) * HL Γ [(0, 1, 0, 0), (0, 0, 1, 0)] + (15) * HL Γ [(1, 0, 0, 1), (0, 1, 0, 0)] + (3) * HL Γ [(1, 0, 1, 0), (0, 1, 1, -1)] + (10) * HL Γ [(1, 0, 1, 1), (0, 1, 1, 0)] + (-16) * HL Γ [(1, 0, 0, 1), (0, 1, 0, 0), (0, 0, 1, 0)] := by
    norm_num at cut153
    linarith only [cut153, cut153_0, cut153_1, cut153_2, cut153_4, cut153_01, cut153_02, cut153_03, cut153_04, cut153_12, cut153_13, cut153_14, cut153_23, cut153_012, cut153_013, cut153_014, cut153_023]
  exact cut153_row

private theorem two_copy_row_e167 (Γ : Finset (G × G)) :
    HL Γ [(0, 1, 1, -1)] = HL Γ [(1, -1, 0, 1)] := by
  rw [← HL_swap Γ [(0, 1, 1, -1)]]
  simp only [List.map_cons, List.map_nil, sw4]

private theorem two_copy_row_e168 (Γ : Finset (G × G)) :
    HL Γ [(0, 1, 1, 1)] = HL Γ [(1, 1, 0, 1)] := by
  rw [← HL_swap Γ [(0, 1, 1, 1)]]
  simp only [List.map_cons, List.map_nil, sw4]

private theorem two_copy_row_e169 (Γ : Finset (G × G)) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, -1, -1, 0)] = HL Γ [(1, 0, -1, 1)] := by
  rw [← HL_swap Γ [(1, -1, -1, 0)]]
  simp only [List.map_cons, List.map_nil, sw4]
  exact HL_eq_norm hinj (by decide)

private theorem two_copy_row_e170 (Γ : Finset (G × G)) :
    HL Γ [(1, 0, 1, 1)] = HL Γ [(1, 1, 1, 0)] := by
  rw [← HL_swap Γ [(1, 0, 1, 1)]]
  simp only [List.map_cons, List.map_nil, sw4]

private theorem two_copy_row_e171 (Γ : Finset (G × G)) :
    HL Γ [(0, 1, 1, 0), (0, 0, 0, 1)] = HL Γ [(1, 0, 0, 1), (0, 1, 0, 0)] := by
  rw [← HL_swap Γ [(0, 1, 1, 0), (0, 0, 0, 1)]]
  simp only [List.map_cons, List.map_nil, sw4]

private theorem two_copy_row_e172 (Γ : Finset (G × G)) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 1)] = HL Γ [(0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] := by
  rw [← HL_swap Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 1)]]
  simp only [List.map_cons, List.map_nil, sw4]
  exact HL_eq_norm hinj (by decide)

private theorem two_copy_row_e173 (Γ : Finset (G × G)) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 0, -1, 0), (0, 0, 0, 1)] = HL Γ [(1, 0, -1, 0), (0, 1, 0, 0)] := by
  rw [← HL_swap Γ [(1, 0, -1, 0), (0, 0, 0, 1)]]
  simp only [List.map_cons, List.map_nil, sw4]
  exact HL_eq_norm hinj (by decide)

private theorem two_copy_row_e174 (Γ : Finset (G × G)) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 0, 0, 0), (0, 0, 0, 1)] = HL Γ [(0, 1, 0, 0), (0, 0, 1, 0)] := by
  rw [← HL_swap Γ [(1, 0, 0, 0), (0, 0, 0, 1)]]
  simp only [List.map_cons, List.map_nil, sw4]
  exact HL_eq_norm hinj (by decide)

private theorem two_copy_row_e175 (Γ : Finset (G × G)) :
    HL Γ [(1, 0, 1, 0), (0, 0, 0, 1)] = HL Γ [(1, 0, 1, 0), (0, 1, 0, 0)] := by
  rw [← HL_swap Γ [(1, 0, 1, 0), (0, 0, 0, 1)]]
  simp only [List.map_cons, List.map_nil, sw4]

private theorem two_copy_row_e176 (Γ : Finset (G × G)) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 1, 0, 0), (0, 0, 0, 1)] = HL Γ [(0, 1, 0, 0), (0, 0, 1, 1)] := by
  rw [← HL_swap Γ [(1, 1, 0, 0), (0, 0, 0, 1)]]
  simp only [List.map_cons, List.map_nil, sw4]
  exact HL_eq_norm hinj (by decide)

private theorem two_copy_row_e177 (Γ : Finset (G × G)) :
    HL Γ [(1, 1, 1, 0), (0, 0, 0, 1)] = HL Γ [(1, 0, 1, 1), (0, 1, 0, 0)] := by
  rw [← HL_swap Γ [(1, 1, 1, 0), (0, 0, 0, 1)]]
  simp only [List.map_cons, List.map_nil, sw4]

private theorem two_copy_row_e178 (Γ : Finset (G × G)) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 0, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0)] := by
  rw [← HL_swap Γ [(1, 0, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]]
  simp only [List.map_cons, List.map_nil, sw4]
  exact HL_eq_norm hinj (by decide)

private theorem two_copy_row_e179 (Γ : Finset (G × G)) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 1)] := by
  rw [← HL_swap Γ [(1, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]]
  simp only [List.map_cons, List.map_nil, sw4]
  exact HL_eq_norm hinj (by decide)

private theorem two_copy_row_e180 (Γ : Finset (G × G)) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(0, 1, 0, -1), (0, 0, 1, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, -1)] := by
  rw [← HL_swap Γ [(0, 1, 0, -1), (0, 0, 1, 0)]]
  simp only [List.map_cons, List.map_nil, sw4]
  exact HL_eq_norm hinj (by decide)

private theorem two_copy_row_e181 (Γ : Finset (G × G)) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(0, 1, 0, 1), (0, 0, 1, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, 1)] := by
  rw [← HL_swap Γ [(0, 1, 0, 1), (0, 0, 1, 0)]]
  simp only [List.map_cons, List.map_nil, sw4]
  exact HL_eq_norm hinj (by decide)

private theorem two_copy_row_e182 (Γ : Finset (G × G)) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 0, 0, 1), (0, 0, 1, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 1, 0)] := by
  rw [← HL_swap Γ [(1, 0, 0, 1), (0, 0, 1, 0)]]
  simp only [List.map_cons, List.map_nil, sw4]
  exact HL_eq_norm hinj (by decide)

private theorem two_copy_row_e183 (Γ : Finset (G × G)) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 1, 0, 0), (0, 0, 1, 0)] = HL Γ [(1, 0, 0, 0), (0, 0, 1, 1)] := by
  rw [← HL_swap Γ [(1, 1, 0, 0), (0, 0, 1, 0)]]
  simp only [List.map_cons, List.map_nil, sw4]
  exact HL_eq_norm hinj (by decide)

private theorem two_copy_row_e184 (Γ : Finset (G × G)) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(0, 1, 0, -1), (0, 0, 1, 1)] = HL Γ [(1, 0, 0, 1), (0, 1, 0, -1)] := by
  rw [← HL_swap Γ [(0, 1, 0, -1), (0, 0, 1, 1)]]
  simp only [List.map_cons, List.map_nil, sw4]
  exact HL_eq_norm hinj (by decide)

private theorem two_copy_row_e185 (Γ : Finset (G × G)) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 0, 0, 1), (0, 0, 1, 1)] = HL Γ [(1, 0, -1, 0), (0, 1, 1, 0)] := by
  rw [← HL_swap Γ [(1, 0, 0, 1), (0, 0, 1, 1)]]
  simp only [List.map_cons, List.map_nil, sw4]
  exact HL_eq_norm hinj (by decide)

private theorem two_copy_row_e186 (Γ : Finset (G × G)) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 0, 0, 1), (0, 1, 1, -1)] = HL Γ [(1, 0, 1, 1), (0, 1, 1, 0)] := by
  rw [← HL_swap Γ [(1, 0, 0, 1), (0, 1, 1, -1)]]
  simp only [List.map_cons, List.map_nil, sw4]
  exact HL_eq_norm hinj (by decide)

private theorem two_copy_row_e187 (Γ : Finset (G × G)) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 0, -1, 1), (0, 1, 1, 0)] = HL Γ [(1, 0, 0, 1), (0, 1, 1, 1)] := by
  rw [← HL_swap Γ [(1, 0, -1, 1), (0, 1, 1, 0)]]
  simp only [List.map_cons, List.map_nil, sw4]
  exact HL_eq_norm hinj (by decide)

private theorem two_copy_row_e188 (Γ : Finset (G × G)) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 0, 0, 0), (0, 1, 1, 0), (0, 0, 0, 1)] = HL Γ [(1, 0, 0, 1), (0, 1, 0, 0), (0, 0, 1, 0)] := by
  rw [← HL_swap Γ [(1, 0, 0, 0), (0, 1, 1, 0), (0, 0, 0, 1)]]
  simp only [List.map_cons, List.map_nil, sw4]
  exact HL_eq_norm hinj (by decide)

private theorem two_copy_row_e189 (Γ : Finset (G × G)) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 0, -1, 0), (0, 1, 1, 0), (0, 0, 0, 1)] = HL Γ [(1, 0, 0, 1), (0, 1, 0, 0), (0, 0, 1, 1)] := by
  rw [← HL_swap Γ [(1, 0, -1, 0), (0, 1, 1, 0), (0, 0, 0, 1)]]
  simp only [List.map_cons, List.map_nil, sw4]
  exact HL_eq_norm hinj (by decide)

private theorem two_copy_row_e190 (Γ : Finset (G × G)) (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') :
    HL Γ [(1, 0, 0, 1), (0, 1, 0, -1), (0, 0, 1, 0)] = HL Γ [(1, 0, 0, 0), (0, 1, 0, -1), (0, 0, 1, 1)] := by
  rw [← HL_swap Γ [(1, 0, 0, 1), (0, 1, 0, -1), (0, 0, 1, 0)]]
  simp only [List.map_cons, List.map_nil, sw4]
  exact HL_eq_norm hinj (by decide)

/-- **Two-copy inequality (Proposition 4.1).**  For a coupled pair (uniform on `Γ ⊆ X × Y`, differences
pairwise distinct) with marginals `μ, ν` and `h(i,j) = H(μ^{*i} * ν^{*j})`:
`194497 log|Γ| ≤ 49470 log|X+Y| + 73899 h(1,1) + 99532 h(1,0) + 98433 h(0,1) + 4986 h(2,0) + 6659 h(0,2)`. -/
theorem two_copy_ineq {Γ : Finset (G × G)} (hΓ : Γ.Nonempty)
    (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q') {X Y : Finset G}
    (hXY : Γ ⊆ X ×ˢ Y) :
    194497 * Real.log #Γ ≤ 49470 * Real.log #(X + Y)
      + 73899 * ent (P (margFst Γ) (margSnd Γ) 1 1) + 99532 * ent (P (margFst Γ) (margSnd Γ) 1 0)
      + 98433 * ent (P (margFst Γ) (margSnd Γ) 0 1) + 4986 * ent (P (margFst Γ) (margSnd Γ) 2 0)
      + 6659 * ent (P (margFst Γ) (margSnd Γ) 0 2) := by
  set μ := margFst Γ with hμd
  set ν := margSnd Γ with hνd
  have hμ : IsLaw μ := isLaw_margFst hΓ
  have hν : IsLaw ν := isLaw_margSnd hΓ
  set h : ℕ → ℕ → ℝ := fun i j => ent (P μ ν i j) with hh
  set L := Real.log #Γ
  have s116 := two_copy_row_s116 Γ hΓ hinj
  have s117 := two_copy_row_s117 Γ hΓ hinj
  have s118 := two_copy_row_s118 Γ hΓ hinj
  have s119 := two_copy_row_s119 Γ hΓ hinj
  have s120 := two_copy_row_s120 Γ hΓ hinj
  have s121 := two_copy_row_s121 Γ hΓ hinj
  have s122 := two_copy_row_s122 Γ hΓ hinj
  have s123 := two_copy_row_s123 Γ hΓ hinj
  have s124 := two_copy_row_s124 Γ hΓ hinj
  have s125 := two_copy_row_s125 Γ hΓ hinj
  have s126 := two_copy_row_s126 Γ hΓ hinj
  have s127 := two_copy_row_s127 Γ hΓ hinj
  have s128 := two_copy_row_s128 Γ hΓ hinj
  have s129 := two_copy_row_s129 Γ hΓ hinj
  have s130 := two_copy_row_s130 Γ hΓ hinj
  have s131 := two_copy_row_s131 Γ hΓ hinj
  have s132 := two_copy_row_s132 Γ hΓ hinj
  have s133 := two_copy_row_s133 Γ hΓ
  have s134 := two_copy_row_s134 Γ hΓ hinj
  have s135 := two_copy_row_s135 Γ hΓ hinj
  have s136 := two_copy_row_s136 Γ hΓ hinj
  have s137 := two_copy_row_s137 Γ hΓ hinj
  have s138 := two_copy_row_s138 Γ hΓ hinj
  have s139 := two_copy_row_s139 Γ hΓ hinj
  have s140 := two_copy_row_s140 Γ hΓ hinj
  have s141 := two_copy_row_s141 Γ hΓ hinj
  have s142 := two_copy_row_s142 Γ hΓ hinj
  have r143 := HL_X1Y1_le hΓ hXY
  have cut144_row := two_copy_row_cut144 Γ hΓ hinj
  have cut145_row := two_copy_row_cut145 Γ hΓ hinj
  have cut146_row := two_copy_row_cut146 Γ hΓ hinj
  have cut147_row := two_copy_row_cut147 Γ hΓ hinj
  have cut148_row := two_copy_row_cut148 Γ hΓ hinj
  have cut149_row := two_copy_row_cut149 Γ hΓ hinj
  have cut150_row := two_copy_row_cut150 Γ hΓ hinj
  have cut151_row := two_copy_row_cut151 Γ hΓ hinj
  have cut152_row := two_copy_row_cut152 Γ hΓ hinj
  have cut153_row := two_copy_row_cut153 Γ hΓ hinj
  have e154 : HL Γ [(0, 0, 0, 1)] = h 0 1 := by rw [HL_Y2 hΓ]; simp [hh, P, hμd, hνd]
  have e155 : HL Γ [(0, 0, 1, 0)] = h 1 0 := by rw [HL_X2 hΓ]; simp [hh, P, hμd, hνd]
  have e156 : HL Γ [(0, 1, 0, 0)] = h 0 1 := by rw [HL_Y1 hΓ]; simp [hh, P, hμd, hνd]
  have e157 : HL Γ [(0, 1, 0, 1)] = h 0 2 := by rw [HL_Y1Y2 Γ]; simp [hh, P, pow_two, hμd, hνd]
  have e158 : HL Γ [(0, 1, 1, 0)] = h 1 1 := by rw [HL_Y1X2 Γ]; simp [hh, P, hμd, hνd]
  have e159 : HL Γ [(1, 0, 0, 0)] = h 1 0 := by rw [HL_X1 hΓ]; simp [hh, P, hμd, hνd]
  have e160 : HL Γ [(1, 0, 0, 1)] = h 1 1 := by rw [HL_X1Y2 Γ]; simp [hh, P, hμd, hνd]
  have e161 : HL Γ [(1, 0, 1, 0)] = h 2 0 := by rw [HL_X1X2 Γ]; simp [hh, P, pow_two, hμd, hνd]
  have e162 := HL_indep hΓ [(0, 1, 0, 0)] [(0, 0, 0, 1)] (by decide) (by decide)
  simp only [List.cons_append, List.nil_append] at e162
  have e163 := HL_indep hΓ [(1, 0, 0, 0), (0, 1, 0, 0)] [(0, 0, 1, 0), (0, 0, 0, 1)] (by decide) (by decide)
  simp only [List.cons_append, List.nil_append] at e163
  have e164 := HL_indep hΓ [(1, 0, 0, 0)] [(0, 0, 1, 0)] (by decide) (by decide)
  simp only [List.cons_append, List.nil_append] at e164
  have e165 : HL Γ [(1, 0, 0, 0), (0, 1, 0, 0)] = L := HL_pair1 hΓ
  have e166 : HL Γ [(0, 0, 1, 0), (0, 0, 0, 1)] = L := HL_pair2 hΓ
  have e167 := two_copy_row_e167 Γ
  have e168 := two_copy_row_e168 Γ
  have e169 := two_copy_row_e169 Γ hinj
  have e170 := two_copy_row_e170 Γ
  have e171 := two_copy_row_e171 Γ
  have e172 := two_copy_row_e172 Γ hinj
  have e173 := two_copy_row_e173 Γ hinj
  have e174 := two_copy_row_e174 Γ hinj
  have e175 := two_copy_row_e175 Γ
  have e176 := two_copy_row_e176 Γ hinj
  have e177 := two_copy_row_e177 Γ
  have e178 := two_copy_row_e178 Γ hinj
  have e179 := two_copy_row_e179 Γ hinj
  have e180 := two_copy_row_e180 Γ hinj
  have e181 := two_copy_row_e181 Γ hinj
  have e182 := two_copy_row_e182 Γ hinj
  have e183 := two_copy_row_e183 Γ hinj
  have e184 := two_copy_row_e184 Γ hinj
  have e185 := two_copy_row_e185 Γ hinj
  have e186 := two_copy_row_e186 Γ hinj
  have e187 := two_copy_row_e187 Γ hinj
  have e188 := two_copy_row_e188 Γ hinj
  have e189 := two_copy_row_e189 Γ hinj
  have e190 := two_copy_row_e190 Γ hinj
  have e0 : HL Γ [] = 0 := HL_nil Γ hΓ
  -- Proposition 4.1 is the following integer combination of the rows above (the weights of
  -- Tables 1 and 2 of the proof paper).
  show 194497 * L ≤ 49470 * Real.log #(X + Y) + 73899 * h 1 1 + 99532 * h 1 0 + 98433 * h 0 1
      + 4986 * h 2 0 + 6659 * h 0 2
  linear_combination 21105 * s116 + 9814 * s117 + 17442 * s118 + 4986 * s119 + 26370 * s120
    + 16965 * s121 + 12564 * s122 + 11708 * s123 + 1304 * s124 + 4896 * s125 + 7764 * s126
    + 6659 * s127 + 16839 * s128 + 23100 * s129 + 2376 * s130 + 18522 * s131 + 26001 * s132
    + 4016 * s133 + 3564 * s134 + 2277 * s135 + 2520 * s136 + 748 * s137 + 2376 * s138 + 6024 * s139
    + 4149 * s140 + 6576 * s141 + 7806 * s142 + 49470 * r143 + 4794 * cut144_row + 1188 * cut145_row
    + 1146 * cut146_row + 2008 * cut147_row + 516 * cut148_row + 1506 * cut149_row
    + 963 * cut150_row + 396 * cut151_row + 420 * cut152_row + 153 * cut153_row + 90808 * e154
    + 57392 * e155 + 7625 * e156 + 6659 * e157 + 57060 * e158 + 42140 * e159 + 16839 * e160
    + 4986 * e161 + 16247 * e162 - 118570 * e163 + 14574 * e164 - 123364 * e165 - 71133 * e166
    - 8811 * e167 - 17334 * e168 + 9927 * e169 + 17334 * e170 - 2295 * e171 + 23049 * e172
    - 184 * e173 - 17442 * e174 - 4986 * e175 - 16740 * e176 + 2376 * e177 - 11708 * e178
    - 4896 * e179 + 1980 * e180 - 2141 * e181 - 12690 * e182 - 1584 * e183 + 6576 * e184
    + 7806 * e185 + 14616 * e186 - 11556 * e187 - 1116 * e188 + 1434 * e189 - 4356 * e190
    - 226231 * e0

end CoupledForms

end SumsDifferences
