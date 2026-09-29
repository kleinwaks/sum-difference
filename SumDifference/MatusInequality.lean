module

/-
# Matúš's infinite family of non-Shannon entropy inequalities

For five random variables `a, b, c, d, z` on a finite probability space write `(x, y ‖ w)` for
the conditional mutual information and `[abcd] = -(a,b) + (a,b‖c) + (a,b‖d) + (c,d)` for the
Ingleton expression.  F. Matúš (*Infinitely many information inequalities*, ISIT 2007; the five-variable form is also
reproduced with proof in Csirmaz–Csirmaz, arXiv:2512.23316v2, Theorem 22) proved
that for every `k ≥ 0`

  `(b,z‖a) + k·([abcd] + (a,z‖b) + (a,b‖z)) + k(k-1)/2·((a,c‖b) + (a,b‖c)) ≥ 0`,

and the same with `[abcd]` replaced by `[acbd]` (Theorem 3.4 of the proof paper,
where the left-hand side is written `M_k[abcd]`, resp. `M_k[acbd]`).  The proof is by induction
on `k`: by the copy lemma (`copy_step`, Lemma 3.6) one may replace `z` by a copy that is
conditionally independent of `(c, d)` given `(a, b)`; the inequality for `k`, applied to
`(a, c, b, d, z)` with the other Ingleton variant, finitely many Shannon inequalities and
`(cd, z‖ab) = 0` then give the inequality for `k + 1`.

Here all five variables take values in one type `G`; joint entropies of subfamilies are encoded
by `HS s p v S` (the entropy of the tuple `(v j)_{j ∈ S}`, padded with `0`).  Main result:
`matus_ineq`.
-/
public import Mathlib
public import SumDifference.CopyLemma
public import SumDifference.EntropyEquality

@[expose] public section

open Finset

namespace SumsDifferences

namespace NonShannon

variable {ι G : Type*} [DecidableEq G] [Zero G]

/-- The joint entropy of the subfamily `(v j)_{j ∈ S}` (other coordinates padded by `0`). -/
noncomputable def HS {n : ℕ} (s : Finset ι) (p : ι → ℝ) (v : Fin n → ι → G)
    (S : Finset (Fin n)) : ℝ :=
  pushEntropy s p (fun i => fun j : Fin n => if j ∈ S then v j i else 0)

/-- The tuple of a subfamily. -/
def tup {n : ℕ} (v : Fin n → ι → G) (S : Finset (Fin n)) (i : ι) : Fin n → G :=
  fun j => if j ∈ S then v j i else 0

theorem HS_eq {n : ℕ} (s : Finset ι) (p : ι → ℝ) (v : Fin n → ι → G) (S : Finset (Fin n)) :
    HS s p v S = pushEntropy s p (tup v S) := rfl

/-- Restriction of tuples. -/
def restr {n : ℕ} (S : Finset (Fin n)) (f : Fin n → G) : Fin n → G :=
  fun j => if j ∈ S then f j else 0

omit [DecidableEq G] in
theorem restr_tup {n : ℕ} (v : Fin n → ι → G) {S T : Finset (Fin n)} (h : S ⊆ T) (i : ι) :
    restr S (tup v T i) = tup v S i := by
  funext j; simp only [restr, tup]
  split_ifs with h1 h2 <;> first | rfl | exact absurd (h h1) h2

theorem HS_mono {n : ℕ} {s : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i)
    (v : Fin n → ι → G) {S T : Finset (Fin n)} (h : S ⊆ T) : HS s p v S ≤ HS s p v T := by
  have := pushEntropy_comp_le hp (tup v T) (restr S)
  simp only [restr_tup v h] at this
  exact this

theorem HS_empty {n : ℕ} {s : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i)
    (hsum : ∑ i ∈ s, p i = 1) (v : Fin n → ι → G) : HS s p v ∅ = 0 := by
  classical
  have h1 : HS s p v ∅ = pushEntropy s p (fun _ : ι => (0 : Fin n → G)) := by
    unfold HS; congr 1
  rw [h1]
  refine le_antisymm ?_ (pushEntropy_nonneg hp hsum)
  have := pushEntropy_le_log_card (s := s) (p := p) (f := fun _ : ι => (0 : Fin n → G))
    (t := {0}) hp hsum (fun i _ => Finset.mem_singleton_self _)
  simpa using this

/-- **Submodularity** of `HS`. -/
theorem HS_submod {n : ℕ} {s : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i)
    (hsum : ∑ i ∈ s, p i = 1) (v : Fin n → ι → G) (S T : Finset (Fin n)) :
    HS s p v (S ∪ T) + HS s p v (S ∩ T) ≤ HS s p v S + HS s p v T := by
  classical
  have key := pushEntropy_submodular hp hsum (tup v S) (tup v (S ∩ T)) (tup v T)
  have e1 : pushEntropy s p (fun i => (tup v S i, tup v (S ∩ T) i, tup v T i)) = HS s p v (S ∪ T) := by
    refine (pushEntropy_eq_of_comp hp (fun f => restr (S ∪ T) (fun j => if j ∈ S then f.1 j else f.2.2 j))
      (fun g => (restr S g, restr (S ∩ T) g, restr T g)) ?_ ?_).symm.trans rfl |>.symm
    · intro i _
      funext j; simp only [restr, tup]
      by_cases hS : j ∈ S <;> by_cases hT : j ∈ T <;> simp [hS, hT]
    · intro i _
      simp only [Prod.mk.injEq]
      refine ⟨restr_tup v Finset.subset_union_left i, restr_tup v ?_ i, restr_tup v Finset.subset_union_right i⟩
      exact Finset.inter_subset_left.trans Finset.subset_union_left
  have e2 : pushEntropy s p (fun i => (tup v S i, tup v (S ∩ T) i)) = HS s p v S := by
    refine (pushEntropy_eq_of_comp hp (fun f => f.1) (fun g => (g, restr (S ∩ T) g)) ?_ ?_)
    · intro i _; rfl
    · intro i _; exact Prod.ext rfl (restr_tup v Finset.inter_subset_left i)
  have e3 : pushEntropy s p (fun i => (tup v (S ∩ T) i, tup v T i)) = HS s p v T := by
    refine (pushEntropy_eq_of_comp hp (fun f => f.2) (fun g => (restr (S ∩ T) g, g)) ?_ ?_)
    · intro i _; rfl
    · intro i _; exact Prod.ext (restr_tup v Finset.inter_subset_right i) rfl
  rw [e1, e2, e3] at key
  exact key

/-- Relabelling the family by a permutation. -/
theorem HS_comp_perm {n : ℕ} {s : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i)
    (v : Fin n → ι → G) (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    HS s p (fun j => v (σ j)) S = HS s p v (S.map σ.toEmbedding) := by
  classical
  refine pushEntropy_eq_of_comp hp (fun f => fun j => f (σ.symm j)) (fun g => fun j => g (σ j)) ?_ ?_
  · intro i _
    funext j
    simp only [Finset.mem_map_equiv, Equiv.apply_symm_apply]
  · intro i _
    funext j
    simp only [Finset.mem_map_equiv, Equiv.symm_apply_apply]

theorem HS_perm_lit {n : ℕ} {s : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i)
    (v : Fin n → ι → G) (σ : Equiv.Perm (Fin n)) {S S' : Finset (Fin n)}
    (h : S.map σ.toEmbedding = S') : HS s p (fun j => v (σ j)) S = HS s p v S' := by
  rw [HS_comp_perm hp, h]

theorem HS_submod_lit {n : ℕ} {s : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i)
    (hsum : ∑ i ∈ s, p i = 1) (v : Fin n → ι → G) {S T U V : Finset (Fin n)}
    (hU : S ∪ T = U) (hV : S ∩ T = V) : HS s p v U + HS s p v V ≤ HS s p v S + HS s p v T := by
  rw [← hU, ← hV]; exact HS_submod hp hsum v S T

/-! ## The copy of `z` over `(a, b)` -/

/-- The key `(a, b)`. -/
def keyAB (v : Fin 5 → ι → G) (i : ι) : G × G := (v 0 i, v 1 i)

/-- The family on the copy space: `a, b, c, d` from the first coordinate, `z` from the second. -/
def copyFam (v : Fin 5 → ι → G) : Fin 5 → ι × ι → G :=
  fun j q => if j = 4 then v j q.2 else v j q.1

omit [Zero G] in
theorem copyW_sum {s : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i) (hsum : ∑ i ∈ s, p i = 1)
    (K : ι → G × G) : ∑ q ∈ copySet s K, copyW s p K q = 1 := by
  have := copy_sum_fst hp K (fun _ => 1)
  simp only [mul_one] at this
  rw [this, hsum]

theorem HS_copy_fst {s : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i) (v : Fin 5 → ι → G)
    {S : Finset (Fin 5)} (h4 : (4 : Fin 5) ∉ S) :
    HS (copySet s (keyAB v)) (copyW s p (keyAB v)) (copyFam v) S = HS s p v S := by
  have e : (fun q : ι × ι => fun j : Fin 5 => if j ∈ S then copyFam v j q else 0)
      = fun q => tup v S q.1 := by
    funext q j
    simp only [tup, copyFam]
    by_cases hj : j ∈ S
    · have : j ≠ 4 := fun h => h4 (h ▸ hj)
      simp [hj, this]
    · simp [hj]
  unfold HS
  rw [e, pushEntropy_copy_fst hp (keyAB v) (tup v S)]
  rfl

theorem HS_copy_snd {s : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i) (v : Fin 5 → ι → G)
    {S : Finset (Fin 5)} (hS : S ⊆ {0, 1, 4}) :
    HS (copySet s (keyAB v)) (copyW s p (keyAB v)) (copyFam v) S = HS s p v S := by
  unfold HS
  rw [pushEntropy_congr (g := fun q => tup v S q.2), pushEntropy_copy_snd hp (keyAB v) (tup v S)]
  · rfl
  intro q hq
  have hk := (mem_copySet.mp hq).2.2
  simp only [keyAB, Prod.mk.injEq] at hk
  funext j
  simp only [tup, copyFam]
  by_cases hj : j ∈ S
  · have hj' := hS hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj'
    rcases hj' with rfl | rfl | rfl
    · simp [hj, hk.1]
    · simp [hj, hk.2]
    · simp [hj]
  · simp [hj]

theorem HS_copy_ci {s : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i) (v : Fin 5 → ι → G) :
    HS (copySet s (keyAB v)) (copyW s p (keyAB v)) (copyFam v) {0, 1, 2, 3, 4} + HS s p v {0, 1}
      = HS s p v {0, 1, 2, 3} + HS s p v {0, 1, 4} := by
  classical
  have key := pushEntropy_copy_ci hp (keyAB v) (fun i => (v 2 i, v 3 i)) (v 4)
  have hp' : ∀ q ∈ copySet s (keyAB v), 0 ≤ copyW s p (keyAB v) q := fun q hq => copyW_nonneg hp _ hq
  have e1 : pushEntropy (copySet s (keyAB v)) (copyW s p (keyAB v))
      (fun q => ((v 2 q.1, v 3 q.1), v 4 q.2, keyAB v q.1))
      = HS (copySet s (keyAB v)) (copyW s p (keyAB v)) (copyFam v) {0, 1, 2, 3, 4} := by
    refine pushEntropy_eq_of_comp hp'
      (fun x => fun j : Fin 5 => if j = 0 then x.2.2.1 else if j = 1 then x.2.2.2 else
        if j = 2 then x.1.1 else if j = 3 then x.1.2 else x.2.1)
      (fun f => ((f 2, f 3), f 4, (f 0, f 1))) ?_ ?_
    · intro q _; funext j; fin_cases j <;> simp [copyFam, keyAB]
    · intro q _; simp [copyFam, keyAB]
  have e2 : pushEntropy s p (fun i => ((v 2 i, v 3 i), keyAB v i)) = HS s p v {0, 1, 2, 3} := by
    refine pushEntropy_eq_of_comp hp
      (fun x => fun j : Fin 5 => if j = 0 then x.2.1 else if j = 1 then x.2.2 else
        if j = 2 then x.1.1 else if j = 3 then x.1.2 else 0)
      (fun f => ((f 2, f 3), (f 0, f 1))) ?_ ?_
    · intro i _; funext j; fin_cases j <;> simp [keyAB]
    · intro i _; simp [keyAB]
  have e3 : pushEntropy s p (fun i => (v 4 i, keyAB v i)) = HS s p v {0, 1, 4} := by
    refine pushEntropy_eq_of_comp hp
      (fun x => fun j : Fin 5 => if j = 0 then x.2.1 else if j = 1 then x.2.2 else
        if j = 4 then x.1 else 0)
      (fun f => (f 4, (f 0, f 1))) ?_ ?_
    · intro i _; funext j; fin_cases j <;> simp [keyAB]
    · intro i _; simp [keyAB]
  have e4 : pushEntropy s p (keyAB v) = HS s p v {0, 1} := by
    refine pushEntropy_eq_of_comp hp
      (fun x => fun j : Fin 5 => if j = 0 then x.1 else if j = 1 then x.2 else 0)
      (fun f => (f 0, f 1)) ?_ ?_
    · intro i _; funext j; fin_cases j <;> simp [keyAB]
    · intro i _; simp [keyAB]
  rw [e1, e2, e3, e4] at key
  exact key

/-- **The copy step** (Lemma 3.6), shared by `matus_ineq` and `companion_ineq`: for five
variables `a, b, c, d, z` (`v 0, …, v 4`) there is a new family on a finite probability space with
the same joint law of `(a, b, c, d)`, the same joint law of `(a, b, z)`, and with `z` conditionally
independent of `(c, d)` given `(a, b)`.  (It is `copyFam v` on the copy space over the key `(a, b)`.) -/
theorem copy_step {ι : Type*} {s : Finset ι} {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i)
    (hsum : ∑ i ∈ s, p i = 1) (v : Fin 5 → ι → G) :
    ∃ (s' : Finset (ι × ι)) (p' : ι × ι → ℝ) (v' : Fin 5 → ι × ι → G),
      (∀ q ∈ s', 0 ≤ p' q) ∧ ∑ q ∈ s', p' q = 1 ∧
      (∀ S : Finset (Fin 5), (4 : Fin 5) ∉ S → HS s' p' v' S = HS s p v S) ∧
      (∀ S : Finset (Fin 5), S ⊆ {0, 1, 4} → HS s' p' v' S = HS s p v S) ∧
      HS s' p' v' {0, 1, 2, 3, 4} + HS s' p' v' {0, 1}
        = HS s' p' v' {0, 1, 2, 3} + HS s' p' v' {0, 1, 4} := by
  refine ⟨copySet s (keyAB v), copyW s p (keyAB v), copyFam v,
    fun q hq => copyW_nonneg hp _ hq, copyW_sum hp hsum _,
    fun S hS => HS_copy_fst hp v hS, fun S hS => HS_copy_snd hp v hS, ?_⟩
  have CI := HS_copy_ci hp v
  rw [HS_copy_fst hp v (S := {0, 1}) (by decide), HS_copy_fst hp v (S := {0, 1, 2, 3}) (by decide),
    HS_copy_snd hp v (S := {0, 1, 4}) (by decide)]
  exact CI

/-! ## Information expressions on set functions -/

/-- Conditional mutual information `(A, B ‖ C)` of a set function. -/
def cmi {n : ℕ} (h : Finset (Fin n) → ℝ) (A B C : Finset (Fin n)) : ℝ :=
  h (A ∪ C) + h (B ∪ C) - h (A ∪ B ∪ C) - h C

/-- The Ingleton expression `[abcd]`. -/
def ingl {n : ℕ} (h : Finset (Fin n) → ℝ) (a b c d : Fin n) : ℝ :=
  -cmi h {a} {b} ∅ + cmi h {a} {b} {c} + cmi h {a} {b} {d} + cmi h {c} {d} ∅

/-- Matúš's expression (`sw = false`: with `[abcd]`; `sw = true`: with `[acbd]`), for the
variables `a, b, c, d, z` with indices `0, 1, 2, 3, 4`. -/
noncomputable def matusExpr (h : Finset (Fin 5) → ℝ) (k : ℕ) (sw : Bool) : ℝ :=
  cmi h {1} {4} {0}
    + (k : ℝ) * ((if sw then ingl h 0 2 1 3 else ingl h 0 1 2 3) + cmi h {0} {4} {1} + cmi h {0} {1} {4})
    + ((k : ℝ) * ((k : ℝ) - 1) / 2) * (cmi h {0} {2} {1} + cmi h {0} {1} {2})

/-- Matúš's expression written out on the subsets of `{a, b, c, d, z} = {0, 1, 2, 3, 4}`:
`(b,z‖a) + k·(slb + (a,z‖b) + (a,b‖z)) + k(k-1)/2·((a,c‖b) + (a,b‖c))`, where
`slb = [abcd]` (`sw = false`) or `slb = [acbd]` (`sw = true`). -/
noncomputable def matusL (h : Finset (Fin 5) → ℝ) (k : ℝ) (sw : Bool) : ℝ :=
  (- h {0} + h {0, 1} + h {0, 4} - h {0, 1, 4})
    + k * (if sw then (- h {0} - h {1} - h {2} - h {4} + 2 * h {0, 1} + h {0, 2} + h {0, 3} + h {0, 4} + h {1, 2} - h {1, 3} + 2 * h {1, 4} + h {2, 3} - h {0, 1, 2} - 2 * h {0, 1, 4} - h {0, 2, 3})
      else (- h {0} - 2 * h {1} - h {4} + 2 * h {0, 1} + h {0, 2} + h {0, 3} + h {0, 4} + h {1, 2} + h {1, 3} + 2 * h {1, 4} - h {2, 3} - h {0, 1, 2} - h {0, 1, 3} - 2 * h {0, 1, 4}))
    + (k * (k - 1) / 2) * (- h {1} - h {2} + h {0, 1} + h {0, 2} + 2 * h {1, 2} - 2 * h {0, 1, 2})

set_option maxHeartbeats 2000000 in
/-- **Matúš's inequalities** (Theorem 3.4; F. Matúš, *Infinitely many information inequalities*,
2007):
for five random variables `a, b, c, d, z` (here `v 0, …, v 4`) on a finite probability space and
every `k ∈ ℕ`,
`(b,z‖a) + k·([abcd] + (a,z‖b) + (a,b‖z)) + k(k-1)/2·((a,c‖b) + (a,b‖c)) ≥ 0`, and the same with
`[acbd]` in place of `[abcd]`. -/
theorem matus_ineq (k : ℕ) : ∀ (sw : Bool) {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (_hp : ∀ i ∈ s, 0 ≤ p i) (_hsum : ∑ i ∈ s, p i = 1) (v : Fin 5 → ι → G),
    0 ≤ matusL (HS s p v) k sw := by
  induction k with
  | zero =>
    intro sw ι s p hp hsum v
    have := HS_submod_lit hp hsum v (S := {0, 1}) (T := {0, 4}) (U := {0, 1, 4}) (V := {0})
      (by decide) (by decide)
    simp only [matusL, Nat.cast_zero, zero_mul, add_zero, zero_sub, mul_neg, mul_one,
      neg_zero, zero_div]
    linarith
  | succ k ih =>
    intro sw ι s p hp hsum v
    obtain ⟨s', p', v', hp', hsum', Hfst, Hsnd, CI⟩ := copy_step hp hsum v
    set σ : Equiv.Perm (Fin 5) := Equiv.swap 1 2
    set w : Fin 5 → ι × ι → G := fun j => v' (σ j)
    have IH := ih (!sw) s' p' hp' hsum' w
    have P0 : HS s' p' w {0} = HS s' p' v' {0} := HS_perm_lit hp' v' σ (by decide)
    have P1 : HS s' p' w {1} = HS s' p' v' {2} := HS_perm_lit hp' v' σ (by decide)
    have P2 : HS s' p' w {2} = HS s' p' v' {1} := HS_perm_lit hp' v' σ (by decide)
    have P4 : HS s' p' w {4} = HS s' p' v' {4} := HS_perm_lit hp' v' σ (by decide)
    have P01 : HS s' p' w {0, 1} = HS s' p' v' {0, 2} := HS_perm_lit hp' v' σ (by decide)
    have P02 : HS s' p' w {0, 2} = HS s' p' v' {0, 1} := HS_perm_lit hp' v' σ (by decide)
    have P03 : HS s' p' w {0, 3} = HS s' p' v' {0, 3} := HS_perm_lit hp' v' σ (by decide)
    have P04 : HS s' p' w {0, 4} = HS s' p' v' {0, 4} := HS_perm_lit hp' v' σ (by decide)
    have P12 : HS s' p' w {1, 2} = HS s' p' v' {1, 2} := HS_perm_lit hp' v' σ (by decide)
    have P13 : HS s' p' w {1, 3} = HS s' p' v' {2, 3} := HS_perm_lit hp' v' σ (by decide)
    have P14 : HS s' p' w {1, 4} = HS s' p' v' {2, 4} := HS_perm_lit hp' v' σ (by decide)
    have P23 : HS s' p' w {2, 3} = HS s' p' v' {1, 3} := HS_perm_lit hp' v' σ (by decide)
    have P012 : HS s' p' w {0, 1, 2} = HS s' p' v' {0, 1, 2} := HS_perm_lit hp' v' σ (by decide)
    have P013 : HS s' p' w {0, 1, 3} = HS s' p' v' {0, 2, 3} := HS_perm_lit hp' v' σ (by decide)
    have P014 : HS s' p' w {0, 1, 4} = HS s' p' v' {0, 2, 4} := HS_perm_lit hp' v' σ (by decide)
    have P023 : HS s' p' w {0, 2, 3} = HS s' p' v' {0, 1, 3} := HS_perm_lit hp' v' σ (by decide)
    have F0 : HS s' p' v' {0} = HS s p v {0} := Hfst _ (by decide)
    have F1 : HS s' p' v' {1} = HS s p v {1} := Hfst _ (by decide)
    have F2 : HS s' p' v' {2} = HS s p v {2} := Hfst _ (by decide)
    have F3 : HS s' p' v' {3} = HS s p v {3} := Hfst _ (by decide)
    have F01 : HS s' p' v' {0, 1} = HS s p v {0, 1} := Hfst _ (by decide)
    have F02 : HS s' p' v' {0, 2} = HS s p v {0, 2} := Hfst _ (by decide)
    have F03 : HS s' p' v' {0, 3} = HS s p v {0, 3} := Hfst _ (by decide)
    have F12 : HS s' p' v' {1, 2} = HS s p v {1, 2} := Hfst _ (by decide)
    have F13 : HS s' p' v' {1, 3} = HS s p v {1, 3} := Hfst _ (by decide)
    have F23 : HS s' p' v' {2, 3} = HS s p v {2, 3} := Hfst _ (by decide)
    have F012 : HS s' p' v' {0, 1, 2} = HS s p v {0, 1, 2} := Hfst _ (by decide)
    have F013 : HS s' p' v' {0, 1, 3} = HS s p v {0, 1, 3} := Hfst _ (by decide)
    have F023 : HS s' p' v' {0, 2, 3} = HS s p v {0, 2, 3} := Hfst _ (by decide)
    have F123 : HS s' p' v' {1, 2, 3} = HS s p v {1, 2, 3} := Hfst _ (by decide)
    have F4 : HS s' p' v' {4} = HS s p v {4} := Hsnd _ (by decide)
    have F04 : HS s' p' v' {0, 4} = HS s p v {0, 4} := Hsnd _ (by decide)
    have F14 : HS s' p' v' {1, 4} = HS s p v {1, 4} := Hsnd _ (by decide)
    have F014 : HS s' p' v' {0, 1, 4} = HS s p v {0, 1, 4} := Hsnd _ (by decide)
    have S01_24 := HS_submod_lit hp' hsum' v' (S := {0, 2, 4}) (T := {1, 2, 4}) (U := {0, 1, 2, 4}) (V := {2, 4}) (by decide) (by decide)
    have S01_34 := HS_submod_lit hp' hsum' v' (S := {0, 3, 4}) (T := {1, 3, 4}) (U := {0, 1, 3, 4}) (V := {3, 4}) (by decide) (by decide)
    have S04_123 := HS_submod_lit hp' hsum' v' (S := {0, 1, 2, 3}) (T := {1, 2, 3, 4}) (U := {0, 1, 2, 3, 4}) (V := {1, 2, 3}) (by decide) (by decide)
    have S14_23 := HS_submod_lit hp' hsum' v' (S := {1, 2, 3}) (T := {2, 3, 4}) (U := {1, 2, 3, 4}) (V := {2, 3}) (by decide) (by decide)
    have S23_4 := HS_submod_lit hp' hsum' v' (S := {2, 4}) (T := {3, 4}) (U := {2, 3, 4}) (V := {4}) (by decide) (by decide)
    have S24_1 := HS_submod_lit hp' hsum' v' (S := {1, 2}) (T := {1, 4}) (U := {1, 2, 4}) (V := {1}) (by decide) (by decide)
    have S24_013 := HS_submod_lit hp' hsum' v' (S := {0, 1, 2, 3}) (T := {0, 1, 3, 4}) (U := {0, 1, 2, 3, 4}) (V := {0, 1, 3}) (by decide) (by decide)
    have S34_0 := HS_submod_lit hp' hsum' v' (S := {0, 3}) (T := {0, 4}) (U := {0, 3, 4}) (V := {0}) (by decide) (by decide)
    have S34_1 := HS_submod_lit hp' hsum' v' (S := {1, 3}) (T := {1, 4}) (U := {1, 3, 4}) (V := {1}) (by decide) (by decide)
    have S34_012 := HS_submod_lit hp' hsum' v' (S := {0, 1, 2, 3}) (T := {0, 1, 2, 4}) (U := {0, 1, 2, 3, 4}) (V := {0, 1, 2}) (by decide) (by decide)
    have S02_34 := HS_submod_lit hp' hsum' v' (S := {0, 3, 4}) (T := {2, 3, 4}) (U := {0, 2, 3, 4}) (V := {3, 4}) (by decide) (by decide)
    have S04_13 := HS_submod_lit hp' hsum' v' (S := {0, 1, 3}) (T := {1, 3, 4}) (U := {0, 1, 3, 4}) (V := {1, 3}) (by decide) (by decide)
    have S13_4 := HS_submod_lit hp' hsum' v' (S := {1, 4}) (T := {3, 4}) (U := {1, 3, 4}) (V := {4}) (by decide) (by decide)
    have S14_023 := HS_submod_lit hp' hsum' v' (S := {0, 1, 2, 3}) (T := {0, 2, 3, 4}) (U := {0, 1, 2, 3, 4}) (V := {0, 2, 3}) (by decide) (by decide)
    have S34_2 := HS_submod_lit hp' hsum' v' (S := {2, 3}) (T := {2, 4}) (U := {2, 3, 4}) (V := {2}) (by decide) (by decide)
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hii : 0 ≤ (- HS s' p' v' {1} + HS s' p' v' {0, 1} + HS s' p' v' {1, 2} + HS s' p' v' {1, 4}
        - HS s' p' v' {2, 4} - HS s' p' v' {0, 1, 2} - HS s' p' v' {0, 1, 4}
        + HS s' p' v' {0, 2, 4}) := by linarith
    have hkii := mul_nonneg hk hii
    unfold matusL at IH ⊢
    cases sw
    · have hi : 0 ≤ (- HS s' p' v' {0} - 2 * HS s' p' v' {1} - HS s' p' v' {4}
          + 3 * HS s' p' v' {0, 1} + HS s' p' v' {0, 3} + HS s' p' v' {0, 4} + HS s' p' v' {1, 2}
          + HS s' p' v' {1, 3} + 2 * HS s' p' v' {1, 4} - HS s' p' v' {2, 3} - HS s' p' v' {0, 1, 2}
          - HS s' p' v' {0, 1, 3} - 3 * HS s' p' v' {0, 1, 4} + HS s' p' v' {0, 2, 4}) := by linarith
      simp only [Bool.not_false, if_true, Bool.false_eq_true, if_false] at IH ⊢
      simp only [P0, P1, P2, P4, P01, P02, P03, P04, P12, P13, P14, P23, P012, P014, P023] at IH
      simp only [F0, F1, F2, F01, F02, F03, F12, F13, F23, F012, F013, F4, F04, F14, F014] at IH hi hkii
      push_cast
      linarith only [IH, hi, hkii]
    · have hi : 0 ≤ (- HS s' p' v' {0} - HS s' p' v' {1} - HS s' p' v' {2} - HS s' p' v' {4}
          + 3 * HS s' p' v' {0, 1} + HS s' p' v' {0, 3} + HS s' p' v' {0, 4} + HS s' p' v' {1, 2}
          - HS s' p' v' {1, 3} + 2 * HS s' p' v' {1, 4} + HS s' p' v' {2, 3} - HS s' p' v' {0, 1, 2}
          - 3 * HS s' p' v' {0, 1, 4} - HS s' p' v' {0, 2, 3} + HS s' p' v' {0, 2, 4}) := by linarith
      simp only [Bool.not_true, if_true, Bool.false_eq_true, if_false] at IH ⊢
      simp only [P0, P1, P2, P4, P01, P02, P03, P04, P12, P13, P14, P23, P012, P013, P014] at IH
      simp only [F0, F1, F2, F01, F02, F03, F12, F13, F23, F012, F023, F4, F04, F14, F014] at IH hi hkii
      push_cast
      linarith only [IH, hi, hkii]

end NonShannon

end SumsDifferences
