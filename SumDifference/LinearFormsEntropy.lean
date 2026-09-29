module

/-
# Joint entropies of linear forms in two independent coupled pairs

Let `Γ ⊆ G × G` be a nonempty set of pairs with pairwise distinct differences (one representative
pair per difference).  On `Ω = Γ × Γ` with the uniform product law, the four coordinates
`X₁, Y₁, X₂, Y₂` of `q = ((X₁, Y₁), (X₂, Y₂))` are two independent copies of the coupled pair.
For a list `l` of integer coefficient vectors `c = (c₁, c₂, c₃, c₄)` we write

  `HL Γ l = H((c₁X₁ + c₂Y₁ + c₃X₂ + c₄Y₂)_{c ∈ l})`

for the joint entropy of the corresponding linear forms (written `𝐇[F]` in §3.3 of
the proof paper).  This file provides the entropy calculus used by the two-copy
inequality (Proposition 4.1, `SumDifference/ThetaTwoCopyLemma.lean`):

* `HL_eq_of_det`: two lists of forms that determine each other have the same joint entropy,
  where "determine" (`Det`) is witnessed by integer linear combinations, possibly using that
  `X₁ - Y₁` determines `(X₁, Y₁)` and `X₂ - Y₂` determines `(X₂, Y₂)` (`Det.gen`; rules (R1),
  (R2));
* `HL_submod`: submodularity (fact (E3));
* `HL_swap`: invariance under exchanging the two pairs (rule (R3));
* `HL_indep`, `HL_pair1`, `HL_pair2`, `HL_nil`: rules (R4), (R5);
* `HL_X1`, …, `HL_Y1Y2`: identification of single forms with the convolution entropies
  `h(i, j) = ent (μ^i ν^j)` of `SumDifference/CoupledEntropyCore.lean` (rule (R6));
* `HL_X1Y1_le`: the support bound `H(X₁ + Y₁) ≤ log |X + Y|` (rule (R7));
* `HS_eq_HL`: the bridge from the five-variable set function `HS` of
  `SumDifference/MatusInequality.lean` to `HL`.
-/
public import Mathlib
public import SumDifference.MatusInequality
public import SumDifference.CoupledEntropyCore
public import SumDifference.EntropyCompute

@[expose] public section

open Finset Pointwise

namespace SumsDifferences

namespace CoupledForms

open CoupledEntropy NonShannon

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Integer coefficient vectors for the forms `c₁X₁ + c₂Y₁ + c₃X₂ + c₄Y₂`. -/
abbrev V4 := ℤ × ℤ × ℤ × ℤ

/-- The value of a linear form at `q = ((X₁, Y₁), (X₂, Y₂))`. -/
def form (c : V4) (q : (G × G) × (G × G)) : G :=
  c.1 • q.1.1 + c.2.1 • q.1.2 + c.2.2.1 • q.2.1 + c.2.2.2 • q.2.2

omit [DecidableEq G] in
theorem form_add (c d : V4) (q : (G × G) × (G × G)) : form (c + d) q = form c q + form d q := by
  simp only [form, Prod.fst_add, Prod.snd_add, add_smul]; abel

omit [DecidableEq G] in
theorem form_smul (a : ℤ) (c : V4) (q : (G × G) × (G × G)) : form (a • c) q = a • form c q := by
  simp only [form, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_smul, smul_add]

omit [DecidableEq G] in
theorem form_zero (q : (G × G) × (G × G)) : form 0 q = 0 := by simp [form]

/-- Integer linear combination of coefficient vectors. -/
def lc (m : List ℤ) (l : List V4) : V4 := (List.zipWith (fun a c => a • c) m l).sum

/-- Integer linear combination of values. -/
def lcv (m : List ℤ) (x : List G) : G := (List.zipWith (fun a y => a • y) m x).sum

omit [DecidableEq G] in
theorem form_lc (m : List ℤ) (l : List V4) (q : (G × G) × (G × G)) :
    form (lc m l) q = lcv m (l.map fun c => form c q) := by
  induction m generalizing l with
  | nil => simp [lc, lcv, form_zero]
  | cons a m ih =>
    cases l with
    | nil => simp [lc, lcv, form_zero]
    | cons c l =>
      simp only [lc, lcv, List.zipWith_cons_cons, List.sum_cons, List.map_cons] at ih ⊢
      rw [form_add, form_smul, ih]

/-- The uniform product law on `Γ × Γ`. -/
noncomputable def pw (Γ : Finset (G × G)) : (G × G) × (G × G) → ℝ :=
  productLaw (fun _ => (#Γ : ℝ)⁻¹) (fun _ => (#Γ : ℝ)⁻¹)

omit [AddCommGroup G] [DecidableEq G] in
theorem pw_nonneg (Γ : Finset (G × G)) : ∀ q ∈ Γ ×ˢ Γ, 0 ≤ pw Γ q :=
  productLaw_nonneg (fun _ _ => by positivity) (fun _ _ => by positivity)

omit [AddCommGroup G] [DecidableEq G] in
theorem pw_sum {Γ : Finset (G × G)} (hΓ : Γ.Nonempty) : ∑ q ∈ Γ ×ˢ Γ, pw Γ q = 1 :=
  productLaw_sum (uniform_sum hΓ) (uniform_sum hΓ)

/-- Joint entropy of a list of linear forms. -/
noncomputable def HL (Γ : Finset (G × G)) (l : List V4) : ℝ :=
  pushEntropy (Γ ×ˢ Γ) (pw Γ) (fun q => l.map fun c => form c q)

/-- `l` determines the form `f` on `Γ × Γ`. -/
def Det (Γ : Finset (G × G)) (l : List V4) (f : V4) : Prop :=
  ∃ φ : List G → G, ∀ q ∈ Γ ×ˢ Γ, φ (l.map fun c => form c q) = form f q

/-- **Mutual determination**: equal joint entropies. -/
theorem HL_eq_of_det {Γ : Finset (G × G)} {l₁ l₂ : List V4}
    (h₁₂ : ∀ f ∈ l₂, Det Γ l₁ f) (h₂₁ : ∀ f ∈ l₁, Det Γ l₂ f) : HL Γ l₁ = HL Γ l₂ := by
  classical
  refine pushEntropy_eq_of_comp (pw_nonneg Γ)
    (fun y => l₂.map fun f => if h : Det Γ l₁ f then h.choose y else 0)
    (fun y => l₁.map fun f => if h : Det Γ l₂ f then h.choose y else 0) ?_ ?_
  · intro q hq
    refine List.map_congr_left fun f hf => ?_
    rw [dif_pos (h₁₂ f hf)]
    exact (h₁₂ f hf).choose_spec q hq
  · intro q hq
    refine List.map_congr_left fun f hf => ?_
    rw [dif_pos (h₂₁ f hf)]
    exact (h₂₁ f hf).choose_spec q hq

/-- The pair of a difference in `Γ` (by choice; correct on `Γ` by injectivity). -/
noncomputable def rep (Γ : Finset (G × G)) (d : G) : G × G :=
  if h : ∃ p ∈ Γ, p.1 - p.2 = d then h.choose else 0

theorem rep_eq {Γ : Finset (G × G)} (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q')
    {p : G × G} (hp : p ∈ Γ) : rep Γ (p.1 - p.2) = p := by
  have h : ∃ p' ∈ Γ, p'.1 - p'.2 = p.1 - p.2 := ⟨p, hp, rfl⟩
  rw [rep, dif_pos h]
  exact hinj _ h.choose_spec.1 _ hp h.choose_spec.2

/-- **General determination witness**: `f = Σ mₖ lₖ + a X₁ + b Y₁ + c X₂ + e Y₂`, where
`X₁, Y₁` may be used only if `X₁ - Y₁` is an integer combination of `l`, and similarly for the
second pair. -/
theorem Det.gen {Γ : Finset (G × G)}
    (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q')
    {l : List V4} {f : V4} (m m₁ m₂ : List ℤ) (a b c e : ℤ)
    (hf : f = lc m l + (a, b, c, e))
    (h₁ : (a = 0 ∧ b = 0) ∨ lc m₁ l = (1, -1, 0, 0))
    (h₂ : (c = 0 ∧ e = 0) ∨ lc m₂ l = (0, 0, 1, -1)) : Det Γ l f := by
  refine ⟨fun y => lcv m y + a • (rep Γ (lcv m₁ y)).1 + b • (rep Γ (lcv m₁ y)).2
      + c • (rep Γ (lcv m₂ y)).1 + e • (rep Γ (lcv m₂ y)).2, fun q hq => ?_⟩
  obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hq
  set y := l.map fun c => form c q with hy
  set R1 := rep Γ (lcv m₁ y)
  set R2 := rep Γ (lcv m₂ y)
  have k1 : a • R1.1 + b • R1.2 = a • q.1.1 + b • q.1.2 := by
    rcases h₁ with ⟨rfl, rfl⟩ | h₁
    · simp
    · have : lcv m₁ y = q.1.1 - q.1.2 := by
        rw [hy, ← form_lc, h₁]; simp [form, sub_eq_add_neg]
      simp only [R1, this, rep_eq hinj hq1]
  have k2 : c • R2.1 + e • R2.2 = c • q.2.1 + e • q.2.2 := by
    rcases h₂ with ⟨rfl, rfl⟩ | h₂
    · simp
    · have : lcv m₂ y = q.2.1 - q.2.2 := by
        rw [hy, ← form_lc, h₂]; simp [form, sub_eq_add_neg]
      simp only [R2, this, rep_eq hinj hq2]
  have hform : form ((a, b, c, e) : V4) q = a • q.1.1 + b • q.1.2 + c • q.2.1 + e • q.2.2 := rfl
  show lcv m y + a • R1.1 + b • R1.2 + c • R2.1 + e • R2.2 = form f q
  rw [hf, form_add, form_lc, ← hy, hform]
  calc lcv m y + a • R1.1 + b • R1.2 + c • R2.1 + e • R2.2
      = lcv m y + (a • R1.1 + b • R1.2) + (c • R2.1 + e • R2.2) := by abel
    _ = lcv m y + (a • q.1.1 + b • q.1.2 + c • q.2.1 + e • q.2.2) := by rw [k1, k2]; abel

omit [DecidableEq G] in
/-- Linear determination (no pair closure). -/
theorem Det.lin {Γ : Finset (G × G)} {l : List V4} {f : V4} (m : List ℤ) (hf : f = lc m l) :
    Det Γ l f :=
  ⟨fun y => lcv m y, fun q _ => by rw [hf, form_lc]⟩

/-! ## Tuples of lists -/

theorem HL_pair (Γ : Finset (G × G)) (l₁ l₂ : List V4) :
    pushEntropy (Γ ×ˢ Γ) (pw Γ) (fun q => (l₁.map fun c => form c q, l₂.map fun c => form c q))
      = HL Γ (l₁ ++ l₂) := by
  refine pushEntropy_eq_of_comp (pw_nonneg Γ) (fun x => x.1 ++ x.2)
    (fun y => (y.take l₁.length, y.drop l₁.length)) ?_ ?_
  · intro q _; simp [List.map_append]
  · intro q _
    simp only [List.map_append]
    refine Prod.ext ?_ ?_
    · simp
    · simp

theorem HL_triple (Γ : Finset (G × G)) (l₁ l₂ l₃ : List V4) :
    pushEntropy (Γ ×ˢ Γ) (pw Γ) (fun q => (l₁.map fun c => form c q, l₂.map fun c => form c q,
      l₃.map fun c => form c q)) = HL Γ (l₁ ++ l₂ ++ l₃) := by
  refine pushEntropy_eq_of_comp (pw_nonneg Γ) (fun x => x.1 ++ x.2.1 ++ x.2.2)
    (fun y => (y.take l₁.length, (y.drop l₁.length).take l₂.length,
      y.drop (l₁.length + l₂.length))) ?_ ?_
  · intro q _; simp [List.map_append]
  · intro q _
    simp only [List.map_append, List.append_assoc]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp
    · simp
    · simp [List.drop_append]

/-- **Submodularity** for lists of forms: `H(A, B, C) + H(B) ≤ H(A, B) + H(B, C)`. -/
theorem HL_submod {Γ : Finset (G × G)} (hΓ : Γ.Nonempty) (l₁ l₂ l₃ : List V4) :
    HL Γ (l₁ ++ l₂ ++ l₃) + HL Γ l₂ ≤ HL Γ (l₁ ++ l₂) + HL Γ (l₂ ++ l₃) := by
  have h := pushEntropy_submodular (pw_nonneg Γ) (pw_sum hΓ) (fun q => l₁.map fun c => form c q)
    (fun q => l₂.map fun c => form c q) (fun q => l₃.map fun c => form c q)
  rw [HL_triple, HL_pair, HL_pair] at h
  exact h

theorem HL_nil (Γ : Finset (G × G)) (hΓ : Γ.Nonempty) : HL Γ [] = 0 := by
  classical
  refine le_antisymm ?_ (pushEntropy_nonneg (pw_nonneg Γ) (pw_sum hΓ))
  have := pushEntropy_le_log_card (s := Γ ×ˢ Γ) (p := pw Γ)
    (f := fun q => ([] : List V4).map fun c => form c q) (t := {[]}) (pw_nonneg Γ) (pw_sum hΓ)
    (fun q _ => by simp)
  simpa [HL] using this

/-! ## Exchanging the two pairs -/

/-- Exchange of the two pairs on coefficient vectors. -/
def sw4 (c : V4) : V4 := (c.2.2.1, c.2.2.2, c.1, c.2.1)

theorem HL_swap (Γ : Finset (G × G)) (l : List V4) : HL Γ (l.map sw4) = HL Γ l := by
  classical
  have hinjs : Set.InjOn (Prod.swap : (G × G) × (G × G) → (G × G) × (G × G)) ↑(Γ ×ˢ Γ) :=
    fun a _ b _ h => Prod.swap_injective h
  have himg : (Γ ×ˢ Γ).image Prod.swap = Γ ×ˢ Γ := by
    ext q; simp
  have h := pushEntropy_reindex (p := pw Γ) (p' := pw Γ) Prod.swap hinjs
    (fun q _ => by simp [pw, productLaw]) (fun q => l.map fun c => form c q)
  rw [himg] at h
  unfold HL
  rw [← h]
  congr 1
  funext q
  simp only [List.map_map]
  refine List.map_congr_left fun c _ => ?_
  simp [sw4, form]
  abel

/-! ## Single forms and independent blocks -/

theorem HL_single (Γ : Finset (G × G)) (c : V4) :
    HL Γ [c] = pushEntropy (Γ ×ˢ Γ) (pw Γ) (form c) :=
  pushEntropy_eq_of_comp (pw_nonneg Γ) (fun y => y.headD 0) (fun x => [x])
    (fun _ _ => rfl) (fun _ _ => rfl)

theorem HL_X1 {Γ : Finset (G × G)} (hΓ : Γ.Nonempty) : HL Γ [(1, 0, 0, 0)] = ent (margFst Γ) := by
  rw [HL_single]
  have e : (form ((1, 0, 0, 0) : V4) : (G × G) × (G × G) → G) = fun q => Prod.fst q.1 := by
    funext q; simp [form]
  rw [e, pw, pushEntropy_productLaw_fst (fun _ _ => by positivity) (fun _ _ => by positivity)
    (uniform_sum hΓ) (uniform_sum hΓ), pushEntropy_eq_ent (pushWeight_fst_eq_margFst Γ)]

theorem HL_Y1 {Γ : Finset (G × G)} (hΓ : Γ.Nonempty) : HL Γ [(0, 1, 0, 0)] = ent (margSnd Γ) := by
  rw [HL_single]
  have e : (form ((0, 1, 0, 0) : V4) : (G × G) × (G × G) → G) = fun q => Prod.snd q.1 := by
    funext q; simp [form]
  rw [e, pw, pushEntropy_productLaw_fst (fun _ _ => by positivity) (fun _ _ => by positivity)
    (uniform_sum hΓ) (uniform_sum hΓ), pushEntropy_eq_ent (pushWeight_snd_eq_margSnd Γ)]

theorem HL_X2 {Γ : Finset (G × G)} (hΓ : Γ.Nonempty) : HL Γ [(0, 0, 1, 0)] = ent (margFst Γ) := by
  rw [HL_single]
  have e : (form ((0, 0, 1, 0) : V4) : (G × G) × (G × G) → G) = fun q => Prod.fst q.2 := by
    funext q; simp [form]
  rw [e, pw, pushEntropy_productLaw_snd (fun _ _ => by positivity) (fun _ _ => by positivity)
    (uniform_sum hΓ) (uniform_sum hΓ), pushEntropy_eq_ent (pushWeight_fst_eq_margFst Γ)]

theorem HL_Y2 {Γ : Finset (G × G)} (hΓ : Γ.Nonempty) : HL Γ [(0, 0, 0, 1)] = ent (margSnd Γ) := by
  rw [HL_single]
  have e : (form ((0, 0, 0, 1) : V4) : (G × G) × (G × G) → G) = fun q => Prod.snd q.2 := by
    funext q; simp [form]
  rw [e, pw, pushEntropy_productLaw_snd (fun _ _ => by positivity) (fun _ _ => by positivity)
    (uniform_sum hΓ) (uniform_sum hΓ), pushEntropy_eq_ent (pushWeight_snd_eq_margSnd Γ)]

theorem HL_X1Y2 (Γ : Finset (G × G)) :
    HL Γ [(1, 0, 0, 1)] = ent (margFst Γ * margSnd Γ) := by
  rw [HL_single]
  have e : (form ((1, 0, 0, 1) : V4) : (G × G) × (G × G) → G) = fun q => q.1.1 + q.2.2 := by
    funext q; simp [form]
  rw [e]
  exact pushEntropy_eq_ent (pushWeight_add_eq_mul (F₁ := Prod.fst) (F₂ := Prod.snd)
    (pushWeight_fst_eq_margFst Γ) (pushWeight_snd_eq_margSnd Γ))

theorem HL_Y1X2 (Γ : Finset (G × G)) :
    HL Γ [(0, 1, 1, 0)] = ent (margFst Γ * margSnd Γ) := by
  rw [HL_single]
  have e : (form ((0, 1, 1, 0) : V4) : (G × G) × (G × G) → G) = fun q => q.1.2 + q.2.1 := by
    funext q; simp [form]
  rw [e, mul_comm]
  exact pushEntropy_eq_ent (pushWeight_add_eq_mul (F₁ := Prod.snd) (F₂ := Prod.fst)
    (pushWeight_snd_eq_margSnd Γ) (pushWeight_fst_eq_margFst Γ))

theorem HL_X1X2 (Γ : Finset (G × G)) :
    HL Γ [(1, 0, 1, 0)] = ent (margFst Γ * margFst Γ) := by
  rw [HL_single]
  have e : (form ((1, 0, 1, 0) : V4) : (G × G) × (G × G) → G) = fun q => q.1.1 + q.2.1 := by
    funext q; simp [form]
  rw [e]
  exact pushEntropy_eq_ent (pushWeight_add_eq_mul (F₁ := Prod.fst) (F₂ := Prod.fst)
    (pushWeight_fst_eq_margFst Γ) (pushWeight_fst_eq_margFst Γ))

theorem HL_Y1Y2 (Γ : Finset (G × G)) :
    HL Γ [(0, 1, 0, 1)] = ent (margSnd Γ * margSnd Γ) := by
  rw [HL_single]
  have e : (form ((0, 1, 0, 1) : V4) : (G × G) × (G × G) → G) = fun q => q.1.2 + q.2.2 := by
    funext q; simp [form]
  rw [e]
  exact pushEntropy_eq_ent (pushWeight_add_eq_mul (F₁ := Prod.snd) (F₂ := Prod.snd)
    (pushWeight_snd_eq_margSnd Γ) (pushWeight_snd_eq_margSnd Γ))

/-- The dependent sum `X₁ + Y₁` takes values in `X + Y`. -/
theorem HL_X1Y1_le {Γ : Finset (G × G)} (hΓ : Γ.Nonempty) {X Y : Finset G} (hXY : Γ ⊆ X ×ˢ Y) :
    HL Γ [(1, 1, 0, 0)] ≤ Real.log #(X + Y) := by
  rw [HL_single]
  refine pushEntropy_le_log_card (pw_nonneg Γ) (pw_sum hΓ) fun q hq => ?_
  have h1 := hXY (Finset.mem_product.mp hq).1
  simp only [form, one_smul, zero_smul, add_zero]
  exact Finset.add_mem_add (Finset.mem_product.mp h1).1 (Finset.mem_product.mp h1).2

/-- Independence of the two pairs: `H(F(pair 1), F'(pair 2)) = H(F) + H(F')` for forms supported
on one pair each. -/
theorem HL_indep {Γ : Finset (G × G)} (hΓ : Γ.Nonempty) (l₁ l₂ : List V4)
    (h₁ : ∀ c ∈ l₁, c.2.2 = (0, 0)) (h₂ : ∀ c ∈ l₂, c.1 = 0 ∧ c.2.1 = 0) :
    HL Γ (l₁ ++ l₂) = HL Γ l₁ + HL Γ l₂ := by
  have hu : ∀ q ∈ Γ, 0 ≤ (fun _ => (#Γ : ℝ)⁻¹) q := fun _ _ => by positivity
  have key := pushEntropy_productLaw_pair hu hu (uniform_sum hΓ) (uniform_sum hΓ)
    (fun p : G × G => l₁.map fun c => form c (p, (0 : G × G)))
    (fun p : G × G => l₂.map fun c => form c ((0 : G × G), p))
  have f1 : ∀ q : (G × G) × (G × G), ∀ c ∈ l₁, form c q = form c (q.1, (0 : G × G)) := by
    intro q c hc; have := h₁ c hc; simp only [form, Prod.fst_zero, Prod.snd_zero, smul_zero,
      add_zero]; rw [show c.2.2 = (0, 0) from this]; simp
  have f2 : ∀ q : (G × G) × (G × G), ∀ c ∈ l₂, form c q = form c ((0 : G × G), q.2) := by
    intro q c hc; have := h₂ c hc; simp only [form, Prod.fst_zero, Prod.snd_zero, smul_zero,
      zero_add]; rw [this.1, this.2]; simp
  have e1 : HL Γ l₁ = pushEntropy (Γ ×ˢ Γ) (pw Γ)
      (fun q => l₁.map fun c => form c (q.1, (0 : G × G))) := by
    unfold HL; congr 1; funext q; exact List.map_congr_left (f1 q)
  have e2 : HL Γ l₂ = pushEntropy (Γ ×ˢ Γ) (pw Γ)
      (fun q => l₂.map fun c => form c ((0 : G × G), q.2)) := by
    unfold HL; congr 1; funext q; exact List.map_congr_left (f2 q)
  rw [e1, e2, pw, pushEntropy_productLaw_fst hu hu (uniform_sum hΓ) (uniform_sum hΓ)
    (fun p : G × G => l₁.map fun c => form c (p, (0 : G × G))),
    pushEntropy_productLaw_snd hu hu (uniform_sum hΓ) (uniform_sum hΓ)
    (fun p : G × G => l₂.map fun c => form c ((0 : G × G), p)), ← key, ← HL_pair]
  unfold pw
  congr 1
  funext q
  exact Prod.ext (List.map_congr_left (f1 q)) (List.map_congr_left (f2 q))

/-- The coupled pair itself has entropy `log #Γ`. -/
theorem HL_pair1 {Γ : Finset (G × G)} (hΓ : Γ.Nonempty) :
    HL Γ [(1, 0, 0, 0), (0, 1, 0, 0)] = Real.log #Γ := by
  have hu : ∀ q ∈ Γ, 0 ≤ (fun _ => (#Γ : ℝ)⁻¹) q := fun _ _ => by positivity
  have e : HL Γ [(1, 0, 0, 0), (0, 1, 0, 0)]
      = pushEntropy (Γ ×ˢ Γ) (pw Γ) (fun q => (id q.1 : G × G)) :=
    pushEntropy_eq_of_comp (pw_nonneg Γ) (fun y => (y.headD 0, y.getD 1 0)) (fun p => [p.1, p.2])
      (fun q _ => by simp [form]) (fun q _ => by simp [form])
  rw [e, pw, pushEntropy_productLaw_fst hu hu (uniform_sum hΓ) (uniform_sum hΓ)]
  exact pushEntropy_unif_of_injOn (f := id) (fun a _ b _ h => h)

theorem HL_pair2 {Γ : Finset (G × G)} (hΓ : Γ.Nonempty) :
    HL Γ [(0, 0, 1, 0), (0, 0, 0, 1)] = Real.log #Γ := by
  have := HL_swap Γ [(1, 0, 0, 0), (0, 1, 0, 0)]
  simp only [List.map_cons, List.map_nil, sw4] at this
  rw [this, HL_pair1 hΓ]

/-! ## Bridge to the five-variable set function -/

omit [DecidableEq G] in
theorem lookup_zip_map {α : Type*} [DecidableEq α] (L : List α) (g : α → G) {j : α} (hj : j ∈ L) :
    ((L.zip (L.map g)).lookup j).getD 0 = g j := by
  induction L with
  | nil => simp at hj
  | cons x L ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.lookup_cons]
    by_cases h : j = x
    · subst h; simp
    · have hj' : j ∈ L := by simpa [h] using hj
      have : (j == x) = false := by simpa using h
      rw [this]; exact ih hj'

/-- `HS` of the forms `cv 0, …, cv 4` on a subfamily listed by `Ls` equals `HL` of those forms. -/
theorem HS_eq_HL (Γ : Finset (G × G)) (cv : Fin 5 → V4) (Ls : List (Fin 5)) :
    HS (Γ ×ˢ Γ) (pw Γ) (fun j q => form (cv j) q) Ls.toFinset = HL Γ (Ls.map cv) := by
  classical
  refine pushEntropy_eq_of_comp (pw_nonneg Γ) (fun t => Ls.map t)
    (fun y => fun j => if j ∈ Ls.toFinset then ((Ls.zip y).lookup j).getD 0 else 0) ?_ ?_
  · intro q _
    simp only [List.map_map]
    refine List.map_congr_left fun j hj => ?_
    simp [hj]
  · intro q _
    funext j
    by_cases hj : j ∈ Ls
    · simp only [List.mem_toFinset, hj, if_true, List.map_map]
      exact lookup_zip_map Ls (fun j => form (cv j) q) hj
    · simp [hj]


/-- **Monotonicity**: adding forms does not decrease the joint entropy. -/
theorem HL_mono (Γ : Finset (G × G)) (l₁ l₂ : List V4) : HL Γ l₁ ≤ HL Γ (l₁ ++ l₂) := by
  have h := pushEntropy_comp_le (pw_nonneg Γ) (fun q => (l₁ ++ l₂).map fun c => form c q)
    (fun y => y.take l₁.length)
  simpa [HL, List.map_append] using h


omit [DecidableEq G] in
/-- A member of `l` is determined by `l`. -/
theorem Det.mem {Γ : Finset (G × G)} {l : List V4} {f : V4} (hf : f ∈ l) : Det Γ l f :=
  letI : BEq V4 := instBEqOfDecidableEq
  ⟨fun y => ((l.zip y).lookup f).getD 0, fun q _ => lookup_zip_map l (fun c => form c q) hf⟩

/-- Appending forms determined by `l₁` does not change the joint entropy. -/
theorem HL_append_det {Γ : Finset (G × G)} {l₁ l₂ : List V4} (h : ∀ f ∈ l₂, Det Γ l₁ f) :
    HL Γ (l₁ ++ l₂) = HL Γ l₁ :=
  HL_eq_of_det (fun f hf => Det.mem (List.mem_append_left _ hf)) fun f hf => by
    rcases List.mem_append.mp hf with h' | h'
    · exact Det.mem h'
    · exact h f h'

end CoupledForms

end SumsDifferences
