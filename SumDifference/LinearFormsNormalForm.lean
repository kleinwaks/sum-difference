/-
# One normal-form lemma for determination

`HL Γ l` (`SumDifference/LinearFormsEntropy.lean`) is the joint entropy of the integer linear forms
`l` in two independent copies `(X₁, Y₁)`, `(X₂, Y₂)` of a coupled pair.  It depends only on the
lattice spanned by `l`, closed under "`X_k − Y_k` gives `(X_k, Y_k)`" (the differences in `Γ` are
distinct), and it is invariant under exchanging the copies: rules (R1)–(R3) of §4.3 of
the proof paper.

This file turns that into **one lemma**, `HL_eq_norm`: `HL Γ l₁ = HL Γ l₂` whenever the Boolean
`hlEq l₁ l₂` evaluates to `true`.  `hlEq` runs a small integer-elimination solver (`solve`) that
writes each form of one list as an integer combination of the other list (with `X₁, Y₁` resp.
`X₂, Y₂` added as generators when `X₁ − Y₁` resp. `X₂ − Y₂` lies in its span), in both directions
and, if needed, after exchanging the copies.  The solver is not trusted: its output is re-checked
(`verifyWit`), and only that check enters the soundness proof.  So a use of the lemma is closed by
`decide`, with no witnesses written out.
-/
import Mathlib
import SumDifference.LinearFormsEntropy

namespace SumsDifferences

namespace CoupledForms

/-! ### Computable vector arithmetic on `V4` -/

/-- `v − q • w`, componentwise. -/
def vsubq (v w : V4) (q : ℤ) : V4 :=
  (v.1 - q * w.1, v.2.1 - q * w.2.1, v.2.2.1 - q * w.2.2.1, v.2.2.2 - q * w.2.2.2)

/-- Coordinate `k` of a vector. -/
def col (k : ℕ) (v : V4) : ℤ :=
  match k with
  | 0 => v.1
  | 1 => v.2.1
  | 2 => v.2.2.1
  | _ => v.2.2.2

/-- Integer combination `Σ mᵢ lᵢ`, computed componentwise. -/
def lcI : List ℤ → List V4 → V4
  | a :: m, c :: l =>
    let r := lcI m l
    (a * c.1 + r.1, a * c.2.1 + r.2.1, a * c.2.2.1 + r.2.2.1, a * c.2.2.2 + r.2.2.2)
  | _, _ => (0, 0, 0, 0)

theorem lcI_eq_lc (m : List ℤ) (l : List V4) : lcI m l = lc m l := by
  induction m generalizing l with
  | nil => cases l <;> rfl
  | cons a m ih =>
    cases l with
    | nil => rfl
    | cons c l =>
      simp only [lcI, lc, List.zipWith_cons_cons, List.sum_cons]
      rw [ih l]
      rfl

/-! ### The (untrusted) solver -/

/-- A solver row: a vector together with its coefficients with respect to the input list. -/
abbrev SRow := V4 × List ℤ

/-- Euclid's algorithm on column `k`: returns a pivot row (the only row with a nonzero entry in
column `k`, if any) and the remaining rows, all zero in column `k`.  `fuel` bounds the work; running
out of fuel only makes the solver fail, never unsound. -/
def euclid (k : ℕ) : ℕ → List SRow → Option SRow × List SRow
  | 0, rs => (none, rs.filter fun r => col k r.1 == 0)
  | fuel + 1, rs =>
    let nz := rs.filter fun r => col k r.1 != 0
    let z := rs.filter fun r => col k r.1 == 0
    match nz with
    | [] => (none, z)
    | [p] => (some p, z)
    | r0 :: rest =>
      let p := rest.foldl (fun a b => if (col k b.1).natAbs < (col k a.1).natAbs then b else a) r0
      let others := (nz.erase p).map fun r =>
        let q := col k r.1 / col k p.1
        (vsubq r.1 p.1 q, List.zipWith (fun x y => x - q * y) r.2 p.2)
      euclid k fuel (p :: others ++ z)

/-- Echelon form (with coefficient tracking) of the rows, column by column: a list of
`(column, pivot row)`. -/
def echelon : List ℕ → List SRow → List (ℕ × SRow)
  | [], _ => []
  | k :: ks, rs =>
    match euclid k 40 rs with
    | (none, rest) => echelon ks rest
    | (some p, rest) => (k, p) :: echelon ks rest

/-- Reduce the target `g` (with accumulated coefficients `c`) along an echelon basis. -/
def reduceT : List (ℕ × SRow) → V4 × List ℤ → Option (List ℤ)
  | [], (g, c) => if g = (0, 0, 0, 0) then some c else none
  | (k, p) :: bs, (g, c) =>
    let d := col k p.1
    if col k g % d = 0 then
      let q := col k g / d
      reduceT bs (vsubq g p.1 q, List.zipWith (fun x y => x + q * y) c p.2)
    else none

/-- Solver rows for a list `l`: each form with its unit coefficient vector. -/
def initRows (l : List V4) : List SRow :=
  let n := l.length
  (List.range n).zip l |>.map fun (i, v) => (v, (List.range n).map fun j => if j = i then 1 else 0)

/-- Try to write `g` as an integer combination of `l`. -/
def solve (l : List V4) (g : V4) : Option (List ℤ) :=
  reduceT (echelon [0, 1, 2, 3] (initRows l)) (g, List.replicate l.length 0)

/-- Precomputed data for a list `l`: the witnesses `m₁`, `m₂` for `X₁ − Y₁`, `X₂ − Y₂` (if they
lie in the span of `l`) and the echelon basis of `l` extended by the generators they allow. -/
structure Prep where
  n : ℕ
  m1 : Option (List ℤ)
  m2 : Option (List ℤ)
  basis : List (ℕ × SRow)
  len : ℕ

def prep (l : List V4) : Prep :=
  let m1 := solve l (1, -1, 0, 0)
  let m2 := solve l (0, 0, 1, -1)
  let e1 : List V4 := if m1.isSome then [(1, 0, 0, 0), (0, 1, 0, 0)] else []
  let e2 : List V4 := if m2.isSome then [(0, 0, 1, 0), (0, 0, 0, 1)] else []
  let l' := l ++ e1 ++ e2
  ⟨l.length, m1, m2, echelon [0, 1, 2, 3] (initRows l'), l'.length⟩

/-- A candidate witness `(m, m₁, m₂, (a, b, c, e))` for `Det.gen`. -/
def detWitP (P : Prep) (f : V4) : Option (List ℤ × List ℤ × List ℤ × V4) :=
  match reduceT P.basis (f, List.replicate P.len 0) with
  | none => none
  | some k =>
    let r := k.drop P.n
    let ab : ℤ × ℤ := if P.m1.isSome then (r.getD 0 0, r.getD 1 0) else (0, 0)
    let r' := if P.m1.isSome then r.drop 2 else r
    let ce : ℤ × ℤ := if P.m2.isSome then (r'.getD 0 0, r'.getD 1 0) else (0, 0)
    some (k.take P.n, P.m1.getD [], P.m2.getD [], (ab.1, ab.2, ce.1, ce.2))

/-! ### The trusted check and its soundness -/

/-- Checks the hypotheses of `Det.gen` for a candidate witness. -/
def verifyWit (l : List V4) (f : V4) (w : List ℤ × List ℤ × List ℤ × V4) : Bool :=
  let e := w.2.2.2
  let s := lcI w.1 l
  decide (f = (s.1 + e.1, s.2.1 + e.2.1, s.2.2.1 + e.2.2.1, s.2.2.2 + e.2.2.2)) &&
  (decide (e.1 = 0 ∧ e.2.1 = 0) || decide (lcI w.2.1 l = (1, -1, 0, 0))) &&
  (decide (e.2.2.1 = 0 ∧ e.2.2.2 = 0) || decide (lcI w.2.2.1 l = (0, 0, 1, -1)))

/-- `l` determines `f` (computable check, using precomputed data `P` for `l`). -/
def detCheckP (l : List V4) (P : Prep) (f : V4) : Bool :=
  match detWitP P f with
  | some w => verifyWit l f w
  | none => false

/-- `l` determines every form of `l'` (computable check). -/
def detAll (l l' : List V4) : Bool :=
  l'.all (detCheckP l (prep l))

/-- `l₁` and `l₂` determine each other (computable check). -/
def detEq (l₁ l₂ : List V4) : Bool :=
  detAll l₁ l₂ && detAll l₂ l₁

/-- `l₁` and `l₂` determine each other, possibly after exchanging the two copies in `l₂`. -/
def hlEq (l₁ l₂ : List V4) : Bool :=
  detEq l₁ l₂ || detEq l₁ (l₂.map sw4)

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem Det_of_verifyWit {Γ : Finset (G × G)}
    (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q')
    {l : List V4} {f : V4} {w : List ℤ × List ℤ × List ℤ × V4} (h : verifyWit l f w = true) :
    Det Γ l f := by
  obtain ⟨m, m₁, m₂, a, b, c, e⟩ := w
  simp only [verifyWit, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hf, h₁⟩, h₂⟩ := h
  refine Det.gen hinj m m₁ m₂ a b c e ?_ ?_ ?_
  · rw [hf, ← lcI_eq_lc]; rfl
  · rwa [← lcI_eq_lc]
  · rwa [← lcI_eq_lc]

theorem Det_of_detCheckP {Γ : Finset (G × G)}
    (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q')
    {l : List V4} {P : Prep} {f : V4} (h : detCheckP l P f = true) : Det Γ l f := by
  unfold detCheckP at h
  split at h
  · exact Det_of_verifyWit hinj h
  · exact absurd h Bool.false_ne_true

theorem HL_eq_of_detEq {Γ : Finset (G × G)}
    (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q')
    {l₁ l₂ : List V4} (h : detEq l₁ l₂ = true) : HL Γ l₁ = HL Γ l₂ := by
  simp only [detEq, detAll, Bool.and_eq_true, List.all_eq_true] at h
  exact HL_eq_of_det (fun f hf => Det_of_detCheckP hinj (h.1 f hf))
    (fun f hf => Det_of_detCheckP hinj (h.2 f hf))

/-- **Normal-form lemma for determination** (rules (R1)–(R3)).  If `hlEq l₁ l₂` evaluates to
`true`, i.e. the two lists of forms span the same lattice after closing under
"`X_k − Y_k` gives `(X_k, Y_k)`", up to exchanging the copies, then they have the same joint entropy.
Uses are closed by `decide`. -/
theorem HL_eq_norm {Γ : Finset (G × G)}
    (hinj : ∀ q ∈ Γ, ∀ q' ∈ Γ, q.1 - q.2 = q'.1 - q'.2 → q = q')
    {l₁ l₂ : List V4} (h : hlEq l₁ l₂ = true) : HL Γ l₁ = HL Γ l₂ := by
  simp only [hlEq, Bool.or_eq_true] at h
  rcases h with h | h
  · exact HL_eq_of_detEq hinj h
  · rw [← HL_swap Γ l₂]; exact HL_eq_of_detEq hinj h

end CoupledForms

end SumsDifferences
