/-
# Joint (pair-valued) variables for the five-variable set function

`HS_eq_HL2`: the five-variable set function `HS` of pair-valued variables
`q ↦ (form (cv₁ j) q, form (cv₂ j) q)` equals the joint entropy `HL` of all the forms involved.
This lets the non-Shannon inequalities (Theorems 4.4 and 4.5 of the proof paper)
be applied to joint variables such as the pair `(X₁, Y₂)`, as in several rows of Table 2.
-/
import Mathlib
import SumDifference.LinearFormsEntropy

open Finset

namespace SumsDifferences

namespace CoupledForms

open NonShannon

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
theorem lookup_zip_eq {α β : Type*} [DecidableEq α] [Zero β] (L : List α) (g : α → β) {j : α}
    (hj : j ∈ L) : ((L.zip (L.map g)).lookup j).getD 0 = g j := by
  induction L with
  | nil => simp at hj
  | cons x L ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.lookup_cons]
    by_cases h : j = x
    · subst h; simp
    · have hj' : j ∈ L := by simpa [h] using hj
      have : (j == x) = false := by simpa using h
      rw [this]; exact ih hj'

/-- `HS` of the pair-valued variables `(cv₁ j, cv₂ j)` on a subfamily listed by `Ls` equals `HL` of
the forms `cv₁ j` followed by the forms `cv₂ j`, `j ∈ Ls`. -/
theorem HS_eq_HL2 (Γ : Finset (G × G)) (cv₁ cv₂ : Fin 5 → V4) (Ls : List (Fin 5)) :
    HS (Γ ×ˢ Γ) (pw Γ) (fun j q => (form (cv₁ j) q, form (cv₂ j) q)) Ls.toFinset
      = HL Γ (Ls.map cv₁ ++ Ls.map cv₂) := by
  classical
  refine pushEntropy_eq_of_comp (pw_nonneg Γ)
    (fun t => Ls.map (fun j => (t j).1) ++ Ls.map (fun j => (t j).2))
    (fun y => fun j => if j ∈ Ls.toFinset then
      (((Ls.zip (y.take Ls.length)).lookup j).getD 0,
       ((Ls.zip (y.drop Ls.length)).lookup j).getD 0) else 0) ?_ ?_
  · intro q _
    simp only [List.map_append, List.map_map]
    congr 1
    · refine List.map_congr_left fun j hj => ?_
      simp [hj]
    · refine List.map_congr_left fun j hj => ?_
      simp [hj]
  · intro q _
    funext j
    by_cases hj : j ∈ Ls
    · simp only [List.mem_toFinset, hj, if_true, List.map_map, List.map_append]
      rw [List.take_left' (by simp), List.drop_left' (by simp)]
      refine Prod.ext ?_ ?_
      · exact lookup_zip_eq Ls (fun j => form (cv₁ j) q) hj
      · exact lookup_zip_eq Ls (fun j => form (cv₂ j) q) hj
    · simp [hj]

/-- Width-four version of `HS_eq_HL2`: variables `((cv₁ j, cv₂ j), (cv₃ j, cv₄ j))`. -/
theorem HS_eq_HL4 (Γ : Finset (G × G)) (cv₁ cv₂ cv₃ cv₄ : Fin 5 → V4) (Ls : List (Fin 5)) :
    HS (Γ ×ˢ Γ) (pw Γ)
        (fun j q => ((form (cv₁ j) q, form (cv₂ j) q), (form (cv₃ j) q, form (cv₄ j) q))) Ls.toFinset
      = HL Γ (Ls.map cv₁ ++ Ls.map cv₂ ++ Ls.map cv₃ ++ Ls.map cv₄) := by
  classical
  set n := Ls.length
  refine pushEntropy_eq_of_comp (pw_nonneg Γ)
    (fun t => Ls.map (fun j => (t j).1.1) ++ Ls.map (fun j => (t j).1.2) ++
      Ls.map (fun j => (t j).2.1) ++ Ls.map (fun j => (t j).2.2))
    (fun y => fun j => if j ∈ Ls.toFinset then
      ((((Ls.zip (y.take n)).lookup j).getD 0,
        ((Ls.zip ((y.drop n).take n)).lookup j).getD 0),
       (((Ls.zip ((y.drop (n + n)).take n)).lookup j).getD 0,
        ((Ls.zip (y.drop (n + n + n))).lookup j).getD 0)) else 0) ?_ ?_
  · intro q _
    simp only [List.map_append, List.map_map]
    congr 1; congr 1; congr 1
    all_goals
      refine List.map_congr_left fun j hj => ?_
      simp [hj]
  · intro q _
    funext j
    by_cases hj : j ∈ Ls
    · simp only [List.mem_toFinset, hj, if_true, List.map_map, List.map_append, List.append_assoc]
      have e1 : ∀ (u v w x : List G), u.length = n →
          (u ++ (v ++ (w ++ x))).take n = u := fun u v w x hu => List.take_left' hu
      have e2 : ∀ (u v w x : List G), u.length = n → v.length = n →
          ((u ++ (v ++ (w ++ x))).drop n).take n = v := fun u v w x hu hv => by
        rw [List.drop_left' hu, List.take_left' hv]
      have e3 : ∀ (u v w x : List G), u.length = n → v.length = n → w.length = n →
          ((u ++ (v ++ (w ++ x))).drop (n + n)).take n = w := fun u v w x hu hv hw => by
        rw [← List.drop_drop, List.drop_left' hu, List.drop_left' hv, List.take_left' hw]
      have e4 : ∀ (u v w x : List G), u.length = n → v.length = n → w.length = n →
          (u ++ (v ++ (w ++ x))).drop (n + n + n) = x := fun u v w x hu hv hw => by
        rw [← List.drop_drop, ← List.drop_drop, List.drop_left' hu, List.drop_left' hv,
          List.drop_left' hw]
      rw [e1 _ _ _ _ (by simp [n]), e2 _ _ _ _ (by simp [n]) (by simp [n]),
        e3 _ _ _ _ (by simp [n]) (by simp [n]) (by simp [n]),
        e4 _ _ _ _ (by simp [n]) (by simp [n]) (by simp [n])]
      refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
      · exact lookup_zip_eq Ls (fun j => form (cv₁ j) q) hj
      · exact lookup_zip_eq Ls (fun j => form (cv₂ j) q) hj
      · exact lookup_zip_eq Ls (fun j => form (cv₃ j) q) hj
      · exact lookup_zip_eq Ls (fun j => form (cv₄ j) q) hj
    · simp [hj]

end CoupledForms

end SumsDifferences
