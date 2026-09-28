module

public import Mathlib

/-!
# The grid lemma (§6 of the proof paper)

A statement about real arrays, proved by an explicit dual certificate valid in every degree:

**Proposition 6.1** (`grid_closed_form`).  Let `h : ℕ → ℕ → ℝ` be nonnegative, concave and nondecreasing
along each axis, with the links `L + h(i,j) ≤ h(i+1,j) + h(i,j+1)`, `h(1,1) ≤ S`, and the symmetric
two-copy inequality
`22882 L ≤ 5820 S + 8694 h(1,1) + 11645 (h(1,0)+h(0,1)) + 685 (h(2,0)+h(0,2))`.
Then `(21512 e + 3148) L ≤ (37804 e − 13144) S`, i.e. `L ≤ λ∞ S` with
`λ∞ = (9451 e − 3286)/(5378 e + 787) ≈ 1.45427744891`.

**Proof.**  Replace `h` by `(h + hᵀ)/2`, so `h` is symmetric (§6.1).  Put
`w_k = Z k = ∫₀¹ t (1−t)^k e^t dt` (Lemma 6.2: `w₀ = 1`, `w₁ = 3 − e`,
`w_{k+2} = (k+4) w_{k+1} − (k+1) w_k`; `w` is nonnegative, nonincreasing, convex and
`w_k ≤ 1/(k+1)`).  For a concave row `f = h(·, j)` put `τ_m = m f(1) − (m−1) f(0) − f(m) ≥ 0`;
then `w_{m+1} τ_{m+2} ≤ w_{m+2} τ_{m+4}` (`psi_nonneg`, Lemma 6.3).  A base combination of the
links at `(0,1)`, `(0,2)`, the rows 1 and 2, `h(1,1) ≤ S` and the two-copy inequality
(`inv_base`), followed for `j = 3, 4, …` by the link at `(0, j)` with weight `w_{j−1} − w_j` and
the row inequality of row `j` (`inv_step`), gives the invariant (6.2)
`(N − w_{m+2}) L ≤ Λ S + (w_{m+1} − w_{m+2}) h(0, m+3) − w_{m+1} h(m+2, m+3)` for every `m`
(`inv_all`, Lemma 6.4), with `N = 1 + 21512 κ`, `Λ = e + 13144 κ`, `κ = (e − 1)/24660`.  Let
`m → ∞` (`grid_closed_sym`).
-/

public section


open Real

namespace SumsDifferences
namespace GridClosedForm

/-- `B(m, k) = ∫₀¹ t^m (1-t)^k e^t dt` (§6.2). -/
noncomputable def B (m k : ℕ) : ℝ := ∫ t in (0:ℝ)..1, t ^ m * (1 - t) ^ k * exp t

lemma B_nonneg (m k : ℕ) : 0 ≤ B m k := by
  unfold B
  apply intervalIntegral.integral_nonneg zero_le_one
  intro t ht
  have h1 : 0 ≤ 1 - t := by linarith [ht.2]
  have h0 : 0 ≤ t := ht.1
  positivity

lemma B_split (m k : ℕ) : B m k = B m (k + 1) + B (m + 1) k := by
  unfold B
  rw [← intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  congr 1; ext t; ring

lemma B_zero_zero : B 0 0 = exp 1 - 1 := by
  unfold B; simp [integral_exp]

lemma B_one_zero : B 1 0 = 1 := by
  unfold B
  have hd : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun t => (t - 1) * exp t) (t ^ 1 * (1 - t) ^ 0 * exp t) t := by
    intro t _
    have := ((hasDerivAt_id t).sub_const 1).mul (hasDerivAt_exp t)
    convert this using 1; simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp

lemma B_zero_succ (k : ℕ) : B 0 (k + 1) = (k + 1) * B 0 k - 1 := by
  have hd : ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun t => (1 - t) ^ (k + 1) * exp t)
      (t ^ 0 * (1 - t) ^ (k + 1) * exp t - (k + 1) * (t ^ 0 * (1 - t) ^ k * exp t)) t := by
    intro t _
    have h1 := ((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).pow (k + 1)
    have := h1.mul (hasDerivAt_exp t)
    convert this using 1; simp; ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (by apply Continuous.intervalIntegrable; fun_prop)
  rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_const_mul] at hint
  unfold B
  simp only [pow_zero, one_mul] at hint ⊢
  norm_num at hint
  linarith


/-- The weights `w_k = Z k = ∫₀¹ t (1-t)^k e^t dt` of Lemma 6.2. -/
noncomputable def Z (k : ℕ) : ℝ := B 1 k

lemma Z_eq (k : ℕ) : Z k = 1 - k * B 0 k := by
  have h1 := B_split 0 k
  have h2 := B_zero_succ k
  unfold Z; linarith

lemma Z_zero : Z 0 = 1 := B_one_zero

lemma Z_one : Z 1 = 3 - exp 1 := by
  have h1 := Z_eq 1
  have h2 := B_zero_succ 0
  have h3 := B_zero_zero
  push_cast at h1 h2
  linarith

lemma Z_rec (k : ℕ) : Z (k + 2) = (k + 4) * Z (k + 1) - (k + 1) * Z k := by
  have e0 := Z_eq k
  have e1 := Z_eq (k + 1)
  have e2 := Z_eq (k + 2)
  have a1 := B_zero_succ k
  have a2 := B_zero_succ (k + 1)
  push_cast at e0 e1 e2 a1 a2
  rw [e0, e1, e2, a2, a1]
  ring

lemma Z_nonneg (k : ℕ) : 0 ≤ Z k := B_nonneg 1 k

lemma Z_succ_le (k : ℕ) : Z (k + 1) ≤ Z k := by
  have := B_split 1 k
  have := B_nonneg 2 k
  unfold Z; linarith

lemma Z_convex (k : ℕ) : 2 * Z (k + 1) ≤ Z k + Z (k + 2) := by
  have h1 := B_split 1 k
  have h2 := B_split 1 (k + 1)
  have h3 := B_split 2 k
  have := B_nonneg 3 k
  unfold Z; linarith

lemma Z_le (k : ℕ) : Z k ≤ 1 / (k + 1) := by
  have hA : 0 ≤ B 0 (k + 1) := B_nonneg 0 (k + 1)
  rw [B_zero_succ] at hA
  rw [Z_eq, le_div_iff₀ (by positivity)]
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

lemma Z_weight (m : ℕ) : (m + 1) * Z (m + 1) ≤ (m + 3) * Z (m + 2) := by
  have hc := Z_convex (m + 1)
  have hr := Z_rec (m + 1)
  push_cast at hr
  linarith

/-! ### Concave sequences -/

/-- Tangent defect `τ_m(f)` of a sequence at `m` (§6.3): `m f(1) - (m-1) f(0) - f(m)` (`≥ 0` if `f` is concave). -/
def tau (f : ℕ → ℝ) (m : ℕ) : ℝ := m * f 1 - (m - 1) * f 0 - f m

lemma tau_succ (f : ℕ → ℝ) (m : ℕ) :
    tau f (m + 1) = tau f m + ((f 1 - f 0) - (f (m + 1) - f m)) := by
  unfold tau; push_cast; ring

section concave

variable {f : ℕ → ℝ} (hf : ∀ k, f (k + 2) + f k ≤ 2 * f (k + 1))
include hf

lemma incr_le (k m : ℕ) : f (k + m + 1) - f (k + m) ≤ f (k + 1) - f k := by
  induction m with
  | zero => simp
  | succ m ih =>
    have := hf (k + m)
    rw [show k + (m + 1) + 1 = k + m + 2 by ring, show k + (m + 1) = k + m + 1 by ring]
    linarith

lemma tau_nonneg (m : ℕ) : 0 ≤ tau f m := by
  induction m with
  | zero => simp [tau]
  | succ m ih =>
    rw [tau_succ f m]
    have := incr_le hf 0 m
    simp only [zero_add] at this
    linarith

lemma tau_bound (m : ℕ) : tau f (m + 1) ≤ m * ((f 1 - f 0) - (f (m + 2) - f (m + 1))) := by
  induction m with
  | zero => simp [tau]
  | succ m ih =>
    rw [tau_succ f (m + 1)]
    have h1 := hf (m + 1)
    have h2 := incr_le hf 0 (m + 1)
    simp only [zero_add] at h2
    push_cast
    rw [show m + 1 + 2 = m + 3 by ring, show m + 1 + 1 = m + 2 by ring]
    rw [show m + 1 + 1 = m + 2 by ring] at h1
    have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith

lemma tau_ratio (m : ℕ) : (m + 1) * tau f (m + 1) ≤ m * tau f (m + 2) := by
  have e : tau f (m + 2) = tau f (m + 1) + ((f 1 - f 0) - (f (m + 2) - f (m + 1))) :=
    tau_succ f (m + 1)
  have := tau_bound hf m
  rw [e]
  nlinarith

lemma tau_two (m : ℕ) : (m + 3) * tau f (m + 2) ≤ (m + 1) * tau f (m + 4) := by
  have r1 := tau_ratio hf (m + 1)
  have r2 := tau_ratio hf (m + 2)
  push_cast at r1 r2
  rw [show m + 1 + 1 = m + 2 by ring, show m + 1 + 2 = m + 3 by ring] at r1
  rw [show m + 2 + 1 = m + 3 by ring, show m + 2 + 2 = m + 4 by ring] at r2
  have t2 := tau_nonneg hf (m + 2)
  have t3 := tau_nonneg hf (m + 3)
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
  -- (m+1)(m+2) τ(m+4) ≥ (m+1)(m+3) τ(m+3) ≥ (m+3)(m+2) τ(m+2)
  have key : (m + 2) * ((m + 3) * tau f (m + 2)) ≤ (m + 2) * ((m + 1) * tau f (m + 4)) := by
    nlinarith
  exact le_of_mul_le_mul_left key (by positivity)

/-- The row inequality of Lemma 6.3: `w_{m+1} τ_{m+2}(f) ≤ w_{m+2} τ_{m+4}(f)` for concave `f`. -/
lemma psi_nonneg (m : ℕ) : Z (m + 1) * tau f (m + 2) ≤ Z (m + 2) * tau f (m + 4) := by
  have hw := Z_weight m
  have ht := tau_two hf m
  have t2 := tau_nonneg hf (m + 2)
  have z2 := Z_nonneg (m + 2)
  have key : (m + 1) * (Z (m + 1) * tau f (m + 2)) ≤ (m + 1) * (Z (m + 2) * tau f (m + 4)) := by
    nlinarith [mul_le_mul_of_nonneg_right hw t2, mul_le_mul_of_nonneg_left ht z2]
  exact le_of_mul_le_mul_left key (by positivity)

end concave


/-! ### The certificate (§6.4) and the grid lemma -/

/-- `κ = (e − 1)/24660`, the weight of the two-copy inequality in the certificate. -/
noncomputable def kap : ℝ := (exp 1 - 1) / 24660
/-- `Λ = e + 13144 κ`, the coefficient of `S`. -/
noncomputable def Lam : ℝ := exp 1 + 13144 * kap
/-- `N = 1 + 21512 κ`, the coefficient of `L`. -/
noncomputable def Nin : ℝ := 1 + 21512 * kap

lemma mono_row {h : ℕ → ℕ → ℝ} (hmx : ∀ i j, h i j ≤ h (i + 1) j) (j n : ℕ) : h 0 j ≤ h n j := by
  induction n with
  | zero => exact le_refl _
  | succ n ih => exact ih.trans (hmx n j)

section sym

variable {h : ℕ → ℕ → ℝ} {L S : ℝ}
  (hsym : ∀ i j, h i j = h j i)
  (hcx : ∀ i j, h (i + 2) j + h i j ≤ 2 * h (i + 1) j)
  (hlk : ∀ j, L + h 0 j ≤ h 1 j + h 0 (j + 1))

include hsym hcx hlk in
/-- Inductive step of Lemma 6.4: add the link at `(0, m+3)` and the row inequality of row `m+3`. -/
lemma inv_step (m : ℕ)
    (hI : (Nin - Z (m + 2)) * L ≤ Lam * S + (Z (m + 1) - Z (m + 2)) * h 0 (m + 3)
      - Z (m + 1) * h (m + 2) (m + 3)) :
    (Nin - Z (m + 3)) * L ≤ Lam * S + (Z (m + 2) - Z (m + 3)) * h 0 (m + 4)
      - Z (m + 2) * h (m + 3) (m + 4) := by
  have hl := hlk (m + 3)
  have hP := psi_nonneg (f := fun i => h i (m + 3)) (fun k => hcx k (m + 3)) m
  have hw := Z_succ_le (m + 2)
  have hr := Z_rec (m + 1)
  unfold tau at hP
  simp only at hP
  rw [hsym (m + 4) (m + 3)] at hP
  push_cast at hP hr
  rw [← sub_nonneg] at hI ⊢
  have hl' : 0 ≤ h 1 (m + 3) + h 0 (m + 3 + 1) - h 0 (m + 3) - L := by linarith
  have hP' := sub_nonneg.mpr hP
  have key : Lam * S + (Z (m + 2) - Z (m + 3)) * h 0 (m + 4) - Z (m + 2) * h (m + 3) (m + 4)
      - (Nin - Z (m + 3)) * L
      = (Lam * S + (Z (m + 1) - Z (m + 2)) * h 0 (m + 3) - Z (m + 1) * h (m + 2) (m + 3)
          - (Nin - Z (m + 2)) * L)
        + (Z (m + 2) - Z (m + 3)) * (h 1 (m + 3) + h 0 (m + 3 + 1) - h 0 (m + 3) - L)
        + (Z (m + 2) * ((m + 4) * h 1 (m + 3) - (m + 4 - 1) * h 0 (m + 3) - h (m + 3) (m + 4))
          - Z (m + 1) * ((m + 2) * h 1 (m + 3) - (m + 2 - 1) * h 0 (m + 3) - h (m + 2) (m + 3))) := by
    rw [hr]; ring
  rw [key]
  exact add_nonneg (add_nonneg hI (mul_nonneg (by linarith) hl')) hP'

variable (hs : h 1 1 ≤ S)
  (hstar : 22882 * L ≤ 5820 * S + 8694 * h 1 1 + 23290 * h 0 1 + 1370 * h 0 2)

include hsym hcx hlk hs hstar in
/-- Base case of Lemma 6.4 (links at `(0,1)`, `(0,2)`, rows 1 and 2, `h(1,1) ≤ S` and the
two-copy inequality). -/
lemma inv_base :
    (Nin - Z 2) * L ≤ Lam * S + (Z 1 - Z 2) * h 0 3 - Z 1 * h 2 3 := by
  have z2 : Z 2 = 4 * Z 1 - Z 0 := by have := Z_rec 0; push_cast at this; linarith
  rw [z2, Z_one, Z_zero]
  have hE1 := Real.exp_one_gt_d9
  have hE2 := Real.exp_one_lt_d9
  have l1 := hlk 1
  have l2 := hlk 2
  have p1 := hcx 0 1
  have p2a := hcx 0 2
  have p2b := hcx 1 2
  rw [hsym 2 1] at p1
  rw [hsym 3 2] at p2b
  have s1 : 0 ≤ h 1 1 + h 0 2 - h 0 1 - L := by linarith
  have s2 : 0 ≤ h 1 2 + h 0 3 - h 0 2 - L := by linarith
  have q1 : 0 ≤ 2 * h 1 1 - h 1 2 - h 0 1 := by linarith
  have q2 : 0 ≤ 3 * h 1 2 - 2 * h 0 2 - h 2 3 := by norm_num at p2a p2b; linarith
  have sS : 0 ≤ S - h 1 1 := by linarith
  have sT : 0 ≤ 5820 * S + 8694 * h 1 1 + 23290 * h 0 1 + 1370 * h 0 2 - 22882 * L := by linarith
  rw [← sub_nonneg]
  have key : Lam * S + (3 - exp 1 - (4 * (3 - exp 1) - 1)) * h 0 3 - (3 - exp 1) * h 2 3
      - (Nin - (4 * (3 - exp 1) - 1)) * L
      = (exp 1 - 2 - 1370 * kap) * (h 1 1 + h 0 2 - h 0 1 - L)
        + (3 * exp 1 - 8) * (h 1 2 + h 0 3 - h 0 2 - L)
        + (2 * h 1 1 - h 1 2 - h 0 1)
        + (3 - exp 1) * (3 * h 1 2 - 2 * h 0 2 - h 2 3)
        + (exp 1 + 7324 * kap) * (S - h 1 1)
        + kap * (5820 * S + 8694 * h 1 1 + 23290 * h 0 1 + 1370 * h 0 2 - 22882 * L) := by
    unfold Lam Nin kap; ring
  rw [key]
  have hk : 0 ≤ kap := by unfold kap; linarith
  have hk2 : kap ≤ 1 / 10000 := by unfold kap; linarith
  refine add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg ?_ ?_) q1) ?_) ?_) ?_
  · exact mul_nonneg (by linarith) s1
  · exact mul_nonneg (by linarith) s2
  · exact mul_nonneg (by linarith) q2
  · exact mul_nonneg (by linarith) sS
  · exact mul_nonneg hk sT

include hsym hcx hlk hs hstar in
/-- **The invariant** (Lemma 5.4, inequality (5.2)). -/
lemma inv_all (m : ℕ) :
    (Nin - Z (m + 2)) * L ≤ Lam * S + (Z (m + 1) - Z (m + 2)) * h 0 (m + 3)
      - Z (m + 1) * h (m + 2) (m + 3) := by
  induction m with
  | zero => simpa using inv_base hsym hcx hlk hs hstar
  | succ m ih => exact inv_step hsym hcx hlk m ih

include hsym hcx hlk hs hstar in
/-- **Grid lemma, symmetric case** (end of §5.4): `N · L ≤ Λ · S`. -/
theorem grid_closed_sym (hmx : ∀ i j, h i j ≤ h (i + 1) j) (hnn : ∀ i j, 0 ≤ h i j) :
    Nin * L ≤ Lam * S := by
  have hE1 := Real.exp_one_gt_d9
  have hk : 0 ≤ kap := by unfold kap; linarith
  have hS : 0 ≤ S := (hnn 1 1).trans hs
  have hLam : 0 ≤ Lam := by unfold Lam; positivity
  -- for every `m`: `(Nin - Z (m+2)) L ≤ Lam S`
  have hm : ∀ m : ℕ, (Nin - Z (m + 2)) * L ≤ Lam * S := by
    intro m
    have hI := inv_all hsym hcx hlk hs hstar m
    have h1 := mono_row hmx (m + 3) (m + 2)
    have h2 := hnn 0 (m + 3)
    have z1 := Z_succ_le (m + 1)
    have z2 := Z_nonneg (m + 2)
    nlinarith [mul_le_mul_of_nonneg_left h1 (Z_nonneg (m + 1)), mul_nonneg z2 h2]
  rcases le_or_gt L 0 with hL | hL
  · have : Nin * L ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by unfold Nin; linarith) hL
    linarith [mul_nonneg hLam hS]
  · by_contra hcon
    push_neg at hcon
    obtain ⟨m, hmk⟩ := exists_nat_gt (L / (Nin * L - Lam * S))
    have hpos : 0 < Nin * L - Lam * S := by linarith
    have hz := Z_le (m + 2)
    have hmm := hm m
    push_cast at hz
    rw [div_lt_iff₀ hpos] at hmk
    have : Z (m + 2) * L ≤ L / (m + 3) := by
      rw [show (m:ℝ) + 2 + 1 = m + 3 by ring] at hz
      calc Z (m + 2) * L ≤ 1 / (m + 3) * L := mul_le_mul_of_nonneg_right hz hL.le
        _ = L / (m + 3) := by ring
    have h3 : L / (m + 3) < Nin * L - Lam * S := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith
    linarith

end sym

/-- **Grid lemma** (Proposition 6.1).  Let `h : ℕ → ℕ → ℝ` be nonnegative, concave and nondecreasing along
each axis, with the links `L + h(i,j) ≤ h(i+1,j) + h(i,j+1)`, `h(1,1) ≤ S`, and the symmetric
two-copy inequality `22882 L ≤ 5820 S + 8694 h(1,1) + 11645 (h(1,0)+h(0,1)) + 685 (h(2,0)+h(0,2))`.
Then `(21512 e + 3148) L ≤ (37804 e - 13144) S`, i.e. `L ≤ λ∞ S` with
`λ∞ = (9451 e - 3286)/(5378 e + 787) ≈ 1.4542774489`. -/
theorem grid_closed_form (h : ℕ → ℕ → ℝ) (L S : ℝ)
    (hcx : ∀ i j, h (i + 2) j + h i j ≤ 2 * h (i + 1) j)
    (hcy : ∀ i j, h i (j + 2) + h i j ≤ 2 * h i (j + 1))
    (hmx : ∀ i j, h i j ≤ h (i + 1) j)
    (hmy : ∀ i j, h i j ≤ h i (j + 1))
    (hnn : ∀ i j, 0 ≤ h i j)
    (hlk : ∀ i j, L + h i j ≤ h (i + 1) j + h i (j + 1))
    (hs : h 1 1 ≤ S)
    (hstar : 22882 * L ≤ 5820 * S + 8694 * h 1 1 + 11645 * (h 1 0 + h 0 1)
      + 685 * (h 2 0 + h 0 2)) :
    (21512 * exp 1 + 3148) * L ≤ (37804 * exp 1 - 13144) * S := by
  set g : ℕ → ℕ → ℝ := fun i j => (h i j + h j i) / 2 with hg
  have key := grid_closed_sym (h := g) (L := L) (S := S)
    (fun i j => by simp only [hg]; ring)
    (fun i j => by simp only [hg]; linarith [hcx i j, hcy j i])
    (fun j => by simp only [hg]; linarith [hlk 0 j, hlk j 0])
    (by simp only [hg]; linarith)
    (by simp only [hg]; linarith)
    (fun i j => by simp only [hg]; linarith [hmx i j, hmy j i])
    (fun i j => by simp only [hg]; linarith [hnn i j, hnn j i])
  unfold Nin Lam kap at key
  linarith

end GridClosedForm
end SumsDifferences

end
