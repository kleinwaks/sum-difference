module

public import Mathlib
public import SumDifference.ThetaLocalization

/-!
# Part I: the multi-scale transfer `θ ≤ 2 − 1/λ`

§2 of the proof paper.  If every pair of finite sets of integers satisfies
`|X − Y| ≤ |X + Y|^λ`, then `θ ≤ 2 − 1/λ` (`theta_le_of_pair_ceiling`, Theorem 1.2); in terms of
the pair exponent `λ_*` (the pair-exponent definition, `lamSup`) this is `θ ≤ 2 − 1/λ_*`
(`theta_le_two_sub_inv_lamSup`).  The proof localises at the scales `D = hB − hB`,
`h = 1, 4, …, 4^J` (Lemma 2.4, Proposition 2.5) and uses Plünnecke–Ruzsa.  The general lemmas
allow a constant `C` in the pair ceiling; the paper and the proof of Theorem 1.2 use `C = 1`.
-/

@[expose] public section

open Finset Pointwise

namespace SumsDifferences

namespace MultiScale

section general

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

/-- Monotonicity of `|mB − nB|` in `m` and `n`. -/
theorem card_nsmul_sub_nsmul_mono {B : Finset G} (hB : B.Nonempty) {m n m' n' : ℕ}
    (hm : m ≤ m') (hn : n ≤ n') : #(m • B - n • B) ≤ #(m' • B - n' • B) := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hm
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hn
  have e : (m + p) • B - (n + q) • B = (m • B - n • B) + (p • B - q • B) := by
    rw [add_nsmul, add_nsmul, sub_add_sub_comm]
  rw [e]
  exact card_le_card_add_right (hB.nsmul.sub hB.nsmul)

theorem sub_sub_eq (B : Finset G) (h : ℕ) :
    (h • B - h • B) - (h • B - h • B) - B = (2 * h) • B - (2 * h + 1) • B := by
  rw [sub_eq_add_neg (h • B - h • B) (h • B - h • B), neg_sub, sub_add_sub_comm, ← add_nsmul,
    sub_sub, ← succ_nsmul, two_mul]

theorem sub_add_sub_eq (B : Finset G) (h : ℕ) :
    (h • B - h • B) - (h • B - h • B) + (h • B - h • B) - B = (3 * h) • B - (3 * h + 1) • B := by
  rw [sub_eq_add_neg (h • B - h • B) (h • B - h • B), neg_sub, sub_add_sub_comm, ← add_nsmul,
    sub_add_sub_comm, ← add_nsmul, sub_sub, ← succ_nsmul]
  congr 2 <;> ring_nf

/-- **One scale** (Lemma 2.4).  If every `X ⊆ A` obeys `|X − B| ≤ C |X + B|^λ`, then for `h ≥ 1`
`|A − B| · |hB − hB| ≤ C^{1/λ} |4hB − 4hB|^{2 − 1/λ} |A + B|`. -/
theorem card_sub_mul_le_scale {A B : Finset G} (hB : B.Nonempty) {lam C : ℝ} (hlam : 1 ≤ lam)
    (hC : 0 < C) (hpair : ∀ X ⊆ A, (#(X - B) : ℝ) ≤ C * (#(X + B) : ℝ) ^ lam) {h : ℕ}
    (hh : 1 ≤ h) :
    (#(A - B) : ℝ) * #(h • B - h • B) ≤
      C ^ (1 / lam) * (#((4 * h) • B - (4 * h) • B) : ℝ) ^ (2 - 1 / lam) * #(A + B) := by
  have hD : (h • B - h • B).Nonempty := hB.nsmul.sub hB.nsmul
  have hloc := ConverseAmplification.card_sub_mul_card_le_localized_const A B (h • B - h • B) hD
    hlam hC (fun X hX _ _ => hpair X hX)
  rw [sub_sub_eq, sub_add_sub_eq] at hloc
  have hU : (#((2 * h) • B - (2 * h + 1) • B) : ℝ) ≤ #((4 * h) • B - (4 * h) • B) := by
    exact_mod_cast card_nsmul_sub_nsmul_mono hB (by omega) (by omega)
  have hW : (#((3 * h) • B - (3 * h + 1) • B) : ℝ) ≤ #((4 * h) • B - (4 * h) • B) := by
    exact_mod_cast card_nsmul_sub_nsmul_mono hB (by omega) (by omega)
  have hMpos : (0 : ℝ) < #((4 * h) • B - (4 * h) • B) := by
    have : ((4 * h) • B - (4 * h) • B).Nonempty := hB.nsmul.sub hB.nsmul
    exact_mod_cast this.card_pos
  set M : ℝ := (#((4 * h) • B - (4 * h) • B) : ℝ)
  have hlam0 : 0 < lam := by linarith
  have ha : 0 ≤ 1 - 1 / lam := by rw [sub_nonneg, div_le_one hlam0]; exact hlam
  have hM0 : 0 ≤ M := by positivity
  have hUa : (#((2 * h) • B - (2 * h + 1) • B) : ℝ) ^ (1 - 1 / lam) ≤ M ^ (1 - 1 / lam) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hU ha
  have hsplit : M ^ (2 - 1 / lam) = M ^ (1 - 1 / lam) * M := by
    rw [show (2 : ℝ) - 1 / lam = (1 - 1 / lam) + 1 by ring, Real.rpow_add hMpos, Real.rpow_one]
  calc (#(A - B) : ℝ) * #(h • B - h • B)
      ≤ C ^ (1 / lam) * ((#((2 * h) • B - (2 * h + 1) • B) : ℝ) ^ (1 - 1 / lam) * #(A + B) *
          #((3 * h) • B - (3 * h + 1) • B)) := hloc
    _ ≤ C ^ (1 / lam) * (M ^ (1 - 1 / lam) * #(A + B) * M) := by gcongr
    _ = C ^ (1 / lam) * M ^ (2 - 1 / lam) * #(A + B) := by rw [hsplit]; ring

/-- **Telescoping over the scales `4^j`** (proof of Proposition 2.5).  `|A − B|^J · |B − B| ≤ (C^{1/λ} |A + B|)^J ·
|4^J B − 4^J B|^{1 + J(1 − 1/λ)}`. -/
theorem card_sub_pow_mul_le_telescope {A B : Finset G} (hB : B.Nonempty) {lam C : ℝ}
    (hlam : 1 ≤ lam) (hC : 0 < C)
    (hpair : ∀ X ⊆ A, (#(X - B) : ℝ) ≤ C * (#(X + B) : ℝ) ^ lam) (J : ℕ) :
    (#(A - B) : ℝ) ^ J * #(1 • B - 1 • B) ≤
      (C ^ (1 / lam) * #(A + B)) ^ J *
        (#((4 ^ J) • B - (4 ^ J) • B) : ℝ) ^ (1 + J * (1 - 1 / lam)) := by
  have hlam0 : 0 < lam := by linarith
  have ha : 0 ≤ 1 - 1 / lam := by rw [sub_nonneg, div_le_one hlam0]; exact hlam
  set c : ℝ := C ^ (1 / lam) with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg hC.le _
  set d : ℝ := (#(A - B) : ℝ)
  set s : ℝ := (#(A + B) : ℝ)
  have hd0 : 0 ≤ d := by positivity
  have hs0 : 0 ≤ s := by positivity
  let m : ℕ → ℝ := fun j => (#((4 ^ j) • B - (4 ^ j) • B) : ℝ)
  have hmpos : ∀ j, 0 < m j := fun j => by
    have : ((4 ^ j) • B - (4 ^ j) • B).Nonempty := hB.nsmul.sub hB.nsmul
    show (0 : ℝ) < #((4 ^ j) • B - (4 ^ j) • B)
    exact_mod_cast this.card_pos
  have hmono : ∀ j, m j ≤ m (j + 1) := fun j => by
    have : 4 ^ j ≤ 4 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ j)
    show (#((4 ^ j) • B - (4 ^ j) • B) : ℝ) ≤ #((4 ^ (j + 1)) • B - (4 ^ (j + 1)) • B)
    exact_mod_cast card_nsmul_sub_nsmul_mono hB this this
  have hstep : ∀ j, d * m j ≤ c * m (j + 1) ^ (2 - 1 / lam) * s := fun j => by
    have := card_sub_mul_le_scale hB hlam hC hpair (h := 4 ^ j) (Nat.one_le_pow _ _ (by norm_num))
    simp only [m, pow_succ']
    exact this
  have key : ∀ j : ℕ, d ^ j * m 0 ≤ (c * s) ^ j * m j ^ (1 + j * (1 - 1 / lam)) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hmj := hmpos j
      have hmj1 := hmpos (j + 1)
      have hja : 0 ≤ (j : ℝ) * (1 - 1 / lam) := mul_nonneg (Nat.cast_nonneg _) ha
      have e1 : m j ^ (1 + j * (1 - 1 / lam)) = m j * m j ^ ((j : ℝ) * (1 - 1 / lam)) := by
        rw [Real.rpow_add hmj, Real.rpow_one]
      have e2 : m (j + 1) ^ (1 + ((j + 1 : ℕ) : ℝ) * (1 - 1 / lam)) =
          m (j + 1) ^ (2 - 1 / lam) * m (j + 1) ^ ((j : ℝ) * (1 - 1 / lam)) := by
        rw [← Real.rpow_add hmj1]; push_cast; ring_nf
      have hle : m j ^ ((j : ℝ) * (1 - 1 / lam)) ≤ m (j + 1) ^ ((j : ℝ) * (1 - 1 / lam)) :=
        Real.rpow_le_rpow hmj.le (hmono j) hja
      calc d ^ (j + 1) * m 0 = d * (d ^ j * m 0) := by ring
        _ ≤ d * ((c * s) ^ j * m j ^ (1 + j * (1 - 1 / lam))) := by gcongr
        _ = (c * s) ^ j * (d * m j) * m j ^ ((j : ℝ) * (1 - 1 / lam)) := by rw [e1]; ring
        _ ≤ (c * s) ^ j * (c * m (j + 1) ^ (2 - 1 / lam) * s) *
              m (j + 1) ^ ((j : ℝ) * (1 - 1 / lam)) := by
            have hcsj : 0 ≤ (c * s) ^ j := pow_nonneg (mul_nonneg hc0 hs0) j
            have hY : 0 ≤ (c * s) ^ j * (c * m (j + 1) ^ (2 - 1 / lam) * s) :=
              mul_nonneg hcsj (le_trans (by positivity) (hstep j))
            exact mul_le_mul (mul_le_mul_of_nonneg_left (hstep j) hcsj) hle
              (Real.rpow_nonneg hmj.le _) hY
        _ = (c * s) ^ (j + 1) * m (j + 1) ^ (1 + ((j + 1 : ℕ) : ℝ) * (1 - 1 / lam)) := by
            rw [e2]; ring
  simpa [m] using key J

/-- **Multi-scale inequality** (Proposition 2.5).  If `|A + B| ≤ K|A|` and every `X ⊆ A` obeys
`|X − B| ≤ C |X + B|^λ`, then for every `J`
`|A − B|^J ≤ (C^{1/λ} |A + B|)^J · (K^{2·4^J} |A|)^{1 + J(1 − 1/λ)}`. -/
theorem card_sub_pow_le_multiscale {A B : Finset G} {K lam C : ℝ} (hA : A.Nonempty)
    (hB : B.Nonempty) (hK : (#(A + B) : ℝ) ≤ K * #A) (hlam : 1 ≤ lam) (hC : 0 < C)
    (hpair : ∀ X ⊆ A, (#(X - B) : ℝ) ≤ C * (#(X + B) : ℝ) ^ lam) (J : ℕ) :
    (#(A - B) : ℝ) ^ J ≤
      (C ^ (1 / lam) * #(A + B)) ^ J * (K ^ (2 * 4 ^ J) * #A) ^ (1 + J * (1 - 1 / lam)) := by
  have hlam0 : 0 < lam := by linarith
  have ha : 0 ≤ 1 - 1 / lam := by rw [sub_nonneg, div_le_one hlam0]; exact hlam
  have ht := card_sub_pow_mul_le_telescope hB hlam hC hpair J
  have h1 : (1 : ℝ) ≤ #(1 • B - 1 • B) := by
    have : (1 • B - 1 • B).Nonempty := hB.nsmul.sub hB.nsmul
    exact_mod_cast this.card_pos
  have hM : (#((4 ^ J) • B - (4 ^ J) • B) : ℝ) ≤ K ^ (2 * 4 ^ J) * #A := by
    have := ConverseAmplification.card_nsmul_sub_nsmul_le_real hA hK (4 ^ J) (4 ^ J)
    rwa [show 4 ^ J + 4 ^ J = 2 * 4 ^ J by ring] at this
  have hexp : 0 ≤ 1 + (J : ℝ) * (1 - 1 / lam) := by positivity
  have hMa : (#((4 ^ J) • B - (4 ^ J) • B) : ℝ) ^ (1 + J * (1 - 1 / lam)) ≤
      (K ^ (2 * 4 ^ J) * #A) ^ (1 + J * (1 - 1 / lam)) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hM hexp
  have hd0 : (0 : ℝ) ≤ (#(A - B) : ℝ) ^ J := by positivity
  calc (#(A - B) : ℝ) ^ J ≤ (#(A - B) : ℝ) ^ J * #(1 • B - 1 • B) := le_mul_of_one_le_right hd0 h1
    _ ≤ _ := ht
    _ ≤ _ := by gcongr

end general

/-- **Multi-scale transfer to admissible exponents.**  If every pair of finite sets of integers
satisfies `|X − Y| ≤ C |X + Y|^λ` (`C > 0`, `λ ≥ 1`), then every admissible exponent is at most
`2 − 1/λ + 1/J` for every `J ≥ 1`. -/
theorem admissible_le_of_pairCeiling_multiscale_J {θ lam C : ℝ} (hlam : 1 ≤ lam) (hC : 0 < C)
    (hpair : ∀ X Y : Finset ℤ, (#(X - Y) : ℝ) ≤ C * (#(X + Y) : ℝ) ^ lam)
    (h : Admissible θ) {J : ℕ} (hJ : 1 ≤ J) : θ ≤ 2 - 1 / lam + 1 / J := by
  have hlam0 : 0 < lam := by linarith
  have ha : 0 ≤ 1 - 1 / lam := by rw [sub_nonneg, div_le_one hlam0]; exact hlam
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
  set e : ℝ := 1 + J * (1 - 1 / lam) with he
  have he0 : 0 ≤ e := by positivity
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = (2 : ℝ) ^ (2 * 4 ^ J) := ⟨_, rfl⟩
  have hk0 : 0 < k := by rw [hk]; positivity
  set c : ℝ := C ^ (1 / lam) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos hC _
  refine admissible_le_of_rpow_bound (C := c * k ^ (e / J)) (by positivity) ?_ h
  intro A B hA hB hs
  have hmain := card_sub_pow_le_multiscale (K := 2) hA hB hs hlam hC (fun X _ => hpair X B) J
  rw [← hk] at hmain
  have hm0 : (0 : ℝ) < #A := by exact_mod_cast hA.card_pos
  have hms : (#A : ℝ) ≤ #(A + B) := by exact_mod_cast card_le_card_add_right hB
  have hs0 : (0 : ℝ) < #(A + B) := hm0.trans_le hms
  set s : ℝ := (#(A + B) : ℝ)
  set d : ℝ := (#(A - B) : ℝ)
  have hd0 : 0 ≤ d := by positivity
  have hcs : 0 ≤ c * s := by positivity
  have hks : 0 ≤ k * s := by positivity
  have hkse : 0 ≤ (k * s) ^ e := Real.rpow_nonneg hks _
  have hJi : (0 : ℝ) ≤ 1 / (J : ℝ) := by positivity
  have h2 : (k * #A) ^ e ≤ (k * s) ^ e :=
    Real.rpow_le_rpow (by positivity) (by gcongr) he0
  have hdJ : d ^ J ≤ (c * s) ^ J * (k * s) ^ e := hmain.trans (by gcongr)
  -- take `J`-th roots
  have hJne : (J : ℝ) ≠ 0 := hJ0.ne'
  have hroot : d = (d ^ J) ^ (1 / (J : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd0, mul_one_div_cancel hJne, Real.rpow_one]
  rw [hroot]
  calc (d ^ J) ^ (1 / (J : ℝ)) ≤ ((c * s) ^ J * (k * s) ^ e) ^ (1 / (J : ℝ)) :=
        Real.rpow_le_rpow (pow_nonneg hd0 _) hdJ hJi
    _ = c * s * (k * s) ^ (e / J) := by
        rw [Real.mul_rpow (pow_nonneg hcs _) hkse, ← Real.rpow_natCast,
          ← Real.rpow_mul hcs, mul_one_div_cancel hJne, Real.rpow_one,
          ← Real.rpow_mul hks, mul_one_div]
    _ = c * k ^ (e / J) * s ^ (2 - 1 / lam + 1 / J) := by
        rw [Real.mul_rpow hk0.le hs0.le]
        have : (2 : ℝ) - 1 / lam + 1 / J = 1 + e / J := by
          rw [he]; field_simp; ring
        rw [this, Real.rpow_add hs0, Real.rpow_one]; ring

/-- **Multi-scale transfer**: a pair ceiling `|X − Y| ≤ C |X + Y|^λ` for all pairs of finite
sets of integers implies that every admissible exponent is at most `2 − 1/λ`. -/
theorem admissible_le_of_pairCeiling_multiscale {θ lam C : ℝ} (hlam : 1 ≤ lam) (hC : 0 < C)
    (hpair : ∀ X Y : Finset ℤ, (#(X - Y) : ℝ) ≤ C * (#(X + Y) : ℝ) ^ lam)
    (h : Admissible θ) : θ ≤ 2 - 1 / lam := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨J, hJ⟩ := exists_nat_gt (1 / (θ - (2 - 1 / lam)))
  have hpos : 0 < θ - (2 - 1 / lam) := by linarith
  have hJ1 : 1 ≤ J := by
    have : (0 : ℝ) < J := lt_trans (by positivity) hJ
    exact_mod_cast this
  have hb := admissible_le_of_pairCeiling_multiscale_J hlam hC hpair h hJ1
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ1
  have : 1 / (J : ℝ) < θ - (2 - 1 / lam) := by
    rw [div_lt_iff₀ hJ0]
    rw [div_lt_iff₀ hpos] at hJ
    linarith
  linarith

end MultiScale

/-- A pair ceiling `|X − Y| ≤ |X + Y|^λ` for all finite `X, Y ⊆ ℤ` forces `λ ≥ 1`
(take `X = {0}`, `Y = {0, 1}`). -/
lemma one_le_of_pair_ceiling {lam : ℝ}
    (hpair : ∀ X Y : Finset ℤ, (#(X - Y) : ℝ) ≤ (#(X + Y) : ℝ) ^ lam) : 1 ≤ lam := by
  have h := hpair {0} {0, 1}
  have e1 : ({0} : Finset ℤ) - {0, 1} = {0, -1} := by decide
  have e2 : ({0} : Finset ℤ) + {0, 1} = {0, 1} := by decide
  rw [e1, e2] at h
  norm_num at h
  by_contra hlt
  push_neg at hlt
  have : (2 : ℝ) ^ lam < 2 ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hlt
  rw [Real.rpow_one] at this
  linarith

/-- **Theorem 1.2, first statement.**  If `|X − Y| ≤ |X + Y|^λ` for all finite sets of integers
`X`, `Y` (no constant), then `θ ≤ 2 − 1/λ`. -/
theorem theta_le_of_pair_ceiling {lam : ℝ}
    (hpair : ∀ X Y : Finset ℤ, (#(X - Y) : ℝ) ≤ (#(X + Y) : ℝ) ^ lam) : theta ≤ 2 - 1 / lam := by
  have hlam := one_le_of_pair_ceiling hpair
  refine Real.sSup_le (fun _ ht =>
    MultiScale.admissible_le_of_pairCeiling_multiscale (C := 1) hlam one_pos
      (fun X Y => by simpa using hpair X Y) ht) ?_
  rw [sub_nonneg, div_le_iff₀ (by linarith)]
  linarith

/-! ### The pair exponent `λ_*` (the pair-exponent definition) -/

/-- The exponents `λ` for which the constant-free pair ceiling `|X − Y| ≤ |X + Y|^λ` holds for
all finite sets of integers `X`, `Y`. -/
def pairCeilingExponents : Set ℝ :=
  {lam : ℝ | ∀ X Y : Finset ℤ, (#(X - Y) : ℝ) ≤ (#(X + Y) : ℝ) ^ lam}

/-- **The pair exponent** `λ_* = inf {λ : |X − Y| ≤ |X + Y|^λ for all finite X, Y ⊆ ℤ}`.
The upper-bound argument uses this infimum definition directly. -/
noncomputable def lamSup : ℝ := sInf pairCeilingExponents

/-- The trivial ceiling `|X − Y| ≤ |X| |Y| ≤ |X + Y|²`. -/
lemma two_mem_pairCeilingExponents : (2 : ℝ) ∈ pairCeilingExponents := by
  intro X Y
  rcases X.eq_empty_or_nonempty with rfl | hX
  · simp
  rcases Y.eq_empty_or_nonempty with rfl | hY
  · simp
  have h1 : #(X - Y) ≤ #X * #Y := Finset.card_sub_le
  have h2 : #X ≤ #(X + Y) := card_le_card_add_right hY
  have h3 : #Y ≤ #(X + Y) := card_le_card_add_left hX
  have h4 : #(X - Y) ≤ #(X + Y) ^ 2 := h1.trans (by rw [sq]; exact Nat.mul_le_mul h2 h3)
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact_mod_cast h4

lemma pairCeilingExponents_bddBelow : BddBelow pairCeilingExponents :=
  ⟨1, fun _ h => one_le_of_pair_ceiling h⟩

/-- Every constant-free pair ceiling exponent is at least `λ_*`. -/
lemma lamSup_le_of_pair_ceiling {lam : ℝ}
    (hpair : ∀ X Y : Finset ℤ, (#(X - Y) : ℝ) ≤ (#(X + Y) : ℝ) ^ lam) : lamSup ≤ lam :=
  csInf_le pairCeilingExponents_bddBelow hpair

lemma one_le_lamSup : 1 ≤ lamSup :=
  le_csInf ⟨2, two_mem_pairCeilingExponents⟩ fun _ h => one_le_of_pair_ceiling h

/-- **Theorem 1.2, second statement**: `θ ≤ 2 − 1/λ_*`. -/
theorem theta_le_two_sub_inv_lamSup : theta ≤ 2 - 1 / lamSup := by
  have h2 : theta ≤ 2 - 1 / 2 := theta_le_of_pair_ceiling two_mem_pairCeilingExponents
  have hl := one_le_lamSup
  by_contra hlt
  push_neg at hlt
  have hpos : 0 < 2 - theta := by linarith
  have hlt' : lamSup < 1 / (2 - theta) := by
    rw [lt_div_iff₀ hpos]
    have : 1 / lamSup > 2 - theta := by linarith
    rw [gt_iff_lt, lt_div_iff₀ (by linarith)] at this
    linarith
  obtain ⟨lam, hlam, hlam'⟩ :=
    exists_lt_of_csInf_lt ⟨2, two_mem_pairCeilingExponents⟩ hlt'
  have h := theta_le_of_pair_ceiling hlam
  have hl1 := one_le_of_pair_ceiling hlam
  have : 2 - theta < 1 / lam := by
    rw [lt_div_iff₀ (by linarith)]
    rw [lt_div_iff₀ hpos] at hlam'
    linarith
  linarith

end SumsDifferences
