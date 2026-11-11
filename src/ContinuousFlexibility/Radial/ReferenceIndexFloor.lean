import ContinuousFlexibility.Radial.ScaleSlowVariation

/-!
# Removing the zero label from an accumulating reference

Replacing only label zero by label one preserves the quantitative
accumulating-profile specification. A uniform shift of all labels would
not preserve the Gaussian distance scale, so the definition uses max.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Filter Real Set
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

def positiveIndexReference (D : ReferenceData) : ReferenceData :=
  { D with cellIndex := fun m => max (D.cellIndex m) 1 }

@[simp] theorem positiveIndexReference_index (D : ReferenceData) (m : ℕ) :
    (positiveIndexReference D).cellIndex m = max (D.cellIndex m) 1 := rfl

theorem positiveIndexReference_index_pos (D : ReferenceData) (m : ℕ) :
    1 ≤ (positiveIndexReference D).cellIndex m :=
  Nat.le_max_right _ _

private theorem floorIndex_gaussian (n : ℕ) :
    exp (-(n : ℝ) ^ 2) ≤ exp 1 * exp (-((max n 1 : ℕ) : ℝ) ^ 2) := by
  by_cases hn : n = 0
  · subst n
    norm_num only [Nat.max_eq_right (by omega : 0 ≤ 1), Nat.cast_zero,
      Nat.cast_one, zero_pow, one_pow, neg_zero, exp_zero]
    rw [← exp_add]
    norm_num
  · have hn' : 1 ≤ n := by omega
    rw [Nat.max_eq_left hn']
    exact le_mul_of_one_le_left (exp_pos _).le
      (one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1))

private theorem floorIndex_gaussian_mul {C C' : ℝ}
    (hC : 0 ≤ C) (hC' : exp 1 * C ≤ C') (n : ℕ) :
    C * exp (-(n : ℝ) ^ 2) ≤
      C' * exp (-((max n 1 : ℕ) : ℝ) ^ 2) := by
  calc
    _ ≤ C * (exp 1 * exp (-((max n 1 : ℕ) : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left (floorIndex_gaussian n) hC
    _ = (exp 1 * C) * exp (-((max n 1 : ℕ) : ℝ) ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hC' (exp_pos _).le

private theorem floorIndex_inverse_power_le {C C' : ℝ}
    (hC : 0 ≤ C) (hCC' : C ≤ C') (n : ℕ) :
    radialE n ^ C ≤ radialE (max n 1) ^ C' := by
  rw [radialE, radialE, Real.rpow_def_of_pos (exp_pos _),
    Real.rpow_def_of_pos (exp_pos _), log_exp, log_exp]
  apply exp_le_exp.mpr
  exact mul_le_mul (radialQ_monotone (Nat.le_max_left n 1)) hCC'
    hC (radialQ_nonneg _)

private theorem floorIndex_negative_power_le {K : ℝ} (hK : 0 ≤ K) (n : ℕ) :
    radialE (max n 1) ^ (-K) ≤ radialE n ^ (-K) := by
  rw [radialE, radialE, Real.rpow_def_of_pos (exp_pos _),
    Real.rpow_def_of_pos (exp_pos _), log_exp, log_exp]
  apply exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_right
    (radialQ_monotone (Nat.le_max_left n 1)) (neg_nonpos.mpr hK)

/-- The same profile, cells and localizers with the zero label removed
still satisfy every accumulating-profile clause. -/
theorem isAccumulatingProfile_positiveIndexReference {D : ReferenceData}
    (hD : IsAccumulatingProfile D) :
    IsAccumulatingProfile (positiveIndexReference D) := by
  rcases hD with ⟨C, hGeo, hPart, hC, hNE, hFin, hLoc, hDist,
    hLower, hJet, hInvJet, hWidth, hAbsorb, hTrace⟩
  let C' : ℕ → ℝ := fun s => (exp 1 + 1) * C s + 1
  have hExp : 1 ≤ exp 1 := one_le_exp_iff.mpr (by norm_num)
  have hC' (s : ℕ) : 0 < C' s := by
    have hp : 0 < (exp 1 + 1) * C s := mul_pos (by positivity) (hC s)
    dsimp only [C']
    linarith
  have hOne (s : ℕ) : 1 ≤ C' s := by
    dsimp only [C']
    have := mul_nonneg (show 0 ≤ exp 1 + 1 by positivity) (hC s).le
    linarith
  have hCC' (s : ℕ) : C s ≤ C' s := by
    dsimp only [C']
    nlinarith [hC s, mul_nonneg (sub_nonneg.mpr hExp) (hC s).le]
  have hEC' (s : ℕ) : exp 1 * C s ≤ C' s := by
    dsimp only [C']
    nlinarith [hC s]
  refine ⟨C', hGeo, hPart, hC', hNE, ?_, hLoc, ?_, ?_, ?_, ?_, ?_,
    hAbsorb, ?_⟩
  · intro N
    apply (hFin N).subset
    intro m hm
    change max (D.cellIndex m) 1 ≤ N at hm
    exact (Nat.le_max_left _ _).trans hm
  · intro m r hr
    obtain ⟨hlo, hhi⟩ := hDist m r hr
    refine ⟨?_, ?_⟩
    · change (C' 0)⁻¹ * exp (-(((max (D.cellIndex m) 1 : ℕ) : ℝ) + 1) ^ 2) ≤
        min (r - D.a) (D.b - r)
      have hcast : (D.cellIndex m : ℝ) ≤ (max (D.cellIndex m) 1 : ℕ) := by
        exact_mod_cast Nat.le_max_left (D.cellIndex m) 1
      have hs : ((D.cellIndex m : ℝ) + 1) ^ 2 ≤
          (((max (D.cellIndex m) 1 : ℕ) : ℝ) + 1) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity) _ 2
        linarith
      have he := exp_le_exp.mpr (neg_le_neg hs)
      exact (mul_le_mul (inv_anti₀ (hC 0) (hCC' 0)) he
        (exp_pos _).le (inv_nonneg.mpr (hC 0).le)).trans hlo
    · exact hhi.trans (floorIndex_gaussian_mul (hC 0).le (hEC' 0) (D.cellIndex m))
  · intro m r hr
    have h := hLower m r hr
    change exp (-(((max (D.cellIndex m) 1 : ℕ) : ℝ) ^ (5 / 2 : ℝ)) -
      C' 0 * ((max (D.cellIndex m) 1 : ℕ) : ℝ) ^ 2) ≤ D.w r
    by_cases hn : D.cellIndex m = 0
    · have hw : 1 ≤ D.w r := by simpa [hn] using h
      rw [hn]
      norm_num only [Nat.max_eq_right (by omega : 0 ≤ 1), Nat.cast_one,
        Real.one_rpow, one_pow, mul_one]
      exact (exp_le_one_iff.mpr (by linarith [hC' 0])).trans hw
    · have hn' : 1 ≤ D.cellIndex m := by omega
      rw [Nat.max_eq_left hn']
      apply le_trans _ h
      apply exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_right (hCC' 0) (sq_nonneg (D.cellIndex m : ℝ))
      linarith
  · intro m r hr s
    have h := hJet m r hr s
    change |radialJet s D.w r| ≤ C' s *
      exp (-(((max (D.cellIndex m) 1 : ℕ) : ℝ) ^ (5 / 2 : ℝ)) +
        C' s * ((max (D.cellIndex m) 1 : ℕ) : ℝ) ^ 2)
    by_cases hn : D.cellIndex m = 0
    · have h' : |radialJet s D.w r| ≤ C s := by simpa [hn] using h
      rw [hn]
      norm_num only [Nat.max_eq_right (by omega : 0 ≤ 1), Nat.cast_one,
        Real.one_rpow, one_pow, mul_one]
      have he : 1 ≤ exp (-1 + C' s) :=
        one_le_exp_iff.mpr (by linarith [hOne s])
      exact h'.trans ((hCC' s).trans (le_mul_of_one_le_right (hC' s).le he))
    · have hn' : 1 ≤ D.cellIndex m := by omega
      rw [Nat.max_eq_left hn']
      apply h.trans
      apply mul_le_mul (hCC' s) _ (exp_pos _).le (hC' s).le
      apply exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right (hCC' s) (sq_nonneg (D.cellIndex m : ℝ))
      linarith
  · intro m r hr s
    have h := hInvJet m r hr s
    change |radialJet s (fun t => (D.w t)⁻¹) r| ≤
      C' s * radialE (max (D.cellIndex m) 1) ^ C' s
    apply h.trans
    exact mul_le_mul (hCC' s)
      (floorIndex_inverse_power_le (hC s).le (hCC' s) (D.cellIndex m))
      (Real.rpow_nonneg (exp_pos _).le _) (hC' s).le
  · intro m
    obtain ⟨l, h, hsub, hlen⟩ := hWidth m
    exact ⟨l, h, hsub, hlen.trans
      (floorIndex_gaussian_mul (hC 0).le (hEC' 0) (D.cellIndex m))⟩
  · obtain ⟨centers, widths, K, hK, hsc, hdisj⟩ := hTrace
    refine ⟨centers, widths, K, hK, ?_, hdisj⟩
    intro m
    obtain ⟨hcenter, hpos, hbound, hinc⟩ := hsc m
    refine ⟨hcenter, hpos, ?_, hinc⟩
    exact (mul_le_mul_of_nonneg_left
      (floorIndex_negative_power_le hK.le (D.cellIndex m))
      (inv_nonneg.mpr hK.le)).trans hbound

end ContinuousFlexibility.Radial
