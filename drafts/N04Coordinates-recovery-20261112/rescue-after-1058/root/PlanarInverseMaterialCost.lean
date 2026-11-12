import ContinuousFlexibility.Analysis.PlanarInverseJacobianMaterialJets

/-!
# Explicit material cost of the genuine planar inverse

The numerical inverse-Jacobian cost is retained as a power of the same
material envelope. The first inverse derivative follows from the true
inverse germ and the forward derivative matrix; the existing nonlinear
inverse theorem then gives all higher positive jets with one high state
factor. No derivative of the inverse is a quantitative input.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

theorem planarInverse_positiveJets_of_material_jacobian_cost
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (hI : HasInterpolation p)
    (inputLoss : ℕ) :
    ∃ base loss : ℕ, ∀ K : ℝ, 1 ≤ K →
      ∀ A : ℕ → ℝ, (∀ n, 1 ≤ A n) →
      ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z : E, p base z ≤ 1 → ∀ W : ℝ, 1 ≤ W →
      ∀ F G : PolarPoint → PolarPoint, ∀ x : PolarPoint,
        ContDiffAt ℝ ∞ F (G x) → ContDiffAt ℝ ∞ G x →
        F ∘ G =ᶠ[𝓝 x] (id : PolarPoint → PolarPoint) →
        G ∘ F =ᶠ[𝓝 (G x)] (id : PolarPoint → PolarPoint) →
      ∀ κ : ℝ, 0 < κ → κ⁻¹ ≤ K * W ^ K →
        κ ≤ |planeJacobian F (G x)| →
        (∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n F (G x)‖ ≤
          A n * W ^ (A n) * (1 + p (n + inputLoss) z)) →
        ∀ n : ℕ, 1 ≤ n → ‖iteratedFDeriv ℝ n G x‖ ≤
          B n * W ^ (B n) * (1 + p (n + loss) z) := by
  obtain ⟨base, loss, hinverse⟩ := nonlinearInverse_positiveJets_le_material hp hI inputLoss
  refine ⟨base, loss, ?_⟩
  intro K hK A hA
  let R : ℕ → ℝ := fun j => max 1 (max (A (j + 1)) (max (2 * A 1 * K) (A 1 + K)))
  have hR (j : ℕ) : 1 ≤ R j := le_max_left _ _
  have hAR (j : ℕ) : A (j + 1) ≤ R j :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hfirstC (j : ℕ) : 2 * A 1 * K ≤ R j :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hfirstE (j : ℕ) : A 1 + K ≤ R j :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨B, hB, hbound⟩ := hinverse R hR
  refine ⟨B, hB, ?_⟩
  intro z hz W hW F G x hF hG hright hleft κ hκ hκinv hJ hraw n hn
  have hW0 : 0 < W := zero_lt_one.trans_le hW
  have hFx : F (G x) = x := hright.eq_of_nhds
  have hFd : DifferentiableAt ℝ F (G x) := hF.differentiableAt (by simp)
  have hGd : DifferentiableAt ℝ G (F (G x)) := by
    rw [hFx]
    exact hG.differentiableAt (by simp)
  let L : PolarPoint →L[ℝ] PolarPoint := fderiv ℝ G x
  have hL : L.comp (fderiv ℝ F (G x)) = ContinuousLinearMap.id ℝ PolarPoint := by
    calc
      _ = (fderiv ℝ G (F (G x))).comp (fderiv ℝ F (G x)) := by rw [hFx]
      _ = fderiv ℝ (G ∘ F) (G x) := (fderiv_comp (G x) hGd hFd).symm
      _ = fderiv ℝ (id : PolarPoint → PolarPoint) (G x) := hleft.fderiv_eq
      _ = _ := by rw [fderiv_id]
  let S : ℝ := 1 + p (inputLoss + 1) z
  have hS : 0 ≤ S := add_nonneg zero_le_one (apply_nonneg _ _)
  let M : ℝ := A 1 * W ^ (A 1) * S
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg (zero_le_one.trans (hA 1)) (Real.rpow_nonneg hW0.le _)) hS
  have hfirst : ‖fderiv ℝ F (G x)‖ ≤ M := by
    simpa only [norm_iteratedFDeriv_one, M, S, Nat.add_comm 1 inputLoss] using hraw 1 le_rfl
  have hcolumn (v : PolarPoint) (hv : ‖v‖ ≤ 1) :
      ‖fderiv ℝ F (G x) v‖ ≤ M :=
    ((fderiv ℝ F (G x)).le_opNorm v).trans
      ((mul_le_mul_of_nonneg_left hv (norm_nonneg _)).trans
        (by simpa only [mul_one] using hfirst))
  have hcolR := hcolumn (1, 0) (by norm_num [Prod.norm_def])
  have hcolT := hcolumn (0, 1) (by norm_num [Prod.norm_def])
  have h11 : |(fderiv ℝ F (G x) (1, 0)).1| ≤ M := by
    simpa only [Real.norm_eq_abs] using (norm_fst_le _).trans hcolR
  have h12 : |(fderiv ℝ F (G x) (0, 1)).1| ≤ M := by
    simpa only [Real.norm_eq_abs] using (norm_fst_le _).trans hcolT
  have h21 : |(fderiv ℝ F (G x) (1, 0)).2| ≤ M := by
    simpa only [Real.norm_eq_abs] using (norm_snd_le _).trans hcolR
  have h22 : |(fderiv ℝ F (G x) (0, 1)).2| ≤ M := by
    simpa only [Real.norm_eq_abs] using (norm_snd_le _).trans hcolT
  have hLnorm : ‖L‖ ≤ 2 * M / κ := by
    have he := fderiv_inverse_norm_le_of_germ hFd hGd hleft hκ hJ h11 h12 h21 h22
    simpa only [hFx, L] using he
  have hLbound : ‖L‖ ≤ R 0 * W ^ (R 0) * (1 + p (inputLoss + 1) z) := by
    calc
      _ ≤ 2 * M / κ := hLnorm
      _ ≤ (2 * M) * (K * W ^ K) := by
        simpa only [div_eq_mul_inv] using
          mul_le_mul_of_nonneg_left hκinv (mul_nonneg (by norm_num) hM)
      _ = (2 * A 1 * K) * W ^ (A 1 + K) * S := by
        rw [Real.rpow_add hW0]
        dsimp only [M]
        ring
      _ ≤ R 0 * W ^ (R 0) * S :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (hfirstC 0)
            (Real.rpow_le_rpow_of_exponent_le hW (hfirstE 0))
            (Real.rpow_nonneg hW0.le _) (zero_le_one.trans (hR 0))) hS
  have hforward (j : ℕ) (_hj : 1 ≤ j) :
      ‖iteratedFDeriv ℝ (j + 1) F (G x)‖ ≤
        R j * W ^ (R j) * (1 + p (j + inputLoss + 1) z) := by
    have he := (hraw (j + 1) (by omega)).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul (hAR j)
          (Real.rpow_le_rpow_of_exponent_le hW (hAR j))
          (Real.rpow_nonneg hW0.le _) (zero_le_one.trans (hR j)))
        (add_nonneg zero_le_one (apply_nonneg _ _)))
    simpa only [show j + 1 + inputLoss = j + inputLoss + 1 by omega] using he
  exact hbound z hz W hW PolarPoint PolarPoint F G x hF hG hright
    L hL hLbound hforward n hn

end ContinuousFlexibility.Analysis
