import ContinuousFlexibility.Analysis.PointwiseMaterialJetOperations

/-!
# Actual ordinary jets under a fixed affine pullback

The affine coordinate map contributes its operator norm to the power of
the spatial order, and no state derivative loss. The proof only needs
ordinary smoothness at the evaluation point.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

theorem norm_iteratedFDeriv_comp_linear_le_at
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (L : X →L[ℝ] Y) {f : Y → Z} {x : X}
    (hf : ContDiffAt ℝ ∞ f (L x)) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ n f (L x)‖ * ‖L‖ ^ n := by
  obtain ⟨U, hU, hxU, hfU⟩ := hf.contDiffOn' (m := (n : ℕ∞ω)) (by simp) (by simp)
  have hf' : ContDiffOn ℝ n f U := by simpa using hfU
  have hpre : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have he := L.iteratedFDerivWithin_comp_right hf' hU.uniqueDiffOn hpre.uniqueDiffOn hxU le_rfl
  rw [iteratedFDerivWithin_of_isOpen n hpre hxU,
    iteratedFDerivWithin_of_isOpen n hU hxU] at he
  rw [he]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (iteratedFDeriv ℝ n f (L x)).norm_compContinuousLinearMap_le (fun _ => L)

theorem PointwiseMaterialJetBound.affine_comp
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {p : ℕ → Seminorm ℝ E} {loss : ℕ} {A : ℕ → ℝ} {z : E}
    (L : X →L[ℝ] Y) (a : Y) {f : Y → Z} {x : X}
    (hf : ContDiffAt ℝ ∞ f (a + L x))
    (hb : PointwiseMaterialJetBound p loss A z f (a + L x)) :
    PointwiseMaterialJetBound p loss (fun n => ‖L‖ ^ n * A n) z
      (fun y => f (a + L y)) x := by
  have hshift : ContDiffAt ℝ ∞ (fun y => f (a + y)) (L x) := by
    exact hf.comp (L x) (contDiffAt_const.add contDiffAt_id)
  intro n
  have hnorm := norm_iteratedFDeriv_comp_linear_le_at L hshift n
  rw [iteratedFDeriv_comp_add_left] at hnorm
  exact hnorm.trans ((mul_le_mul_of_nonneg_right (hb n) (pow_nonneg (norm_nonneg L) n)).trans_eq
    (by ring))

end ContinuousFlexibility.Analysis
