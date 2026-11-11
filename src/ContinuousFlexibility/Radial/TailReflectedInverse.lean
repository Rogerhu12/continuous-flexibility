import ContinuousFlexibility.Radial.ReflectedFormInverse
import ContinuousFlexibility.Radial.TailPositiveResolvent

/-!
# A genuine tail inverse from the low mode projection

This module applies the reflection argument on the actual closed Friedrichs
form space. Its hypotheses are precisely the low and high energy estimates;
its conclusion is the operator graph and `4 / Λ` norm bound required by R06a.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

/-- The function coordinate on the actual energy space. -/
def tailFormBase (T : DeepTailData) (endCut : ℝ) :
    tailGradientSpace T endCut →L[ℝ] DeepTailL2 T :=
  WithLp.fstL 2 ℝ (DeepTailL2 T) (DeepTailL2 T) ∘L
    (tailGradientSpace T endCut).toSubmodule.subtypeL

/-- The derivative coordinate on the actual energy space. -/
def tailFormGradient (T : DeepTailData) (endCut : ℝ) :
    tailGradientSpace T endCut →L[ℝ] DeepTailL2 T :=
  WithLp.sndL 2 ℝ (DeepTailL2 T) (DeepTailL2 T) ∘L
    (tailGradientSpace T endCut).toSubmodule.subtypeL

theorem tailFormBase_apply (T : DeepTailData) (endCut : ℝ)
    (u : tailGradientSpace T endCut) :
    tailFormBase T endCut u = (u : GradientHilbert (DeepTailL2 T)).fst := by
  simp only [tailFormBase, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, WithLp.fstL_apply]

theorem tailFormGradient_apply (T : DeepTailData) (endCut : ℝ)
    (u : tailGradientSpace T endCut) :
    tailFormGradient T endCut u = (u : GradientHilbert (DeepTailL2 T)).snd := by
  simp only [tailFormGradient, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, WithLp.sndL_apply]

theorem tailForm_norm_sq (T : DeepTailData) (endCut : ℝ)
    (u : tailGradientSpace T endCut) :
    ‖u‖ ^ 2 = ‖tailFormBase T endCut u‖ ^ 2 + ‖tailFormGradient T endCut u‖ ^ 2 := by
  simpa only [tailFormBase_apply, tailFormGradient_apply, Submodule.coe_norm] using
    WithLp.prod_norm_sq_eq_of_L2 (u : GradientHilbert (DeepTailL2 T))

/-- No inverse is hidden in these hypotheses: a projection and the two energy
inequalities construct the bounded inverse of the actual Friedrichs relation. -/
theorem exists_tailInverse_of_lowModeProjection (T : DeepTailData) (endCut : ℝ)
    (hΛ : 0 < T.Λ)
    (P : tailGradientSpace T endCut →L[ℝ] tailGradientSpace T endCut)
    (hP : ∀ u, P (P u) = P u)
    (hlow : ∀ u, ‖tailFormGradient T endCut (P u)‖ ^ 2 ≤
      (T.Λ / 2) * ‖tailFormBase T endCut (P u)‖ ^ 2)
    (hhigh : ∀ u, T.Λ * ‖tailFormBase T endCut (u - P u)‖ ^ 2 ≤
      (1 / 2 : ℝ) * ‖tailFormGradient T endCut (u - P u)‖ ^ 2) :
    ∃ G : DeepTailL2 T →L[ℝ] DeepTailL2 T,
      ‖G‖ ≤ 4 / T.Λ ∧
      (∀ f, TailFriedrichsGraph T endCut (G f) (f + T.Λ • G f)) ∧
      (∀ u f, TailFriedrichsGraph T endCut u (f + T.Λ • u) → G f = u) := by
  obtain ⟨X, hX, huniq, hbound⟩ := exists_reflectedFormInverse
    (tailFormBase T endCut) (tailFormGradient T endCut) hΛ P hP
    (tailForm_norm_sq T endCut) hlow hhigh
  let G : DeepTailL2 T →L[ℝ] DeepTailL2 T := tailFormBase T endCut ∘L X
  refine ⟨G, hbound, ?_, ?_⟩
  · intro f
    apply (tailFriedrichsGraph_iff_closedGradientGraph T endCut _ _).mpr
    refine ⟨(X f : GradientHilbert (DeepTailL2 T)), (X f).property, ?_, ?_⟩
    · exact (tailFormBase_apply T endCut (X f)).symm
    · intro r hr
      have h := hX f (⟨r, hr⟩ : tailGradientSpace T endCut)
      rw [shiftedEnergyForm_apply, tailFormGradient_apply, tailFormGradient_apply,
        tailFormBase_apply, tailFormBase_apply] at h
      simp only [inner_add_left, real_inner_smul_left]
      have hG : G f = (X f : GradientHilbert (DeepTailL2 T)).fst := by
        rw [ContinuousLinearMap.comp_apply, tailFormBase_apply]
      rw [hG]
      linarith
  · intro u f hu
    obtain ⟨q, hq, hqu, hform⟩ :=
      (tailFriedrichsGraph_iff_closedGradientGraph T endCut _ _).mp hu
    have hx : X f = (⟨q, hq⟩ : tailGradientSpace T endCut) := by
      apply huniq
      intro v
      have h := hform (v : GradientHilbert (DeepTailL2 T)) v.property
      simp only [inner_add_left, real_inner_smul_left] at h
      rw [shiftedEnergyForm_apply, tailFormBase_apply, tailFormGradient_apply,
        tailFormBase_apply, tailFormGradient_apply, hqu]
      linarith
    rw [ContinuousLinearMap.comp_apply, hx, tailFormBase_apply, hqu]

end ContinuousFlexibility.Radial
