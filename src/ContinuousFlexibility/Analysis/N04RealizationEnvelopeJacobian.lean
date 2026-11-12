import ContinuousFlexibility.Analysis.N04RealizationEnvelopeDifferential
import ContinuousFlexibility.Analysis.N07aAngularJacobianEnvelope

/-!
# Actual Jacobian envelopes from positive chart jets

The determinant uses four entries of the genuine first derivative.
Only positive coordinate jets enter the estimate. Absolute value is
transferred through its existing local sign identity at nonzero Jacobians.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

theorem n04Realization_envelope_neg_jets
    {X D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : X → ℝ} (p : X → D) (f : X → D → E) (n : ℕ)
    (hf : HasPositiveEnvelope W (fun x => ‖iteratedFDeriv ℝ n (f x) (p x)‖)) :
    HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ n (fun y => -(f x y)) (p x)‖) := by
  apply hf.mono
  intro x
  have he : ‖iteratedFDeriv ℝ n (fun y => -(f x y)) (p x)‖ =
      ‖iteratedFDeriv ℝ n (f x) (p x)‖ := by
    simpa only [Pi.neg_def, norm_neg] using congrArg norm
      (iteratedFDeriv_neg_apply (𝕜 := ℝ) (i := n) (f := f x) (x := p x))
  exact he.le

theorem n04Realization_envelope_jets_congr
    {X D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : X → ℝ} (p : X → D) (f g : X → D → E) (n : ℕ)
    (hf : HasPositiveEnvelope W (fun x => ‖iteratedFDeriv ℝ n (f x) (p x)‖))
    (he : ∀ x, f x =ᶠ[𝓝 (p x)] g x) :
    HasPositiveEnvelope W (fun x => ‖iteratedFDeriv ℝ n (g x) (p x)‖) := by
  exact hf.mono (fun x =>
    (congrArg norm ((he x).iteratedFDeriv ℝ n).eq_of_nhds).symm.le)

theorem n04Realization_envelope_abs_jets
    {X D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {W : X → ℝ} (p : X → D) (f : X → D → ℝ)
    (hf : ∀ x, ContinuousAt (f x) (p x)) (hne : ∀ x, f x (p x) ≠ 0) (n : ℕ)
    (hfj : HasPositiveEnvelope W (fun x => ‖iteratedFDeriv ℝ n (f x) (p x)‖)) :
    HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ n (fun y => |f x y|) (p x)‖) := by
  exact hfj.mono (fun x => (n07a_norm_iteratedFDeriv_abs (hf x) (hne x) n).le)

theorem n04Realization_envelope_planeJacobian_jets
    {X : Type*} {W : X → ℝ} (hW : ∀ x, 1 ≤ W x)
    (p : X → PolarPoint) (F : X → PolarPoint → PolarPoint)
    (hF : ∀ x, ContDiffAt ℝ ∞ (F x) (p x)) (n : ℕ)
    (hFj : ∀ j, 0 < j → j ≤ n + 1 → HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ j (F x) (p x)‖)) :
    HasPositiveEnvelope W
      (fun x => ‖iteratedFDeriv ℝ n (planeJacobian (F x)) (p x)‖) := by
  let d : PolarPoint → (PolarPoint →L[ℝ] ℝ) → X → PolarPoint → ℝ :=
    fun v A x y => A (fderiv ℝ (F x) y v)
  have hs (v : PolarPoint) (A : PolarPoint →L[ℝ] ℝ) (x : X) :
      ContDiffAt ℝ ∞ (d v A x) (p x) :=
    A.contDiff.contDiffAt.comp (p x)
      (((hF x).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const)
  have hj (v : PolarPoint) (A : PolarPoint →L[ℝ] ℝ) (k : ℕ) (hk : k ≤ n) :
      HasPositiveEnvelope W (fun x => ‖iteratedFDeriv ℝ k (d v A x) (p x)‖) := by
    have hd := n04Realization_envelope_directional_jets hW p F (fun _ => v) hF k
      (hasPositiveEnvelope_const W hW ‖v‖) (hFj (k + 1) (by omega) (by omega))
    have h := n04Realization_envelope_clm_comp_jets hW p (fun _ => A)
      (fun x y => fderiv ℝ (F x) y v)
      (fun x => ((hF x).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const) k
      (hasPositiveEnvelope_const W hW ‖A‖) hd
    simpa only [d, Function.comp_apply] using h
  let fst : PolarPoint →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  let snd : PolarPoint →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  have hP := n04Realization_envelope_mul_jets hW p
    (d (1, 0) fst) (d (0, 1) snd) (hs _ _) (hs _ _) n (hj _ _) (hj _ _)
  have hQ := n04Realization_envelope_mul_jets hW p
    (d (1, 0) snd) (d (0, 1) fst) (hs _ _) (hs _ _) n (hj _ _) (hj _ _)
  have hneg := n04Realization_envelope_neg_jets p
    (fun x y => d (1, 0) snd x y * d (0, 1) fst x y) n hQ
  have hadd := n04Realization_envelope_add_jets hW p
    (fun x y => d (1, 0) fst x y * d (0, 1) snd x y)
    (fun x y => -(d (1, 0) snd x y * d (0, 1) fst x y))
    (fun x => (hs _ _ x).mul (hs _ _ x))
    (fun x => ((hs _ _ x).mul (hs _ _ x)).neg) n hP hneg
  simpa only [planeJacobian, d, fst, snd, ContinuousLinearMap.fst_apply,
    ContinuousLinearMap.snd_apply, sub_eq_add_neg] using hadd

end ContinuousFlexibility.Analysis
