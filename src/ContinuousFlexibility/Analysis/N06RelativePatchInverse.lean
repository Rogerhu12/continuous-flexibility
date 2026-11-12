import ContinuousFlexibility.Analysis.N06BoundaryPatchBounds
import ContinuousFlexibility.Analysis.N06RelativeChartHeightPatch
import ContinuousFlexibility.Analysis.N06SmoothStripInverse
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# A smooth inverse for the actual relative unit-strip patch

The correction here is precisely the degree-four Taylor patch already
constructed from the target-minus-reference boundary fields. Its true
derivative is estimated by those boundary jets and the chosen collar
width. This supplies the small derivative hypothesis of the global strip
inverse theorem and gives a nonzero Jacobian at the closed endpoints.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

private theorem n06_fderiv_pair_norm_le
    {f g : PolarPoint → ℝ} {p : PolarPoint} {A : ℝ}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p)
    (hfb : ‖fderiv ℝ f p‖ ≤ A) (hgb : ‖fderiv ℝ g p‖ ≤ A) :
    ‖fderiv ℝ (fun q => (f q, g q)) p‖ ≤ A := by
  rw [hf.fderiv_prodMk hg, ContinuousLinearMap.opNorm_prod, Prod.norm_def]
  exact max_le hfb hgb

/-- A bound on the actual degree-four endpoint data bounds the
derivative of the actual chart correction everywhere. -/
theorem n06RelativeChartPatch_derivative_bound :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (l r δ M : ℝ)
      (F₀ : PolarPoint → PolarPoint) (F : Bool → PolarPoint → PolarPoint),
      0 < δ → δ ≤ 1 → 0 ≤ M →
      (∀ (side : Bool) θ, ContDiffAt ℝ ∞ F₀ (if side then r else l, θ)) →
      (∀ (side : Bool) θ, ContDiffAt ℝ ∞ (F side) (if side then r else l, θ)) →
      (∀ side j, j ≤ 4 → ∀ k, k ≤ 1 → ∀ θ,
        |iteratedDeriv k (radialBoundaryJet
          (fun p => (F side p).1 - (F₀ p).1) (if side then r else l) j) θ| ≤ M ∧
        |iteratedDeriv k (radialBoundaryJet
          (fun p => (F side p).2 - (F₀ p).2) (if side then r else l) j) θ| ≤ M) →
      ∀ p : PolarPoint, ContDiffAt ℝ ∞ F₀ p →
        ‖fderiv ℝ (fun q => n06RelativeChartPatch l r δ F₀ F q - F₀ q) p‖ ≤
          A * δ⁻¹ * M := by
  obtain ⟨C, hC, hb⟩ := n06RelativeBoundaryPatch_difference_frechet_bound 4 1
  refine ⟨1 + C, by linarith, ?_⟩
  intro l r δ M F₀ F hδ hδ1 hM h₀ hF hdata p hp
  have hP := n06RelativeChartPatch_contDiffAt (δ := δ) h₀ hF hp
  have hb₁ := hb l r δ M (fun q => (F₀ q).1) (fun s q => (F s q).1)
    hδ hδ1 hM (fun s θ => (h₀ s θ).fst) (fun s θ => (hF s θ).fst)
    (fun s j hj k hk θ => (hdata s j hj k hk θ).1) 1 le_rfl p
  have hb₂ := hb l r δ M (fun q => (F₀ q).2) (fun s q => (F s q).2)
    hδ hδ1 hM (fun s θ => (h₀ s θ).snd) (fun s θ => (hF s θ).snd)
    (fun s j hj k hk θ => (hdata s j hj k hk θ).2) 1 le_rfl p
  simp only [norm_iteratedFDeriv_one, pow_one] at hb₁ hb₂
  have hpair := n06_fderiv_pair_norm_le
    ((hP.fst.sub hp.fst).differentiableAt (by simp))
    ((hP.snd.sub hp.snd).differentiableAt (by simp)) hb₁ hb₂
  have he : (fun q => n06RelativeChartPatch l r δ F₀ F q - F₀ q) =
      fun q => ((n06RelativeChartPatch l r δ F₀ F q).1 - (F₀ q).1,
        (n06RelativeChartPatch l r δ F₀ F q).2 - (F₀ q).2) := by
    funext q
    exact Prod.ext (Prod.fst_sub _ _) (Prod.snd_sub _ _)
  rw [he]
  exact hpair.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith : C ≤ 1 + C) (inv_nonneg.mpr hδ.le)) hM)

/-- The existing relative patch has one genuine smooth inverse when
its actual boundary differences fit the explicit collar budget. The
radial boundary values of the target are retained exactly. -/
theorem n06_relativeUnitChartPatch_smooth_inverse :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (δ M : ℝ) (F : Bool → PolarPoint → PolarPoint),
      0 < δ → 2 * δ ≤ 1 → 0 ≤ M →
      (∀ (side : Bool) θ, ContDiffAt ℝ ∞ (F side) (if side then 1 else 0, θ)) →
      (∀ (side : Bool) θ, (F side (if side then 1 else 0, θ)).1 = if side then 1 else 0) →
      (∀ side j, j ≤ 4 → ∀ k, k ≤ 1 → ∀ θ,
        |iteratedDeriv k (radialBoundaryJet
          (fun p => (F side p).1 - p.1) (if side then 1 else 0) j) θ| ≤ M ∧
        |iteratedDeriv k (radialBoundaryJet
          (fun p => (F side p).2 - p.2) (if side then 1 else 0) j) θ| ≤ M) →
      A * δ⁻¹ * M ≤ (1 / 2 : ℝ) →
      let P := n06RelativeChartPatch 0 1 δ (fun p => p) F
      ∃ G : PolarPoint → PolarPoint,
        MapsTo P (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) ∧
        MapsTo G (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) ∧
        Function.LeftInverse G P ∧ Function.RightInverse G P ∧
        ContDiff ℝ ∞ G ∧
        ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ), planeJacobian P p ≠ 0 := by
  obtain ⟨A, hA, hb⟩ := n06RelativeChartPatch_derivative_bound
  refine ⟨A, hA, ?_⟩
  intro δ M F hδ hgap hM hF hrad hdata hsmall
  dsimp only
  let P : PolarPoint → PolarPoint := n06RelativeChartPatch 0 1 δ (fun p => p) F
  let g : PolarPoint → PolarPoint := fun p => P p - p
  have hδ1 : δ ≤ 1 := by linarith
  have hP (p : PolarPoint) : ContDiffAt ℝ ∞ P p :=
    n06RelativeChartPatch_contDiffAt (fun _ _ => contDiffAt_id) hF contDiffAt_id
  have hg (p : PolarPoint) : ContDiffAt ℝ ∞ g p := (hP p).sub contDiffAt_id
  have hbound (p : PolarPoint) : ‖fderiv ℝ g p‖ ≤ (1 / 2 : ℝ) :=
    (hb 0 1 δ M (fun p => p) F hδ hδ1 hM
      (fun _ _ => contDiffAt_id) hF hdata p contDiffAt_id).trans hsmall
  have hradial (side : Bool) (θ : ℝ) : (g (if side then 1 else 0, θ)).1 = 0 := by
    have he := (n06RelativeChartPatch_boundary_jets (l := 0) (r := 1) hδ
      (by simpa only [sub_zero] using hgap)
      (fun _ _ => contDiffAt_id) hF side (j := 0) (by norm_num) θ).1
    simp only [radialBoundaryJet, iteratedDeriv_zero] at he
    change (P (if side then 1 else 0, θ)).1 = (F side (if side then 1 else 0, θ)).1 at he
    simp only [g, Prod.fst_sub, he, hrad side θ, sub_self]
  have hz (θ : ℝ) : (g (0, θ)).1 = 0 ∧ (g (1, θ)).1 = 0 :=
    ⟨hradial false θ, hradial true θ⟩
  have he : (fun p => p + g p) = P := by
    funext p
    dsimp only [g]
    rw [← add_sub_assoc, add_sub_cancel_left]
  have hlip := n06_stripCorrection_lipschitz_of_derivative
    (fun p _ => (hg p).differentiableAt (by simp)) (fun p _ => hbound p)
  have hstrip := n06_smallStripPerturbation_bijOn hlip hz
  obtain ⟨hleft, hright, hsmooth, _⟩ := n06_smallGlobalPerturbation_smooth_inverse
    (contDiff_iff_contDiffAt.mpr hg) hbound
  let G := Function.invFun (fun p => p + g p)
  have hG : MapsTo G (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ))
      (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
    intro p hp
    obtain ⟨q, hq, heq⟩ := hstrip.surjOn hp
    change Function.invFun (fun p => p + g p) p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)
    rw [← heq, hleft q]
    exact hq
  refine ⟨G, ?_, hG, ?_, ?_, hsmooth, ?_⟩
  · simpa only [he] using hstrip.mapsTo
  · intro p
    simpa only [congrFun he p] using hleft p
  · intro p
    change P (G p) = p
    calc
      P (G p) = (fun q => q + g q) (G p) := (congrFun he (G p)).symm
      _ = p := hright p
  · intro p _
    change planeJacobian P p ≠ 0
    rw [← he]
    exact n06_smallStripCorrection_jacobian_ne_zero
      ((hg p).differentiableAt (by simp)) (hbound p)

end ContinuousFlexibility.Analysis
