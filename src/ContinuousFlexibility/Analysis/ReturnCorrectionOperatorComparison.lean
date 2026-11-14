module

public import ContinuousFlexibility.Analysis.ReturnOpticalCorrectionSource

/-!
# The actual operator difference at the actual residual

The independent coefficient-error map equals the original-minus-patched
coefficients on the open annulus. Its proved C¹ regularity therefore
proves C¹ regularity of the actual patched coefficients. The exact
divergence comparison can then be applied without assuming any extra
differentiability of the corrected operator or its fluxes.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

section ActualOperator

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}
  (hN01 : N01Properties D T S C base loss ε)
  (hN02 : N02Properties D T S C R base ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S z.1)
  (χ : ℕ → ℝ → ℝ) (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
  (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
  (hsupp : ∀ m, Function.support (deriv (χ m)) ⊆ Ioo (C.left m) (C.right m))
  (hend : ∀ m, χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
    χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1))
  (hdisc : ∀ m p, p.1 ∈ tsupport (deriv (χ m)) →
    0 < (originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)

include hN01 hN02 hS hz hsector hdisc

theorem N01Properties.returnCorrectionCoefficientError_at_actual_of_cutoffs
    (p : PolarPoint) (hp : p ∈ annularOpen D) :
    returnCorrectionCoefficientError D S C R χ z p (R.residual z) =
      ((originalCoefficients D S C z).b p -
        (returnCorrectedCoefficients D S C χ z).b p,
       (originalCoefficients D S C z).c p -
        (returnCorrectedCoefficients D S C χ z).c p) := by
  apply returnCorrectionCoefficientError_at_actual hN01 hN02 hS
    χ hz hsector p hp
  intro m _ hm
  exact (hdisc m p (subset_tsupport _ hm)).le

include hT hχ hχrange hsupp hend

theorem N01Properties.returnCorrectedCoefficients_contDiffAt_one
    (p : PolarPoint) (hp : p ∈ annularOpen D) :
    ContDiffAt ℝ 1 (returnCorrectedCoefficients D S C χ z).a p ∧
    ContDiffAt ℝ 1 (returnCorrectedCoefficients D S C χ z).b p ∧
    ContDiffAt ℝ 1 (returnCorrectedCoefficients D S C χ z).c p := by
  have hreg := hN01.originalCoefficients_contDiffAt hS hT hz hsector hp
  have herr : ContDiffAt ℝ 1
      (fun q => returnCorrectionCoefficientError D S C R χ z q (R.residual z)) p :=
    (hN01.returnCorrectionCoefficientError_contDiffAt_of_cutoffs hS hT R hz hsector
      χ hχ hχrange hsupp hend hdisc (R.residual z) p hp).of_le (by simp)
  have hb : (returnCorrectedCoefficients D S C χ z).b =ᶠ[𝓝 p]
      fun q => (originalCoefficients D S C z).b q -
        (returnCorrectionCoefficientError D S C R χ z q
          (R.residual z)).1 := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
    have h := congrArg Prod.fst
      (hN01.returnCorrectionCoefficientError_at_actual_of_cutoffs hN02 hS hz hsector χ hdisc q hq)
    dsimp only [Prod.fst] at h
    linarith
  have hc : (returnCorrectedCoefficients D S C χ z).c =ᶠ[𝓝 p]
      fun q => (originalCoefficients D S C z).c q -
        (returnCorrectionCoefficientError D S C R χ z q
          (R.residual z)).2 := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
    have h := congrArg Prod.snd
      (hN01.returnCorrectionCoefficientError_at_actual_of_cutoffs hN02 hS hz hsector χ hdisc q hq)
    dsimp only [Prod.snd] at h
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [returnCorrectedCoefficients_a]
    exact hreg.1.of_le (by simp)
  · exact (((hreg.2.1).of_le (by simp)).sub herr.fst).congr_of_eventuallyEq hb
  · exact (((hreg.2.2).of_le (by simp)).sub herr.snd).congr_of_eventuallyEq hc

theorem N01Properties.divergenceOperator_returnCorrectedCoefficients
    (η : HeightPair S) (p : PolarPoint) (hp : p ∈ annularOpen D) :
    divergenceOperator (originalCoefficients D S C z) (heightPairField S η) p -
      divergenceOperator (returnCorrectedCoefficients D S C χ z)
        (heightPairField S η) p =
      returnCorrectionResidualErrorField D S C R χ z
        (R.residual z) η p := by
  let L := originalCoefficients D S C z
  let K := returnCorrectedCoefficients D S C χ z
  let u := heightPairField S η
  have hL := hN01.originalCoefficients_contDiffAt hS hT hz hsector hp
  have hK := hN01.returnCorrectedCoefficients_contDiffAt_one hN02 hS hT hz hsector
    χ hχ hχrange hsupp hend hdisc p hp
  have hu : ContDiff ℝ ∞ u :=
    physical_height_with_cutoff_contDiff hT hS (by norm_num : (0 : ℝ) < 3 / 4) η.1 η.2
  have hur : ContDiffAt ℝ 1 (radialPartial u) p :=
    (contDiffAt_radialPartial hu.contDiffAt (m := ∞) (by simp)).of_le (by simp)
  have hut : ContDiffAt ℝ 1 (angularPartial u) p :=
    (contDiffAt_angularPartial hu.contDiffAt (m := ∞) (by simp)).of_le (by simp)
  have hKr : DifferentiableAt ℝ (symmetricNormalFlux K.a K.b u) p :=
    ((hK.1.mul hur).add (hK.2.1.mul hut)).differentiableAt one_ne_zero
  have hKt : DifferentiableAt ℝ (symmetricAngularFlux K.b K.c u) p :=
    ((hK.2.1.mul hur).add (hK.2.2.mul hut)).differentiableAt one_ne_zero
  have hcmp := divergenceOperator_difference_same_radial L K
    (returnCorrectedCoefficients_a D S C χ z).symm u p
    ((contDiffAt_symmetricNormalFlux hL.1 hL.2.1 hu.contDiffAt).differentiableAt (by simp))
    hKr
    ((contDiffAt_symmetricAngularFlux hL.2.1 hL.2.2 hu.contDiffAt).differentiableAt (by simp))
    hKt
  have heq : ∀ᶠ q in 𝓝 p,
      returnCorrectionCoefficientError D S C R χ z q (R.residual z) =
        (L.b q - K.b q, L.c q - K.c q) := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
    exact hN01.returnCorrectionCoefficientError_at_actual_of_cutoffs hN02 hS hz hsector χ hdisc q hq
  have hF : (fun q => (L.b q - K.b q) * angularPartial u q) =ᶠ[𝓝 p]
      returnCorrectionRadialErrorFlux D S C R χ z (R.residual z) η := by
    filter_upwards [heq] with q hq
    simp only [returnCorrectionRadialErrorFlux, hq, u]
  have hG : (fun q => (L.b q - K.b q) * radialPartial u q +
      (L.c q - K.c q) * angularPartial u q) =ᶠ[𝓝 p]
      returnCorrectionAngularErrorFlux D S C R χ z (R.residual z) η := by
    filter_upwards [heq] with q hq
    simp only [returnCorrectionAngularErrorFlux, hq, u]
  have hFr : radialPartial (fun q => (L.b q - K.b q) * angularPartial u q) p =
      radialPartial (returnCorrectionRadialErrorFlux D S C R
        χ z (R.residual z) η) p :=
    congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (1, 0)) (hF.fderiv_eq (𝕜 := ℝ))
  have hGt : angularPartial (fun q => (L.b q - K.b q) * radialPartial u q +
      (L.c q - K.c q) * angularPartial u q) p =
      angularPartial (returnCorrectionAngularErrorFlux D S C R
        χ z (R.residual z) η) p :=
    congrArg (fun A : PolarPoint →L[ℝ] ℝ => A (0, 1)) (hG.fderiv_eq (𝕜 := ℝ))
  rw [hFr, hGt] at hcmp
  change divergenceOperator L u p - divergenceOperator K u p = _
  rw [hcmp]
  simp only [returnCorrectionResidualErrorField, if_pos hp]
  rfl

theorem N01Properties.divergenceOperator_returnCorrectionResidualErrorBilinear
    (η : HeightPair S) (p : PolarPoint) (hp : p ∈ annularOpen D) :
    divergenceOperator (originalCoefficients D S C z) (heightPairField S η) p -
      divergenceOperator (returnCorrectedCoefficients D S C χ z)
        (heightPairField S η) p =
      returnCorrectionResidualErrorBilinearOfCutoffs hN01 hS hT R hz hsector
        χ hχ hχrange hsupp hend hdisc (R.residual z) η p := by
  rw [returnCorrectionResidualErrorBilinearOfCutoffs_apply]
  exact hN01.divergenceOperator_returnCorrectedCoefficients hN02 hS hT hz hsector
    χ hχ hχrange hsupp hend hdisc η p hp

end ActualOperator

end ContinuousFlexibility.Statements
