import ContinuousFlexibility.Analysis.ReturnOpticalCutoffPatching
import ContinuousFlexibility.Analysis.N01OpticalCollarPositivity

/-!
# Actual optical-cutoff error and source compatibility

The quantitative cutoff family has a strictly positive actual
characteristic discriminant on its transition supports. This closes
the regularity input of the frozen independent-residual error. The
actual differential field is smooth on the open annulus, bilinear in
the original residual and height spaces, and has zero physical source
integral. Weighted jet integrability is isolated as the remaining
source-membership condition.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis
open scoped Topology ContDiff

section CutoffError

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (R : ReturnEquationData S) {z : AnnularState S × ℝ}
  (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
  (χ : ℕ → ℝ → ℝ) (hχ : ∀ m, ContDiff ℝ ∞ (χ m))
  (hχrange : ∀ m r, r ∈ Icc (C.left m) (C.right m) → χ m r ∈ Icc (0 : ℝ) 1)
  (hsupp : ∀ m, Function.support (deriv (χ m)) ⊆ Ioo (C.left m) (C.right m))
  (hend : ∀ m, χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
    χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1))
  (hdisc : ∀ m p, p.1 ∈ tsupport (deriv (χ m)) →
    0 < (originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)

include hN hS hT hz hsector hχ hχrange hsupp hend hdisc

theorem N01Properties.returnCorrectionErrorFluxes_contDiffAt_of_cutoffs
    (ρ : CircleSpace S) (η : HeightPair S) (p : PolarPoint) (hp : p ∈ annularOpen D) :
    ContDiffAt ℝ ∞ (returnCorrectionRadialErrorFlux D S C R χ z ρ η) p ∧
      ContDiffAt ℝ ∞ (returnCorrectionAngularErrorFlux D S C R χ z ρ η) p := by
  have hc := hN.returnCorrectionCoefficientError_contDiffAt_of_cutoffs
    hS hT R hz hsector χ hχ hχrange hsupp hend hdisc ρ p hp
  have hu : ContDiff ℝ ∞ (heightPairField S η) :=
    physical_height_with_cutoff_contDiff hT hS (by norm_num : (0 : ℝ) < 3 / 4) η.1 η.2
  have hur : ContDiffAt ℝ ∞ (radialPartial (heightPairField S η)) p :=
    contDiffAt_radialPartial hu.contDiffAt (m := ∞) (by simp)
  have hut : ContDiffAt ℝ ∞ (angularPartial (heightPairField S η)) p :=
    contDiffAt_angularPartial hu.contDiffAt (m := ∞) (by simp)
  exact ⟨hc.fst.mul hut, (hc.fst.mul hur).add (hc.snd.mul hut)⟩

theorem N01Properties.returnCorrectionResidualErrorField_contDiffOn_of_cutoffs
    (ρ : CircleSpace S) (η : HeightPair S) :
    ContDiffOn ℝ ∞ (returnCorrectionResidualErrorField D S C R χ z ρ η) (annularOpen D) := by
  intro p hp
  obtain ⟨hF, hG⟩ := hN.returnCorrectionErrorFluxes_contDiffAt_of_cutoffs
    hS hT R hz hsector χ hχ hχrange hsupp hend hdisc ρ η p hp
  have hs := (contDiffAt_radialPartial hF (m := ∞) (by simp)).add
    (contDiffAt_angularPartial hG (m := ∞) (by simp))
  apply ContDiffAt.contDiffWithinAt
  apply hs.congr_of_eventuallyEq
  have hmem : ∀ᶠ q : PolarPoint in 𝓝 p, q ∈ annularOpen D :=
    (isOpen_Ioo.prod isOpen_univ).mem_nhds hp
  filter_upwards [hmem] with q hq
  unfold returnCorrectionResidualErrorField
    returnCorrectionRadialErrorFlux returnCorrectionAngularErrorFlux
  split_ifs with h
  · rfl
  · exact False.elim (h hq)

omit hS hT hz hsector hχ hχrange hdisc in
theorem N01Properties.returnCorrectionResidualErrorField_eq_zero_outside_of_cutoffs
    (ρ : CircleSpace S) (η : HeightPair S) (p : PolarPoint)
    (hp : p ∈ annularOpen D)
    (hout : ¬ ∃ m, p.1 ∈ Ioo (C.left m) (C.right m)) :
    returnCorrectionResidualErrorField D S C R χ z ρ η p = 0 := by
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  have hn : 0 ≤ deriv D.w p.1 := by
    by_contra h
    exact hout (hC.2.2.2.2.1 p.1 hp.1 (lt_of_not_ge h))
  exact returnCorrectionResidualErrorField_eq_zero_of_eventually_zero D S C R χ z ρ η p
    (returnCorrectionCoefficientError_eventually_zero D S C R χ z p
      (hN.cutoffs_deriv_eventually_zero_of_nonnegative χ hsupp hend hp.1 hn))

theorem N01Properties.returnCorrectionResidualErrorField_componentIntegral_of_cutoffs
    (ρ : CircleSpace S) (η : HeightPair S) (m : ℕ) :
    (∫ r in C.left m..C.right m, angularMean (fun θ =>
      returnCorrectionResidualErrorField D S C R χ z ρ η (r, θ))) = 0 := by
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  let F := returnCorrectionRadialErrorFlux D S C R χ z ρ η
  let G := returnCorrectionAngularErrorFlux D S C R χ z ρ η
  have hcore (r : ℝ) (hr : r ∈ uIcc (C.left m) (C.right m)) (θ : ℝ) :
      (r, θ) ∈ annularOpen D := by
    rw [uIcc_of_le (hC.1 m).2.1.le] at hr
    exact ⟨⟨(hC.1 m).1.trans_le hr.1, hr.2.trans_lt (hC.1 m).2.2⟩, mem_univ _⟩
  have hF : ∀ p ∈ uIcc (C.left m) (C.right m) ×ˢ uIcc (0 : ℝ) Real.pi,
      ContDiffAt ℝ 1 F p := by
    intro p hp
    exact (hN.returnCorrectionErrorFluxes_contDiffAt_of_cutoffs
      hS hT R hz hsector χ hχ hχrange hsupp hend hdisc
      ρ η p (hcore p.1 hp.1 p.2)).1.of_le (by simp)
  have hG : ∀ p ∈ uIcc (C.left m) (C.right m) ×ˢ uIcc (0 : ℝ) Real.pi,
      ContDiffAt ℝ 1 G p := by
    intro p hp
    exact (hN.returnCorrectionErrorFluxes_contDiffAt_of_cutoffs
      hS hT R hz hsector χ hχ hχrange hsupp hend hdisc
      ρ η p (hcore p.1 hp.1 p.2)).2.of_le (by simp)
  have hperiod : ∀ r ∈ uIcc (C.left m) (C.right m), G (r, Real.pi) = G (r, 0) := by
    intro r _
    simpa only [G, Prod.mk_add_mk, add_zero, zero_add] using
      (hN.returnCorrectionErrorFluxes_periodic hS R χ hz hsector hχrange ρ η).2 (r, 0)
  have hrootzero (r : ℝ) (hr : r ∈ Ioo D.a D.b) (hr0 : deriv D.w r = 0) (θ : ℝ) :
      F (r, θ) = 0 := by
    have heq := (returnCorrectionCoefficientError_eventually_zero D S C R χ z (r, θ)
      (hN.cutoffs_deriv_eventually_zero_of_nonnegative χ hsupp hend hr
        (by rw [hr0]))).eq_of_nhds
    simp only [F, returnCorrectionRadialErrorFlux, heq, LinearMap.zero_apply,
      Prod.fst_zero, zero_mul]
  have hboundary : ∀ θ ∈ uIcc (0 : ℝ) Real.pi,
      F (C.right m, θ) = F (C.left m, θ) := by
    intro θ _
    rw [hrootzero (C.right m)
      ⟨(hC.1 m).1.trans (hC.1 m).2.1, (hC.1 m).2.2⟩ (hC.2.1 m).2.1 θ,
      hrootzero (C.left m)
        ⟨(hC.1 m).1, (hC.1 m).2.1.trans (hC.1 m).2.2⟩ (hC.2.1 m).1 θ]
  let α : PlaneOneForm := ⟨fun p => -G p, F⟩
  have h := integral_exteriorCoefficient_eq_zero (α := α)
    (fun p hp => (hG p hp).neg) hF
    (fun r hr => congrArg Neg.neg (hperiod r hr)) hboundary
  change (∫ r in C.left m..C.right m, ∫ θ in (0 : ℝ)..Real.pi,
    radialPartial F (r, θ) - angularPartial (fun p => -G p) (r, θ)) = 0 at h
  simp only [angularPartial_neg_total, sub_neg_eq_add] at h
  calc
    (∫ r in C.left m..C.right m, angularMean (fun θ =>
        returnCorrectionResidualErrorField D S C R χ z ρ η (r, θ))) =
      ∫ r in C.left m..C.right m, (1 / Real.pi) *
        ∫ θ in (0 : ℝ)..Real.pi, radialPartial F (r, θ) + angularPartial G (r, θ) := by
      apply intervalIntegral.integral_congr
      intro r hr
      apply congrArg ((1 / Real.pi) * ·)
      apply intervalIntegral.integral_congr
      intro θ _
      simp only [returnCorrectionResidualErrorField, if_pos (hcore r hr θ)]
      rfl
    _ = (1 / Real.pi) * ∫ r in C.left m..C.right m, ∫ θ in (0 : ℝ)..Real.pi,
        radialPartial F (r, θ) + angularPartial G (r, θ) := by
      rw [intervalIntegral.integral_const_mul]
    _ = 0 := by rw [h, mul_zero]

theorem N01Properties.returnCorrectionResidualErrorField_sourceIntegral_of_cutoffs
    (ρ : CircleSpace S) (η : HeightPair S) :
    physicalSourceIntegral D (returnCorrectionResidualErrorField D S C R χ z ρ η) = 0 := by
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  have hab : D.a ≤ D.b := ((hC.1 0).1.trans ((hC.1 0).2.1.trans (hC.1 0).2.2)).le
  apply intervalIntegral_eq_zero_of_disjoint_components hab C.left C.right hC.1 hC.2.2.1
  · intro r hr hout
    have hzero (θ : ℝ) :=
      hN.returnCorrectionResidualErrorField_eq_zero_outside_of_cutoffs
        R (z := z) χ hsupp hend ρ η (r, θ) ⟨hr, mem_univ _⟩ hout
    simp only [angularMean, hzero, intervalIntegral.integral_zero, mul_zero]
  · exact hN.returnCorrectionResidualErrorField_componentIntegral_of_cutoffs
      hS hT R hz hsector χ hχ hχrange hsupp hend hdisc ρ η

def returnCorrectionResidualErrorBilinearOfCutoffs :
    CircleSpace S →ₗ[ℝ] HeightPair S →ₗ[ℝ] (PolarPoint → ℝ) :=
  spatialDirectionalBilinear (annularOpen D) (1, 0)
      (returnCorrectionRadialErrorFluxBilinear hS hT C R χ z)
      (fun ρ η p hp => by
        rw [returnCorrectionRadialErrorFluxBilinear_apply]
        exact (hN.returnCorrectionErrorFluxes_contDiffAt_of_cutoffs
          hS hT R hz hsector χ hχ hχrange hsupp hend hdisc
          ρ η p hp).1.differentiableAt (by simp)) +
    spatialDirectionalBilinear (annularOpen D) (0, 1)
      (returnCorrectionAngularErrorFluxBilinear hS hT C R χ z)
      (fun ρ η p hp => by
        rw [returnCorrectionAngularErrorFluxBilinear_apply]
        exact (hN.returnCorrectionErrorFluxes_contDiffAt_of_cutoffs
          hS hT R hz hsector χ hχ hχrange hsupp hend hdisc
          ρ η p hp).2.differentiableAt (by simp))

theorem returnCorrectionResidualErrorBilinearOfCutoffs_apply
    (ρ : CircleSpace S) (η : HeightPair S) :
    returnCorrectionResidualErrorBilinearOfCutoffs
      hN hS hT R hz hsector χ hχ hχrange hsupp hend hdisc ρ η =
      returnCorrectionResidualErrorField D S C R χ z ρ η := by
  classical
  funext p
  simp only [returnCorrectionResidualErrorBilinearOfCutoffs, LinearMap.add_apply, Pi.add_apply,
    spatialDirectionalBilinear_apply, returnCorrectionRadialErrorFluxBilinear_apply,
    returnCorrectionAngularErrorFluxBilinear_apply]
  by_cases hp : p ∈ annularOpen D
  · simp only [if_pos hp, returnCorrectionResidualErrorField, if_pos hp,
      radialPartial, angularPartial]
    unfold returnCorrectionRadialErrorFlux returnCorrectionAngularErrorFlux
    rfl
  · simp only [if_neg hp, returnCorrectionResidualErrorField, if_neg hp, add_zero]

theorem N01Properties.returnCorrectionResidualErrorField_heightMember_iff
    (ρ : CircleSpace S) (η : HeightPair S) :
    HeightMember D T (3 / 4 : ℝ) (returnCorrectionResidualErrorField D S C R χ z ρ η) ↔
      ∀ a b c : ℕ, MemLp (weightedPhysicalJet T (3 / 4 : ℝ) a b c
        (returnCorrectionResidualErrorField D S C R χ z ρ η)) 2 materialCylinderMeasure := by
  constructor
  · exact fun h => h.2.2.2.2
  · intro h
    exact ⟨hN.returnCorrectionResidualErrorField_contDiffOn_of_cutoffs
        hS hT R hz hsector χ hχ hχrange hsupp hend hdisc ρ η,
      returnCorrectionResidualErrorField_even hS C R χ z ρ η,
      hN.returnCorrectionResidualErrorField_periodic hS R χ hz hsector hχrange ρ η,
      returnCorrectionResidualErrorField_zero_outside D S C R χ z ρ η, h⟩

end CutoffError

/-- One actual cutoff family and one common N01 neighborhood provide
smooth bilinear physical errors with the exact source-kernel identity,
for every independent residual and height increment. -/
theorem N01Properties.exists_opticalCorrection_error_compatible
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    ∃ base' : ℕ, ∃ ε' : ℝ, ∃ χ : ℕ → ℝ → ℝ,
      base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      N01Properties D T S C base' loss ε' ∧
      (∀ m, ContDiff ℝ ∞ (χ m) ∧ ∀ r, χ m r ∈ Icc (0 : ℝ) 1) ∧
      (∀ m, χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
        χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1) ∧
        tsupport (deriv (χ m)) ⊆ Ioo (C.left m) (C.right m)) ∧
      ∀ R : ReturnEquationData S, ∀ z ∈ stateNeighborhood S C base' ε',
        stateSector S z.1 →
        ∃ E : CircleSpace S →ₗ[ℝ] HeightPair S →ₗ[ℝ] (PolarPoint → ℝ),
        ∀ ρ η,
          E ρ η = returnCorrectionResidualErrorField D S C R χ z ρ η ∧
          ContDiffOn ℝ ∞ (E ρ η) (annularOpen D) ∧
          physicalSourceIntegral D (E ρ η) = 0 ∧
          (HeightMember D T (3 / 4 : ℝ) (E ρ η) ↔
            ∀ a b c : ℕ, MemLp (weightedPhysicalJet T (3 / 4 : ℝ) a b c
              (E ρ η)) 2 materialCylinderMeasure) := by
  obtain ⟨base', ε', χ, j, A, lam, P, hbase, hε', hεε, hA, hlam, hP,
    hnew, hcell, hχ, hend, hjets, hpositive⟩ :=
    hN.exists_positive_opticalCorrectionCutoffs hT
  refine ⟨base', ε', χ, hbase, hε', hεε, hnew, hχ, hend, ?_⟩
  intro R z hz hsector
  have hsupp (m : ℕ) : Function.support (deriv (χ m)) ⊆ Ioo (C.left m) (C.right m) :=
    (subset_tsupport _).trans (hend m).2.2
  have hχrange (m : ℕ) (r : ℝ) (_ : r ∈ Icc (C.left m) (C.right m)) :
      χ m r ∈ Icc (0 : ℝ) 1 := (hχ m).2 r
  have hdisc (m : ℕ) (p : PolarPoint) (hp : p.1 ∈ tsupport (deriv (χ m))) :
      0 < (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p :=
    (hpositive z hz m p hp).2.2.2.2
  let E := returnCorrectionResidualErrorBilinearOfCutoffs
    hnew hS hT R hz hsector χ (fun m => (hχ m).1) hχrange hsupp
    (fun m => ⟨(hend m).1, (hend m).2.1⟩) hdisc
  refine ⟨E, fun ρ η => ?_⟩
  have hE : E ρ η = returnCorrectionResidualErrorField D S C R χ z ρ η :=
    returnCorrectionResidualErrorBilinearOfCutoffs_apply
      hnew hS hT R hz hsector χ (fun m => (hχ m).1) hχrange hsupp
      (fun m => ⟨(hend m).1, (hend m).2.1⟩) hdisc ρ η
  refine ⟨hE, ?_⟩
  rw [hE]
  exact ⟨hnew.returnCorrectionResidualErrorField_contDiffOn_of_cutoffs
      hS hT R hz hsector χ (fun m => (hχ m).1) hχrange hsupp
      (fun m => ⟨(hend m).1, (hend m).2.1⟩) hdisc ρ η,
    hnew.returnCorrectionResidualErrorField_sourceIntegral_of_cutoffs
      hS hT R hz hsector χ (fun m => (hχ m).1) hχrange hsupp
      (fun m => ⟨(hend m).1, (hend m).2.1⟩) hdisc ρ η,
    hnew.returnCorrectionResidualErrorField_heightMember_iff
      hS hT R hz hsector χ (fun m => (hχ m).1) hχrange hsupp
      (fun m => ⟨(hend m).1, (hend m).2.1⟩) hdisc ρ η⟩

end ContinuousFlexibility.Statements

