import ContinuousFlexibility.Analysis.N01FlowJointSmoothness
import ContinuousFlexibility.Analysis.ReturnCorrectionResidualBilinear
import ContinuousFlexibility.Analysis.MaterialCylinderPointwise

/-!
# Smoothness of the actual independent-residual error

Joint smoothness of the forward flow on the positive-discriminant
region gives smoothness of its actual inverse and angular variation.
Every operation in the frozen correction is therefore smooth. The
global component selector agrees locally with the corresponding smooth
formula or with zero, including at every simple turning radius.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

section ActualVelocity

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN01 : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S z.1) (χ : ℕ → ℝ → ℝ) (m : ℕ)
  (hχ : ContDiff ℝ ∞ (χ m))
  (hχrange : ∀ r ∈ Icc (C.left m) (C.right m), χ m r ∈ Icc (0 : ℝ) 1)

include hN01 hS hT hz hsector hχ hχrange

theorem N01Properties.returnCorrectionVelocityLinear_contDiffAt
    (ρ : CircleSpace S) (p : PolarPoint) (hp : p.1 ∈ Ioo (C.left m) (C.right m))
    (hdisc : 0 < (originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p) :
    ContDiffAt ℝ ∞ (fun q : PolarPoint => returnCorrectionVelocityLinear D S C χ z m q ρ) p := by
  let A : PolarPoint → ℝ := fun q => Function.invFun (C.minusFlow z m q.1) q.2
  let B : PolarPoint → ℝ := fun q =>
    Function.invFun (returnInterpolation (χ m q.1) (returnCorrectionInitialMap S C z m)) (A q)
  have hA : ContDiffAt ℝ ∞ A p :=
    hN01.minusFlow_invFun_contDiffAt_of_discriminant hS hT hz hsector m p hp hdisc
  have hB : ContDiffAt ℝ ∞ B p := by
    have ho : ContDiffAt ℝ ∞ (fun q : PolarPoint =>
        Function.invFun (returnInterpolation (χ m q.1)
          (returnCorrectionInitialMap S C z m)) q.2) (p.1, A p) :=
      hN01.returnInterpolation_invFun_contDiffAt hS hT hz hsector χ m hχ hχrange
        (p.1, A p) hp
    simpa only [B, Function.comp_def] using ho.comp p (contDiffAt_fst.prodMk hA)
  have hclosed : p.1 ∈ Icc (C.left m) (C.right m) := ⟨hp.1.le, hp.2.le⟩
  have hsurj := returnLift_surjective Real.pi_pos
    (N01Properties.minusFlow_differentiable S C z m hN01 hz hclosed).continuous
    (hN01.minusFlow_add_period hz m hclosed)
  have hpoint : (p.1, C.minusFlow z m p.1 (A p)) = p := by
    apply Prod.ext
    · rfl
    · exact Function.rightInverse_invFun hsurj p.2
  have hdisc' : 0 < (originalCoefficients D S C z).b
        (p.1, C.minusFlow z m p.1 (A p)) ^ 2 -
      (originalCoefficients D S C z).a (p.1, C.minusFlow z m p.1 (A p)) *
        (originalCoefficients D S C z).c (p.1, C.minusFlow z m p.1 (A p)) := by
    rw [hpoint]
    exact hdisc
  have hvariation : ContDiffAt ℝ ∞
      (fun q : PolarPoint => deriv (C.minusFlow z m q.1) (A q)) p := by
    have ho : ContDiffAt ℝ ∞ (fun q : PolarPoint => deriv (C.minusFlow z m q.1) q.2)
        (p.1, A p) :=
      hN01.minusFlow_angular_deriv_contDiffAt_of_discriminant hS hT hz hsector m
        (p.1, A p) hp hdisc'
    simpa only [Function.comp_def] using ho.comp p (contDiffAt_fst.prodMk hA)
  have hcutoff : ContDiffAt ℝ ∞ (fun q : PolarPoint => deriv (χ m) q.1) p :=
    ((contDiff_infty_iff_deriv.mp hχ).2.comp contDiff_fst).contDiffAt
  have hdisplacement : ContDiffAt ℝ ∞
      (fun q : PolarPoint => returnCorrectionDisplacementLinear S C z m (B q) ρ) p :=
    (hN01.returnCorrectionDisplacementLinear_contDiff hS hT hz hsector m ρ).contDiffAt.comp p hB
  exact ((hvariation.mul hcutoff).mul hdisplacement).congr_of_eventuallyEq
    (Eventually.of_forall fun q => by
      simp only [returnCorrectionVelocityLinear, LinearMap.smul_apply, smul_eq_mul,
        Pi.mul_apply, A, B])

theorem N01Properties.returnCorrectionDriftSpeedLinear_contDiffAt
    (ρ : CircleSpace S) (p : PolarPoint) (hp : p.1 ∈ Ioo (C.left m) (C.right m))
    (hdisc : 0 < (originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p) :
    ContDiffAt ℝ ∞ (fun q : PolarPoint => returnCorrectionDriftLinear D S C χ z m q ρ) p ∧
      ContDiffAt ℝ ∞ (fun q : PolarPoint => returnCorrectionSpeedLinear D S C χ z m q ρ) p := by
  have hv := hN01.returnCorrectionVelocityLinear_contDiffAt hS hT hz hsector
    χ m hχ hχrange ρ p hp hdisc
  obtain ⟨ha, hb, hc⟩ := originalCoefficients_parity_of_physical hS C z p.1 p.2
  have hdisc' : 0 < (originalCoefficients D S C z).b (p.1, -p.2) ^ 2 -
      (originalCoefficients D S C z).a (p.1, -p.2) *
        (originalCoefficients D S C z).c (p.1, -p.2) := by
    rw [ha, hb, hc, neg_sq]
    exact hdisc
  have href : ContDiffAt ℝ ∞ (fun q : PolarPoint => (q.1, -q.2)) p :=
    contDiffAt_fst.prodMk contDiffAt_snd.neg
  have hvr := (hN01.returnCorrectionVelocityLinear_contDiffAt hS hT hz hsector
    χ m hχ hχrange ρ (p.1, -p.2) hp hdisc').comp p href
  constructor
  · exact ((hv.sub hvr).div_const 2).congr_of_eventuallyEq
      (Eventually.of_forall fun q => by
        simp only [returnCorrectionDriftLinear_apply, Pi.sub_apply, Function.comp_def])
  · exact ((hvr.neg.sub hv).div_const 2).congr_of_eventuallyEq
      (Eventually.of_forall fun q => by
        simp only [returnCorrectionSpeedLinear_apply, Pi.neg_apply, Pi.sub_apply, Function.comp_def])

end ActualVelocity

theorem N01Properties.returnCorrectionLocalCoefficientError_contDiffAt
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (R : ReturnEquationData S) {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (χ : ℕ → ℝ → ℝ) (m : ℕ) (hχ : ContDiff ℝ ∞ (χ m))
    (hχrange : ∀ r ∈ Icc (C.left m) (C.right m), χ m r ∈ Icc (0 : ℝ) 1)
    (ρ : CircleSpace S) (p : PolarPoint) (hp : p.1 ∈ Ioo (C.left m) (C.right m))
    (hdisc : 0 < (originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p) :
    ContDiffAt ℝ ∞ (fun q => returnCorrectionLocalCoefficientError D S C R χ z m q ρ) p := by
  have hC : controlGeometryConditions D S C := hN01.2.2.2.1
  have hpD : p ∈ annularOpen D :=
    ⟨⟨(hC.1 m).1.trans hp.1, hp.2.trans (hC.1 m).2.2⟩, mem_univ _⟩
  obtain ⟨ha, hb, hc⟩ := hN01.originalCoefficients_contDiffAt hS hT hz hsector hpD
  have hapos := hN01.originalRadialCoefficient_pos hz hsector hpD
  have hd := hb.div ha hapos.ne'
  have hv := (((hb.pow 2).sub (ha.mul hc)).sqrt hdisc.ne').div ha hapos.ne'
  have hsρ := hN01.returnCorrectionDriftSpeedLinear_contDiffAt
    hS hT hz hsector χ m hχ hχrange ρ p hp hdisc
  have hse := hN01.returnCorrectionDriftSpeedLinear_contDiffAt
    hS hT hz hsector χ m hχ hχrange (R.residual z) p hp hdisc
  have htwod : ContDiffAt ℝ ∞ (fun q : PolarPoint =>
      (2 : ℝ) * ((originalCoefficients D S C z).b q /
        (originalCoefficients D S C z).a q)) p := contDiffAt_const.mul hd
  have htwov : ContDiffAt ℝ ∞ (fun q : PolarPoint =>
      (2 : ℝ) * (Real.sqrt ((originalCoefficients D S C z).b q ^ 2 -
        (originalCoefficients D S C z).a q * (originalCoefficients D S C z).c q) /
          (originalCoefficients D S C z).a q)) p := contDiffAt_const.mul hv
  have hfirst := ha.neg.mul hsρ.1
  have hsecond := ((ha.neg.mul (htwod.add hse.1)).mul hsρ.1).add
    ((ha.mul (htwov.add hse.2)).mul hsρ.2)
  exact (hfirst.prodMk hsecond).congr_of_eventuallyEq
    (Eventually.of_forall fun q => by
      simp only [returnCorrectionLocalCoefficientError, returnCoefficientError_apply])

section GlobalError

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN01 : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (R : ReturnEquationData S) {z : AnnularState S × ℝ}
  (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
  (hdisc : ∀ m p, p.1 ∈ Icc ((2 * C.left m + C.right m) / 3)
      ((C.left m + 2 * C.right m) / 3) →
    0 < (originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)

include hN01 hS hT hz hsector hdisc

theorem N01Properties.returnCorrectionCoefficientError_contDiffAt
    (ρ : CircleSpace S) (p : PolarPoint) (hp : p ∈ annularOpen D) :
    ContDiffAt ℝ ∞
      (fun q => returnCorrectionCoefficientError D S C R (returnCorrectionCutoffs C) z q ρ) p := by
  have hC : controlGeometryConditions D S C := hN01.2.2.2.1
  by_cases hex : ∃ m, p.1 ∈ Ioo (C.left m) (C.right m)
  · obtain ⟨m, hm⟩ := hex
    have heq := returnCorrectionCoefficientError_eventually_local (D := D)
      hC.2.2.1 R (returnCorrectionCutoffs C) z m p hm
    by_cases hmid : p.1 ∈ Icc ((2 * C.left m + C.right m) / 3)
        ((C.left m + 2 * C.right m) / 3)
    · have hl := hN01.returnCorrectionLocalCoefficientError_contDiffAt
        hS hT R hz hsector (returnCorrectionCutoffs C) m
        (returnCorrectionCutoff_contDiff _ _)
        (fun r _ => returnCorrectionCutoff_mem_Icc _ _ r) ρ p hm (hdisc m p hmid)
      apply hl.congr_of_eventuallyEq
      filter_upwards [heq] with q hq
      exact congrArg (fun L : CircleSpace S →ₗ[ℝ] ℝ × ℝ => L ρ) hq
    · have hmid' : ∀ᶠ r in 𝓝 p.1,
          r ∉ Icc ((2 * C.left m + C.right m) / 3)
            ((C.left m + 2 * C.right m) / 3) :=
        isClosed_Icc.isOpen_compl.mem_nhds hmid
      have hz' : (fun q => returnCorrectionCoefficientError D S C R
          (returnCorrectionCutoffs C) z q ρ) =ᶠ[𝓝 p] fun _ => (0 : ℝ × ℝ) := by
        filter_upwards [heq, continuous_fst.continuousAt.preimage_mem_nhds hmid'] with q hq hqm
        have hd : deriv (returnCorrectionCutoffs C m) q.1 = 0 := by
          by_contra hne
          exact hqm (returnCorrectionCutoff_deriv_support_subset (hC.1 m).2.1 hne)
        rw [hq, returnCorrectionLocalCoefficientError_eq_zero_of_deriv_zero
          D S C R (returnCorrectionCutoffs C) z m q hd, LinearMap.zero_apply]
      exact contDiffAt_const.congr_of_eventuallyEq hz'
  · have hn : 0 ≤ deriv D.w p.1 := by
      by_contra h
      exact hex (hC.2.2.2.2.1 p.1 hp.1 (lt_of_not_ge h))
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [hN01.returnCorrectionCoefficientError_eventually_zero_of_nonnegative
      R z p hp hn] with q hq
    rw [hq, LinearMap.zero_apply]

theorem N01Properties.returnCorrectionErrorFluxes_contDiffAt
    (ρ : CircleSpace S) (η : HeightPair S) (p : PolarPoint) (hp : p ∈ annularOpen D) :
    ContDiffAt ℝ ∞ (returnCorrectionRadialErrorFlux D S C R
      (returnCorrectionCutoffs C) z ρ η) p ∧
    ContDiffAt ℝ ∞ (returnCorrectionAngularErrorFlux D S C R
      (returnCorrectionCutoffs C) z ρ η) p := by
  have hc := hN01.returnCorrectionCoefficientError_contDiffAt hS hT R hz hsector hdisc ρ p hp
  have hu : ContDiff ℝ ∞ (heightPairField S η) :=
    physical_height_with_cutoff_contDiff hT hS (by norm_num : (0 : ℝ) < 3 / 4) η.1 η.2
  have hur : ContDiffAt ℝ ∞ (radialPartial (heightPairField S η)) p :=
    contDiffAt_radialPartial hu.contDiffAt (m := ∞) (by simp)
  have hut : ContDiffAt ℝ ∞ (angularPartial (heightPairField S η)) p :=
    contDiffAt_angularPartial hu.contDiffAt (m := ∞) (by simp)
  exact ⟨(hc.fst).mul hut, ((hc.fst).mul hur).add ((hc.snd).mul hut)⟩

theorem N01Properties.returnCorrectionResidualErrorField_contDiffOn
    (ρ : CircleSpace S) (η : HeightPair S) :
    ContDiffOn ℝ ∞
      (returnCorrectionResidualErrorField D S C R (returnCorrectionCutoffs C) z ρ η)
      (annularOpen D) := by
  intro p hp
  obtain ⟨hF, hG⟩ := hN01.returnCorrectionErrorFluxes_contDiffAt hS hT R hz hsector hdisc ρ η p hp
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

theorem N01Properties.returnCorrectionResidualErrorField_materialPullback_contDiff
    (ρ : CircleSpace S) (η : HeightPair S) :
    ContDiff ℝ ∞ (materialPullback T (3 / 4 : ℝ)
      (returnCorrectionResidualErrorField D S C R (returnCorrectionCutoffs C) z ρ η)) :=
  contDiff_materialPullback hT
    (hN01.returnCorrectionResidualErrorField_contDiffOn hS hT R hz hsector hdisc ρ η)

end GlobalError

end ContinuousFlexibility.Statements
