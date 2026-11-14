module

public import ContinuousFlexibility.Analysis.ReturnCorrectionErrorSupport
public import ContinuousFlexibility.Analysis.ReturnCorrectionVelocityRegularity

/-!
# Regularity of the actual frozen coefficient error

The forward flow, its inverse, interpolation inverse and divided
difference have already been constructed from N01. Their established
regularity proves C¹ regularity of the actual independent-residual
coefficient error. The sole geometric input is positivity of the original
characteristic discriminant on the closed correction collars.

Away from those collars the actual coefficient map is identically zero
on a neighborhood. Thus no regularity of a square root at a turning point
is assumed, and the global selector introduces no interface term.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

theorem N01Properties.originalCoefficients_contDiffAt
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    ContDiffAt ℝ ∞ (originalCoefficients D S C z).a p ∧
      ContDiffAt ℝ ∞ (originalCoefficients D S C z).b p ∧
      ContDiffAt ℝ ∞ (originalCoefficients D S C z).c p := by
  have hreg := hN01.characteristic_coefficient_regular hS hT hz hsector hp
  obtain ⟨_, hgeom⟩ := hN01.1.1
  have hr : p.1 ≠ 0 := (hgeom.1.1.trans hp.1.1).ne'
  have hw := contDiff_stateProfile_of_n01 hS hT hN01 z.1
  have hh := hN01.stateHeight_contDiff hS hT z
  have hc := (contDiffAt_heightLinearCoefficients hw.contDiffAt hh.contDiffAt
    hr hreg.2.1 hreg.2.2.1).2.2.2.1
  exact ⟨hreg.2.2.2.1, hreg.2.2.2.2.1, hc⟩

theorem N01Properties.returnCorrectionLocalCoefficientError_contDiffAt_one
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (R : ReturnEquationData S) {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (χ : ℕ → ℝ → ℝ) (m : ℕ) (hχ : ContDiff ℝ ∞ (χ m))
    (hχrange : ∀ r ∈ Icc (C.left m) (C.right m), χ m r ∈ Icc (0 : ℝ) 1)
    (ρ : CircleSpace S) (p : PolarPoint) (hp : p.1 ∈ Ioo (C.left m) (C.right m))
    (hdisc : (originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p ≠ 0) :
    ContDiffAt ℝ 1 (fun q => returnCorrectionLocalCoefficientError D S C R χ z m q ρ) p := by
  have hC : controlGeometryConditions D S C := hN01.2.2.2.1
  have hpD : p ∈ annularOpen D :=
    ⟨⟨(hC.1 m).1.trans hp.1, hp.2.trans (hC.1 m).2.2⟩, mem_univ _⟩
  have hreg := hN01.originalCoefficients_contDiffAt hS hT hz hsector hpD
  have ha : ContDiffAt ℝ 1 (originalCoefficients D S C z).a p := hreg.1.of_le (by simp)
  have hb : ContDiffAt ℝ 1 (originalCoefficients D S C z).b p := hreg.2.1.of_le (by simp)
  have hc : ContDiffAt ℝ 1 (originalCoefficients D S C z).c p := hreg.2.2.of_le (by simp)
  have hapos := hN01.originalRadialCoefficient_pos hz hsector hpD
  have hd := hb.div ha hapos.ne'
  have hv := (((hb.pow 2).sub (ha.mul hc)).sqrt hdisc).div ha hapos.ne'
  have hsρ := hN01.returnCorrectionDriftSpeedLinear_contDiffAt_one
    hS hT hz hsector χ m hχ hχrange ρ p hp
  have hse := hN01.returnCorrectionDriftSpeedLinear_contDiffAt_one
    hS hT hz hsector χ m hχ hχrange (R.residual z) p hp
  have htwod : ContDiffAt ℝ 1 (fun q : PolarPoint =>
      (2 : ℝ) * ((originalCoefficients D S C z).b q /
        (originalCoefficients D S C z).a q)) p := contDiffAt_const.mul hd
  have htwov : ContDiffAt ℝ 1 (fun q : PolarPoint =>
      (2 : ℝ) * (Real.sqrt ((originalCoefficients D S C z).b q ^ 2 -
        (originalCoefficients D S C z).a q * (originalCoefficients D S C z).c q) /
          (originalCoefficients D S C z).a q)) p := contDiffAt_const.mul hv
  have hfirst := ha.neg.mul hsρ.1
  have hsecond := ((ha.neg.mul (htwod.add hse.1)).mul hsρ.1).add
    ((ha.mul (htwov.add hse.2)).mul hsρ.2)
  exact (hfirst.prodMk hsecond).congr_of_eventuallyEq
    (Eventually.of_forall fun q => by
      simp only [returnCorrectionLocalCoefficientError, returnCoefficientError_apply])

/-- Actual C¹ regularity on the open annulus. Positivity is needed only
on the closed middle thirds supporting the actual cutoff derivatives. -/
theorem N01Properties.returnCorrectionCoefficientError_contDiffAt_one
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (R : ReturnEquationData S) {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (hdisc : ∀ m p, p.1 ∈ Icc ((2 * C.left m + C.right m) / 3)
        ((C.left m + 2 * C.right m) / 3) →
      0 < (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)
    (ρ : CircleSpace S) (p : PolarPoint) (hp : p ∈ annularOpen D) :
    ContDiffAt ℝ 1
      (fun q => returnCorrectionCoefficientError D S C R (returnCorrectionCutoffs C) z q ρ) p := by
  have hC : controlGeometryConditions D S C := hN01.2.2.2.1
  by_cases hex : ∃ m, p.1 ∈ Ioo (C.left m) (C.right m)
  · obtain ⟨m, hm⟩ := hex
    have heq := returnCorrectionCoefficientError_eventually_local (D := D)
      hC.2.2.1 R (returnCorrectionCutoffs C) z m p hm
    by_cases hmid : p.1 ∈ Icc ((2 * C.left m + C.right m) / 3)
        ((C.left m + 2 * C.right m) / 3)
    · have hl := hN01.returnCorrectionLocalCoefficientError_contDiffAt_one
        hS hT R hz hsector (returnCorrectionCutoffs C) m
        (returnCorrectionCutoff_contDiff _ _)
        (fun r _ => returnCorrectionCutoff_mem_Icc _ _ r) ρ p hm (hdisc m p hmid).ne'
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

theorem N01Properties.returnCorrectionErrorFluxes_contDiffAt_one
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN01 : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (R : ReturnEquationData S) {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (hdisc : ∀ m p, p.1 ∈ Icc ((2 * C.left m + C.right m) / 3)
        ((C.left m + 2 * C.right m) / 3) →
      0 < (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p)
    (ρ : CircleSpace S) (η : HeightPair S) (p : PolarPoint) (hp : p ∈ annularOpen D) :
    ContDiffAt ℝ 1 (returnCorrectionRadialErrorFlux D S C R
      (returnCorrectionCutoffs C) z ρ η) p ∧
    ContDiffAt ℝ 1 (returnCorrectionAngularErrorFlux D S C R
      (returnCorrectionCutoffs C) z ρ η) p := by
  have hc := hN01.returnCorrectionCoefficientError_contDiffAt_one hS hT R hz hsector hdisc ρ p hp
  have hu : ContDiff ℝ ∞ (heightPairField S η) :=
    physical_height_with_cutoff_contDiff hT hS (by norm_num : (0 : ℝ) < 3 / 4) η.1 η.2
  have hur : ContDiffAt ℝ 1 (radialPartial (heightPairField S η)) p :=
    (contDiffAt_radialPartial hu.contDiffAt (m := ∞) (by simp)).of_le (by simp)
  have hut : ContDiffAt ℝ 1 (angularPartial (heightPairField S η)) p :=
    (contDiffAt_angularPartial hu.contDiffAt (m := ∞) (by simp)).of_le (by simp)
  exact ⟨(hc.fst).mul hut, ((hc.fst).mul hur).add ((hc.snd).mul hut)⟩

end ContinuousFlexibility.Statements
