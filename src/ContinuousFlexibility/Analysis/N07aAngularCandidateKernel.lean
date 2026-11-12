import ContinuousFlexibility.Analysis.N07aAngularCandidateDomain
import ContinuousFlexibility.Analysis.N07aAngularCandidateOperator
import ContinuousFlexibility.Analysis.N07aAngularHeightInjective

/-!
# The exact homogeneous physical scalar equation has trivial kernel

An arbitrary normalized physical height pair is first placed in the
actual fixed N05 graph. Its original differential equation forces its
actual N06 image to vanish. The already proved inverse identities then
kill the graph element and, through the genuine coordinates, the height.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {b base loss : ℕ} {B : CanonicalDomainData S K V b}
  {P : RelativeInverseData S K V b B} {ε : ℝ}

theorem n07a_heightPair_homogeneous_eq_zero
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hborder : RadialTrueBorder D)
    (hrad : CanonicalGeometry.ReferenceRadial S C K)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hRatio : N07aActualMaterialRatios T S C K base ε)
    (hcanonical : CanonicalPrimitiveGeometry D T S C L K base ε)
    (h05 : N05Properties D T S C K V b B)
    (h06 : N06Properties D S C K L V b B P base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (u : HeightPair S) (μ : ℝ)
    (hrow : referenceRow D (heightPairField S u) = 0)
    (heq : ∀ p ∈ annularOpen D,
      divergenceOperator (L.coefficients (liftSectorParameter S C z))
        (heightPairField S u) p + μ * nuColumnField D S C (liftSectorParameter S C z) p = 0) :
    (u, μ) = 0 := by
  have domain := n07a_currentHeightPair_enters_referenceDomain
    hD hT hS h01 h02 h03 h04 hborder hrad href hcur hRatio hcanonical h05 z hz u μ hrow
  let d : B.Space := domain.choose
  have haL : d.val.1.2.1 = u.2 := domain.choose_spec.1
  have hμ : d.val.1.2.2.1 = μ := domain.choose_spec.2.1
  have hAux : d.val.1.2.2.2 = 0 := domain.choose_spec.2.2.1
  have hU := domain.choose_spec.2.2.2
  have hz' := liftSectorParameter_mem_stateNeighborhood (C := C) hz le_rfl
  have hs := h01.2.2.1.liftSectorParameter_sector z
  have hPd := n07a_candidate_operator_eq_zero hD.choose_spec.1.2.1.le hS hT h01 h03 h04
    href hcur h05.2.1 h06 z hz u μ d haL hμ hAux hU heq
  have hd : d = 0 := n07a_operator_injective h05 h06 hz' hs
    (hPd.trans (P.operator (liftSectorParameter S C z)).map_zero.symm)
  have ha0 : d.val.1.2.1 = 0 := by
    simpa only [Submodule.coe_zero, Prod.fst_zero, Prod.snd_zero] using
      congrArg (fun x : B.Space => x.val.1.2.1) hd
  have hμ0 : d.val.1.2.2.1 = 0 := by
    simpa only [Submodule.coe_zero, Prod.fst_zero, Prod.snd_zero] using
      congrArg (fun x : B.Space => x.val.1.2.2.1) hd
  have hheight : u.1 = 0 := by
    apply n07a_height_eq_zero_of_canonical hS h04 hz' hs u.1
    intro m
    have hcoord : d.val.1.1 m = (0 : CanonicalL2 S K m) := by
      simpa only [Submodule.coe_zero, Prod.fst_zero, lp.coeFn_zero, Pi.zero_apply] using
        congrArg (fun x : B.Space => x.val.1.1 m) hd
    have hcoordFunction : (d.val.1.1 m : PolarPoint → ℝ) =
        ((0 : CanonicalL2 S K m) : PolarPoint → ℝ) :=
      congrArg (fun x : CanonicalL2 S K m => (x : PolarPoint → ℝ)) hcoord
    have hzero : ((0 : CanonicalL2 S K m) : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K m] fun _ => 0 :=
      Lp.coeFn_zero ℝ 2 (canonicalMeasure S K m)
    have hae : (d.val.1.1 m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        ((0 : CanonicalL2 S K m) : PolarPoint → ℝ) :=
      Eventually.of_forall (fun p => congrFun hcoordFunction p)
    exact (hU m).symm.trans (hae.trans hzero)
  exact Prod.ext (Prod.ext hheight (haL.symm.trans ha0)) (hμ.symm.trans hμ0)

end ContinuousFlexibility.Analysis
