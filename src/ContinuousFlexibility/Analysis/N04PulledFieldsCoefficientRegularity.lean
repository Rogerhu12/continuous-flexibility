import ContinuousFlexibility.Analysis.N04bOpticalFieldRealization
import ContinuousFlexibility.Analysis.N04RealizationCoefficientAnnularTowers
import ContinuousFlexibility.Analysis.N04RealizationJointMixedRegularity
import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentSplit
import ContinuousFlexibility.Analysis.N01cPhysicalFlowGraph

/-!
# Genuine mixed towers for the retained corrected coefficients

The optical coefficient jets describe the independently linear correction
error.  Substitution of the actual return residual gives the difference
between the original and corrected coefficients.  This module performs
that substitution before constructing the mixed towers of the retained
physical field, on its original state neighborhood and whole annulus.

The local material estimate is retained with its actual quantifiers.  It
does not by itself assert one neighborhood for every parameter order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

local instance n04PulledFieldsCoefficientRegularityStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

set_option backward.isDefEq.respectTransparency false

private def n04PulledFields_errorProjection (i : Fin 3) : (ℝ × ℝ) →L[ℝ] ℝ :=
  if i = 0 then 0 else if i = 1 then ContinuousLinearMap.fst ℝ ℝ ℝ
    else ContinuousLinearMap.snd ℝ ℝ ℝ

private theorem n04PulledFields_coefficient_reconstruction
    (i : Fin 3) (A B : SymmetricCoefficients) (ha : B.a = A.a) (p : PolarPoint) :
    canonicalCoefficientComponent i A p -
        n04PulledFields_errorProjection i (A.b p - B.b p, A.c p - B.c p) =
      canonicalCoefficientComponent i B p := by
  fin_cases i <;> simp [n04PulledFields_errorProjection, canonicalCoefficientComponent, ha]

private theorem n04PulledFields_error_zero_germ
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (R : ReturnEquationData S) (χ : ℕ → ℝ → ℝ)
    {p : PolarPoint} (hzero : ∀ᶠ r in 𝓝 p.1, ∀ m, deriv (χ m) r = 0)
    (z : AnnularState S × ℝ) (ρ : CircleSpace S) (π : (ℝ × ℝ) →L[ℝ] ℝ) :
    (fun q => π (returnCorrectionCoefficientError D S C R χ z q ρ)) =ᶠ[𝓝 p]
      (fun _ => 0) := by
  have hnear : ∀ᶠ q : PolarPoint in 𝓝 p, ∀ m, deriv (χ m) q.1 = 0 :=
    (continuous_fst.tendsto p).eventually hzero
  filter_upwards [hnear] with q hq
  have hinactive : ¬ ∃ m,
      q.1 ∈ Ioo (C.left m) (C.right m) ∧ deriv (χ m) q.1 ≠ 0 := by
    rintro ⟨m, _, hm⟩
    exact hm (hq m)
  simp only [returnCorrectionCoefficientError, dif_neg hinactive,
    LinearMap.zero_apply, map_zero]

private theorem n04PulledFields_mixed_zero_of_germ
    {f : PolarPoint → ℝ} {p : PolarPoint}
    (hz : f =ᶠ[𝓝 p] fun _ => 0) (a b : ℕ) :
    mixedDerivative a b f p = 0 :=
  (mixedDerivative_congr_of_eventuallyEq hz a b).trans
    (by simp only [mixedDerivative, iteratedDeriv_const, ite_self])

private def n04PulledFields_zeroGermParameterTower
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {U : Set E} (hU : IsOpen U) (f : E → PolarPoint → ℝ) (p : PolarPoint)
    (hz : ∀ x ∈ U, f x =ᶠ[𝓝 p] fun _ => 0) (a b : ℕ) :
    SmoothDirections U (fun x => mixedDerivative a b (f x) p) :=
  (smoothDirections_constant hU (0 : ℝ)).congrOn
    (fun x hx => (n04PulledFields_mixed_zero_of_germ (hz x hx) a b).symm)

section OpticalError

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}
  (Q : N04bOpticalCutoffData D S C base ε)
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hR : N02Properties D T S C R base ε)

/-- Zeroth order of the retained smooth coefficient jets is the actual
independent-residual error, including the global inactive extension. -/
theorem n04PulledFields_opticalCoefficientJets_zero
    (x : (StateDirections S × ℝ) × CircleSpace S)
    (hx : x ∈ sectorNeighborhood S base ε ε ×ˢ univ) :
    (Q.coefficientJets hN hS hT hR 0 x Fin.elim0).val =
      fun p => returnCorrectionCoefficientError D S C R Q.cutoff
        (liftSectorParameter S C x.1) p x.2 :=
  (Q.coefficientJets_apply hN hS hT hR 0 x hx Fin.elim0).trans
    (hN.returnCorrectionCoefficientScalarJets_zero hS hT hR Q.cell Q.component_cell
      Q.cutoff Q.range_on_component Q.derivative_bounds Q.active_discriminant x hx)

private theorem n04PulledFields_opticalError_spatial
    (π : (ℝ × ℝ) →L[ℝ] ℝ) (x : (StateDirections S × ℝ) × CircleSpace S)
    (hx : x ∈ sectorNeighborhood S base ε ε ×ˢ univ) :
    ContDiffOn ℝ ∞
      (fun p => π (returnCorrectionCoefficientError D S C R Q.cutoff
        (liftSectorParameter S C x.1) p x.2)) (annularOpen D) := by
  have hs := (Q.coefficientJets hN hS hT hR 0 x Fin.elim0).property
  rw [n04PulledFields_opticalCoefficientJets_zero Q hN hS hT hR x hx] at hs
  exact π.contDiff.contDiffOn.comp hs (fun _ _ => mem_univ _)

private def n04PulledFields_opticalErrorStripMixedRegularity
    (π : (ℝ × ℝ) →L[ℝ] ℝ) (m : ℕ) :
    MixedJetRegularity (sectorNeighborhood S base ε ε ×ˢ univ)
      (Ioo (Q.stripLeft m) (Q.stripRight m) ×ˢ univ)
      (fun x p => π (returnCorrectionCoefficientError D S C R Q.cutoff
        (liftSectorParameter S C x.1) p x.2)) := by
  let J := solveSmoothDirectionsPostcomp
    (hN.returnCorrectionCoefficient_parameterSpatialTower hS hT hR
      Q.cutoff Q.cutoff_smooth Q.range_on_component m (Q.cell m) (Q.component_cell m)
      (Q.stripLeft m) (Q.stripRight m) (Q.stripLeft_gt m) (Q.stripRight_lt m)
      (fun z hz q hq => Q.strip_discriminant hN hS hT z hz m q hq)) π
  have hU : IsOpen (sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S))) :=
    (sectorNeighborhood_isOpen S base ε ε).prod isOpen_univ
  have hV : IsOpen (Ioo (Q.stripLeft m) (Q.stripRight m) ×ˢ (univ : Set ℝ)) :=
    isOpen_Ioo.prod isOpen_univ
  have hc : Convex ℝ
      ((sectorNeighborhood S base ε ε ×ˢ (univ : Set (CircleSpace S))) ×ˢ
        (Ioo (Q.stripLeft m) (Q.stripRight m) ×ˢ (univ : Set ℝ))) :=
    ((sectorNeighborhood_convex S base ε ε).prod convex_univ).prod
      ((convex_Ioo _ _).prod convex_univ)
  exact n04Realization_jointMixedRegularity J hU hV hc

private def n04PulledFields_opticalErrorParameterTower
    (π : (ℝ × ℝ) →L[ℝ] ℝ) (a b : ℕ) (p : PolarPoint) (hp : p ∈ annularOpen D) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun x => mixedDerivative a b
        (fun q => π (returnCorrectionCoefficientError D S C R Q.cutoff
          (liftSectorParameter S C x.1) q x.2)) p) := by
  classical
  by_cases hstrip : ∃ m, p.1 ∈ Ioo (Q.stripLeft m) (Q.stripRight m)
  · exact (n04PulledFields_opticalErrorStripMixedRegularity Q hN hS hT hR π
      hstrip.choose).parameter a b p ⟨hstrip.choose_spec, mem_univ _⟩
  · have hz := (hN.cutoffStrip_or_eventually_zero Q.cutoff Q.support_interior
      Q.endpoint_germs Q.stripLeft Q.stripRight Q.strip_support hp.1).resolve_left hstrip
    exact n04PulledFields_zeroGermParameterTower
      ((sectorNeighborhood_isOpen S base ε ε).prod isOpen_univ)
      (fun x q => π (returnCorrectionCoefficientError D S C R Q.cutoff
        (liftSectorParameter S C x.1) q x.2)) p
      (fun x _ => n04PulledFields_error_zero_germ (D := D) (C := C) R Q.cutoff hz
        (liftSectorParameter S C x.1) x.2 π) a b

/-- The actual error has mixed spatial/parameter towers on the unchanged
open sector neighborhood.  The strip-or-zero cover is uniform in the state. -/
def n04PulledFields_opticalErrorMixedRegularity (π : (ℝ × ℝ) →L[ℝ] ℝ) :
    MixedJetRegularity (sectorNeighborhood S base ε ε ×ˢ univ) (annularOpen D)
      (fun x p => π (returnCorrectionCoefficientError D S C R Q.cutoff
        (liftSectorParameter S C x.1) p x.2)) where
  spatial := n04PulledFields_opticalError_spatial Q hN hS hT hR π
  parameter := n04PulledFields_opticalErrorParameterTower Q hN hS hT hR π

/-- Substitution of the genuine N02 residual is carried out in the
actual parameter towers, retaining all mixed spatial derivatives. -/
def n04PulledFields_actualErrorMixedRegularity (π : (ℝ × ℝ) →L[ℝ] ℝ) :
    MixedJetRegularity (sectorNeighborhood S base ε ε) (annularOpen D)
      (fun z p => π (returnCorrectionCoefficientError D S C R Q.cutoff
        (liftSectorParameter S C z) p (R.residual (liftSectorParameter S C z)))) := by
  let H := S.circle (3 / 4 : ℝ)
  letI : LocallyConvexSpace ℝ ((StateDirections S × ℝ) × CircleSpace S) :=
    (withSeminorms_pairGrading (sectorPairGrading_withSeminorms S)
      (withSeminorms_graded (fun n => H.level n) H.bond)).toLocallyConvexSpace
  have hU : IsOpen (sectorNeighborhood S base ε ε) :=
    sectorNeighborhood_isOpen S base ε ε
  have hres : SmoothTameOn (pairGrading (sectorGrading S) realGrading) H.grading
      (sectorNeighborhood S base ε ε)
      (fun z => R.residual (liftSectorParameter S C z)) :=
    hR.2.2.2.2.2.2.2.2.2.2
  let J : SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z : StateDirections S × ℝ => (z, R.residual (liftSectorParameter S C z))) :=
    smoothDirectionsProd
      (smoothDirectionsLinearOn (ContinuousLinearMap.id ℝ (StateDirections S × ℝ)) hU)
      hres.choose
  let F := n04PulledFields_opticalErrorMixedRegularity Q hN hS hT hR π
  refine ⟨fun z hz => F.spatial (z, R.residual (liftSectorParameter S C z))
    ⟨hz, mem_univ _⟩, fun a b p hp => ?_⟩
  exact smoothDirections_realCompTVS J (F.parameter a b p hp)
    (fun _ hz => ⟨hz, mem_univ _⟩)

end OpticalError

/-- Every retained corrected coefficient has genuine mixed towers on
the whole physical annulus and the original, common state neighborhood. -/
def n04PulledFields_correctedCoefficientMixedRegularity
    (W : N04RealizationStart) (i : Fin 3) :
    MixedJetRegularity (sectorNeighborhood W.S W.base W.ε W.ε) (annularOpen W.D)
      (fun z => canonicalCoefficientComponent i
        (W.L.coefficients (liftSectorParameter W.S W.C z))) := by
  have hU := sectorNeighborhood_isOpen W.S W.base W.ε W.ε
  have hΩ : IsOpen (annularOpen W.D) := isOpen_Ioo.prod isOpen_univ
  let F := n04Realization_annularOriginalMixedRegularity W.through03.1.1 W.hS W.hT i
  let A := n04PulledFields_actualErrorMixedRegularity W.cutoff W.through03.1.1 W.hS W.hT
    W.through03.1.2 (n04PulledFields_errorProjection i)
  let N := A.scalarComp hU hΩ isOpen_univ
    (contDiff_id.neg.contDiffOn : ContDiffOn ℝ ∞ (fun t : ℝ => -t) univ)
    (fun _ _ _ _ => mem_univ _)
  apply (F.add N hU hΩ).congr hΩ
  · intro z hz
    have h := W.field.smooth_coefficients (liftSectorParameter W.S W.C z)
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (W.through03.1.1.2.2.1.liftSectorParameter_sector z)
    unfold canonicalCoefficientComponent
    split_ifs
    · exact h.1
    · exact h.2.1
    · exact h.2.2
  · intro z hz p hp
    have hz' := liftSectorParameter_mem_stateNeighborhood hz le_rfl
    have hs := W.through03.1.1.2.2.1.liftSectorParameter_sector z
    have he := returnCorrectionCoefficientError_at_actual W.through03.1.1
      W.through03.1.2 W.hS W.cutoff.cutoff hz' hs p hp
      (fun m hm hd => (W.cutoff.active_discriminant _ hz' hs m p hm hd).le)
    change originalCoefficientEntry W.D W.S W.C i (liftSectorParameter W.S W.C z) p +
        -n04PulledFields_errorProjection i
          (returnCorrectionCoefficientError W.D W.S W.C W.R W.cutoff.cutoff
            (liftSectorParameter W.S W.C z) p
              (W.R.residual (liftSectorParameter W.S W.C z))) = _
    rw [he, ← sub_eq_add_neg]
    have hentry : originalCoefficientEntry W.D W.S W.C i
        (liftSectorParameter W.S W.C z) p =
      canonicalCoefficientComponent i
        (originalCoefficients W.D W.S W.C (liftSectorParameter W.S W.C z)) p := by
      simp only [originalCoefficientEntry, canonicalCoefficientComponent, ite_apply]
    rw [hentry]
    exact n04PulledFields_coefficient_reconstruction i _ _
      (returnCorrectedCoefficients_a W.D W.S W.C W.cutoff.cutoff _) p

/-- Replacing the auxiliary column preserves the same physical mixed
towers.  The neighborhood is fixed by `G.W` before choosing `η`. -/
def n04PulledFields_gaugeCoefficientMixedRegularity
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space) (i : Fin 3) :
    MixedJetRegularity (sectorNeighborhood (G.S η) G.W.base G.W.ε G.W.ε)
      (annularOpen G.W.D) (fun z => G.coefficientField η i (G.lift η z)) :=
  n04PulledFields_correctedCoefficientMixedRegularity G.W i

/-- The quantitative companion belongs to the retained independent-error
jets.  Its order-dependent local neighborhoods are kept explicit. -/
theorem n04PulledFields_retainedCoefficientJets_localMaterialBounds
    (W : N04RealizationStart) :
    LocalCoefficientMaterialTameBounds (T := W.T)
      (U := sectorNeighborhood W.S W.base W.ε W.ε ×ˢ (univ : Set (CircleSpace W.S)))
      (pairGrading (pairGrading (sectorGrading W.S) realGrading)
        (W.S.circle (3 / 4 : ℝ)).grading)
      (W.cutoff.coefficientJets W.through03.1.1 W.hS W.hT W.through03.1.2) :=
  W.cutoff.coefficientJets_local_bounds W.through03.1.1 W.hS W.hT W.through03.1.2

end ContinuousFlexibility.Analysis
