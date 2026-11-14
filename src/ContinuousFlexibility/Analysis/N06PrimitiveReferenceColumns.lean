module

public import ContinuousFlexibility.Analysis.N06PrimitiveScalarSources
public import ContinuousFlexibility.Analysis.N07aReferenceOpenCoefficients

/-!
# The actual reference columns in the original volume model

The three physical columns have a common compact support. Primitive
reference jets make the pieces meeting it finite. The original local
source construction then puts their actual reference transforms in any
fixed material level, without a controlled-coordinate hypothesis.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {b base loss : ℕ} {ε : ℝ}
  {B : CanonicalDomainData S K V b}

private theorem n06_referenceScalarOpen_value
    (hJ : CanonicalGeometry.ReferenceJets D T S C L K)
    (m : ℕ) (hm : K.left m < K.right m) (i : Fin 3) :
    (n07aReferenceScalarOpenCoefficient hJ m hm i).value =
      canonicalSource S K (C.referenceState, 0) m
        (n06CurrentScalarField D S C L (C.referenceState, 0) i) := by
  fin_cases i <;> rfl

private theorem n06_referenceScalar_current_even
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (i : Fin 3) (p : PolarPoint) :
    n06CurrentScalarField D S C L (C.referenceState, 0) i (p.1, -p.2) =
      n06CurrentScalarField D S C L (C.referenceState, 0) i p := by
  have hz := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  fin_cases i
  · exact n06_currentLeftColumn_even hT hS h01 h03 hz hs p
  · exact n06_nuColumn_even hT hS h01 (C.referenceState, 0) p
  · exact ((hS.1 (3 / 4 : ℝ)).2.2.2.1 S.psi).2.1 p.1 p.2

private theorem n06_referenceScalar_source_exists
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (hV : IsVolumeModel T S K V)
    (hJ : CanonicalGeometry.ReferenceJets D T S C L K)
    (γ t : ℝ) (i : Fin 3) :
    ∃ F : V.level γ t 0, ∀ m,
      (V.forget γ t 0 F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalSource S K (C.referenceState, 0) m
          (n06CurrentScalarField D S C L (C.referenceState, 0) i) := by
  have hz := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  obtain ⟨J, hcompact, hJD, hzero⟩ :=
    n06_primitiveActual_scalarFields_commonSupport (L := L) hT hS h01
  have hfinite : Set.Finite {m : ℕ |
      (physicalPieceOpen S K (C.referenceState, 0) m ∩
        (J ×ˢ (univ : Set ℝ))).Nonempty} :=
    n06_physicalSupportPieces_finite_of_primitive h01.1.1 hT h01.2.2.2.1 h04 hJ
      hz hs hcompact hJD
  have hf := n06_currentScalarField_contDiff hT hS h01 h03 hz hs i
  have hp := n06_currentScalarField_periodic hT hS h01 h03 hz hs i
  obtain ⟨δ, hδ, hbound⟩ :=
    n06_currentSource_finiteJets_bounded h04 hz hs hf hp 0 hfinite.toFinset
  obtain ⟨F, hF, _⟩ := n06Volume_exists_finite_canonical_source
    h01.1.1 hT hV h04.1 hz hs γ t 0 hfinite hf.contDiffOn
    (fun p _ => hp p) (fun p _ => n06_referenceScalar_current_even hT hS h01 h03 i p)
    (hzero (C.referenceState, 0) i) hδ hbound
  exact ⟨F, hF⟩

/-- These are the literal three reference source coefficients used in
the original reference equation. The selected source level is unchanged. -/
theorem n06_primitiveReference_scalarColumnVolumes
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hJ : CanonicalGeometry.ReferenceJets D T S C L K)
    (γ t : ℝ) (hI : ∀ m, K.left m < K.right m) :
    ∃ Col : Fin 3 → V.level γ t 0, ∀ i,
      V.forget γ t 0 (Col i) =
        fun m => (n07aReferenceScalarOpenCoefficient hJ m (hI m) i).toLp := by
  classical
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have h03 : N03Properties D T S C R L base ε := h.1.1.2
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  choose Col hCol using fun i : Fin 3 =>
    n06_referenceScalar_source_exists hT hS h01 h03 h04 h.2.2.1 hJ γ t i
  refine ⟨Col, fun i => funext fun m => ?_⟩
  apply Lp.ext
  have hLp := (n07aReferenceScalarOpenCoefficient hJ m (hI m) i).toLp_ae
  rw [n06_referenceScalarOpen_value hJ m (hI m) i] at hLp
  exact (hCol i m).trans hLp.symm

end ContinuousFlexibility.Statements
