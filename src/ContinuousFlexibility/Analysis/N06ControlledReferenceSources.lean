import ContinuousFlexibility.Analysis.N06ReferenceSourceJets
import ContinuousFlexibility.Analysis.N06CanonicalProperties
import ContinuousFlexibility.Analysis.N06ControlledPieceFiniteness

/-!
# Constructing the three reference columns in the selected source scale

For controlled reference coordinates, compact support and actual smooth
periodic physical fields suffice. The required finite piece set and all
angular jet bounds are proved here from the original geometric data.
Neither source membership nor a bound on canonical source jets is an
input. All resulting elements belong to the same selected volume model.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

theorem n06_controlledReferenceSource_finiteJets_bounded
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f (0, Real.pi)) (b : ℕ) (I : Finset ℕ) :
    ∃ δ : ℝ, 0 ≤ δ ∧ ∀ m ∈ I, ∀ j, j ≤ b →
      ∀ p ∈ canonicalOpen S K m,
        |mixedDerivative 0 j (canonicalSource S K (C.referenceState, 0) m f) p| ≤ δ := by
  obtain ⟨B, hB, hphysical⟩ := n06_smooth_periodic_angularJets_bounded hf hp D.a D.b b
  obtain ⟨A, _hA, hsource⟩ := n06_controlledReferenceSource_angularJet_bound h hcoordinates
  let cost : ℕ → ℝ := fun m => (A * radialE (D.cellIndex (K.cell m)) ^ A) ^ 2 * B
  have hcost : ∀ m, 0 ≤ cost m := fun m => mul_nonneg (sq_nonneg _) hB.le
  refine ⟨∑ m ∈ I, cost m, Finset.sum_nonneg (fun m _ => hcost m), ?_⟩
  intro m hm j hj p hpU
  have hs := hsource f b B hB.le
    (fun j hj q hq => hphysical j hj q ⟨hq.1.le, hq.2.le⟩) m j hj p hpU
  exact hs.trans (Finset.single_le_sum (fun m _ => hcost m) hm)

/-- Actual compact physical sources have an element at every fixed
material weight and angular order of the existing source scale. -/
theorem n06Volume_exists_controlled_reference_source
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {V : VolumeModelData S K} {base loss : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (γ t : ℝ) (b : ℕ)
    {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f (0, Real.pi))
    (he : ∀ p : PolarPoint, f (p.1, -p.2) = f p)
    (hsupport : HasCompactRadialSupport D f) :
    ∃ F : V.level γ t b,
      ∀ m, (V.forget γ t b F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalSource S K (C.referenceState, 0) m f := by
  obtain ⟨J, hJ, hJD, hzero⟩ := hsupport
  have h01 := h.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.2.2.2.2.1
  have hfinite : Set.Finite {m : ℕ |
      (physicalPieceOpen S K (C.referenceState, 0) m ∩
        (J ×ˢ (univ : Set ℝ))).Nonempty} := by
    rw [n06_referenceSourcePieces_eq_referenceIntervals h04.1 J]
    exact n06_controlledReferencePieces_finite_on_compact hD hcoordinates hJ hJD
  obtain ⟨δ, hδ, hbound⟩ := n06_controlledReferenceSource_finiteJets_bounded
    h hcoordinates hf hp b hfinite.toFinset
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hs := n05_referenceState_sector h01.2.2.1
  obtain ⟨F, hF, _⟩ := n06Volume_exists_finite_canonical_source hD hT hV
    h04.1 href hs γ t b hfinite hf.contDiffOn
    (fun p _ => hp p) (fun p _ => he p) hzero hδ hbound
  exact ⟨F, hF⟩

/-- The actual left-tail, nu and compatibility columns are all built in
the original model. Their common finite norm constant is obtained from
the constructed elements, without imposing an estimate on the unknown. -/
theorem n06Volume_exists_controlled_referenceScalarColumns
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {V : VolumeModelData S K} {base loss : ℕ} {ε : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hb : RadialTrueBorder D)
    (hV : IsVolumeModel T S K V)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (γ t : ℝ) (b : ℕ) :
    ∃ F : Fin 3 → V.level γ t b,
      (∀ i m, (V.forget γ t b (F i) m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalSource S K (C.referenceState, 0) m (n06ReferenceScalarField D S i)) ∧
      ∃ M : ℝ, 0 < M ∧ ∀ i, ‖F i‖ ≤ M := by
  classical
  obtain ⟨J, hJ, hJD, hzero⟩ := n06_referenceScalarFields_commonSupport hS hb
  have hsource : ∀ i : Fin 3, ∃ F : V.level γ t b,
      ∀ m, (V.forget γ t b F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalSource S K (C.referenceState, 0) m (n06ReferenceScalarField D S i) := by
    intro i
    exact n06Volume_exists_controlled_reference_source hD hT hV h hcoordinates γ t b
      (n06_referenceScalarField_contDiff hD hT hS hb i)
      (n06_referenceScalarField_periodic hS i)
      (n06_referenceScalarField_even hS i) ⟨J, hJ, hJD, hzero i⟩
  choose F hF using hsource
  have hsum : 0 ≤ ∑ i : Fin 3, ‖F i‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨F, hF, 1 + ∑ i : Fin 3, ‖F i‖, by linarith, ?_⟩
  intro i
  have hi : ‖F i‖ ≤ ∑ j : Fin 3, ‖F j‖ :=
    Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  linarith

end ContinuousFlexibility.Statements
