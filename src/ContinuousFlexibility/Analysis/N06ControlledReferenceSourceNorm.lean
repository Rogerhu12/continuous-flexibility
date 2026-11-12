import ContinuousFlexibility.Analysis.N06ControlledReferenceSources

/-!
# A uniform source norm for one fixed compact physical support

Controlled reference coordinates supply the actual angular source factor.
On a fixed compact radial support, the finitely many resulting factors
give one source norm constant before the physical field or its size is
chosen. The element belongs to the original selected volume model.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

def N06ControlledReferenceSourceNormBound
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (K : CanonicalData S) (V : VolumeModelData S K)
    (γ t : ℝ) (b : ℕ) (J : Set ℝ) (M : ℝ) : Prop :=
  ∀ (f : PolarPoint → ℝ) (δ : ℝ), 0 ≤ δ →
    ContDiff ℝ ∞ f → Function.Periodic f (0, Real.pi) →
    (∀ p : PolarPoint, f (p.1, -p.2) = f p) →
    (∀ r, r ∉ J → ∀ θ, f (r, θ) = 0) →
    (∀ j, j ≤ b → ∀ p ∈ annularOpen D, |mixedDerivative 0 j f p| ≤ δ) →
    ∃ F : V.level γ t b,
      (∀ m, (V.forget γ t b F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalSource S K (C.referenceState, 0) m f) ∧ ‖F‖ ≤ M * δ

theorem n06Volume_controlled_reference_source_norm
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {V : VolumeModelData S K} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hV : IsVolumeModel T S K V)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (γ t : ℝ) (b : ℕ) {J : Set ℝ}
    (hJ : IsCompact J) (hJD : J ⊆ radialCore D) :
    ∃ M : ℝ, 0 ≤ M ∧ N06ControlledReferenceSourceNormBound D S C K V γ t b J M := by
  classical
  have h01 : N01Properties D T S C base loss ε := h.1.1.1
  have h04 : N04Properties D T S C L K base loss ε := h.2.2.2.2
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hsector := n05_referenceState_sector h01.2.2.1
  have hfinite : Set.Finite {m : ℕ |
      (physicalPieceOpen S K (C.referenceState, 0) m ∩
        (J ×ˢ (univ : Set ℝ))).Nonempty} := by
    rw [n06_referenceSourcePieces_eq_referenceIntervals h04.1 J]
    exact n06_controlledReferencePieces_finite_on_compact h01.1.1 hcoordinates hJ hJD
  let I : Finset ℕ := hfinite.toFinset
  obtain ⟨A, _hA, hsource⟩ := n06_controlledReferenceSource_angularJet_bound h hcoordinates
  let cost : ℕ → ℝ := fun m => (A * radialE (D.cellIndex (K.cell m)) ^ A) ^ 2
  let W : ℝ := ∑ m ∈ I, cost m
  let M : ℝ := n06WeakAngularMultiplierCost b * n06FiniteSourceCost T S K γ t b I
  have hcost (m : ℕ) : 0 ≤ cost m := sq_nonneg _
  have hW : 0 ≤ W := Finset.sum_nonneg (fun m _ => hcost m)
  have hM : 0 ≤ M := mul_nonneg (n06WeakAngularMultiplierCost_nonneg b)
    (n06FiniteSourceCost_nonneg T S K γ t b I)
  refine ⟨M * W, mul_nonneg hM hW, ?_⟩
  intro f δ hδ hf hp he hsupport hphysical
  have hbound : ∀ m ∈ hfinite.toFinset, ∀ j, j ≤ b →
      ∀ p ∈ canonicalOpen S K m,
        |mixedDerivative 0 j (canonicalSource S K (C.referenceState, 0) m f) p| ≤ W * δ := by
    intro m hm j hj p hpU
    have hfield : ∀ k, k ≤ b → ∀ q : PolarPoint, q.1 ∈ Ioo D.a D.b →
        |mixedDerivative 0 k f q| ≤ δ := by
      intro k hk q hq
      exact hphysical k hk q ⟨hq, mem_univ _⟩
    have hactual := hsource f b δ hδ hfield m j hj p hpU
    have hmW : cost m ≤ W := Finset.single_le_sum (fun k _ => hcost k) hm
    exact hactual.trans (mul_le_mul_of_nonneg_right hmW hδ)
  obtain ⟨F, hF, hFnorm⟩ := n06Volume_exists_finite_canonical_source
    h01.1.1 hT hV (n06_N04_qualitative_parts h04).1 href hsector γ t b hfinite
    hf.contDiffOn (fun p _ => hp p) (fun p _ => he p) hsupport
    (mul_nonneg hW hδ) hbound
  exact ⟨F, hF, hFnorm.trans_eq (mul_assoc M W δ).symm⟩

end ContinuousFlexibility.Statements
