import ContinuousFlexibility.Analysis.N06ClosedPhysicalTests
import ContinuousFlexibility.Analysis.N06OperatorExtension

/-!
# Extending the actual physical equation on the original N05 space

The test equation of the named periodic reconstruction is closed by its
actual finite canonical pairings. A bounded perturbation on a dense core
therefore extends to the original source space and satisfies the original
physical relation. Closedness is proved from the selected geometry, rather
than imposed on an existential choice of physical representatives.

The controlled reference atlas and the core perturbation estimate remain
explicit inputs; neither is asserted for an arbitrary N04 witness.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {base loss b : ℕ} {ε : ℝ}
  {B : CanonicalDomainData S K V b}

private theorem n06_dense_named_relation
    [CompleteSpace (V.level (3 / 4 : ℝ) 0 b)]
    (z : AnnularState S × ℝ)
    {Core : Type*} [AddCommGroup Core] [Module ℝ Core]
    (i : Core →ₗ[ℝ] V.level (3 / 4 : ℝ) 0 b)
    (R₀ : Core →ₗ[ℝ] V.level (3 / 4 : ℝ) 0 b) (hdense : DenseRange i)
    {q : ℝ} (hbound : ∀ f : Core, ‖R₀ f‖ ≤ q * ‖i f‖)
    (hleft : ∀ u : B.Space, B.inverse u.val.2 = u)
    (hclosed : IsClosed {p : B.Space × V.level (3 / 4 : ℝ) 0 b |
      N06NamedPhysicalWeakRelation D C L B z p.1 p.2})
    (hcore : ∀ f : Core, N06NamedPhysicalWeakRelation D C L B z
      (B.inverse (i f)) (i f + R₀ f)) (u : B.Space) :
    N06NamedPhysicalWeakRelation D C L B z u
      (n06OperatorFromRelative B (n06DenseExtension i R₀) u) := by
  have hall (F : V.level (3 / 4 : ℝ) 0 b) :
      N06NamedPhysicalWeakRelation D C L B z (B.inverse F)
        (F + n06DenseExtension i R₀ F) := by
    refine hdense.induction_on
      (p := fun F => N06NamedPhysicalWeakRelation D C L B z (B.inverse F)
        (F + n06DenseExtension i R₀ F)) F ?_ ?_
    · exact hclosed.preimage
        (B.inverse.continuous.prodMk
          (continuous_id.add (n06DenseExtension i R₀).continuous))
    · intro f
      exact (congrArg
        (fun G : V.level (3 / 4 : ℝ) 0 b =>
          N06NamedPhysicalWeakRelation D C L B z (B.inverse (i f)) (i f + G))
        (n06DenseExtension_on_core i R₀ hdense hbound f)).mpr (hcore f)
  have he := hall u.val.2
  have he' : N06NamedPhysicalWeakRelation D C L B z u
      (u.val.2 + n06DenseExtension i R₀ u.val.2) :=
    (congrArg (fun v : B.Space => N06NamedPhysicalWeakRelation D C L B z v
      (u.val.2 + n06DenseExtension i R₀ u.val.2)) (hleft u)).mp he
  exact (congrArg (N06NamedPhysicalWeakRelation D C L B z u)
    (n06OperatorFromRelative_apply B (n06DenseExtension i R₀) u)).mpr he'

private theorem n06_n05_named_relation_implies
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (u : B.Space) (F : V.level (3 / 4 : ℝ) 0 b)
    (hweak : N06NamedPhysicalWeakRelation D C L B z u F) :
    PerturbedCanonicalRelation D S C K L z u.val.1 (V.forget (3 / 4 : ℝ) 0 b F) := by
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2
  have h01 : N01Properties D T S C base loss ε := h.1.1.1.1
  have href := n05_referenceState_mem (S := S) (C := C) (base := base) h01.2.1
  have hsector := n05_referenceState_sector h01.2.2.1
  obtain ⟨x, hxl, hxr⟩ := exists_between (h04.1.referenceBounds 0).1
  have hx := (h04.1.referenceBounds 0).2.2 ⟨hxl, hxr⟩
  exact n06_namedPhysicalWeakRelation_implies (hx.1.trans hx.2).le
    h04 h.2 href hsector hz hs u F hweak

/-- The same N05 graph supplies normalization, and its actual test
coordinates supply closedness. Only the equation on the dense core is
needed to identify the extended operator with the physical one. -/
theorem n06OperatorFromDense_namedPhysical
    [CompleteSpace (V.level (3 / 4 : ℝ) 0 b)]
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1)
    {Core : Type*} [AddCommGroup Core] [Module ℝ Core]
    (i : Core →ₗ[ℝ] V.level (3 / 4 : ℝ) 0 b)
    (R₀ : Core →ₗ[ℝ] V.level (3 / 4 : ℝ) 0 b) (hdense : DenseRange i)
    {q : ℝ} (hbound : ∀ f : Core, ‖R₀ f‖ ≤ q * ‖i f‖)
    (hcore : ∀ f : Core, N06NamedPhysicalWeakRelation D C L B z
      (B.inverse (i f)) (i f + R₀ f)) :
    ∀ u : B.Space, PerturbedCanonicalRelation D S C K L z u.val.1
      (V.forget (3 / 4 : ℝ) 0 b
        (n06OperatorFromRelative B (n06DenseExtension i R₀) u)) := by
  have hV : IsVolumeModel T S K V := h.2.2.1
  have hclosed := n06_namedPhysicalWeakRelation_isClosed
    (B := B) hT hS h.1 hV hcoordinates hz hs
  have hleft : ∀ u : B.Space, B.inverse u.val.2 = u := h.2.2.2.2.2.2.2.2.2.1
  intro u
  exact n06_n05_named_relation_implies h hz hs u _
    (n06_dense_named_relation z i R₀ hdense hbound hleft hclosed hcore u)

/-- A core displacement estimate gives the same estimate for the actual
physical operator on the chosen N05 graph, without an extra closedness
hypothesis and without changing the source norm. -/
theorem n06_exists_controlled_relativeOperator_of_denseCore
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {Core : Type*} [AddCommGroup Core] [Module ℝ Core]
    (i : Core →ₗ[ℝ] V.level (3 / 4 : ℝ) 0 b) (hdense : DenseRange i)
    (R₀ : AnnularState S × ℝ → Core →ₗ[ℝ] V.level (3 / 4 : ℝ) 0 b)
    (order : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ f : Core, ‖R₀ z f‖ ≤
        (M * (stateGrading S order (z.1 - C.referenceState) + |z.2|)) * ‖i f‖)
    (hcore : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ f : Core, N06NamedPhysicalWeakRelation D C L B z
        (B.inverse (i f)) (i f + R₀ z f)) :
    ∃ P : AnnularState S × ℝ → B.Space →L[ℝ] V.level (3 / 4 : ℝ) 0 b,
      (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        ∀ u : B.Space, PerturbedCanonicalRelation D S C K L z u.val.1
          (V.forget (3 / 4 : ℝ) 0 b (P z u))) ∧
      (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        ‖n06RelativeOperator P z‖ ≤
          M * (stateGrading S order (z.1 - C.referenceState) + |z.2|)) := by
  have hV : IsVolumeModel T S K V := h.2.2.1
  let : CompleteSpace (V.level (3 / 4 : ℝ) 0 b) :=
    (hV.2.1 (3 / 4 : ℝ) 0 b).completeSpace_coe
  let Q : AnnularState S × ℝ →
      V.level (3 / 4 : ℝ) 0 b →L[ℝ] V.level (3 / 4 : ℝ) 0 b :=
    fun z => n06DenseExtension i (R₀ z)
  let P : AnnularState S × ℝ → B.Space →L[ℝ] V.level (3 / 4 : ℝ) 0 b :=
    fun z => n06OperatorFromRelative B (Q z)
  have hright : ∀ F, (B.inverse F).val.2 = F := h.2.2.2.2.2.2.2.2.1
  refine ⟨P, ?_, ?_⟩
  · intro z hz hs
    exact n06OperatorFromDense_namedPhysical hT hS h hcoordinates hz hs i (R₀ z)
      hdense (hbound z hz hs) (hcore z hz hs)
  · intro z hz hs
    calc
      ‖n06RelativeOperator P z‖ = ‖Q z‖ :=
        congrArg (fun A : V.level (3 / 4 : ℝ) 0 b →L[ℝ]
          V.level (3 / 4 : ℝ) 0 b => ‖A‖)
          (n06RelativeOperator_fromRelative B Q hright z)
      _ ≤ M * (stateGrading S order (z.1 - C.referenceState) + |z.2|) :=
        norm_n06DenseExtension_le i (R₀ z) hdense
          (mul_nonneg hM (add_nonneg (apply_nonneg _ _) (abs_nonneg _)))
          (hbound z hz hs)

end ContinuousFlexibility.Statements
