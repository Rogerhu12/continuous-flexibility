import ContinuousFlexibility.Analysis.CoupledN10Assembly
import ContinuousFlexibility.Analysis.CoupledQuadraticSmooth
import ContinuousFlexibility.Analysis.CoupledScalarErrorCoefficientTame
import ContinuousFlexibility.Analysis.CoupledRecoveryComponentsSmooth

/-!
# Constructing the exact N10 error on one common neighborhood

The actual normalized scalar coefficient selects one smaller sector
neighborhood. Every earlier stage is restricted to that neighborhood with
the same data and inverse. The scalar and circle errors then give the two
independent decoding identities, conservation, both genuine derivatives,
and the joint smooth tame tower required by N10.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {Vol : VolumeModelData S K} {b : ℕ} {Domain : CanonicalDomainData S K Vol b}
  {Relative : RelativeInverseData S K Vol b Domain}
  {G : ScalarInverseData S} {P : ResidualData S} {B : ControlColumnData S}
  {N : ControlInverseData S} {V : CoupledInverseData S}
  {base loss : ℕ} {ε q0 : ℝ}

/-- The previously constructed data and the same inverse extend through
N10 once the actual independent return error has its joint tower. -/
theorem coupled_nonlinearPropertiesThrough10_of_returnErrorSmooth
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h09 : NonlinearPropertiesThrough09 D T S C R L K Vol b Domain Relative G P B N V
      base loss ε q0)
    (hRerror : SmoothTameOn
      (pairGrading (pairGrading (pairGrading (sectorGrading S) realGrading)
        (S.circle (3 / 4 : ℝ)).grading) (S.circle (3 / 4 : ℝ)).grading)
      (S.circle (3 / 4 : ℝ)).grading
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ univ)
      (fun z : ((StateDirections S × ℝ) × CircleSpace S) × CircleSpace S =>
        R.error (liftSectorParameter S C z.1.1) z.1.2 z.2)) :
    ∃ base' : ℕ, ∃ ε' q0' : ℝ, ∃ Q : QuadraticErrorData S,
      NonlinearPropertiesThrough09 D T S C R L K Vol b Domain Relative G P B N V
        base' loss ε' q0' ∧ N10Properties D S C R L P B V Q base' ε' q0' := by
  obtain ⟨h7, h8⟩ := h09.1
  obtain ⟨h6, hG, _⟩ := h7
  obtain ⟨h5, _⟩ := h6
  obtain ⟨h4, _⟩ := h5
  obtain ⟨h3all, _, _, _, _⟩ := h4
  obtain ⟨h2all, h3⟩ := h3all
  obtain ⟨h1, h2⟩ := h2all
  have hD : IsAccumulatingProfile D := h1.1.1
  obtain ⟨base', δ, hb, hδ, hδε, htype0⟩ :=
    coupledScalarErrorCoefficient_smoothTameOn hT hS h1
  let q' : ℝ := min q0 δ
  have hq : 0 < q' := lt_min h09.2.1 hδ
  have hqq0 : q' ≤ q0 := min_le_left _ _
  have hqδ : q' ≤ δ := min_le_right _ _
  have h09' := coupled_nonlinearPropertiesThrough09_restrict hT h09
    hb hδε hδ hqq0 hq hqδ
  have h1' := coupled_N01Properties_restrict hT h1 hb hδε hδ
  have h2' := coupled_N02Properties_restrict h2 hb hδε
  have h3' := coupled_N03Properties_restrict h3 hb hδε
  have hG' := coupled_scalarInverseProperties_restrict hG hb hδε
  have h8' := coupled_N08Properties_restrict h8 hb hδε
  have h9' := h09'.2
  let typeCoefficient : AnnularState S × ℝ → CoupledWeakHeight S :=
    coupledScalarErrorCoefficient hT hS h1
  let Q := coupledQuadraticErrorData hD hT hS R L B V typeCoefficient
  have hU := coupled_sectorNeighborhood_isOpen S base' δ q'
  have hsub : sectorNeighborhood S base' δ q' ⊆ sectorNeighborhood S base ε ε :=
    coupled_sectorNeighborhood_mono hb hδε (hqδ.trans hδε)
  have htype := smoothTameOn_mono htype0 hU
    (coupled_sectorNeighborhood_mono (S := S) le_rfl le_rfl hqδ)
  obtain ⟨_, _, _, _, _, _, _, hLerror⟩ := h3
  have hLerror' := smoothTameOn_mono hLerror ((hU.prod isOpen_univ).prod isOpen_univ)
    (Set.prod_mono
      (Set.prod_mono hsub (subset_refl (univ : Set (CircleSpace S))))
      (subset_refl (univ : Set (HeightPair S))))
  have hRerror' := smoothTameOn_mono hRerror ((hU.prod isOpen_univ).prod isOpen_univ)
    (Set.prod_mono
      (Set.prod_mono hsub (subset_refl (univ : Set (CircleSpace S))))
      (subset_refl (univ : Set (CircleSpace S))))
  have hQtame := coupledQuadraticErrorData_smoothTameOn hD hT hS C R L B V
    typeCoefficient hU htype (coupled_recoveredHeight_smoothTameOn h9')
    (coupled_recoveredCircleSolution_smoothTameOn hS h1'.2.2.1 h2' h8' h9')
    hLerror' hRerror'
  have hstate : ∀ z ∈ coupledNeighborhood S C base' δ q',
      z ∈ stateNeighborhood S C base ε := by
    intro z hz
    exact coupled_stateNeighborhood_mono hb hδε ⟨hz.1, hz.2.trans_le hqδ⟩
  refine ⟨base', δ, q', Q, h09', ?_⟩
  apply coupled_N10Properties_of_independent_errors hT hS h1' h2' h3' hG' h8' h9'
  · intro z hz hs r y p hp
    exact coupledQuadraticErrorData_scalar_decode hD hT hS C R L B V typeCoefficient z
      (fun x hx => coupledScalarErrorCoefficient_decode hT hS h1 (hstate z hz) hs hx)
      r y p
  · intro z hz hs r y m θ
    exact coupledQuadraticErrorData_circle_decode hD hT hS R L B V typeCoefficient
      h2 (hstate z hz) hs r y m θ
  · intro z _ _ r y
    exact coupledQuadraticErrorData_source_integral hD hT hS R L B V typeCoefficient z r y
  · exact hQtame

/-- Package the same data into the frozen cumulative interface. -/
theorem coupled_nonlinearStagesThrough10_of_returnErrorSmooth
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h09 : NonlinearPropertiesThrough09 D T S C R L K Vol b Domain Relative G P B N V
      base loss ε q0)
    (hRerror : SmoothTameOn
      (pairGrading (pairGrading (pairGrading (sectorGrading S) realGrading)
        (S.circle (3 / 4 : ℝ)).grading) (S.circle (3 / 4 : ℝ)).grading)
      (S.circle (3 / 4 : ℝ)).grading
      ((sectorNeighborhood S base ε ε ×ˢ univ) ×ˢ univ)
      (fun z : ((StateDirections S × ℝ) × CircleSpace S) × CircleSpace S =>
        R.error (liftSectorParameter S C z.1.1) z.1.2 z.2)) :
    ∃ base' : ℕ, ∃ ε' q0' : ℝ,
      NonlinearStagesThrough10 D T S C R base' loss ε' q0' := by
  obtain ⟨base', ε', q0', Q, h09', h10⟩ :=
    coupled_nonlinearPropertiesThrough10_of_returnErrorSmooth hT hS h09 hRerror
  exact ⟨base', ε', q0', L, K, Vol, b, Domain, Relative, G, P, B, N, V, Q, h09', h10⟩

end ContinuousFlexibility.Statements
