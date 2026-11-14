module

public import ContinuousFlexibility.Analysis.StateNeighborhood
public import ContinuousFlexibility.Analysis.MaterialSampleBounds
public import ContinuousFlexibility.Analysis.N01JetBounds
public import ContinuousFlexibility.Blueprint.CanonicalParts

/-!
# Preserving the cumulative construction on a smaller neighborhood

Every coordinate smallness argument may increase the base order and decrease
the radius. The earlier nonlinear properties, including their genuine
directional derivative towers and the loss selected at each parameter
order, then hold on that same new neighborhood. No data are replaced in
this restriction step.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped BigOperators
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

set_option backward.isDefEq.respectTransparency false

private theorem restrict_directional_bound
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    {U V : Set E} {f : E → ℝ} {p : ℕ → Seminorm ℝ E}
    (hV : IsOpen V) (hsub : V ⊆ U) (hp : Monotone p)
    {base base' high high' : ℕ} (hb : base ≤ base') (hh : high ≤ high')
    (x0 : E) (k : ℕ) {A w : ℝ} (hA : 0 ≤ A)
    (h : ∃ J : SmoothDirections U f, ∀ z ∈ U, ∀ v : Fin k → E,
      w * |J.D k z v| ≤ A * oneHighVariationWeight p base high (z - x0) v) :
    ∃ J : SmoothDirections V f, ∀ z ∈ V, ∀ v : Fin k → E,
      w * |J.D k z v| ≤ A * oneHighVariationWeight p base' high' (z - x0) v := by
  obtain ⟨J, hJ⟩ := h
  refine ⟨smoothDirectionsRestrict J hV hsub, fun z hz v => ?_⟩
  exact (hJ z (hsub hz) v).trans
    (mul_le_mul_of_nonneg_left (oneHighVariationWeight_mono hp hb hh _ v) hA)

private theorem n01CoefficientJetBounds_restrict
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base base' loss loss' : ℕ} {ε ε' : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h : N01CoefficientJetBounds D T S C base loss ε)
    (hb : base ≤ base') (hl : loss ≤ loss') (hε : ε' ≤ ε) :
    N01CoefficientJetBounds D T S C base' loss' ε' := by
  intro k s
  obtain ⟨B, hB, hbound⟩ := h k s
  refine ⟨B, hB, ?_⟩
  intro m i a b p hab hp
  have hgrade : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  simpa only [one_mul] using restrict_directional_bound
    (isOpen_stateNeighborhood S C base' ε') (stateNeighborhood_mono S C hb hε)
    hgrade hb (Nat.add_le_add_left hl s) (C.referenceState, 0) k
    (w := 1) (materialSample_factor_nonneg hD hT hB.le m)
    (by simpa only [one_mul] using hbound m i a b p hab hp)

private theorem n01FlowJetBounds_restrict
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base base' loss loss' : ℕ} {ε ε' : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (h : N01FlowJetBounds T S C base loss ε)
    (hb : base ≤ base') (hl : loss ≤ loss') (hε : ε' ≤ ε) :
    N01FlowJetBounds T S C base' loss' ε' := by
  intro k
  obtain ⟨parameterLoss, horder⟩ := h k
  refine ⟨parameterLoss, ?_⟩
  intro s
  obtain ⟨B, hB, hbound⟩ := horder s
  refine ⟨B, hB, ?_⟩
  intro m a b p hab hp
  have hgrade : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  exact restrict_directional_bound (isOpen_stateNeighborhood S C base' ε')
    (stateNeighborhood_mono S C hb hε) hgrade hb
    (Nat.add_le_add_right (Nat.add_le_add_left hl s) parameterLoss)
    (C.referenceState, 0) k (materialSample_factor_nonneg hD hT hB.le (C.cell m))
    (hbound m a b p hab hp)

/-- Restriction keeps the actual N01 towers and enlarges only their grading
indices. All constants in its coefficient and flow estimates are retained. -/
theorem n01Properties_restrict
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base base' loss loss' : ℕ} {ε ε' : ℝ}
    (hT : IsMaterialData D T) (h : N01Properties D T S C base loss ε)
    (hb : base ≤ base') (hl : loss ≤ loss') (hε' : 0 < ε') (hε : ε' ≤ ε) :
    N01Properties D T S C base' loss' ε' := by
  have hsub := stateNeighborhood_mono S C hb hε
  have hcoefficient := n01CoefficientJetBounds_of_properties h
  have hflowJets := n01FlowJetBounds_of_properties h
  obtain ⟨hD, _, href, hcontrol, hcells, hcontrols, hflow, hleft,
    hinverse, hgeometry, hroots, _, _⟩ := h
  refine ⟨hD, hε', href, hcontrol, hcells, hcontrols,
    (fun z hz => hflow z (hsub hz)),
    (fun z hz => hleft z (hsub hz)),
    (fun z hz => hinverse z (hsub hz)),
    (fun z hz => hgeometry z (hsub hz)),
    (fun z hz => hroots z (hsub hz)),
    n01CoefficientJetBounds_restrict hD.1 hT hcoefficient hb hl hε,
    n01FlowJetBounds_restrict hD.1 hT hflowJets hb hl hε⟩

theorem n02Properties_restrict
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {base base' : ℕ} {ε ε' : ℝ}
    (h : N02Properties D T S C R base ε) (hb : base ≤ base') (hε : ε' ≤ ε) :
    N02Properties D T S C R base' ε' := by
  have hsub := stateNeighborhood_mono S C hb hε
  obtain ⟨hflow, hresidual, hzero, hlinear, herror, hincrement,
    hderivative, hright, hleft, hinverse, htame⟩ := h
  refine ⟨(fun z hz => hflow z (hsub hz)),
    (fun z hz => hresidual z (hsub hz)),
    (fun z hz => hzero z (hsub hz)), hlinear,
    (fun z hz => herror z (hsub hz)),
    (fun z hz => hincrement z (hsub hz)),
    (fun z hz => hderivative z (hsub hz)), hright, hleft, hinverse, ?_⟩
  exact smoothTameOn_mono htame (isOpen_sectorNeighborhood S base' ε' ε')
    (sectorNeighborhood_mono S hb hε hε)

theorem n03Properties_restrict
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base base' : ℕ} {ε ε' : ℝ}
    (h : N03Properties D T S C R L base ε) (hb : base ≤ base') (hε : ε' ≤ ε) :
    N03Properties D T S C R L base' ε' := by
  have hsub := stateNeighborhood_mono S C hb hε
  obtain ⟨ha, hpositive, hroots, hreflection, hflow, herror, hmean, htame, hspatial⟩ := h
  refine ⟨(fun z hz => ha z (hsub hz)),
    (fun z hz => hpositive z (hsub hz)),
    (fun z hz => hroots z (hsub hz)),
    (fun z hz => hreflection z (hsub hz)),
    (fun z hz => hflow z (hsub hz)),
    (fun z hz => herror z (hsub hz)),
    (fun z hz => hmean z (hsub hz)), ?_,
    (fun z hz => hspatial z (hsub hz))⟩
  exact smoothTameOn_mono htame
    (((isOpen_sectorNeighborhood S base' ε' ε').prod isOpen_univ).prod isOpen_univ)
    (Set.prod_mono (Set.prod_mono (sectorNeighborhood_mono S hb hε hε)
      (subset_refl _)) (subset_refl _))

/-- The cumulative N01--N03 construction survives every admissible
base/loss increase and positive radius decrease. -/
theorem nonlinearPropertiesThrough03_restrict
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base base' loss loss' : ℕ} {ε ε' : ℝ}
    (hT : IsMaterialData D T)
    (h : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hb : base ≤ base') (hl : loss ≤ loss') (hε' : 0 < ε') (hε : ε' ≤ ε) :
    NonlinearPropertiesThrough03 D T S C R L base' loss' ε' :=
  ⟨⟨n01Properties_restrict hT h.1.1 hb hl hε' hε,
    n02Properties_restrict h.1.2 hb hε⟩, n03Properties_restrict h.2 hb hε⟩

theorem n04PartA_restrict
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S}
    {base base' : ℕ} {ε ε' : ℝ}
    (h : N04PartA D S C K base ε) (hb : base ≤ base') (hε : ε' ≤ ε) :
    N04PartA D S C K base' ε' := by
  have hsub := stateNeighborhood_mono S C hb hε
  exact
    { normalizationOpen := h.normalizationOpen
      normalizationSupport := h.normalizationSupport
      normalization := fun z hz => h.normalization z (hsub hz)
      referenceBounds := h.referenceBounds
      referencePositive := h.referencePositive
      referenceNegative := h.referenceNegative
      referencePartition := h.referencePartition
      referenceDomain := h.referenceDomain
      domains := fun z hz => h.domains z (hsub hz)
      partition := fun z hz => h.partition z (hsub hz)
      charts := fun z hz => h.charts z (hsub hz)
      boundary := fun z hz => h.boundary z (hsub hz)
      reflection := fun z hz => h.reflection z (hsub hz)
      inverseReflection := fun z hz => h.inverseReflection z (hsub hz) }

theorem n04PartB_restrict
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base base' : ℕ} {ε ε' : ℝ}
    (h : N04PartB S C L K base ε) (hb : base ≤ base') (hε : ε' ≤ ε) :
    N04PartB S C L K base' ε' := by
  have hsub := stateNeighborhood_mono S C hb hε
  obtain ⟨hcuts, htransmission, hoperator, hnegative, hpositive⟩ := h
  exact ⟨⟨hcuts.1, fun z hz => hcuts.2 z (hsub hz)⟩,
    (fun z hz => htransmission z (hsub hz)),
    (fun z hz => hoperator z (hsub hz)),
    (fun z hz => hnegative z (hsub hz)),
    (fun z hz => hpositive z (hsub hz))⟩

end ContinuousFlexibility.Analysis
