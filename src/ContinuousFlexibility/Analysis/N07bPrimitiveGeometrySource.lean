import ContinuousFlexibility.Analysis.N07bSourceBoundPrimitiveLift

/-!
# The actual source estimate from the retained primitive geometry

Only four of the explicit geometric fields enter the original source
lift: its normalized initial factor, the two material inverse-angular
components, and their actual density drift. The finite chain and energy
theorems then supply the source-space element and its uniform norm bound.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff ENNReal

set_option backward.isDefEq.respectTransparency true

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {base : ℕ} {ε : ℝ}

/-- Extract the four actual primitive fields, with the same constants
and the same state quantifiers as the coordinate construction. -/
theorem n07b_sourcePrimitiveGrowth_of_geometric_contract
    (h : CanonicalPrimitiveGeometry D T S C L K base ε) (b : ℕ) :
    N07bSourcePrimitiveE0Growth T S C K base ε b := by
  obtain ⟨r, d, C₀, A, hC₀, _, hbound⟩ := h.materialJets b
  refine ⟨r, d, C₀, A, hC₀.le, ?_⟩
  intro z hz hs m y hy
  have hseed : (fun v : PolarPoint =>
      canonicalPrimitiveField D T C K z m (Sum.inr (Sum.inl 0))
        (T.radius v.1, v.2)) =
      n07bMaterialNormalizedSourceCoefficient T K z m (3 / 4 : ℝ) 0 () := rfl
  have hv₁ : (fun v : PolarPoint =>
      canonicalPrimitiveField D T C K z m (Sum.inl (0, 0))
        (T.radius v.1, v.2)) = n07bMaterialSourceV1 T K z m := rfl
  have hv₂ : (fun v : PolarPoint =>
      canonicalPrimitiveField D T C K z m (Sum.inl (0, 1))
        (T.radius v.1, v.2)) = n07bMaterialSourceV2 T K z m := rfl
  have hq : (fun v : PolarPoint =>
      canonicalPrimitiveField D T C K z m (Sum.inl (0, 2))
        (T.radius v.1, v.2)) = n07bMaterialSourceDrift T K z m := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    simpa only [hseed] using hbound z hz hs m y hy (Sum.inr (Sum.inl 0)) n hn
  · intro n hn
    simpa only [hv₁] using hbound z hz hs m y hy (Sum.inl (0, 0)) n hn
  · intro n hn
    simpa only [hv₂] using hbound z hz hs m y hy (Sum.inl (0, 1)) n hn
  · intro n hn
    simpa only [hq] using hbound z hz hs m y hy (Sum.inl (0, 2)) n hn

/-- The retained coordinate geometry proves the actual source conversion
in the prescribed model. No norm estimate on a source is an input. -/
theorem n07b_sourceLift_of_geometric_contract
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hV : IsVolumeModel T S K V)
    (hK : N04PartA D S C K base ε) (hε : 0 < ε)
    (hgeom : CanonicalPrimitiveGeometry D T S C L K base ε) (b : ℕ) :
    ∃ base' : ℕ, ∃ ε' C₀ : ℝ,
      base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧ ε' ≤ (1 / 2 : ℝ) ∧ 0 < C₀ ∧
      ∀ z ∈ stateNeighborhood S C base' ε', stateSector S z.1 → ∀ f : S.Source,
        ∃ F : V.level (3 / 4 : ℝ) 0 b,
          ‖F‖ ≤ C₀ * S.sourceGrading (b + 1) f ∧
          ∀ m, (V.forget (3 / 4 : ℝ) 0 b F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
            canonicalSource S K z m ((S.height (3 / 4 : ℝ)).decode f.val) :=
  n07b_sourceLift_uniform_bound_of_primitive_E0 hD hT hS hV hK hε
    (n07b_sourcePrimitiveGrowth_of_geometric_contract hgeom b)

end ContinuousFlexibility.Analysis
