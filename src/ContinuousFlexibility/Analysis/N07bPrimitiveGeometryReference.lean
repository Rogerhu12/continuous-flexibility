import ContinuousFlexibility.Analysis.N07bReferenceGeometry
import ContinuousFlexibility.Analysis.N07bReferencePrimitiveGrowth

/-!
# Reference coefficient bounds from the retained primitive geometry

The same fifteen actual scalar fields supply the three direction triples,
the normalized reference-height ratio, and the three reference multipliers.
The coordinate geometry proves their smoothness. The finite direction-chain
estimate then yields a uniform bound at the same height exponent on one
smaller neighborhood. No expanded coefficient, source-space membership or
operator-domain conclusion is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base : ℕ} {ε : ℝ}

/-- All regularity inputs of the reference finite-chain theorem follow
from the actual two chart systems and the smooth flat reference profile. -/
theorem n07b_referenceRegularity_of_canonicalGeometry
    (hgeom : RadialProfileGeometry D) (hK : N04PartA D S C K base ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState) :
    N07bReferenceGeometricRegularity S C K
      (fun z m => canonicalPrimitiveDirection C K z m 1)
      (fun z m => canonicalPrimitiveDirection C K z m 2)
      (canonicalReferenceHeightRatio C K)
      (fun z m => n07bReferenceSeedMultiplier D.w (canonicalReferencePoint C K z m)
        (canonicalReferenceSourceFactor C K z m)) base ε := by
  intro z hz hs m
  refine ⟨?_, ?_, n07b_canonicalReferenceHeightRatio_contDiffOn hK href hsref hz hs m,
    fun k => n07b_canonicalReferenceSeedMultiplier_contDiffOn hK href hsref hz hs hgeom m k⟩
  · simpa only [n07b_canonicalPrimitiveDirection_one] using
      n07b_canonicalReferenceDirection_contDiffOn hK href hsref hz hs m (1, 0)
  · simpa only [n07b_canonicalPrimitiveDirection_two] using
      n07b_canonicalReferenceDirection_contDiffOn hK href hsref hz hs m (0, 1)

/-- The retained primitive jets give the exact input of the finite
reference-chain estimate, with unchanged constants and quantifier order. -/
theorem n07b_referencePrimitiveGrowth_of_geometric_contract
    (h : CanonicalPrimitiveGeometry D T S C L K base ε) (b : ℕ) :
    N07bReferencePrimitiveE0Growth T S C K (3 / 4 : ℝ)
      (fun z m => canonicalPrimitiveDirection C K z m 1)
      (fun z m => canonicalPrimitiveDirection C K z m 2)
      (canonicalReferenceHeightRatio C K)
      (fun z m => n07bReferenceSeedMultiplier D.w (canonicalReferencePoint C K z m)
        (canonicalReferenceSourceFactor C K z m)) base ε b := by
  obtain ⟨r, d, C₀, A, hC₀, _, hbound⟩ := h.materialJets (b + 2)
  refine ⟨r, d, C₀, A, hC₀.le, ?_⟩
  intro z hz hs m y hy
  let R : ℝ := C₀ * T.E0 (T.radius y.1) ^ A *
    (1 + stateGrading S r (z.1 - C.referenceState) + |z.2|) ^ d
  have hdir (i : Fin 3) :
      N07bMaterialDirectionJetBound T K z m (canonicalPrimitiveDirection C K z m i)
        (b + 2) R y := by
    have hv₁ : (fun v : PolarPoint =>
        canonicalPrimitiveField D T C K z m (.inl (i, 0)) (T.radius v.1, v.2)) =
        n07bMaterialDirectionV1 T (canonicalPrimitiveDirection C K z m i) := rfl
    have hv₂ : (fun v : PolarPoint =>
        canonicalPrimitiveField D T C K z m (.inl (i, 1)) (T.radius v.1, v.2)) =
        n07bMaterialDirectionV2 T (canonicalPrimitiveDirection C K z m i) := rfl
    have hq : (fun v : PolarPoint =>
        canonicalPrimitiveField D T C K z m (.inl (i, 2)) (T.radius v.1, v.2)) =
        n07bMaterialDirectionDrift T K z m (canonicalPrimitiveDirection C K z m i) := rfl
    intro n hn
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hv₁] using hbound z hz hs m y hy (.inl (i, 0)) n hn
    · simpa only [hv₂] using hbound z hz hs m y hy (.inl (i, 1)) n hn
    · simpa only [hq] using hbound z hz hs m y hy (.inl (i, 2)) n hn
  have hseed : (fun v : PolarPoint =>
      canonicalPrimitiveField D T C K z m (.inr (.inl 2)) (T.radius v.1, v.2)) =
      (fun v => n07bSourceNormalizer T K z m (3 / 4 : ℝ) (n07bMaterialRadiusChart T v) *
        canonicalReferenceHeightRatio C K z m (n07bMaterialRadiusChart T v)) := rfl
  have hmult (k : Fin 3) : (fun v : PolarPoint =>
      canonicalPrimitiveField D T C K z m (.inr (.inr k)) (T.radius v.1, v.2)) =
      (fun v => n07bReferenceSeedMultiplier D.w (canonicalReferencePoint C K z m)
        (canonicalReferenceSourceFactor C K z m) k (n07bMaterialRadiusChart T v)) := by
    funext v
    exact congrFun (n07b_canonicalPrimitiveField_reference_multiplier D T C K z m k)
      (T.radius v.1, v.2)
  refine ⟨?_, hdir 1, hdir 2, ?_, ?_⟩
  · intro n hn
    simpa only [hseed] using hbound z hz hs m y hy (.inr (.inl 2)) n hn
  · simpa only [n07b_canonicalPrimitiveDirection_zero] using hdir 0
  · intro k n hn
    simpa only [hmult k] using hbound z hz hs m y hy (.inr (.inr k)) n hn

/-- The actual canonical geometry and its primitive jet certificate give
one neighborhood and one constant for all genuine reference coefficients.
The final angular order is fixed before any state or piece is chosen. -/
theorem n07b_referenceAngular_bound_of_geometric_contract
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hK : N04PartA D S C K base ε) (hε : 0 < ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    (hgeom : CanonicalPrimitiveGeometry D T S C L K base ε) (b : ℕ) :
    ∃ base' : ℕ, ∃ ε' A₀ : ℝ,
      base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧ ε' ≤ (1 / 2 : ℝ) ∧ 0 ≤ A₀ ∧
      ∀ z ∈ stateNeighborhood S C base' ε', stateSector S z.1 →
        ∀ m x, x ∈ physicalPieceOpen S K z m →
          ∀ j : ℕ, j ≤ b → ∀ i : n07bReferenceMaterialSeed × n07bAngularChainIndex j,
            (n07bSourceNormalizer T K z m (3 / 4 : ℝ) x *
              n07bReferenceAngularCoefficient T K z m (3 / 4 : ℝ)
                (canonicalPrimitiveDirection C K z m 1) (canonicalPrimitiveDirection C K z m 2)
                (canonicalReferenceHeightRatio C K z m)
                (n07bReferenceSeedMultiplier D.w (canonicalReferencePoint C K z m)
                  (canonicalReferenceSourceFactor C K z m)) j i x) ^ 2 ≤ A₀ * T.M x.1 ^ 2 := by
  have hprofile : RadialProfileGeometry D := by
    obtain ⟨_, hg, _⟩ := hD
    exact hg
  exact n07b_exists_referenceAngular_M_bound_of_primitive_E0 hD hT hK hε (3 / 4 : ℝ)
    (n07b_referenceRegularity_of_canonicalGeometry hprofile hK href hsref)
    (n07b_referencePrimitiveGrowth_of_geometric_contract hgeom b)

end ContinuousFlexibility.Analysis
