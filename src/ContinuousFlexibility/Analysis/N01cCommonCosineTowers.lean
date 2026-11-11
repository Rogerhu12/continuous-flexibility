import ContinuousFlexibility.Analysis.N01cActualCosineSpeedTower
import ContinuousFlexibility.Analysis.N01cCoefficientBaseSelection
import ContinuousFlexibility.Analysis.N01cBoundsRestriction
import ContinuousFlexibility.Analysis.N01cSpeedTowerRestriction
import ContinuousFlexibility.Analysis.N01cOrdinarySpeedJointTowers

/-!
# One common actual cosine-speed tower neighbourhood

The primitive geometric witness supplies the optical root and its
positive endpoint quotient. Smoothing supplies one interpolation base.
Taking the minimum of the two radii and the original radius gives all
component towers on the same original state neighbourhood.
-/

noncomputable section

namespace ContinuousFlexibility.Blueprint

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

/-- All actual cosine speeds have continuous time-indexed state-angle
towers after one enlargement of the low order and one shrinking of the
radius. No characteristic-flow regularity or tame estimate is assumed. -/
theorem n01_exists_commonSpeed_towers
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε)
    (hB : N01PartB D S C base ε)
    (hG : N01PrimitiveGeometry D T S C)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r) :
    ∃ base' : ℕ, ∃ ε' : ℝ, base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      N01PartB D S C base' ε' ∧
      (∀ z ∈ stateNeighborhood S C base' ε', ∀ m r,
        r ∈ Icc (C.left m) (C.right m) →
          0 < twoRootDivided (componentOpticalSquare D S C m z)
            (C.left m) (C.right m) r) ∧
      Nonempty (∀ m, ContinuousTimeSpeedTower (stateNeighborhood S C base' ε')
        (componentCosineSpeed D S C m)) ∧
      Nonempty (OrdinarySpeedRadialTowers D S C (stateNeighborhood S C base' ε')) := by
  letI : IsTopologicalAddGroup (AnnularState S × ℝ) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S × ℝ) := inferInstance
  obtain ⟨εo, hεo, ho⟩ :=
    n01_exists_stateOpticalRoot_endpoint_powerBounds hS hT hA hE hG.1 hG.2.2
  obtain ⟨εq, hεq, hq⟩ :=
    n01_exists_componentOpticalQuotient_positive hS hT hA hG
  let ε' : ℝ := min ε (min (1 / 2) (min εo εq))
  have hε' : 0 < ε' :=
    lt_min hε (lt_min (by norm_num) (lt_min hεo hεq))
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'2 : ε' ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hε'o : ε' ≤ εo :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε'q : ε' ≤ εq :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hpos (b : ℕ) : ∀ z ∈ stateNeighborhood S C b ε', ∀ m r,
      r ∈ Icc (C.left m) (C.right m) →
        0 < twoRootDivided (componentOpticalSquare D S C m z)
          (C.left m) (C.right m) r :=
    fun z hz m r hr => hq b z (stateNeighborhood_subset le_rfl hε'q hz) m r hr
  let P : ℕ → ℕ → Prop := fun b _ =>
    Nonempty (∀ m, ContinuousTimeSpeedTower (stateNeighborhood S C b ε')
      (componentCosineSpeed D S C m)) ∧
    Nonempty (OrdinarySpeedRadialTowers D S C (stateNeighborhood S C b ε'))
  obtain ⟨b, loss, hb, hP⟩ :=
    exists_base_ge_of_spatialPower_continuation
      (pairGrading (stateGrading S) realGrading) (jointStateGrading_monotone S)
      (jointStateGrading_hasInterpolation hS) base 4 P
      (fun b loss hb hI => by
        have hB' : N01PartB D S C b ε' := n01PartB_mono hB hb hε'ε
        have hroot := ho ε' hε' hε'o b loss
        let G := Classical.choice hroot.1
        let F := wholeCharacteristicSpeed_powerControl
          hS hT hA hε' (hε'2.trans (by norm_num)) hB' hE hG.1 hG.2.1 hI G hroot.2
        exact ⟨⟨fun m => componentCosineSpeed_continuousTimeSpeedTower
          hS hT hA hε' hε'2 hB' hE hG.1 hG.2.1 hI
          G hroot.2 (hpos b) m⟩,
          ⟨minusCharacteristicSpeed_radialJointSmoothDirections
            hS hT hA hε'2 hB' hE (hpos b) F⟩⟩)
  exact ⟨b, ε', hb, hε', hε'ε, n01PartB_mono hB hb hε'ε, hpos b, hP.1, hP.2⟩

/-- The cosine-only interface is a projection of the common construction. -/
theorem n01_exists_componentCosineSpeed_towers
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε)
    (hB : N01PartB D S C base ε)
    (hG : N01PrimitiveGeometry D T S C)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r) :
    ∃ base' : ℕ, ∃ ε' : ℝ, base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      N01PartB D S C base' ε' ∧
      (∀ z ∈ stateNeighborhood S C base' ε', ∀ m r,
        r ∈ Icc (C.left m) (C.right m) →
          0 < twoRootDivided (componentOpticalSquare D S C m z)
            (C.left m) (C.right m) r) ∧
      Nonempty (∀ m, ContinuousTimeSpeedTower (stateNeighborhood S C base' ε')
        (componentCosineSpeed D S C m)) := by
  obtain ⟨b, e, hb, he, her, hB', hp, hJ, _⟩ :=
    n01_exists_commonSpeed_towers hS hT hA hε hB hG hE
  exact ⟨b, e, hb, he, her, hB', hp, hJ⟩

/-- After the single choice, every stronger base and smaller positive
radius inherits the same actual towers and endpoint quotient positivity. -/
theorem n01_exists_stable_componentCosineSpeed_towers
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε)
    (hB : N01PartB D S C base ε)
    (hG : N01PrimitiveGeometry D T S C)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r) :
    ∃ base₀ : ℕ, ∃ ε₀ : ℝ, base ≤ base₀ ∧ 0 < ε₀ ∧ ε₀ ≤ ε ∧
      ∀ base' : ℕ, base₀ ≤ base' → ∀ ε' : ℝ, 0 < ε' → ε' ≤ ε₀ →
        N01PartB D S C base' ε' ∧
        (∀ z ∈ stateNeighborhood S C base' ε', ∀ m r,
          r ∈ Icc (C.left m) (C.right m) →
            0 < twoRootDivided (componentOpticalSquare D S C m z)
              (C.left m) (C.right m) r) ∧
        Nonempty (∀ m, ContinuousTimeSpeedTower (stateNeighborhood S C base' ε')
          (componentCosineSpeed D S C m)) := by
  obtain ⟨base₀, ε₀, hb, he, her, hB₀, hpos, ⟨J⟩⟩ :=
    n01_exists_componentCosineSpeed_towers hS hT hA hε hB hG hE
  refine ⟨base₀, ε₀, hb, he, her, fun base' hb' ε' _ he' => ?_⟩
  have hsub : stateNeighborhood S C base' ε' ⊆ stateNeighborhood S C base₀ ε₀ :=
    stateNeighborhood_subset hb' he'
  exact ⟨n01PartB_mono hB₀ hb' he',
    fun z hz m r hr => hpos z (hsub hz) m r hr,
    ⟨fun m => (J m).n01c_restrict (isOpen_stateNeighborhood S C base' ε') hsub⟩⟩

/-- Both kinds of actual speed tower persist on every subsequent
stronger-base, smaller-radius state neighbourhood. -/
theorem n01_exists_stable_commonSpeed_towers
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε)
    (hB : N01PartB D S C base ε)
    (hG : N01PrimitiveGeometry D T S C)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r) :
    ∃ base₀ : ℕ, ∃ ε₀ : ℝ, base ≤ base₀ ∧ 0 < ε₀ ∧ ε₀ ≤ ε ∧
      ∀ base' : ℕ, base₀ ≤ base' → ∀ ε' : ℝ, 0 < ε' → ε' ≤ ε₀ →
        N01PartB D S C base' ε' ∧
        (∀ z ∈ stateNeighborhood S C base' ε', ∀ m r,
          r ∈ Icc (C.left m) (C.right m) →
            0 < twoRootDivided (componentOpticalSquare D S C m z)
              (C.left m) (C.right m) r) ∧
        Nonempty (∀ m, ContinuousTimeSpeedTower (stateNeighborhood S C base' ε')
          (componentCosineSpeed D S C m)) ∧
        Nonempty (OrdinarySpeedRadialTowers D S C (stateNeighborhood S C base' ε')) := by
  obtain ⟨base₀, ε₀, hb, he, her, hB₀, hpos, ⟨J⟩, ⟨R⟩⟩ :=
    n01_exists_commonSpeed_towers hS hT hA hε hB hG hE
  refine ⟨base₀, ε₀, hb, he, her, fun base' hb' ε' _ he' => ?_⟩
  have hsub : stateNeighborhood S C base' ε' ⊆ stateNeighborhood S C base₀ ε₀ :=
    stateNeighborhood_subset hb' he'
  have hU : IsOpen (stateNeighborhood S C base' ε') :=
    isOpen_stateNeighborhood S C base' ε'
  exact ⟨n01PartB_mono hB₀ hb' he',
    fun z hz m r hr => hpos z (hsub hz) m r hr,
    ⟨fun m => (J m).n01c_restrict hU hsub⟩,
    ⟨fun m a r hr => (R m a r hr).restrict (hU.prod isOpen_univ)
      (fun _ hy => ⟨hsub hy.1, hy.2⟩)⟩⟩

end ContinuousFlexibility.Blueprint
