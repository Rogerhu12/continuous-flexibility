module

public import ContinuousFlexibility.Statements.Milestones

/-!
# Statements of blueprint v3

Intermediate statements that the earlier statement layer does not contain. They split
large nodes along the top-level structure of their statements, and state the last link
of the chain for one nonzero parameter. All definitions are built from the existing
data and property definitions of `ContinuousFlexibility.Statements`.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Blueprint

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

/-! ## R05: realization, then mass and resistance -/

/-- The chain of cells and joins is realized for every admissible height sequence. -/
def R05aStatement : Prop :=
  ∀ initial : ℕ, ∃ T : MorseChainData, initial ≤ T.index ∧
    ∃ C : ℕ → ℝ, ∃ family : (ℕ → ℝ) → ReferenceData,
      (∀ σ, (∀ n, 1 ≤ σ n ∧ σ n ≤ 2) → MorseChainRealization T σ (family σ) C) ∧
      (∀ σ τ, (family σ).a = (family τ).a ∧ (family σ).b = (family τ).b ∧
        (family σ).cells = (family τ).cells)

/-- Every realized chain has the mass and resistance bounds, after enlarging the constants. -/
def R05bStatement : Prop :=
  ∀ (T : MorseChainData) (C : ℕ → ℝ) (family : (ℕ → ℝ) → ReferenceData),
    (∀ σ, (∀ n, 1 ≤ σ n ∧ σ n ≤ 2) → MorseChainRealization T σ (family σ) C) →
    ∃ C' : ℕ → ℝ, ∀ σ, (∀ n, 1 ≤ σ n ∧ σ n ≤ 2) →
      MorseChainRealization T σ (family σ) C' ∧ MorseMassResistanceBounds T σ (family σ) C'

/-! ## R06: inverse, then natural line and Green kernel, then the physical clauses -/

/-- Form identification and the inverse with its truncations, for given constants. -/
def R06Operator (C η₀ K₀ : ℝ) : Prop :=
  (∀ T : DeepTailData, DeepTailHypotheses T → T.η ≤ η₀ → K₀ ≤ T.K →
    TailFormIdentification T T.endpoint ∧
    (∀ n, TailFormIdentification T (T.node (n + 1))) ∧
    ∃ G : DeepTailL2 T →L[ℝ] DeepTailL2 T,
      ‖G‖ ≤ C / T.Λ ∧
      (∀ f, TailFriedrichsGraph T T.endpoint (G f) (f + T.Λ • G f)) ∧
      (∀ u f, TailFriedrichsGraph T T.endpoint u (f + T.Λ • u) → G f = u) ∧
      (∃ Gₙ Pₙ : ℕ → (DeepTailL2 T →L[ℝ] DeepTailL2 T),
        (∀ n f, ((Pₙ n f : DeepTailL2 T) : ℝ → ℝ) =ᵐ[deepTailMeasure T]
          fun x => if x < T.node (n + 1) then f x else 0) ∧
        (∀ n f, TailFriedrichsGraph T (T.node (n + 1)) (Gₙ n (Pₙ n f))
          (Pₙ n f + T.Λ • Gₙ n (Pₙ n f))) ∧
        (∀ f, Tendsto (fun n => Gₙ n (Pₙ n f)) atTop (𝓝 (G f)))))

/-- The first clause of `R06Statement`, for given constants. -/
def R06Full (C η₀ K₀ : ℝ) : Prop :=
  (∀ T : DeepTailData, DeepTailHypotheses T → T.η ≤ η₀ → K₀ ≤ T.K →
    TailFormIdentification T T.endpoint ∧
    (∀ n, TailFormIdentification T (T.node (n + 1))) ∧
    ∃ G : DeepTailL2 T →L[ℝ] DeepTailL2 T,
      ‖G‖ ≤ C / T.Λ ∧
      (∀ f, TailFriedrichsGraph T T.endpoint (G f) (f + T.Λ • G f)) ∧
      (∀ u f, TailFriedrichsGraph T T.endpoint u (f + T.Λ • u) → G f = u) ∧
      (∃ Gₙ Pₙ : ℕ → (DeepTailL2 T →L[ℝ] DeepTailL2 T),
        (∀ n f, ((Pₙ n f : DeepTailL2 T) : ℝ → ℝ) =ᵐ[deepTailMeasure T]
          fun x => if x < T.node (n + 1) then f x else 0) ∧
        (∀ n f, TailFriedrichsGraph T (T.node (n + 1)) (Gₙ n (Pₙ n f))
          (Pₙ n f + T.Λ • Gₙ n (Pₙ n f))) ∧
        (∀ f, Tendsto (fun n => Gₙ n (Pₙ n f)) atTop (𝓝 (G f)))) ∧
      TailNaturalLineAndKernel T ∧ TailGreenKernel T G)

/-- The second clause of `R06Statement`, for given constants. -/
def R06Physical (η₀ K₀ : ℝ) : Prop :=
  (∀ D T right j start, IsAccumulatingProfile D → DeepTailHypotheses T →
    T.η ≤ η₀ → K₀ ≤ T.K →
    TailPhysicalRelation D T right j start →
    TailPhysicalFlatConclusion D T right j start ∧ TailPhysicalSourceIdentity D T right j)

def R06aStatement : Prop :=
  ∃ C η₀ K₀ : ℝ, 0 < C ∧ 0 < η₀ ∧ η₀ < 1 ∧ 1 < K₀ ∧ R06Operator C η₀ K₀

def R06bStatement : Prop :=
  ∀ C η₀ K₀ : ℝ, 0 < C → 0 < η₀ → η₀ < 1 → 1 < K₀ → R06Operator C η₀ K₀ →
    ∃ C' η₀' K₀' : ℝ, 0 < C' ∧ 0 < η₀' ∧ η₀' < 1 ∧ 1 < K₀' ∧ R06Full C' η₀' K₀'

def R06cStatement : Prop :=
  ∀ C η₀ K₀ : ℝ, 0 < C → 0 < η₀ → η₀ < 1 → 1 < K₀ → R06Full C η₀ K₀ →
    ∃ C' η₀' K₀' : ℝ, 0 < C' ∧ 0 < η₀' ∧ η₀' < 1 ∧ 1 < K₀' ∧ R06Full C' η₀' K₀' ∧
      R06Physical η₀' K₀' ∧ DeepTailParameterContinuity η₀' K₀'

/-! ## R10: the inner and outer pieces, then the matching -/

/-- Everything in `ActualMatchedRepresentation` that precedes the inversion of the
matching matrix: cuts, the selected margin, the inner and outer realizations. -/
def MatchedPieces (D : ReferenceData) (M : RadialMatchingData D) : Prop :=
  D.a < M.innerLeft ∧ M.innerLeft < M.innerRight ∧ M.innerRight < D.b ∧
    Function.support (referenceColumn D) ⊆ Ioo M.innerLeft M.innerRight ∧
    0 < M.margin ∧
    (∀ i, 0 < M.boundaryScale i ∧ 0 < M.D0 i ∧ M.D0 i ≤ 1 / 2 ∧
      M.margin ≤ |M.A i i * M.D0 i - M.B i i|) ∧
    (∀ i j, |M.Db i j - (if i = j then M.D0 i else 0)| ≤ M.margin / 16) ∧
    MatchingLocalRealizations D M ∧
    (∀ i j, M.Db i j = M.Db j i) ∧
    (∀ i j, i ≠ j → M.A i j = 0 ∧ M.B i j = 0) ∧
    (∀ i, M.A i i ^ 2 + M.B i i ^ 2 = 1)

def R10aStatement : Prop :=
  ∃ D : ReferenceData, IsAccumulatingProfile D ∧ RadialTrueBorder D ∧
    RadialConstructionGeometry D ∧
    ∀ j : ℕ, 2 ≤ j → Even j →
      ∃ M : RadialMatchingData D, M.frequency = j ∧ MatchedPieces D M

def R10bStatement : Prop :=
  ∀ D : ReferenceData, IsAccumulatingProfile D → RadialTrueBorder D →
    ∀ j : ℕ, 2 ≤ j → Even j → ∀ M : RadialMatchingData D, M.frequency = j →
      MatchedPieces D M →
      ∃ G : RadialModePair D →L[ℝ] RadialModePair D,
        ModeInverseProperties D j G ∧
        ∃ M' : RadialMatchingData D, M'.frequency = j ∧ ActualMatchedRepresentation D G M'

/-! ## R11: the weighted inverse estimates, then the first normal estimate -/

/-- `R11Statement` without the first normal estimate. -/
def R11aStatement : Prop :=
  ∃ D : ReferenceData, IsAccumulatingProfile D ∧ RadialTrueBorder D ∧
    RadialConstructionGeometry D ∧
    ∃ ε M₀ M₁ : ℝ, 0 < ε ∧ ε < 1 / 4 ∧
      ∃ G : RadialSource → RadialUnknown,
        (∀ j : ℕ, 2 ≤ j → Even j →
          ∃ Gmode : RadialModePair D →L[ℝ] RadialModePair D,
            ModeInverseProperties D j Gmode ∧
            ∃ M : RadialMatchingData D, M.frequency = j ∧ ActualMatchedRepresentation D Gmode M) ∧
        ∀ γ : ℝ, γ = referenceBeta - ε ∨ γ = referenceBeta ∨ γ = referenceBeta + ε →
          ReferenceInverseProperties D γ M₀ M₁ G

/-! ## N04: canonical coordinates apart from the three standalone targets -/

/-- `N04Statement` without `RootCompositionTarget`, `CubicDivisionTarget` and
`PhysicalTransmissionTarget`, which are independent of all project data. -/
def N04cStatement : Prop :=
  ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
    ∃ C : NonlinearGeometryData S, ∃ R : ReturnEquationData S,
      ∃ L : ReturnCorrectionData S, ∃ K : CanonicalData S,
        ∃ base loss : ℕ, ∃ ε : ℝ,
          IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧
            NonlinearPropertiesThrough03 A.val T S C R L base loss ε ∧
              N04Properties A.val T S C L K base loss ε ∧
                CanonicalGeometry.PrimitiveGeometryProperties A.val T S C L K base ε ∧
                CanonicalPrimitiveGeometry A.val T S C L K base ε

/-! ## N07: the scalar inverse, then its identification with the Banach solution -/

/-- `N07Statement` without `ScalarBanachBridgeProperties`. -/
def N07aStatement : Prop :=
  ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
    ∃ C : NonlinearGeometryData S, ∃ R : ReturnEquationData S,
      ∃ L : ReturnCorrectionData S, ∃ K : CanonicalData S,
        ∃ Vol : VolumeModelData S K, ∃ b : ℕ,
          ∃ Domain : CanonicalDomainData S K Vol b,
            ∃ Relative : RelativeInverseData S K Vol b Domain,
              ∃ G : ScalarInverseData S, ∃ base loss : ℕ, ∃ ε : ℝ,
                IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧
                  NonlinearPropertiesThrough06 A.val T S C R L K Vol b Domain Relative
                    base loss ε ∧
                  ScalarInverseProperties A.val S C L G base ε

/-! ## The nonlinear solution at one nonzero parameter -/

/-- One solution of the scalar and both return equations at one nonzero parameter, on the
same reference, spaces and geometry. This is the pointwise part of `IsWeakBranch`; the
main theorem fixes one nonzero parameter and does not use smoothness of the branch in it. -/
def PointBranchStatement : Prop :=
  ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
    IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧
    ∃ C : NonlinearGeometryData S, ∃ R : ReturnEquationData S, ∃ base loss : ℕ, ∃ ε : ℝ,
      N01Properties A.val T S C base loss ε ∧
      ∃ x : AnnularState S, ∃ q : ℝ, q ≠ 0 ∧
        (x, q) ∈ stateNeighborhood S C base ε ∧
        stateSector S x ∧
        referenceRow A.val (stateU S x) = 1 ∧
        (∀ p ∈ annularOpen A.val, scalarResidualField A.val S C (x, q) p = 0) ∧
        R.residual (x, q) = 0 ∧
        ∀ m θ,
          rightChartCandidate S C (x, q) m (C.minusFlow (x, q) m (C.right m) θ) =
            stateLeftChart S x m θ - C.travel m ∧
          rightChartCandidate S C (x, q) m (-C.minusFlow (x, q) m (C.right m) (-θ)) =
            stateLeftChart S x m θ + C.travel m

/-! ## N01: reference and controls, then one neighbourhood, then the tame bounds -/

/-- The conjuncts of `N01Properties` about the reference and the travel-angle controls. -/
def N01PartA (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) : Prop :=
  IsRadialReference D ∧ referenceStateConditions D S C ∧ controlGeometryConditions D S C ∧
  (∃ B : ℝ, 0 < B ∧ ∀ m,
    |(D.cellIndex (C.cell m) : ℝ) - D.cellIndex m| ≤ B) ∧
  (∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m r,
    r ∈ Ioo (C.left m) (C.right m) →
      |iteratedDeriv s (C.control m) r| ≤ B * T.E0 (T.sample (C.cell m)) ^ B)

/-- The reference geometry used by the nonlinear estimates, retained on the
same data as the controls and material weights. These are primitive support,
placement and nondegeneracy assertions, not tame conclusions. -/
def N01PrimitiveGeometry (D : ReferenceData) (T : MaterialData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S) : Prop :=
  (∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m)) ∧
  tsupport D.chi ⊆ Ioo D.a D.b ∧
  ∃ K : ℝ, 0 < K ∧ ∀ m r,
    r ∈ Ioo (C.left m) (C.right m) →
      K⁻¹ * T.E0 (T.sample (C.cell m)) ^ (-K) *
          min (r - C.left m) (C.right m - r) ≤
        -deriv D.w r / (r * D.w r)

/-- The conjuncts of `N01Properties` about flows, charts, denominators and the type,
on one neighbourhood. -/
def N01PartB (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base : ℕ) (ε : ℝ) : Prop :=
  ordinaryFlowConditions D S C (stateNeighborhood S C base ε) ∧
  (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ m θ,
    (1 / 2 : ℝ) ≤ deriv (stateLeftChart S z.1 m) θ ∧
    deriv (stateLeftChart S z.1 m) θ ≤ 2 ∧
    stateLeftChart S z.1 m (θ + Real.pi) = stateLeftChart S z.1 m θ + Real.pi ∧
    stateLeftChart S z.1 m (-θ) = -stateLeftChart S z.1 m θ) ∧
  (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ m θ,
    let hR : ℝ → ℝ := fun t =>
      ((stateLeftChart S z.1 m (C.minusReturnInverse z m t) - C.travel m) -
        (stateLeftChart S z.1 m (C.minusReturnInverse z m (-t)) - C.travel m)) / 2
    C.minusFlow z m (C.right m) (C.minusReturnInverse z m θ) = θ ∧
    C.minusReturnInverse z m (C.minusFlow z m (C.right m) θ) = θ ∧
    hR (C.rightChartInverse z m θ) = θ ∧ C.rightChartInverse z m (hR θ) = θ) ∧
  (∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ p ∈ annularOpen D,
    (1 / 2 : ℝ) ≤ stateProfile D S C z.1 p.1 / D.w p.1 ∧
    stateProfile D S C z.1 p.1 / D.w p.1 ≤ 2 ∧
    (7 / 8 : ℝ) ≤ heightQ (profileEnergy (stateProfile D S C z.1) p)
      (heightRadial (stateHeight D S C z) p)
      (angularPartial (heightAngular (stateHeight D S C z)) p) /
        stateProfile D S C z.1 p.1 ∧
    heightQ (profileEnergy (stateProfile D S C z.1) p)
      (heightRadial (stateHeight D S C z) p)
      (angularPartial (heightAngular (stateHeight D S C z)) p) /
        stateProfile D S C z.1 p.1 ≤ (9 / 8 : ℝ) ∧
    (1 / 2 : ℝ) ≤ polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p ∧
    polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p ≤ (3 / 2 : ℝ)) ∧
  (∀ z ∈ stateNeighborhood S C base ε, ∀ r ∈ Ioo D.a D.b,
    deriv D.w r = 0 → stateProfile D S C z.1 =ᶠ[𝓝 r] D.w)

def N01aStatement : Prop :=
  ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
    ∃ C : NonlinearGeometryData S,
      IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧ N01PartA A.val T S C ∧
        N01PrimitiveGeometry A.val T S C

def N01bStatement : Prop :=
  ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
    ∃ C : NonlinearGeometryData S, ∃ base : ℕ, ∃ ε : ℝ,
      IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧ N01PartA A.val T S C ∧
        0 < ε ∧ N01PartB A.val S C base ε ∧ N01PrimitiveGeometry A.val T S C

/-! ## N04: pieces and charts, then the canonical form, then bounds and sources -/

/-- The exact common geometry predicate on the actual current physical domains. -/
def N04PartA (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (K : CanonicalData S) (base : ℕ) (ε : ℝ) : Prop :=
  CanonicalGeometry D S C K base ε

/-- The exact common cut and actual canonical operator predicate. -/
def N04PartB (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (K : CanonicalData S) (base : ℕ) (ε : ℝ) : Prop :=
  CanonicalCutOperatorProperties S C L K base ε

def N04aStatement : Prop :=
  ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
    ∃ C : NonlinearGeometryData S, ∃ R : ReturnEquationData S,
      ∃ L : ReturnCorrectionData S, ∃ K : CanonicalData S,
        ∃ base loss : ℕ, ∃ ε : ℝ,
          IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧
            NonlinearPropertiesThrough03 A.val T S C R L base loss ε ∧
              N04PartA A.val S C K base ε

def N04bStatement : Prop :=
  ∃ A : RadialReference, ∃ T : MaterialData, ∃ S : PhysicalSpacesData,
    ∃ C : NonlinearGeometryData S, ∃ R : ReturnEquationData S,
      ∃ L : ReturnCorrectionData S, ∃ K : CanonicalData S,
        ∃ base loss : ℕ, ∃ ε : ℝ,
          IsMaterialData A.val T ∧ IsPhysicalSpaces A.val T S ∧
            NonlinearPropertiesThrough03 A.val T S C R L base loss ε ∧
              N04PartA A.val S C K base ε ∧ N04PartB S C L K base ε

end ContinuousFlexibility.Blueprint
