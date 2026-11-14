module

public import ContinuousFlexibility.Analysis.N01cStateSeminorms
public import ContinuousFlexibility.Analysis.N01cAssembly

/-!
# Restriction of the N01 estimates to one common neighbourhood

Increasing the controlling order and the spatial loss, and decreasing the
radius, preserves the coefficient and ordinary-flow estimates.  The original
constants, parameter losses and directional derivatives are retained.  The
only comparison is the monotonicity of the actual state seminorms; positivity
of the material weights is supplied at the actual sample points.

The final assembly puts independently obtained geometric, coefficient and
flow estimates on their common neighbourhood.  It does not assert any of the
analytic estimates that are the open N01c tasks.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped Topology BigOperators

section RestrictionIdentity

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

/-- Restriction changes the domain of a directional tower, not its derivatives. -/
theorem SmoothDirections.restrict_D {U V : Set E} {f : E → F}
    (J : SmoothDirections U f) (hV : IsOpen V) (hVU : V ⊆ U)
    (n : ℕ) (x : E) (v : Fin n → E) :
    (J.restrict hV hVU).D n x v = J.D n x v := rfl

end RestrictionIdentity


section GenericEstimateRestriction

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

/-- Restrict a scalar directional tower and enlarge its one-high-factor bound.
All algebra in this proof is over an abstract state space.  The scalar map
`φ` may include a fixed spatial weight, so coefficient and flow restrictions
use exactly the same proof. -/
theorem exists_smoothDirections_restrict_oneHighWeight
    {U V : Set E} {f : E → ℝ} {p : ℕ → Seminorm ℝ E}
    {base base' high high' k : ℕ} {center : E} {φ : ℝ → ℝ} {K : ℝ}
    (hV : IsOpen V) (hVU : V ⊆ U) (hp : Monotone p)
    (hb : base ≤ base') (hh : high ≤ high') (hK : 0 ≤ K)
    (h : ∃ J : SmoothDirections U f,
      ∀ z ∈ U, ∀ v : Fin k → E,
        φ (J.D k z v) ≤ K * oneHighVariationWeight p base high (z - center) v) :
    ∃ J : SmoothDirections V f,
      ∀ z ∈ V, ∀ v : Fin k → E,
        φ (J.D k z v) ≤ K * oneHighVariationWeight p base' high' (z - center) v := by
  obtain ⟨J, hJ⟩ := h
  refine ⟨J.restrict hV hVU, ?_⟩
  intro z hz v
  change φ (J.D k z v) ≤ K * oneHighVariationWeight p base' high' (z - center) v
  exact (hJ z (hVU hz) v).trans
    (mul_le_mul_of_nonneg_left (oneHighVariationWeight_mono hp hb hh (z - center) v) hK)


/-- The complete coefficient quantifier pattern restricts over an abstract
state space.  The concrete-state specialization below is a single application. -/
theorem coefficientBounds_restrict
    {U V : Set E} {grading : ℕ → Seminorm ℝ E} {center : E}
    {family : Fin 3 → ℕ → ℕ → PolarPoint → E → ℝ}
    {cells : ℕ → Set ℝ} {weight : ℝ → ℕ → ℝ}
    {base base' loss loss' : ℕ}
    (hV : IsOpen V) (hVU : V ⊆ U) (hp : Monotone grading)
    (hb : base ≤ base') (hl : loss ≤ loss')
    (hw : ∀ B : ℝ, 0 < B → ∀ m : ℕ, 0 ≤ weight B m)
    (h : ∀ k s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m i a b point,
      a + b ≤ s → point.1 ∈ cells m →
      ∃ J : SmoothDirections U (family i a b point),
        ∀ z ∈ U, ∀ v : Fin k → E,
          |J.D k z v| ≤ weight B m *
            oneHighVariationWeight grading base (s + loss) (z - center) v) :
    ∀ k s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m i a b point,
      a + b ≤ s → point.1 ∈ cells m →
      ∃ J : SmoothDirections V (family i a b point),
        ∀ z ∈ V, ∀ v : Fin k → E,
          |J.D k z v| ≤ weight B m *
            oneHighVariationWeight grading base' (s + loss') (z - center) v := by
  intro k s
  obtain ⟨B, hB, hbound⟩ := h k s
  refine ⟨B, hB, ?_⟩
  intro m i a b point hab hpnt
  exact exists_smoothDirections_restrict_oneHighWeight hV hVU hp hb
    (Nat.add_le_add_left hl s) (hw B hB m) (hbound m i a b point hab hpnt)

/-- The complete ordinary-flow quantifier pattern restricts over an abstract
state space, preserving the loss selected at each parameter order. -/
theorem ordinaryFlowBounds_restrict
    {U V : Set E} {grading : ℕ → Seminorm ℝ E} {center : E}
    {family : ℕ → ℕ → ℕ → PolarPoint → E → ℝ}
    {left right : ℕ → ℝ} {weight : ℝ → ℕ → ℝ}
    {base base' loss loss' : ℕ}
    (hV : IsOpen V) (hVU : V ⊆ U) (hp : Monotone grading)
    (hb : base ≤ base') (hl : loss ≤ loss')
    (hw : ∀ B : ℝ, 0 < B → ∀ m : ℕ, 0 ≤ weight B m)
    (h : ∀ k : ℕ, ∃ parameterLoss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ m a b point, a + b ≤ s → point.1 ∈ Ioo (left m) (right m) →
      ∃ J : SmoothDirections U (family m a b point),
        ∀ z ∈ U, ∀ v : Fin k → E,
          min (point.1 - left m) (right m - point.1) ^ a * |J.D k z v| ≤
            weight B m * oneHighVariationWeight grading base
              (s + loss + parameterLoss) (z - center) v) :
    ∀ k : ℕ, ∃ parameterLoss : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ m a b point, a + b ≤ s → point.1 ∈ Ioo (left m) (right m) →
      ∃ J : SmoothDirections V (family m a b point),
        ∀ z ∈ V, ∀ v : Fin k → E,
          min (point.1 - left m) (right m - point.1) ^ a * |J.D k z v| ≤
            weight B m * oneHighVariationWeight grading base'
              (s + loss' + parameterLoss) (z - center) v := by
  intro k
  obtain ⟨parameterLoss, hparameter⟩ := h k
  refine ⟨parameterLoss, fun s => ?_⟩
  obtain ⟨B, hB, hbound⟩ := hparameter s
  refine ⟨B, hB, ?_⟩
  intro m a b point hab hpnt
  exact exists_smoothDirections_restrict_oneHighWeight
    (k := k) (center := center)
    (φ := fun t : ℝ => min (point.1 - left m) (right m - point.1) ^ a * |t|)
    hV hVU hp hb
    (Nat.add_le_add_right (Nat.add_le_add_left hl s) parameterLoss)
    (hw B hB m) (hbound m a b point hab hpnt)

end GenericEstimateRestriction

/-- The component weight multiplying the one-high-factor expression is
nonnegative at every actual material sample. -/
theorem n01_componentWeight_nonneg {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (hsample : ∀ m, T.sample m ∈ Ioo D.a D.b)
    {B : ℝ} (hB : 0 ≤ B) (m : ℕ) :
    0 ≤ B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B := by
  have hH : 0 < T.H (T.sample m) := (hT.2.1 _ (hsample m)).2.1
  have hE : 0 < T.E0 (T.sample m) := (hT.2.1 _ (hsample m)).2.2.1
  exact mul_nonneg (mul_nonneg hB (Real.rpow_nonneg hH.le _))
    (Real.rpow_nonneg hE.le _)

set_option backward.isDefEq.respectTransparency true in
/-- Coefficient estimates persist on a stronger low-order ball with a larger
spatial loss.  No constant or directional derivative is replaced. -/
theorem coefficientFamilyTameBounds_mono {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {base base' loss loss' : ℕ} {ε ε' : ℝ}
    (hT : IsMaterialData D T) (hsample : ∀ m, T.sample m ∈ Ioo D.a D.b)
    (h : CoefficientFamilyTameBounds D T S C base loss ε)
    (hb : base ≤ base') (hl : loss ≤ loss') (hε : ε' ≤ ε) :
    CoefficientFamilyTameBounds D T S C base' loss' ε' := by
  exact coefficientBounds_restrict
    (E := AnnularState S × ℝ)
    (U := stateNeighborhood S C base ε) (V := stateNeighborhood S C base' ε')
    (grading := pairGrading (stateGrading S) realGrading)
    (center := (C.referenceState, 0)) (family := coefficientFamily D S C)
    (cells := D.cells)
    (weight := fun B m =>
      B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B)
    (isOpen_stateNeighborhood S C base' ε') (stateNeighborhood_subset hb hε)
    (jointStateGrading_monotone S) hb hl
    (fun B hB m => n01_componentWeight_nonneg hT hsample hB.le m) h

/-- The accumulating profile supplies the sample-membership hypothesis in the
coefficient restriction theorem. -/
theorem coefficientFamilyTameBounds_mono_of_accumulatingProfile
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base base' loss loss' : ℕ} {ε ε' : ℝ}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (h : CoefficientFamilyTameBounds D T S C base loss ε)
    (hb : base ≤ base') (hl : loss ≤ loss') (hε : ε' ≤ ε) :
    CoefficientFamilyTameBounds D T S C base' loss' ε' := by
  obtain ⟨_, hbounds⟩ := hRef
  exact coefficientFamilyTameBounds_mono hT
    (materialSample_mem_radialCore hT hbounds.2.1) h hb hl hε

set_option backward.isDefEq.respectTransparency true in
/-- Ordinary-flow estimates restrict with exactly the same state-derivative
loss at each parameter order. -/
theorem ordinaryFlowFamilyTameBounds_mono {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {base base' loss loss' : ℕ} {ε ε' : ℝ}
    (hT : IsMaterialData D T) (hsample : ∀ m, T.sample m ∈ Ioo D.a D.b)
    (h : OrdinaryFlowFamilyTameBounds T S C base loss ε)
    (hb : base ≤ base') (hl : loss ≤ loss') (hε : ε' ≤ ε) :
    OrdinaryFlowFamilyTameBounds T S C base' loss' ε' := by
  exact ordinaryFlowBounds_restrict
    (E := AnnularState S × ℝ)
    (U := stateNeighborhood S C base ε) (V := stateNeighborhood S C base' ε')
    (grading := pairGrading (stateGrading S) realGrading)
    (center := (C.referenceState, 0)) (family := ordinaryFlowFamily S C)
    (left := C.left) (right := C.right)
    (weight := fun B m => B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
      T.E0 (T.sample (C.cell m)) ^ B)
    (isOpen_stateNeighborhood S C base' ε') (stateNeighborhood_subset hb hε)
    (jointStateGrading_monotone S) hb hl
    (fun B hB m => n01_componentWeight_nonneg hT hsample hB.le (C.cell m)) h

theorem ordinaryFlowFamilyTameBounds_mono_of_accumulatingProfile
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base base' loss loss' : ℕ} {ε ε' : ℝ}
    (hT : IsMaterialData D T) (hRef : IsAccumulatingProfile D)
    (h : OrdinaryFlowFamilyTameBounds T S C base loss ε)
    (hb : base ≤ base') (hl : loss ≤ loss') (hε : ε' ≤ ε) :
    OrdinaryFlowFamilyTameBounds T S C base' loss' ε' := by
  obtain ⟨_, hbounds⟩ := hRef
  exact ordinaryFlowFamilyTameBounds_mono hT
    (materialSample_mem_radialCore hT hbounds.2.1) h hb hl hε

end ContinuousFlexibility.Statements

namespace ContinuousFlexibility.Blueprint

open Set ContinuousFlexibility.Statements

/-- Every geometric clause already established on the larger state
neighbourhood remains valid on the smaller one. -/
theorem n01PartB_mono {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base base' : ℕ} {ε ε' : ℝ}
    (h : N01PartB D S C base ε) (hb : base ≤ base') (hε : ε' ≤ ε) :
    N01PartB D S C base' ε' := by
  have hsub : stateNeighborhood S C base' ε' ⊆ stateNeighborhood S C base ε :=
    stateNeighborhood_subset hb hε
  obtain ⟨hFlow, hLeftChart, hInverses, hDenominators, hProfile⟩ := h
  exact ⟨ordinaryFlowConditions_mono hFlow hsub,
    fun z hz => hLeftChart z (hsub hz),
    fun z hz => hInverses z (hsub hz),
    fun z hz => hDenominators z (hsub hz),
    fun z hz => hProfile z (hsub hz)⟩

/-- The full N01 package persists after shrinking the positive-radius
neighbourhood and enlarging its base and spatial loss. -/
theorem n01Properties_mono {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {base base' loss loss' : ℕ} {ε ε' : ℝ}
    (hT : IsMaterialData D T) (h : N01Properties D T S C base loss ε)
    (hb : base ≤ base') (hl : loss ≤ loss') (hε : ε' ≤ ε) (hε' : 0 < ε') :
    N01Properties D T S C base' loss' ε' := by
  obtain ⟨hD, _, hReference, hControl, hIndex, hControlBounds,
    hFlow, hLeftChart, hInverses, hDenominators, hProfile,
    hCoefficients, hFlows⟩ := h
  have hA : N01PartA D T S C :=
    ⟨hD, hReference, hControl, hIndex, hControlBounds⟩
  have hB : N01PartB D S C base ε :=
    ⟨hFlow, hLeftChart, hInverses, hDenominators, hProfile⟩
  exact n01Properties_of_parts hA hε' (n01PartB_mono hB hb hε)
    (coefficientFamilyTameBounds_mono_of_accumulatingProfile hT hD.1
      hCoefficients hb hl hε)
    (ordinaryFlowFamilyTameBounds_mono_of_accumulatingProfile hT hD.1
      hFlows hb hl hε)

/-- Geometry, coefficient bounds and flow bounds on three initially different
neighbourhoods assemble on one explicit common neighbourhood.  All three inputs
refer to the same actual reference, spaces and nonlinear geometry. -/
theorem n01Properties_on_common_neighborhood
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    {baseGeometry baseCoefficients baseFlows lossCoefficients lossFlows : ℕ}
    {εGeometry εCoefficients εFlows : ℝ}
    (hT : IsMaterialData D T) (hA : N01PartA D T S C)
    (hGeometry : N01PartB D S C baseGeometry εGeometry)
    (hCoefficients : CoefficientFamilyTameBounds D T S C
      baseCoefficients lossCoefficients εCoefficients)
    (hFlows : OrdinaryFlowFamilyTameBounds T S C baseFlows lossFlows εFlows)
    (hεGeometry : 0 < εGeometry) (hεCoefficients : 0 < εCoefficients)
    (hεFlows : 0 < εFlows) :
    N01Properties D T S C
      (max baseGeometry (max baseCoefficients baseFlows))
      (max lossCoefficients lossFlows)
      (min εGeometry (min εCoefficients εFlows)) := by
  refine n01Properties_of_parts hA ?_ ?_ ?_ ?_
  · exact lt_min hεGeometry (lt_min hεCoefficients hεFlows)
  · exact n01PartB_mono hGeometry (le_max_left _ _) (min_le_left _ _)
  · exact coefficientFamilyTameBounds_mono_of_accumulatingProfile hT hA.1.1
      hCoefficients
      ((le_max_left baseCoefficients baseFlows).trans (le_max_right _ _))
      (le_max_left _ _)
      ((min_le_right _ _).trans (min_le_left εCoefficients εFlows))
  · exact ordinaryFlowFamilyTameBounds_mono_of_accumulatingProfile hT hA.1.1
      hFlows
      ((le_max_right baseCoefficients baseFlows).trans (le_max_right _ _))
      (le_max_right _ _)
      ((min_le_right _ _).trans (min_le_right εCoefficients εFlows))

end ContinuousFlexibility.Blueprint
