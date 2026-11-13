import ContinuousFlexibility.Analysis.N04RealizationCoefficientAnnularTowers
import ContinuousFlexibility.Analysis.N04RealizationMixedJointDirections

/-!
# Small joint-tower adapters before the retained start is substituted

The original coefficient mixed tower is joined with abstract N01 data.
Subtraction is likewise carried out over an arbitrary parameter space.
The retained start then supplies its data to these short constructors.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- Joint scalar subtraction with an explicit on-domain identity. -/
def n04PulledFields_jointSubtraction_on
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    {U : Set E} {f g h : E → ℝ}
    (J : SmoothDirections U f) (K : SmoothDirections U g)
    (heq : ∀ x ∈ U, h x = f x - g x) : SmoothDirections U h := by
  let N := solveSmoothDirectionsPostcomp K (-ContinuousLinearMap.id ℝ ℝ)
  apply (smoothDirectionsAdd J N).congrOn
  intro x hx
  change f x + -g x = h x
  exact (sub_eq_add_neg (f x) (g x)).symm.trans (heq x hx).symm

local instance n04PulledFieldsOriginalJointStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

/-- Join the actual original coefficient tower before substituting a
large retained-start structure into its uniform seminorm certificate. -/
def n04PulledFields_originalCoefficientJointDirections
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (i : Fin 3) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ annularOpen D)
      (fun x : (StateDirections S × ℝ) × PolarPoint =>
        originalCoefficientEntry D S C i (liftSectorParameter S C x.1) x.2) :=
  n04Realization_mixedJointDirections
    (n04Realization_annularOriginalMixedRegularity hN hS hT i)
    (sectorNeighborhood_isOpen S base ε ε) (sectorNeighborhood_convex S base ε ε)
    isOpen_Ioo (convex_Ioo D.a D.b)
    (n04Realization_annularOriginalMixed_uniform hN hS hT i)

end ContinuousFlexibility.Analysis
