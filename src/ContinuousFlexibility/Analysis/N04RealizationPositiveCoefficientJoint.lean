module

public import ContinuousFlexibility.Analysis.N04RealizationCoefficientAnnularTowers
public import ContinuousFlexibility.Analysis.N04RealizationMixedJointDirections
public import ContinuousFlexibility.Analysis.N04RealizationPositiveCoefficientPowerBounds

/-!
# The same corrected coefficient jointly on a fixed positive interval

N03 identifies the actual corrected coefficients with the original
coefficients on every positive physical interval. The genuine annular
mixed towers therefore restrict to that interval on the same state
neighborhood. Their uniform seminorm bounds justify the existing joint
construction without assuming a current canonical jet estimate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

local instance n04RealizationPositiveCoefficientJointStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε l r : ℝ}

theorem n04Realization_positiveCoefficientFixed_eq_original
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hdom : (Ioo l r ×ˢ (univ : Set ℝ)) ⊆
      {p : PolarPoint | p ∈ annularOpen D ∧ 0 < deriv D.w p.1})
    (i : Fin 3) {z : StateDirections S × ℝ}
    (hz : z ∈ sectorNeighborhood S base ε ε)
    {p : PolarPoint} (hp : p ∈ Ioo l r ×ˢ (univ : Set ℝ)) :
    canonicalCoefficientComponent i (L.coefficients (liftSectorParameter S C z)) p =
      originalCoefficientEntry D S C i (liftSectorParameter S C z) p := by
  have he := n04Realization_positiveCoefficient_eq_original hN.2
    (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
    (hN.1.1.2.2.1.liftSectorParameter_sector z) (hdom hp).1 (hdom hp).2 i
  simpa only [coefficientOriginalField, originalCoefficientEntry, ite_apply] using he

def n04Realization_positiveCoefficientFixedMixedRegularity
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hdom : (Ioo l r ×ˢ (univ : Set ℝ)) ⊆
      {p : PolarPoint | p ∈ annularOpen D ∧ 0 < deriv D.w p.1})
    (i : Fin 3) :
    MixedJetRegularity (sectorNeighborhood S base ε ε) (Ioo l r ×ˢ (univ : Set ℝ))
      (fun z => canonicalCoefficientComponent i (L.coefficients (liftSectorParameter S C z))) where
  spatial z hz :=
    ((hN.1.1.original_coefficient_contDiffOn hS hT
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (hN.1.1.2.2.1.liftSectorParameter_sector z) i).mono
      (fun _ hp => (hdom hp).1)).congr
      (fun p hp => n04Realization_positiveCoefficientFixed_eq_original hN hdom i hz hp)
  parameter a b p hp :=
    (n04Realization_annularOriginalMixedTower hN.1.1 hS hT i a b p (hdom hp).1).congr
      (fun z hz => (mixedDerivative_congr_on_open (isOpen_Ioo.prod isOpen_univ)
        (fun q hq => n04Realization_positiveCoefficientFixed_eq_original hN hdom i hz hq)
        a b hp).symm)

theorem n04Realization_positiveCoefficientFixedMixed_uniform
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hdom : (Ioo l r ×ˢ (univ : Set ℝ)) ⊆
      {p : PolarPoint | p ∈ annularOpen D ∧ 0 < deriv D.w p.1})
    (i : Fin 3) (a b : ℕ) :
    UniformScalarJetSeminormBounds
      (fun p : Ioo l r ×ˢ (univ : Set ℝ) =>
        (n04Realization_positiveCoefficientFixedMixedRegularity hN hS hT hdom i).parameter
          a b p p.property) :=
  (n04Realization_annularOriginalMixed_uniform hN.1.1 hS hT i a b).reindex
    (fun p : Ioo l r ×ˢ (univ : Set ℝ) =>
      (⟨p.val, (hdom p.property).1⟩ : annularOpen D))

/-- The supplied interval and original sector neighborhood are retained.
The explicit expansion of this tower is the generic mixed-joint formula. -/
def n04Realization_positiveCoefficientFixedJointDirections
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hdom : (Ioo l r ×ˢ (univ : Set ℝ)) ⊆
      {p : PolarPoint | p ∈ annularOpen D ∧ 0 < deriv D.w p.1})
    (i : Fin 3) :
    SmoothDirections
      (sectorNeighborhood S base ε ε ×ˢ (Ioo l r ×ˢ (univ : Set ℝ)))
      (fun x : (StateDirections S × ℝ) × PolarPoint =>
        canonicalCoefficientComponent i (L.coefficients (liftSectorParameter S C x.1)) x.2) :=
  n04Realization_mixedJointDirections
    (n04Realization_positiveCoefficientFixedMixedRegularity hN hS hT hdom i)
    (sectorNeighborhood_isOpen S base ε ε) (sectorNeighborhood_convex S base ε ε)
    isOpen_Ioo (convex_Ioo l r)
    (n04Realization_positiveCoefficientFixedMixed_uniform hN hS hT hdom i)

end ContinuousFlexibility.Analysis
