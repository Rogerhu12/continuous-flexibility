import ContinuousFlexibility.Analysis.N07aCoefficientParameterJets
import ContinuousFlexibility.Analysis.N07aHeightFamilyTame

/-!
# The two actual diagonal coefficient families in Height

The same construction handles both diagonal slots. The coefficient field,
its decoder, and every parameter derivative are those of N01; the final
closed-graph lift preserves N01's original fixed base and loss.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

attribute [local instance]
  n07aNonlinearDirectionsGroup
  n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup
  n07aNonlinearDirectionsSMul
  n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup
  n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup
  n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε γ : ℝ}

def n07aDiagonalCoefficientHeight
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) (hγ : γ < 3 / 64)
    (i : Fin 3) (hi : i ≠ 1) (z : StateDirections S × ℝ) : (S.height γ).Space := by
  classical
  exact if hz : z ∈ sectorNeighborhood S base ε ε then
    SobolevModelData.liftHeight (hS.1 γ)
      (n07aCoefficientDifferenceField D S C i (liftSectorParameter S C z))
      (n07aCoefficientDifferenceField_heightMember hS hT h01 hγ
        (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
        (h01.2.2.1.liftSectorParameter_sector z) i hi) else 0

theorem n07aDiagonalCoefficientHeight_decode
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) (hγ : γ < 3 / 64)
    (i : Fin 3) (hi : i ≠ 1)
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε) :
    (S.height γ).decode (n07aDiagonalCoefficientHeight hS hT h01 hγ i hi z) =
      n07aCoefficientDifferenceField D S C i (liftSectorParameter S C z) := by
  classical
  unfold n07aDiagonalCoefficientHeight
  rw [dite_eq_left hz]
  exact SobolevModelData.decode_liftHeight (hS.1 γ) _ _

theorem n07aDiagonalCoefficientHeight_fixedNeighborhoodSmoothTame
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) (hγ : γ < 3 / 64)
    (i : Fin 3) (hi : i ≠ 1) :
    FixedNeighborhoodSmoothTame (E := StateDirections S × ℝ) (F := (S.height γ).Space)
      (n07aParameterGrading S) (S.height γ).grading
      (sectorNeighborhood S base ε ε) base loss
      (n07aDiagonalCoefficientHeight hS hT h01 hγ i hi) := by
  apply n07a_heightFamily_fixedNeighborhoodSmoothTame
    (E := StateDirections S × ℝ) (δ := (3 / 64 : ℝ))
    (p := n07aParameterGrading S) (base := base) (loss := loss) (x₀ := 0)
    (hT := hT) (hA := hS.1 γ) (hU := n07a_sectorNeighborhood_isOpen S base ε ε)
    (hp := n07aParameterGrading_withSeminorms S)
    (hg := fun z hz => n07aDiagonalCoefficientHeight_decode hS hT h01 hγ i hi hz)
    (J := n07aCoefficientParameterJet hT h01 i)
    (hJ := ?_) (hγδ := hγ) (hmono := n07aParameterGrading_monotone S)
  intro k s
  let data := n07aCoefficientParameterJet_decay_bound hT h01 k s
  let B : ℝ := data.choose
  have hB : 0 < B := data.choose_spec.1
  have hb := data.choose_spec.2
  refine ⟨B, hB.le, fun a b p hab z hz v => ?_⟩
  simpa only [B, data, sub_zero] using hb i a b p hab z hz v

theorem n07aDiagonalCoefficientHeight_smoothTame
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε) (hγ : γ < 3 / 64)
    (i : Fin 3) (hi : i ≠ 1) :
    SmoothTameOn (E := StateDirections S × ℝ) (F := (S.height γ).Space)
      (n07aParameterGrading S) (S.height γ).grading
      (sectorNeighborhood S base ε ε)
      (n07aDiagonalCoefficientHeight hS hT h01 hγ i hi) :=
  (n07aDiagonalCoefficientHeight_fixedNeighborhoodSmoothTame hS hT h01 hγ i hi).1

end ContinuousFlexibility.Analysis
