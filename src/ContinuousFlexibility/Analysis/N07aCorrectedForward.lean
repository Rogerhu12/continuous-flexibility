import ContinuousFlexibility.Analysis.N07aOriginalForwardTame
import ContinuousFlexibility.Analysis.N07aForwardCorrection

/-!
# The actual return-corrected forward family into Source

The N03 error is subtracted from the already constructed original
divergence map. Its frozen decoder is exactly the required corrected
operator. Both terms take values in the same physical source kernel.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

attribute [local instance]
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}

def n07aCorrectedForwardCLM
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    (z : StateDirections S × ℝ) : HeightPair S →L[ℝ] S.Source :=
  n07aOriginalForwardCLM hS hT h01 z - n07aReturnCorrectionCLM hS h02 h03 z

theorem n07aCorrectedForwardCLM_apply
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    (z : StateDirections S × ℝ) (u : HeightPair S) :
    n07aCorrectedForwardCLM hS hT h01 h02 h03 z u =
      n07aOriginalForwardCLM hS hT h01 z u - n07aReturnCorrectionCLM hS h02 h03 z u :=
  ContinuousLinearMap.sub_apply _ _ _

theorem n07aCorrectedForwardCLM_decode
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε)
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    (u : HeightPair S) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    (S.height (3 / 4 : ℝ)).decode (n07aCorrectedForwardCLM hS hT h01 h02 h03 z u).val p =
      divergenceOperator (L.coefficients (liftSectorParameter S C z))
        (heightPairField S u) p := by
  simp only [n07aCorrectedForwardCLM_apply,
    Submodule.coe_sub, map_sub, Pi.sub_apply]
  rw [n07aOriginalForwardCLM_decode hS hT h01 hz u hp,
    n07aReturnCorrectionCLM_apply hS h02 h03 hz u,
    n07aReturnCorrection_decode h01.2.2.1 h03 hz u hp]
  ring

theorem n07aCorrectedForwardCLM_smoothTame
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε) :
    SmoothTameOn (n07aParameterHeightGrading S) S.sourceGrading
      (sectorNeighborhood S base ε ε ×ˢ univ)
      (fun z : (StateDirections S × ℝ) × HeightPair S =>
        n07aCorrectedForwardCLM hS hT h01 h02 h03 z.1 z.2) := by
  have hnegative := solve_smoothTameOn_postcomp (r := S.sourceGrading)
    (n07aReturnCorrectionCLM_smoothTame hS h02 h03)
    (-ContinuousLinearMap.id ℝ S.Source) (B := 1) zero_le_one
    (fun n f => by simp only [ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.id_apply, map_neg_eq_map, one_mul, le_refl])
  apply smoothTameOn_congr (smoothTameOn_add
    (tamePairGrading_monotone (n07aParameterGrading_monotone S)
      (weighted_scalarCommonHeightGrading_monotone S))
    (n07aOriginalForwardCLM_smoothTame hS hT h01) hnegative)
  intro z _
  have hn (v : S.Source) : (-ContinuousLinearMap.id ℝ S.Source) v = -v := by
    simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply]
  exact (congrArg (fun v : S.Source => n07aOriginalForwardCLM hS hT h01 z.1 z.2 + v)
    (hn (n07aReturnCorrectionCLM hS h02 h03 z.1 z.2))).trans
    ((sub_eq_add_neg _ _).symm.trans
      (n07aCorrectedForwardCLM_apply hS hT h01 h02 h03 z.1 z.2).symm)

end ContinuousFlexibility.Analysis
