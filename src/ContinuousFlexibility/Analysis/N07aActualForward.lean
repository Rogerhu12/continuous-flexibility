import ContinuousFlexibility.Analysis.N07aCorrectedForward
import ContinuousFlexibility.Analysis.N07aNuSource
import ContinuousFlexibility.Analysis.N07aNormalizedForward
import ContinuousFlexibility.Analysis.N07aNeighborhood

/-!
# The actual normalized physical forward family

All fields in this construction come from the original N01/N02/N03 data.
Only the low-order parameter neighborhood is reduced. The forward family
has the prescribed corrected divergence and distinguished scalar column,
with values in the true physical Source space.
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

theorem n07a_exists_actualNormalizedForward
    (hD : IsRadialReference D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h02 : N02Properties D T S C R base ε)
    (h03 : N03Properties D T S C R L base ε) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      ∃ F : (StateDirections S × ℝ) → N07aNormalizedUnknown hD hT hS →L[ℝ] S.Source,
        SmoothTameOn (n07aParameterNormalizedGrading hD hT hS) S.sourceGrading
          (sectorNeighborhood S base' ε' ε' ×ˢ univ)
          (fun z : (StateDirections S × ℝ) × N07aNormalizedUnknown hD hT hS =>
            F z.1 z.2) ∧
        (∀ z ∈ sectorNeighborhood S base' ε' ε',
          ∀ u : N07aNormalizedUnknown hD hT hS, ∀ p ∈ annularOpen D,
            (S.height (3 / 4 : ℝ)).decode (F z u).val p =
              divergenceOperator (L.coefficients (liftSectorParameter S C z))
                (heightPairField S u.val.1) p +
                u.val.2 * nuColumnField D S C (liftSectorParameter S C z) p) := by
  let data := n07a_exists_nuSource hS hT h01
  let base' : ℕ := data.choose
  have hbase : base ≤ base' := data.choose_spec.1
  let ε' : ℝ := data.choose_spec.2.choose
  have he : 0 < ε' := data.choose_spec.2.choose_spec.1
  have hele : ε' ≤ ε := data.choose_spec.2.choose_spec.2.1
  let N : (StateDirections S × ℝ) → S.Source := data.choose_spec.2.choose_spec.2.2.choose
  have hN : SmoothTameOn (n07aParameterGrading S) S.sourceGrading
      (sectorNeighborhood S base' ε' ε') N := data.choose_spec.2.choose_spec.2.2.choose_spec.1
  have hNdecode := data.choose_spec.2.choose_spec.2.2.choose_spec.2
  let F₀ := n07aCorrectedForwardCLM hS hT h01 h02 h03
  let F := n07aNormalizedForwardCLM hD hT hS F₀ N
  have hsub := n07a_sectorNeighborhood_mono (S := S) hbase hele
  have hF₀ := smoothTameOn_mono (n07aCorrectedForwardCLM_smoothTame hS hT h01 h02 h03)
    ((n07a_sectorNeighborhood_isOpen S base' ε' ε').prod isOpen_univ)
    (Set.prod_mono hsub (subset_refl univ))
  refine ⟨base', hbase, ε', he, hele, F,
    n07aNormalizedForwardCLM_smoothTame hD hT hS
      (n07a_sectorNeighborhood_isOpen S base' ε' ε') F₀ N hF₀ hN, ?_⟩
  intro z hz u p hp
  simp only [F, n07aNormalizedForwardCLM_apply, Submodule.coe_add,
    Submodule.coe_smul, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [show (S.height (3 / 4 : ℝ)).decode (F₀ z u.val.1).val p =
      divergenceOperator (L.coefficients (liftSectorParameter S C z))
        (heightPairField S u.val.1) p from
      n07aCorrectedForwardCLM_decode hS hT h01 h02 h03 (hsub hz) u.val.1 hp,
    hNdecode z hz p]

end ContinuousFlexibility.Analysis
