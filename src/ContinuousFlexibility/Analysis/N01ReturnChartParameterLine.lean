import ContinuousFlexibility.Analysis.N01FlowParameterLineRegularity
import ContinuousFlexibility.Analysis.ScalarParameterInverse
import ContinuousFlexibility.Analysis.ReturnCorrectionDisplacementRegularity

/-!
# Actual return charts on arbitrary sector parameter lines

The prescribed inverse charts are jointly smooth in the line parameter
and the angular variable. This follows from the original N01 flow towers,
the actual inverse identities, and positivity of the angular derivatives.
The same conclusion applies to the correction initial map and residual.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

local instance n01ReturnChartParameterLineStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff

theorem stateLeftChart_sectorLine_formula (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (x w : StateDirections S × ℝ) (t : ℝ)
    (m : ℕ) (θ : ℝ) :
    stateLeftChart S (liftSectorParameter S C (x + t • w)).1 m θ =
      stateLeftChart S (liftSectorParameter S C x).1 m θ +
        t * (S.circle (3 / 4 : ℝ)).decode w.1.val.2.2.2 m θ := by
  change θ + (S.circle (3 / 4 : ℝ)).decode
      (C.referenceState.2.2.2 + (x.1.val.2.2.2 + t • w.1.val.2.2.2)) m θ =
    (θ + (S.circle (3 / 4 : ℝ)).decode
      (C.referenceState.2.2.2 + x.1.val.2.2.2) m θ) +
      t * (S.circle (3 / 4 : ℝ)).decode w.1.val.2.2.2 m θ
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem stateLeftChart_sectorLine_contDiff
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (hS : IsPhysicalSpaces D T S)
    (m : ℕ) (x w : StateDirections S × ℝ) :
    ContDiff ℝ ∞ (fun p : PolarPoint =>
      stateLeftChart S (liftSectorParameter S C (x + p.1 • w)).1 m p.2) := by
  have hf := stateLeftChart_contDiff S (liftSectorParameter S C x) m
    (hS.2.1 (3 / 4 : ℝ))
  have hg : ContDiff ℝ ∞ ((S.circle (3 / 4 : ℝ)).decode w.1.val.2.2.2 m) :=
    (((hS.2.1 (3 / 4 : ℝ)).2.2.2.1 w.1.val.2.2.2).1 m).1
  have h := (hf.comp contDiff_snd).add (contDiff_fst.mul (hg.comp contDiff_snd))
  apply contDiff_iff_contDiffAt.mpr
  intro p
  apply h.contDiffAt.congr_of_eventuallyEq
  exact Eventually.of_forall fun q => by
    simpa only [Pi.add_apply, Pi.mul_apply, Function.comp_def] using
      stateLeftChart_sectorLine_formula S C x w q.1 m q.2

section ActualLine

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)

include hN hS hT

theorem N01Properties.transportedLeftChart_sectorLine_contDiffOn
    (m : ℕ) (x w : StateDirections S × ℝ) :
    ContDiffOn ℝ ∞ (fun p : PolarPoint =>
      stateLeftChart S (liftSectorParameter S C (x + p.1 • w)).1 m
        (C.minusReturnInverse (liftSectorParameter S C (x + p.1 • w)) m p.2) -
          C.travel m)
      (((fun t : ℝ => x + t • w) ⁻¹' sectorNeighborhood S base ε ε) ×ˢ univ) := by
  have hi := (hN.minusReturnInverse_sectorLine_contDiffOn hS hT m x w).mono
    (show (((fun t : ℝ => x + t • w) ⁻¹' sectorNeighborhood S base ε ε) ×ˢ univ) ⊆
      {p : PolarPoint | x + p.1 • w ∈ sectorNeighborhood S base ε ε} from fun _ hp => hp.1)
  have h := (scalarParameter_comp_contDiffOn
    (stateLeftChart_sectorLine_contDiff C hS m x w).contDiffOn hi).sub contDiffOn_const
  apply h.congr
  intro p _
  rfl

theorem N01Properties.rightChartCandidate_sectorLine_contDiffOn
    (m : ℕ) (x w : StateDirections S × ℝ) :
    ContDiffOn ℝ ∞ (fun p : PolarPoint =>
      rightChartCandidate S C (liftSectorParameter S C (x + p.1 • w)) m p.2)
      (((fun t : ℝ => x + t • w) ⁻¹' sectorNeighborhood S base ε ε) ×ˢ univ) := by
  have hf := hN.transportedLeftChart_sectorLine_contDiffOn hS hT m x w
  have hn := scalarParameter_comp_contDiffOn hf (contDiffOn_snd.neg)
  apply ((hf.sub hn).div_const 2).congr
  intro p _
  simp only [rightChartCandidate, oddPart, Pi.sub_apply, Pi.div_apply,
    Pi.neg_apply, Function.comp_def]

theorem N01Properties.rightChartInverse_sectorLine_contDiffOn
    (m : ℕ) (x w : StateDirections S × ℝ) :
    ContDiffOn ℝ ∞ (fun p : PolarPoint =>
      C.rightChartInverse (liftSectorParameter S C (x + p.1 • w)) m p.2)
      (((fun t : ℝ => x + t • w) ⁻¹' sectorNeighborhood S base ε ε) ×ˢ univ) := by
  apply scalarParameterInverse_contDiffOn
    ((sectorNeighborhood_isOpen S base ε ε).preimage
      (continuous_const.add (continuous_id.smul continuous_const)))
    (hN.rightChartCandidate_sectorLine_contDiffOn hS hT m x w)
  · intro t ht θ
    exact N01Properties.rightChart_deriv_pos S C _ m hN
      (liftSectorParameter_mem_stateNeighborhood ht (le_refl ε))
      (hN.2.2.1.liftSectorParameter_sector _) θ
  · intro t ht θ
    exact (N01Properties.return_inverse_and_positive S C _ m hN
      (liftSectorParameter_mem_stateNeighborhood ht (le_refl ε))
      (hN.2.2.1.liftSectorParameter_sector _) θ).2.2.1

theorem N01Properties.rightChartInverse_sectorLine_hasDerivAt
    (m : ℕ) (x w : StateDirections S × ℝ) {t : ℝ}
    (ht : x + t • w ∈ sectorNeighborhood S base ε ε) (θ : ℝ) :
    HasDerivAt
      (fun s => C.rightChartInverse (liftSectorParameter S C (x + s • w)) m θ)
      (-deriv (fun s => rightChartCandidate S C (liftSectorParameter S C (x + s • w)) m
          (C.rightChartInverse (liftSectorParameter S C (x + t • w)) m θ)) t /
        deriv (rightChartCandidate S C (liftSectorParameter S C (x + t • w)) m)
          (C.rightChartInverse (liftSectorParameter S C (x + t • w)) m θ)) t := by
  apply scalarParameterInverse_hasDerivAt
    ((sectorNeighborhood_isOpen S base ε ε).preimage
      (continuous_const.add (continuous_id.smul continuous_const)))
    (hN.rightChartCandidate_sectorLine_contDiffOn hS hT m x w)
    (fun s hs y => N01Properties.rightChart_deriv_pos S C _ m hN
      (liftSectorParameter_mem_stateNeighborhood hs (le_refl ε))
      (hN.2.2.1.liftSectorParameter_sector _) y)
    (fun s hs y => (N01Properties.return_inverse_and_positive S C _ m hN
      (liftSectorParameter_mem_stateNeighborhood hs (le_refl ε))
      (hN.2.2.1.liftSectorParameter_sector _) y).2.2.1) ht θ

theorem N01Properties.returnTransportInverse_sectorLine_contDiffOn
    (m : ℕ) (x w : StateDirections S × ℝ) :
    ContDiffOn ℝ ∞ (fun p : PolarPoint =>
      C.minusReturnInverse (liftSectorParameter S C (x + p.1 • w)) m
        (C.rightChartInverse (liftSectorParameter S C (x + p.1 • w)) m p.2))
      (((fun t : ℝ => x + t • w) ⁻¹' sectorNeighborhood S base ε ε) ×ˢ univ) := by
  exact scalarParameter_comp_contDiffOn
    ((hN.minusReturnInverse_sectorLine_contDiffOn hS hT m x w).mono (fun _ hp => hp.1))
    (hN.rightChartInverse_sectorLine_contDiffOn hS hT m x w)

theorem N01Properties.returnCorrectionInitialMap_sectorLine_contDiffOn
    (m : ℕ) (x w : StateDirections S × ℝ) :
    ContDiffOn ℝ ∞ (fun p : PolarPoint =>
      returnCorrectionInitialMap S C (liftSectorParameter S C (x + p.1 • w)) m p.2)
      (((fun t : ℝ => x + t • w) ⁻¹' sectorNeighborhood S base ε ε) ×ˢ univ) := by
  have hg := hN.returnTransportInverse_sectorLine_contDiffOn hS hT m x w
  have hy := (stateLeftChart_sectorLine_contDiff C hS m x w).contDiffOn.sub
    (contDiffOn_const (c := C.travel m))
  apply (scalarParameter_comp_contDiffOn hg hy).congr
  intro p _
  rfl

theorem N01Properties.returnResidualField_sectorLine_contDiffOn
    (m : ℕ) (x w : StateDirections S × ℝ) :
    ContDiffOn ℝ ∞ (fun p : PolarPoint =>
      returnResidualField S C (liftSectorParameter S C (x + p.1 • w)) m p.2)
      (((fun t : ℝ => x + t • w) ⁻¹' sectorNeighborhood S base ε ε) ×ˢ univ) := by
  have hf := hN.transportedLeftChart_sectorLine_contDiffOn hS hT m x w
  have hn := scalarParameter_comp_contDiffOn hf contDiffOn_snd.neg
  have he := (hf.add hn).div_const 2
  have h := scalarParameter_comp_contDiffOn he
    (hN.rightChartInverse_sectorLine_contDiffOn hS hT m x w)
  apply h.congr
  intro p _
  simp only [returnResidualField, evenPart, Pi.add_apply, Pi.div_apply,
    Pi.neg_apply, Function.comp_def]

end ActualLine

end ContinuousFlexibility.Statements
