import ContinuousFlexibility.Analysis.N01ReturnChartParameterLine
import ContinuousFlexibility.Analysis.ScalarParameterDslope

/-!
# Parameter lines of the actual frozen optical correction

The independent circle residual is allowed to vary on its own affine
line. The frozen displacement, interpolation inverse, and velocity
correction are jointly smooth in the state-line parameter and angle.
All inverse maps and the divided difference are the actual maps in the
correction, including at zero residual. Only the value of the given
cutoff at the selected radius enters the interpolation argument.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

local instance returnCorrectionParameterLineStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff

theorem circleDecode_affineLine_contDiff
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (m : ℕ) (ρ σ : CircleSpace S) :
    ContDiff ℝ ∞ (fun p : PolarPoint =>
      (S.circle (3 / 4 : ℝ)).decode (ρ + p.1 • σ) m p.2) := by
  have hρ : ContDiff ℝ ∞ ((S.circle (3 / 4 : ℝ)).decode ρ m) :=
    (((hS.2.1 (3 / 4 : ℝ)).2.2.2.1 ρ).1 m).1
  have hσ : ContDiff ℝ ∞ ((S.circle (3 / 4 : ℝ)).decode σ m) :=
    (((hS.2.1 (3 / 4 : ℝ)).2.2.2.1 σ).1 m).1
  have h := (hρ.comp contDiff_snd).add (contDiff_fst.mul (hσ.comp contDiff_snd))
  apply contDiff_iff_contDiffAt.mpr
  intro p
  apply h.contDiffAt.congr_of_eventuallyEq
  exact Eventually.of_forall fun q => by
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.mul_apply, Function.comp_def]

section ActualLine

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)

include hN hS hT

theorem N01Properties.returnCorrectionDisplacementLinear_sectorLine_contDiffOn
    (m : ℕ) (x w : StateDirections S × ℝ) (ρ σ : CircleSpace S) :
    ContDiffOn ℝ ∞ (fun p : PolarPoint =>
      returnCorrectionDisplacementLinear S C (liftSectorParameter S C (x + p.1 • w))
        m p.2 (ρ + p.1 • σ))
      (((fun t : ℝ => x + t • w) ⁻¹' sectorNeighborhood S base ε ε) ×ˢ univ) := by
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  have hr : C.right m ∈ Icc (C.left m) (C.right m) :=
    ⟨(hC.1 m).2.1.le, le_rfl⟩
  have hI : IsOpen ((fun t : ℝ => x + t • w) ⁻¹' sectorNeighborhood S base ε ε) :=
    (sectorNeighborhood_isOpen S base ε ε).preimage
      (continuous_const.add (continuous_id.smul continuous_const))
  have hflow := (hN.minusFlow_sectorLine_contDiffOn hS hT m (C.right m) hr x w).mono
    (show (((fun t : ℝ => x + t • w) ⁻¹' sectorNeighborhood S base ε ε) ×ˢ univ) ⊆
      {p : PolarPoint | x + p.1 • w ∈ sectorNeighborhood S base ε ε} from fun _ hp => hp.1)
  have hy := scalarParameter_comp_contDiffOn
    (I := (fun t : ℝ => x + t • w) ⁻¹' sectorNeighborhood S base ε ε)
    (F := fun t θ => rightChartCandidate S C (liftSectorParameter S C (x + t • w)) m θ)
    (G := fun t θ => C.minusFlow (liftSectorParameter S C (x + t • w)) m (C.right m) θ)
    (hN.rightChartCandidate_sectorLine_contDiffOn hS hT m x w) hflow
  have he := scalarParameter_comp_contDiffOn
    (I := (fun t : ℝ => x + t • w) ⁻¹' sectorNeighborhood S base ε ε)
    (F := fun t θ => returnResidualField S C (liftSectorParameter S C (x + t • w)) m θ)
    (G := fun t θ => rightChartCandidate S C (liftSectorParameter S C (x + t • w)) m
      (C.minusFlow (liftSectorParameter S C (x + t • w)) m (C.right m) θ))
    (hN.returnResidualField_sectorLine_contDiffOn hS hT m x w) hy
  have hquot := scalarParameter_dslope_comp_contDiffOn
    (G := fun t θ => C.minusReturnInverse (liftSectorParameter S C (x + t • w)) m
      (C.rightChartInverse (liftSectorParameter S C (x + t • w)) m θ)) hI
    (hN.returnTransportInverse_sectorLine_contDiffOn hS hT m x w) hy he
  have hρ := scalarParameter_comp_contDiffOn
    (I := (fun t : ℝ => x + t • w) ⁻¹' sectorNeighborhood S base ε ε)
    (F := fun t θ => (S.circle (3 / 4 : ℝ)).decode (ρ + t • σ) m θ)
    (G := fun t θ => rightChartCandidate S C (liftSectorParameter S C (x + t • w)) m
      (C.minusFlow (liftSectorParameter S C (x + t • w)) m (C.right m) θ))
    (circleDecode_affineLine_contDiff hS m ρ σ).contDiffOn hy
  apply (hquot.mul hρ).congr
  intro p _
  simp only [returnCorrectionDisplacementLinear_apply, Pi.mul_apply, Function.comp_def]

theorem N01Properties.returnInterpolation_sectorLine_contDiffOn
    (m : ℕ) (c : ℝ) (x w : StateDirections S × ℝ) :
    ContDiffOn ℝ ∞ (fun p : PolarPoint =>
      returnInterpolation c
        (returnCorrectionInitialMap S C (liftSectorParameter S C (x + p.1 • w)) m) p.2)
      (((fun t : ℝ => x + t • w) ⁻¹' sectorNeighborhood S base ε ε) ×ˢ univ) := by
  have hK := hN.returnCorrectionInitialMap_sectorLine_contDiffOn hS hT m x w
  apply (contDiffOn_snd.add (contDiffOn_const.mul (hK.sub contDiffOn_snd))).congr
  intro p _
  rfl

theorem N01Properties.returnInterpolation_invFun_sectorLine_contDiffOn
    (m : ℕ) (c : ℝ) (hc : c ∈ Icc (0 : ℝ) 1) (x w : StateDirections S × ℝ) :
    ContDiffOn ℝ ∞ (fun p : PolarPoint =>
      Function.invFun (returnInterpolation c
        (returnCorrectionInitialMap S C (liftSectorParameter S C (x + p.1 • w)) m)) p.2)
      (((fun t : ℝ => x + t • w) ⁻¹' sectorNeighborhood S base ε ε) ×ˢ univ) := by
  apply scalarParameterInverse_contDiffOn
    (I := (fun t : ℝ => x + t • w) ⁻¹' sectorNeighborhood S base ε ε)
    (F := fun t θ => returnInterpolation c
      (returnCorrectionInitialMap S C (liftSectorParameter S C (x + t • w)) m) θ)
    (G := fun t θ => Function.invFun (returnInterpolation c
      (returnCorrectionInitialMap S C (liftSectorParameter S C (x + t • w)) m)) θ)
    ((sectorNeighborhood_isOpen S base ε ε).preimage
      (show Continuous (fun t : ℝ => x + t • w) from
        continuous_const.add (continuous_id.smul continuous_const)))
    (hN.returnInterpolation_sectorLine_contDiffOn hS hT m c x w)
  · intro t ht θ
    have hz := liftSectorParameter_mem_stateNeighborhood ht (le_refl ε)
    have hs := hN.2.2.1.liftSectorParameter_sector (x + t • w)
    have hK := hN.returnCorrectionInitialMap_contDiff hS hT hz hs m
    rw [(returnInterpolation_hasDerivAt (χ := c)
      ((hK.differentiable (by simp) θ).hasDerivAt)).deriv]
    exact returnInterpolation_deriv_pos hc.1 hc.2
      (hN.returnCorrectionInitialMap_deriv_pos hz hs m θ)
  · intro t ht θ
    have hz := liftSectorParameter_mem_stateNeighborhood ht (le_refl ε)
    have hs := hN.2.2.1.liftSectorParameter_sector (x + t • w)
    have hK := hN.returnCorrectionInitialMap_contDiff hS hT hz hs m
    have hcont : Continuous (returnInterpolation c
        (returnCorrectionInitialMap S C (liftSectorParameter S C (x + t • w)) m)) :=
      continuous_id.add (continuous_const.mul (hK.continuous.sub continuous_id))
    have hsurj := returnLift_surjective Real.pi_pos hcont
      (returnInterpolation_periodic_lift
        (hN.returnCorrectionInitialMap_add_period hz hs m) c)
    exact Function.rightInverse_invFun hsurj θ

theorem N01Properties.returnCorrectionVelocityLinear_sectorLine_contDiffOn
    (χ : ℕ → ℝ → ℝ) (m : ℕ) (r : ℝ)
    (hr : r ∈ Icc (C.left m) (C.right m)) (hχ : χ m r ∈ Icc (0 : ℝ) 1)
    (x w : StateDirections S × ℝ) (ρ σ : CircleSpace S) :
    ContDiffOn ℝ ∞ (fun p : PolarPoint =>
      returnCorrectionVelocityLinear D S C χ (liftSectorParameter S C (x + p.1 • w))
        m (r, p.2) (ρ + p.1 • σ))
      (((fun t : ℝ => x + t • w) ⁻¹' sectorNeighborhood S base ε ε) ×ˢ univ) := by
  have hI : IsOpen ((fun t : ℝ => x + t • w) ⁻¹' sectorNeighborhood S base ε ε) :=
    (sectorNeighborhood_isOpen S base ε ε).preimage
      (continuous_const.add (continuous_id.smul continuous_const))
  have hflow := (hN.minusFlow_sectorLine_contDiffOn hS hT m r hr x w).mono
    (show (((fun t : ℝ => x + t • w) ⁻¹' sectorNeighborhood S base ε ε) ×ˢ univ) ⊆
      {p : PolarPoint | x + p.1 • w ∈ sectorNeighborhood S base ε ε} from fun _ hp => hp.1)
  have hA := (hN.minusFlow_invFun_sectorLine_contDiffOn hS hT m r hr x w).mono
    (show (((fun t : ℝ => x + t • w) ⁻¹' sectorNeighborhood S base ε ε) ×ˢ univ) ⊆
      {p : PolarPoint | x + p.1 • w ∈ sectorNeighborhood S base ε ε} from fun _ hp => hp.1)
  have hB := scalarParameter_comp_contDiffOn
    (I := (fun t : ℝ => x + t • w) ⁻¹' sectorNeighborhood S base ε ε)
    (F := fun t θ => Function.invFun (returnInterpolation (χ m r)
      (returnCorrectionInitialMap S C (liftSectorParameter S C (x + t • w)) m)) θ)
    (G := fun t θ => Function.invFun (C.minusFlow
      (liftSectorParameter S C (x + t • w)) m r) θ)
    (hN.returnInterpolation_invFun_sectorLine_contDiffOn hS hT m (χ m r) hχ x w) hA
  have hvariation := scalarParameter_comp_contDiffOn
    (I := (fun t : ℝ => x + t • w) ⁻¹' sectorNeighborhood S base ε ε)
    (F := fun t θ => deriv (C.minusFlow (liftSectorParameter S C (x + t • w)) m r) θ)
    (G := fun t θ => Function.invFun (C.minusFlow
      (liftSectorParameter S C (x + t • w)) m r) θ)
    (scalarParameterAngularDerivative_contDiffOn
      (F := fun t θ => C.minusFlow (liftSectorParameter S C (x + t • w)) m r θ)
      hI hflow) hA
  have hd := scalarParameter_comp_contDiffOn
    (I := (fun t : ℝ => x + t • w) ⁻¹' sectorNeighborhood S base ε ε)
    (F := fun t θ => returnCorrectionDisplacementLinear S C
      (liftSectorParameter S C (x + t • w)) m θ (ρ + t • σ))
    (G := fun t θ => Function.invFun (returnInterpolation (χ m r)
      (returnCorrectionInitialMap S C (liftSectorParameter S C (x + t • w)) m))
        (Function.invFun (C.minusFlow (liftSectorParameter S C (x + t • w)) m r) θ))
    (hN.returnCorrectionDisplacementLinear_sectorLine_contDiffOn hS hT m x w ρ σ) hB
  apply ((hvariation.mul (contDiffOn_const (c := deriv (χ m) r))).mul hd).congr
  intro p _
  simp only [returnCorrectionVelocityLinear_apply, Pi.mul_apply, Function.comp_def]

theorem N01Properties.returnCorrectionDriftSpeedLinear_sectorLine_contDiffOn
    (χ : ℕ → ℝ → ℝ) (m : ℕ) (r : ℝ)
    (hr : r ∈ Icc (C.left m) (C.right m)) (hχ : χ m r ∈ Icc (0 : ℝ) 1)
    (x w : StateDirections S × ℝ) (ρ σ : CircleSpace S) :
    ContDiffOn ℝ ∞ (fun p : PolarPoint =>
      returnCorrectionDriftLinear D S C χ (liftSectorParameter S C (x + p.1 • w))
        m (r, p.2) (ρ + p.1 • σ))
      (((fun t : ℝ => x + t • w) ⁻¹' sectorNeighborhood S base ε ε) ×ˢ univ) ∧
    ContDiffOn ℝ ∞ (fun p : PolarPoint =>
      returnCorrectionSpeedLinear D S C χ (liftSectorParameter S C (x + p.1 • w))
        m (r, p.2) (ρ + p.1 • σ))
      (((fun t : ℝ => x + t • w) ⁻¹' sectorNeighborhood S base ε ε) ×ˢ univ) := by
  have hv := hN.returnCorrectionVelocityLinear_sectorLine_contDiffOn
    hS hT χ m r hr hχ x w ρ σ
  have hn := scalarParameter_comp_contDiffOn
    (I := (fun t : ℝ => x + t • w) ⁻¹' sectorNeighborhood S base ε ε)
    (F := fun t θ => returnCorrectionVelocityLinear D S C χ
      (liftSectorParameter S C (x + t • w)) m (r, θ) (ρ + t • σ))
    (G := fun _ θ => -θ) hv contDiffOn_snd.neg
  constructor
  · apply ((hv.sub hn).div_const 2).congr
    intro p _
    simp only [returnCorrectionDriftLinear_apply, Pi.sub_apply, Pi.div_apply,
      Pi.neg_apply, Function.comp_def]
  · apply ((hn.neg.sub hv).div_const 2).congr
    intro p _
    simp only [returnCorrectionSpeedLinear_apply, Pi.sub_apply, Pi.div_apply,
      Pi.neg_apply, Function.comp_def]

end ActualLine

end ContinuousFlexibility.Statements
