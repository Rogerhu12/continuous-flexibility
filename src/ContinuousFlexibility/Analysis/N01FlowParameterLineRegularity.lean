import ContinuousFlexibility.Analysis.N01EndpointAngularJets
import ContinuousFlexibility.Analysis.SmoothDirectionsAngularLine
import ContinuousFlexibility.Analysis.SmoothDirectionsMixedScalarLine
import ContinuousFlexibility.Analysis.ReturnFlowInverseRegularity

/-!
# Actual N01 flow and inverse along every sector parameter line

The original closed-radius parameter towers, including their angular
derivative identities, give joint smoothness in a genuine parameter
line and angle. The triangular inverse function theorem applies to the
actual fiberwise invFun. The specified endpoint inverse agrees with
that inverse on the entire admissible line domain.

No regularity of the inverse family is assumed.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

local instance n01FlowParameterLineRegularityStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff

section ActualLine

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)

include hN hS hT

theorem N01Properties.minusFlow_sectorLine_contDiffOn
    (m : ℕ) (r : ℝ) (hr : r ∈ Icc (C.left m) (C.right m))
    (x w : StateDirections S × ℝ) :
    ContDiffOn ℝ ∞
      (fun p : PolarPoint => C.minusFlow (liftSectorParameter S C (x + p.1 • w)) m r p.2)
      {p : PolarPoint | x + p.1 • w ∈ sectorNeighborhood S base ε ε} := by
  have hdiff := angularTower_affineLine_contDiffOn
    (hN.sectorFlow_closed_angularTower hS hT m r hr)
    (sectorNeighborhood_isOpen S base ε ε)
    (hN.sectorFlow_closed_angularTower_joint_continuous hS hT m r hr)
    (hN.sectorFlow_closed_angularTower_hasDerivAt hS hT m r hr) x w 0
  have href : ContDiff ℝ ∞ (C.minusFlow (C.referenceState, 0) m r) :=
    hN.minusFlow_angular_contDiff hS hT hN.reference_mem_stateNeighborhood
      hN.2.2.1.stateSector m hr
  apply (hdiff.add ((href.comp contDiff_snd).contDiffOn)).congr
  intro p _
  simp only [ordinaryFlowFamily, mixedDerivative, iteratedDeriv_zero]
  ring

theorem N01Properties.minusFlow_sectorLine_hasDerivAt
    (m : ℕ) (r : ℝ) (hr : r ∈ Icc (C.left m) (C.right m))
    (x w : StateDirections S × ℝ) {t : ℝ}
    (ht : x + t • w ∈ sectorNeighborhood S base ε ε) (θ : ℝ) :
    HasDerivAt
      (fun s => C.minusFlow (liftSectorParameter S C (x + s • w)) m r θ)
      ((hN.sectorFlow_closed_angularTower hS hT m r hr 0 θ).D 1
        (x + t • w) (fun _ => w)) t := by
  have hd := (hN.sectorFlow_closed_angularTower hS hT m r hr 0 θ).hasDerivAt_line x w ht
  apply (hd.add_const (C.minusFlow (C.referenceState, 0) m r θ)).congr_of_eventuallyEq
  exact Eventually.of_forall fun s => by
    simp only [ordinaryFlowFamily, mixedDerivative, iteratedDeriv_zero]
    ring

theorem N01Properties.minusFlow_invFun_sectorLine_contDiffOn
    (m : ℕ) (r : ℝ) (hr : r ∈ Icc (C.left m) (C.right m))
    (x w : StateDirections S × ℝ) :
    ContDiffOn ℝ ∞
      (fun p : PolarPoint =>
        Function.invFun (C.minusFlow (liftSectorParameter S C (x + p.1 • w)) m r) p.2)
      {p : PolarPoint | x + p.1 • w ∈ sectorNeighborhood S base ε ε} := by
  let V : Set PolarPoint := {p | x + p.1 • w ∈ sectorNeighborhood S base ε ε}
  let F (t : ℝ) : ℝ → ℝ := C.minusFlow (liftSectorParameter S C (x + t • w)) m r
  have hV : IsOpen V :=
    (sectorNeighborhood_isOpen S base ε ε).preimage
      (continuous_const.add (continuous_fst.smul continuous_const))
  have hF : ContDiffOn ℝ ∞ (fun p : PolarPoint => F p.1 p.2) V :=
    hN.minusFlow_sectorLine_contDiffOn hS hT m r hr x w
  have hflow : ordinaryFlowConditions D S C (stateNeighborhood S C base ε) :=
    hN.2.2.2.2.2.2.1
  have hpos (t : ℝ) (ht : x + t • w ∈ sectorNeighborhood S base ε ε) (θ : ℝ) :
      0 < deriv (F t) θ :=
    ((hflow _ (liftSectorParameter_mem_stateNeighborhood ht (le_refl ε)) m θ).2.2.2 r hr).1
  intro p hp
  have hz := liftSectorParameter_mem_stateNeighborhood hp (le_refl ε)
  have hsurj : Function.Surjective (F p.1) :=
    returnLift_surjective Real.pi_pos
      (N01Properties.minusFlow_differentiable S C _ m hN hz hr).continuous
      (hN.minusFlow_add_period hz m hr)
  let α : ℝ := Function.invFun (F p.1) p.2
  have hpoint : (p.1, F p.1 α) = p :=
    Prod.ext rfl (Function.rightInverse_invFun hsurj p.2)
  have hinj : ∀ᶠ t in 𝓝 p.1, Function.Injective (F t) := by
    have hmem : ∀ᶠ t in 𝓝 p.1, x + t • w ∈ sectorNeighborhood S base ε ε :=
      (continuous_const.add (continuous_id.smul continuous_const)).continuousAt.eventually
        ((sectorNeighborhood_isOpen S base ε ε).mem_nhds hp)
    filter_upwards [hmem] with t ht
    exact (strictMono_of_deriv_pos (hpos t ht)).injective
  have hs : ContDiffAt ℝ ∞
      (fun q : PolarPoint => Function.invFun (F q.1) q.2) (p.1, F p.1 α) :=
    returnFlow_invFun_contDiffAt
      (hF.contDiffAt (hV.mem_nhds (show (p.1, α) ∈ V from hp)))
      (by simp) (hpos p.1 hp α).ne' hinj
  rw [hpoint] at hs
  exact hs.contDiffWithinAt

theorem N01Properties.minusReturnInverse_sectorLine_contDiffOn
    (m : ℕ) (x w : StateDirections S × ℝ) :
    ContDiffOn ℝ ∞
      (fun p : PolarPoint =>
        C.minusReturnInverse (liftSectorParameter S C (x + p.1 • w)) m p.2)
      {p : PolarPoint | x + p.1 • w ∈ sectorNeighborhood S base ε ε} := by
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  have hr : C.right m ∈ Icc (C.left m) (C.right m) :=
    ⟨(hC.1 m).2.1.le, le_rfl⟩
  apply (hN.minusFlow_invFun_sectorLine_contDiffOn hS hT m (C.right m) hr x w).congr
  intro p hp
  let z := liftSectorParameter S C (x + p.1 • w)
  have hz : z ∈ stateNeighborhood S C base ε :=
    liftSectorParameter_mem_stateNeighborhood hp (le_refl ε)
  have hs : stateSector S z.1 := hN.2.2.1.liftSectorParameter_sector _
  have hflow : ordinaryFlowConditions D S C (stateNeighborhood S C base ε) :=
    hN.2.2.2.2.2.2.1
  have hinj : Function.Injective (C.minusFlow z m (C.right m)) :=
    (strictMono_of_deriv_pos (fun θ => ((hflow z hz m θ).2.2.2 (C.right m) hr).1)).injective
  have heq := Function.leftInverse_invFun hinj (C.minusReturnInverse z m p.2)
  rw [(N01Properties.return_inverse_and_positive S C z m hN hz hs p.2).1] at heq
  exact heq.symm

end ActualLine

end ContinuousFlexibility.Statements

