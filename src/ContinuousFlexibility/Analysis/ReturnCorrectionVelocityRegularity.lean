import ContinuousFlexibility.Analysis.ReturnCorrectionDisplacementRegularity
import ContinuousFlexibility.Analysis.N01FlowAngularJointRegularity

/-!
# Joint regularity of the actual correction velocity

The interpolation inverse is smooth by the inverse-coordinate theorem.
The actual inverse flow and the first angular variation are C¹, so the
frozen velocity correction is C¹ for every independent circle residual.
All regularity premises on the forward and inverse charts have been
discharged using N01 and the physical-space realizations.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

section ActualVelocity

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN01 : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S z.1) (χ : ℕ → ℝ → ℝ) (m : ℕ)
  (hχ : ContDiff ℝ ∞ (χ m))
  (hχrange : ∀ r ∈ Icc (C.left m) (C.right m), χ m r ∈ Icc (0 : ℝ) 1)

include hN01 hS hT hz hsector hχ hχrange

theorem N01Properties.returnInterpolation_invFun_contDiffAt
    (p : PolarPoint) (hp : p.1 ∈ Ioo (C.left m) (C.right m)) :
    ContDiffAt ℝ ∞ (fun q : PolarPoint =>
      Function.invFun (returnInterpolation (χ m q.1) (returnCorrectionInitialMap S C z m)) q.2) p := by
  let K := returnCorrectionInitialMap S C z m
  let J : ℝ → ℝ → ℝ := fun r => returnInterpolation (χ m r) K
  have hK : ContDiff ℝ ∞ K := hN01.returnCorrectionInitialMap_contDiff hS hT hz hsector m
  have hJ : ContDiff ℝ ∞ (fun q : PolarPoint => J q.1 q.2) :=
    hN01.returnInterpolation_joint_contDiff hS hT hz hsector m χ hχ
  have hJlift := returnInterpolation_periodic_lift
    (hN01.returnCorrectionInitialMap_add_period hz hsector m) (χ m p.1)
  have hJcont : Continuous (J p.1) :=
    hJ.continuous.comp (continuous_const.prodMk continuous_id)
  have hsurj : Function.Surjective (J p.1) :=
    returnLift_surjective Real.pi_pos hJcont hJlift
  let α := Function.invFun (J p.1) p.2
  have hpoint : (p.1, J p.1 α) = p := by
    apply Prod.ext
    · rfl
    · exact Function.rightInverse_invFun hsurj p.2
  have hχp := hχrange p.1 ⟨hp.1.le, hp.2.le⟩
  have hpos : 0 < deriv (J p.1) α := by
    rw [(returnInterpolation_hasDerivAt (χ := χ m p.1)
      ((hK.differentiable (by simp) α).hasDerivAt)).deriv]
    exact returnInterpolation_deriv_pos hχp.1 hχp.2
      (hN01.returnCorrectionInitialMap_deriv_pos hz hsector m α)
  have hinj : ∀ᶠ r in 𝓝 p.1, Function.Injective (J r) := by
    filter_upwards [Ioo_mem_nhds hp.1 hp.2] with r hr
    have hχr := hχrange r ⟨hr.1.le, hr.2.le⟩
    exact (returnInterpolation_strictMono hχr.1 hχr.2
      (hN01.returnCorrectionInitialMap_strictMono hz hsector m)).injective
  have h := returnFlow_invFun_contDiffAt (F := J)
    (hJ.contDiffAt (x := (p.1, α))) (by simp) hpos.ne' hinj
  rw [hpoint] at h
  exact h

theorem N01Properties.returnCorrectionVelocityLinear_contDiffAt_one
    (ρ : CircleSpace S) (p : PolarPoint) (hp : p.1 ∈ Ioo (C.left m) (C.right m)) :
    ContDiffAt ℝ 1 (fun q : PolarPoint => returnCorrectionVelocityLinear D S C χ z m q ρ) p := by
  let A : PolarPoint → ℝ := fun q => Function.invFun (C.minusFlow z m q.1) q.2
  let B : PolarPoint → ℝ := fun q =>
    Function.invFun (returnInterpolation (χ m q.1) (returnCorrectionInitialMap S C z m)) (A q)
  have hA : ContDiffAt ℝ 1 A p :=
    hN01.minusFlow_invFun_contDiffAt_one hS hT hz hsector m p hp
  have hB : ContDiffAt ℝ 1 B p := by
    have ho : ContDiffAt ℝ 1 (fun q : PolarPoint =>
        Function.invFun (returnInterpolation (χ m q.1)
          (returnCorrectionInitialMap S C z m)) q.2) (p.1, A p) :=
      (hN01.returnInterpolation_invFun_contDiffAt hS hT hz hsector χ m hχ hχrange
        (p.1, A p) hp).of_le (by simp)
    simpa only [B, Function.comp_def] using ho.comp p (contDiffAt_fst.prodMk hA)
  have hvariation : ContDiffAt ℝ 1
      (fun q : PolarPoint => deriv (C.minusFlow z m q.1) (A q)) p := by
    have ho : ContDiffAt ℝ 1 (fun q : PolarPoint => deriv (C.minusFlow z m q.1) q.2)
        (p.1, A p) :=
      hN01.minusFlow_angular_deriv_contDiffAt_one hS hT hz hsector m (p.1, A p) hp
    simpa only [Function.comp_def] using ho.comp p (contDiffAt_fst.prodMk hA)
  have hcutoff : ContDiffAt ℝ 1 (fun q : PolarPoint => deriv (χ m) q.1) p :=
    (((contDiff_infty_iff_deriv.mp hχ).2.comp contDiff_fst).contDiffAt).of_le (by simp)
  have hdisplacement : ContDiffAt ℝ 1
      (fun q : PolarPoint => returnCorrectionDisplacementLinear S C z m (B q) ρ) p :=
    ((hN01.returnCorrectionDisplacementLinear_contDiff hS hT hz hsector m ρ).contDiffAt.of_le
      (by simp)).comp p hB
  exact ((hvariation.mul hcutoff).mul hdisplacement).congr_of_eventuallyEq
    (Eventually.of_forall fun q => by
      simp only [returnCorrectionVelocityLinear, LinearMap.smul_apply, smul_eq_mul,
        Pi.mul_apply, A, B])

theorem N01Properties.returnCorrectionDriftSpeedLinear_contDiffAt_one
    (ρ : CircleSpace S) (p : PolarPoint) (hp : p.1 ∈ Ioo (C.left m) (C.right m)) :
    ContDiffAt ℝ 1 (fun q : PolarPoint => returnCorrectionDriftLinear D S C χ z m q ρ) p ∧
      ContDiffAt ℝ 1 (fun q : PolarPoint => returnCorrectionSpeedLinear D S C χ z m q ρ) p := by
  have hv := hN01.returnCorrectionVelocityLinear_contDiffAt_one hS hT hz hsector
    χ m hχ hχrange ρ p hp
  have href : ContDiffAt ℝ 1 (fun q : PolarPoint => (q.1, -q.2)) p :=
    contDiffAt_fst.prodMk contDiffAt_snd.neg
  have hvr := (hN01.returnCorrectionVelocityLinear_contDiffAt_one hS hT hz hsector
    χ m hχ hχrange ρ (p.1, -p.2) hp).comp p href
  constructor
  · exact ((hv.sub hvr).div_const 2).congr_of_eventuallyEq
      (Eventually.of_forall fun q => by
        simp only [returnCorrectionDriftLinear_apply, Pi.sub_apply, Function.comp_def])
  · exact ((hvr.neg.sub hv).div_const 2).congr_of_eventuallyEq
      (Eventually.of_forall fun q => by
        simp only [returnCorrectionSpeedLinear_apply, Pi.neg_apply, Pi.sub_apply, Function.comp_def])

end ActualVelocity

end ContinuousFlexibility.Statements
