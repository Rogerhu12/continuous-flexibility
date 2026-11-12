import ContinuousFlexibility.Analysis.N04bSingletonType
import ContinuousFlexibility.Analysis.N01OrdinaryFlowLoss
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.Abel

/-!
# Strict radial profile type on the full N01 neighborhood

Every affine state line through the reference state is a logarithmic
profile perturbation. Its first radial flow jet is therefore an affine
optical square root. The N01 directional tower prevents this radicand
from crossing zero anywhere in the original state neighborhood.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology ContDiff

local instance n04bStateProfileTypeStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul
local instance n04bStateProfileTypeRealNormedSpace : NormedSpace ℝ ℝ :=
  NormedField.toNormedSpace

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

def n04bStateLogExponent (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (v : AnnularState S) (r : ℝ) : ℝ :=
  v.2.1 * D.chi r + stateControlSum C v r

private theorem n04b_stateType_zero_add_smul {E : Type*}
    [AddCommGroup E] [Module ℝ E] (x₀ v : E) (h₀ : x₀ = 0) (t : ℝ) :
    x₀ + t • v = t • v := by
  rw [h₀, zero_add]

private theorem n04b_stateType_mean_smul
    (u : CircleSpace S) (m : ℕ) (t : ℝ) :
    angularMean ((S.circle (3 / 4 : ℝ)).decode (t • u) m) =
      t * angularMean ((S.circle (3 / 4 : ℝ)).decode u m) := by
  have hd : (S.circle (3 / 4 : ℝ)).decode (t • u) m =
      fun θ => t * (S.circle (3 / 4 : ℝ)).decode u m θ :=
    congrFun ((S.circle (3 / 4 : ℝ)).decode.map_smul t u) m
  have hm (f : ℝ → ℝ) :
      angularMean (fun θ => t * f θ) = t * angularMean f := by
    unfold angularMean
    rw [intervalIntegral.integral_const_mul]
    ring
  exact (congrArg angularMean hd).trans (hm _)

private theorem n04b_stateType_seminorm_affine {E : Type*}
    [AddCommGroup E] [Module ℝ E] (p : Seminorm ℝ E) (x v : E) (t : ℝ) :
    p ((x + t • v) - x) = |t| * p v := by
  rw [add_sub_cancel_left, map_smul_eq_mul, Real.norm_eq_abs]

private theorem n04b_stateType_affine_zero {E : Type*}
    [AddCommGroup E] [Module ℝ E] (x v : E) :
    x + (0 : ℝ) • v = x := by
  rw [zero_smul, add_zero]

theorem n04b_stateKappa_reference_line
    (href : referenceStateConditions D S C)
    (v : AnnularState S) (t : ℝ) (m : ℕ) :
    stateKappa S (C.referenceState + t • v) m = t * stateKappa S v m := by
  have hcoord : (C.referenceState + t • v).2.2.1 = t • v.2.2.1 := by
    change C.referenceState.2.2.1 + t • v.2.2.1 = t • v.2.2.1
    exact n04b_stateType_zero_add_smul _ _ href.2.2.2.1 t
  unfold stateKappa
  exact (congrArg
    (fun u : CircleSpace S => angularMean ((S.circle (3 / 4 : ℝ)).decode u m))
      hcoord).trans (n04b_stateType_mean_smul v.2.2.1 m t)

theorem n04b_stateProfile_reference_line
    (href : referenceStateConditions D S C) (v : AnnularState S) (t : ℝ) :
    stateProfile D S C (C.referenceState + t • v) =
      opticalLogPerturbation D.w (n04bStateLogExponent D S C v) t := by
  funext r
  have hnu : (C.referenceState + t • v).2.1 = t * v.2.1 := by
    change C.referenceState.2.1 + t • v.2.1 = _
    rw [href.2.2.1, zero_add, smul_eq_mul]
  have hsum : (∑' m, stateKappa S (C.referenceState + t • v) m * C.control m r) =
      t * stateControlSum C v r := by
    simp only [n04b_stateKappa_reference_line href, mul_assoc,
      tsum_mul_left, stateControlSum]
  simp only [stateProfile, hnu, hsum, opticalLogPerturbation,
    n04bStateLogExponent]
  congr 2
  ring

theorem N01Properties.n04b_stateLogExponent_contDiffAt
    (hN : N01Properties D T S C base loss ε)
    (v : AnnularState S) {r : ℝ} (hr : r ∈ Ioo D.a D.b) :
    ContDiffAt ℝ ∞ (n04bStateLogExponent D S C v) r := by
  have hborder : RadialTrueBorder D := hN.1.2.2.2.1
  exact (contDiffAt_const.mul hborder.1.contDiffAt).add
    ((contDiffOn_stateControlSum hN.2.2.2.1 v).contDiffAt
      (isOpen_Ioo.mem_nhds hr))

theorem n04b_state_reference_line_mem
    (v : AnnularState S) {t : ℝ} (hε : 0 < ε)
    (ht : |t| * stateGrading S base v < ε) :
    (C.referenceState + t • v, (0 : ℝ)) ∈ stateNeighborhood S C base ε := by
  constructor
  · exact lt_of_eq_of_lt
      (n04b_stateType_seminorm_affine (stateGrading S base) C.referenceState v t) ht
  · simpa only [abs_zero] using hε

private theorem n04b_state_joint_line (v : AnnularState S) (t : ℝ) :
    (C.referenceState, (0 : ℝ)) + t • (v, (0 : ℝ)) =
      (C.referenceState + t • v, (0 : ℝ)) := by
  change (C.referenceState + t • v, (0 : ℝ) + t • (0 : ℝ)) = _
  simp only [smul_zero, add_zero]

private theorem n04b_stateType_reference_profile
    (href : referenceStateConditions D S C) (v : AnnularState S) :
    stateProfile D S C C.referenceState = D.w := by
  have hprofile := n04b_stateProfile_reference_line href v 0
  have hzero := n04b_stateType_affine_zero C.referenceState v
  have hperturbation : opticalLogPerturbation D.w (n04bStateLogExponent D S C v) 0 =
      D.w := by
    funext r
    simp only [opticalLogPerturbation, zero_mul, Real.exp_zero, mul_one]
  exact (congrArg (stateProfile D S C) hzero).symm.trans
    (hprofile.trans hperturbation)

private theorem n04b_stateType_opticalSpeed_affine
    (hN : N01Properties D T S C base loss ε) (v : AnnularState S) (m : ℕ)
    {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) (t : ℝ) :
    opticalSpeed (opticalLogPerturbation D.w (n04bStateLogExponent D S C v) t) r =
      Real.sqrt (-deriv D.w r / (r * D.w r) +
        (-deriv (n04bStateLogExponent D S C v) r / r) * t) := by
  obtain ⟨_, hgeom⟩ := hN.1.1
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  have hrD : r ∈ Ioo D.a D.b :=
    ⟨(hcontrol.1 m).1.trans hr.1, hr.2.trans (hcontrol.1 m).2.2⟩
  exact n04b_opticalSpeed_logPerturbation_affine
    (hgeom.1.2.2.1.1.differentiable (by simp) r)
    ((hN.n04b_stateLogExponent_contDiffAt v hrD).differentiableAt (by simp))
    (hgeom.1.1.trans hrD.1).ne' (hgeom.1.2.2.2.2.1 r hrD).ne'

theorem N01Properties.n04b_ordinaryFlowFamily_stateLine_radial
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (v : AnnularState S) (m : ℕ) (θ : ℝ) {r t : ℝ}
    (hr : r ∈ Ioo (C.left m) (C.right m))
    (ht : (C.referenceState + t • v, (0 : ℝ)) ∈ stateNeighborhood S C base ε) :
    ordinaryFlowFamily S C m 1 0 (r, θ) (C.referenceState + t • v, 0) =
      opticalSpeed D.w r -
        Real.sqrt (-deriv D.w r / (r * D.w r) +
          (-deriv (n04bStateLogExponent D S C v) r / r) * t) := by
  have href := n04b_stateType_reference_profile hN.2.2.1 v
  have hprofile := n04b_stateProfile_reference_line hN.2.2.1 v t
  exact (hN.n04b_ordinaryFlowFamily_radial_zero hS hT ht m θ hr).trans
    (congrArg₂ (fun a b : ℝ => a - b)
      (congrArg (fun w : ℝ → ℝ => opticalSpeed w r) href)
      ((congrArg (fun w : ℝ → ℝ => opticalSpeed w r) hprofile).trans
        (n04b_stateType_opticalSpeed_affine hN v m hr t)))

theorem N01Properties.n04b_sqrt_stateLine_differentiableAt
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (v : AnnularState S) (m : ℕ) {r t : ℝ}
    (hr : r ∈ Ioo (C.left m) (C.right m))
    (ht : |t| * stateGrading S base v < ε) :
    DifferentiableAt ℝ (fun s : ℝ => Real.sqrt
      (-deriv D.w r / (r * D.w r) +
        (-deriv (n04bStateLogExponent D S C v) r / r) * s)) t := by
  obtain ⟨B, hB, htower⟩ := hN.ordinaryFlowFamily_bound 0 1
  obtain ⟨J, hJ⟩ := htower m 1 0 (r, 0) (by norm_num) hr
  have hmem : (C.referenceState, (0 : ℝ)) + t • (v, (0 : ℝ)) ∈
      stateNeighborhood S C base ε := by
    rw [n04b_state_joint_line]
    exact n04b_state_reference_line_mem v hN.2.1 ht
  have hdiff := J.n04b_differentiableAt_line (C.referenceState, 0) (v, 0) hmem
  have hnear : ∀ᶠ s in 𝓝 t, |s| * stateGrading S base v < ε :=
    (isOpen_lt (continuous_abs.mul continuous_const) continuous_const).mem_nhds ht
  have heq : (fun s : ℝ => Real.sqrt
      (-deriv D.w r / (r * D.w r) +
        (-deriv (n04bStateLogExponent D S C v) r / r) * s))
      =ᶠ[𝓝 t] (fun s : ℝ => opticalSpeed D.w r -
        ordinaryFlowFamily S C m 1 0 (r, 0)
          ((C.referenceState, 0) + s • (v, (0 : ℝ)))) := by
    filter_upwards [hnear] with s hs
    rw [n04b_state_joint_line,
      hN.n04b_ordinaryFlowFamily_stateLine_radial hS hT v m 0 hr
        (n04b_state_reference_line_mem v hN.2.1 hs)]
    ring
  exact ((hdiff.hasDerivAt.const_sub (opticalSpeed D.w r)).congr_of_eventuallyEq
    heq).differentiableAt

theorem N01Properties.n04b_stateLine_radicand_pos
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (v : AnnularState S) (m : ℕ) {r t : ℝ}
    (hr : r ∈ Ioo (C.left m) (C.right m))
    (ht : |t| * stateGrading S base v < ε) :
    0 < -deriv D.w r / (r * D.w r) +
      (-deriv (n04bStateLogExponent D S C v) r / r) * t := by
  obtain ⟨_, hgeom⟩ := hN.1.1
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  have hrD : r ∈ Ioo D.a D.b :=
    ⟨(hcontrol.1 m).1.trans hr.1, hr.2.trans (hcontrol.1 m).2.2⟩
  have hbase : 0 < -deriv D.w r / (r * D.w r) :=
    div_pos (neg_pos.mpr (hcontrol.2.2.2.1 m r hr))
      (mul_pos (hgeom.1.1.trans hrD.1) (hgeom.1.2.2.2.2.1 r hrD))
  exact Analysis.n04b_affine_pos_of_sqrt_differentiableAt_weighted_ball
    hbase (apply_nonneg (stateGrading S base) _)
    (fun s hs => hN.n04b_sqrt_stateLine_differentiableAt hS hT v m hr hs) ht

/-- The controlled profile retains the strict reference sign on every
negative component throughout the original N01 neighborhood. -/
theorem N01Properties.n04b_stateProfile_deriv_neg
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {x : AnnularState S} (hx : stateGrading S base (x - C.referenceState) < ε)
    (m : ℕ) {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) :
    deriv (stateProfile D S C x) r < 0 := by
  let v : AnnularState S := x - C.referenceState
  have hline : C.referenceState + (1 : ℝ) • v = x := by
    dsimp only [v]
    rw [one_smul]
    abel
  have ht : |(1 : ℝ)| * stateGrading S base v < ε := by
    simpa only [abs_one, one_mul, v] using hx
  have hpositive := hN.n04b_stateLine_radicand_pos hS hT v m hr ht
  obtain ⟨_, hgeom⟩ := hN.1.1
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  have hrD : r ∈ Ioo D.a D.b :=
    ⟨(hcontrol.1 m).1.trans hr.1, hr.2.trans (hcontrol.1 m).2.2⟩
  have hrpos : 0 < r := hgeom.1.1.trans hrD.1
  have hwpos : 0 < D.w r := hgeom.1.2.2.2.2.1 r hrD
  have hprofile : stateProfile D S C x =
      opticalLogPerturbation D.w (n04bStateLogExponent D S C v) 1 := by
    simpa only [hline] using n04b_stateProfile_reference_line hN.2.2.1 v 1
  have hspeed : 0 < opticalSpeed (stateProfile D S C x) r := by
    rw [hprofile, n04b_opticalSpeed_logPerturbation_affine
      (hgeom.1.2.2.1.1.differentiable (by simp) r)
      ((hN.n04b_stateLogExponent_contDiffAt v hrD).differentiableAt (by simp))
      hrpos.ne' hwpos.ne']
    exact Real.sqrt_pos.mpr hpositive
  have hrad : 0 < -deriv (stateProfile D S C x) r / (r * stateProfile D S C x r) :=
    Real.sqrt_pos.mp hspeed
  have hprofilepos : 0 < stateProfile D S C x r :=
    mul_pos hwpos (Real.exp_pos _)
  have hnum := (lt_div_iff₀ (mul_pos hrpos hprofilepos)).mp hrad
  simpa only [zero_mul, neg_pos] using hnum


/-- At zero residual parameter, the actual original field is strictly
hyperbolic at every interior point of every negative component. -/
theorem N01Properties.n04b_originalCoefficients_zero_negative_type
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {x : AnnularState S} (hx : stateGrading S base (x - C.referenceState) < ε)
    (m : ℕ) {p : PolarPoint} (hp : p.1 ∈ Ioo (C.left m) (C.right m)) :
    0 < (originalCoefficients D S C (x, 0)).a p ∧
      (originalCoefficients D S C (x, 0)).b p = 0 ∧
      (originalCoefficients D S C (x, 0)).c p < 0 ∧
      0 < (originalCoefficients D S C (x, 0)).b p ^ 2 -
        (originalCoefficients D S C (x, 0)).a p *
          (originalCoefficients D S C (x, 0)).c p := by
  obtain ⟨_, hgeom⟩ := hN.1.1
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  have hpD : p.1 ∈ Ioo D.a D.b :=
    ⟨(hcontrol.1 m).1.trans hp.1, hp.2.trans (hcontrol.1 m).2.2⟩
  have hrpos : 0 < p.1 := hgeom.1.1.trans hpD.1
  have hwpos : 0 < stateProfile D S C x p.1 :=
    mul_pos (hgeom.1.2.2.2.2.1 p.1 hpD) (Real.exp_pos _)
  have hdneg := hN.n04b_stateProfile_deriv_neg hS hT hx m hp
  have hcneg : deriv (stateProfile D S C x) p.1 / p.1 < 0 :=
    div_neg_of_neg_of_pos hdneg hrpos
  obtain ⟨ha, hb, hc⟩ := originalCoefficients_radial_zero x
    (contDiff_stateProfile_of_n01 hS hT hN x) p
  refine ⟨ha.symm ▸ hwpos, hb, hc.symm ▸ hcneg, ?_⟩
  rw [ha, hb, hc]
  simp only [zero_pow (by decide : 2 ≠ 0), zero_sub]
  exact neg_pos.mpr (mul_neg_of_pos_of_neg hwpos hcneg)

end ContinuousFlexibility.Statements
