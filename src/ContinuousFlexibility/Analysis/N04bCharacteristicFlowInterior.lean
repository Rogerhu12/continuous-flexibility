module

public import ContinuousFlexibility.Analysis.N04bCharacteristicFlowClosed
public import ContinuousFlexibility.Analysis.OneHighCircleFlowInterior
public import ContinuousFlexibility.Analysis.OneHighCircleFlowLocalization

/-!
# Interior joint smoothness of the same actual characteristic flow

On a compact interior radial interval, a smooth clamp extends the scalar
speed. The stored flow is rebased using its actual inverse at that interval's
left endpoint. The existing circle-flow theorem gives joint smoothness of
the rebased flow, and composition with the proved smooth angular slice gives
joint smoothness of the original stored flow. No extension of the stored
flow and no forward joint-regularity hypothesis are introduced.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

theorem n04b_scalarFlow_contDiffAt
    {F Φ : PolarPoint → ℝ} {a b P : ℝ}
    (hF : N04bScalarFieldRegularity F a b P)
    (hinit : ∀ θ, Φ (a, θ) = θ)
    (htrajectory : ∀ θ, ContinuousOn (fun r => Φ (r, θ)) (Icc a b))
    (hode : ∀ θ r, r ∈ Ioo a b →
      HasDerivAt (fun s => Φ (s, θ)) (F (r, Φ (r, θ))) r)
    {p : PolarPoint} (hp : p.1 ∈ Ioo a b) : ContDiffAt ℝ ∞ Φ p := by
  let δ := min (p.1 - a) (b - p.1) / 4
  let c := p.1 - δ
  let e := p.1 + δ
  have hδ : 0 < δ :=
    div_pos (lt_min (sub_pos.mpr hp.1) (sub_pos.mpr hp.2)) (by norm_num)
  have hδa : 4 * δ ≤ p.1 - a := by
    dsimp only [δ]
    linarith [min_le_left (p.1 - a) (b - p.1)]
  have hδb : 4 * δ ≤ b - p.1 := by
    dsimp only [δ]
    linarith [min_le_right (p.1 - a) (b - p.1)]
  have hce : c < e := by dsimp only [c, e]; linarith
  have hc : c ∈ Icc a b := by
    dsimp only [c]
    constructor <;> linarith
  have hclosed : Icc c e ⊆ Icc a b := by
    intro r hr
    dsimp only [c, e] at hr
    constructor <;> linarith [hr.1, hr.2]
  have hopen : Ioo c e ⊆ Ioo a b := by
    intro r hr
    dsimp only [c, e] at hr
    constructor <;> linarith [hr.1, hr.2]
  have hmargin : Ioo (c - δ) (e + δ) ⊆ Ioo a b := by
    intro r hr
    dsimp only [c, e] at hr
    constructor <;> linarith [hr.1, hr.2]
  let G := circleFlowLocalizedSpeed F hce.le hδ
  have hG : ContDiff ℝ ∞ G := contDiff_circleFlowLocalizedSpeed hce.le hδ
    (hF.smooth.mono (fun q hq => ⟨hmargin hq.1, hq.2⟩))
  have hGperiod : ∀ r, Function.Periodic (fun θ => G (r, θ)) P :=
    circleFlowLocalizedSpeed_periodic hce.le hδ
      (fun r hr => hF.periodic r (Ioo_subset_Icc_self (hmargin hr)))
  have hΦc : ContDiff ℝ ∞ (fun θ => Φ (c, θ)) :=
    n04b_scalarFlow_angular_smooth hF hinit htrajectory hode hc
  have hmono : StrictMono (fun θ => Φ (c, θ)) :=
    strictMono_of_deriv_pos
      (n04b_scalarFlow_angular_deriv_pos hF hinit htrajectory hode hc)
  have hsurj : Function.Surjective (fun θ => Φ (c, θ)) :=
    surjective_of_continuous_periodic_lift hF.period_ne_zero hΦc.continuous
      ((n04b_scalarFlow_continuous_periodic hF hinit htrajectory hode).2 c hc)
  let ι := Function.invFun (fun θ => Φ (c, θ))
  let Ψ : PolarPoint → ℝ := fun q => Φ (q.1, ι q.2)
  have hΨinit (θ : ℝ) : Ψ (c, θ) = θ := Function.rightInverse_invFun hsurj θ
  have hΨtrajectory (θ : ℝ) :
      ContinuousOn (fun r => Ψ (r, θ)) (Icc c e) :=
    (htrajectory (ι θ)).mono hclosed
  have hΨode (r : ℝ) (hr : r ∈ Ioo c e) (θ : ℝ) :
      HasDerivAt (fun s => Ψ (s, θ)) (G (r, Ψ (r, θ))) r := by
    have heq : G (r, Ψ (r, θ)) = F (r, Ψ (r, θ)) :=
      circleFlowLocalizedSpeed_eq hce.le hδ (Ioo_subset_Icc_self hr) _
    exact (hode (ι θ) r (hopen hr)).congr_deriv heq.symm
  have hpce : p.1 ∈ Ioo c e := by
    dsimp only [c, e]
    constructor <;> linarith
  have hΨs : ContDiffAt ℝ ∞ Ψ (p.1, Φ (c, p.2)) :=
    circleFlow_contDiffAt hG hF.period_pos hGperiod hΨtrajectory hΨinit hΨode hpce
  have harg : ContDiffAt ℝ ∞ (fun q : PolarPoint => (q.1, Φ (c, q.2))) p :=
    contDiffAt_fst.prodMk (hΦc.contDiffAt.comp p contDiffAt_snd)
  have hs := hΨs.comp p harg
  have heq : (fun q : PolarPoint => Ψ (q.1, Φ (c, q.2))) = Φ := by
    funext q
    exact congrArg (fun θ => Φ (q.1, θ))
      (Function.leftInverse_invFun hmono.injective q.2)
  change ContDiffAt ℝ ∞ (fun q : PolarPoint => Ψ (q.1, Φ (c, q.2))) p at hs
  rw [heq] at hs
  exact hs

/-- All forward regularity used by the actual-first-integral construction
follows from the raw scalar field and the stored trajectory specification. -/
theorem n04bCircleFlowRegularity_of_actual_ode
    {F Φ : PolarPoint → ℝ} {a b P : ℝ}
    (hF : N04bScalarFieldRegularity F a b P)
    (hinit : ∀ θ, Φ (a, θ) = θ)
    (htrajectory : ∀ θ, ContinuousOn (fun r => Φ (r, θ)) (Icc a b))
    (hode : ∀ θ r, r ∈ Ioo a b →
      HasDerivAt (fun s => Φ (s, θ)) (F (r, Φ (r, θ))) r) :
    N04bCircleFlowRegularity Φ a b P := by
  have hc := n04b_scalarFlow_continuous_periodic hF hinit htrajectory hode
  refine ⟨hc.1, ?_, ?_, hc.2⟩
  · intro p hp
    exact (n04b_scalarFlow_contDiffAt hF hinit htrajectory hode hp.1).contDiffWithinAt
  · intro r hr θ
    exact n04b_scalarFlow_angular_deriv_pos hF hinit htrajectory hode hr θ

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

/-- The flow is the very same N03 witness. Its joint regularity is derived
from a raw scalar-field certificate, not inserted into the upstream statement. -/
theorem N03Properties.minusFlow_regularity_of_scalarField
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S} {L : ReturnCorrectionData S}
    {base : ℕ} {ε : ℝ}
    (hN03 : N03Properties D T S C R L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (m : ℕ)
    (hF : N04bScalarFieldRegularity (minusCharacteristicSpeed (L.coefficients z))
      (C.left m) (C.right m) Real.pi) :
    N04bCircleFlowRegularity (fun p : PolarPoint => L.minusFlow z m p.1 p.2)
      (C.left m) (C.right m) Real.pi := by
  have hflow := hN03.2.2.2.2.1 z hz hsector m
  exact n04bCircleFlowRegularity_of_actual_ode hF
    (fun θ => (hflow θ).1) (fun θ => (hflow θ).2.1)
    (fun θ r hr => (hflow θ).2.2.1 r hr)

end ContinuousFlexibility.Statements
