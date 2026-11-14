module

public import ContinuousFlexibility.Statements.Nonlinear
public import ContinuousFlexibility.Analysis.StateNeighborhood
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The angular derivative of the reference ordinary flow

At zero height parameter the actual height is radial.  The actual polar
coefficients, including the corrected angular coefficient, are therefore
independent of angle.  Two angular trajectories have the same radial
derivative, so their difference stays equal to their initial separation on
the closed component.  In particular their angular Jacobian is exactly one.

The total radial derivative identities also cover nondifferentiable radial
profiles, using the standard zero convention for `fderiv` and `deriv`.
Consequently the flow conclusion needs no additional profile hypothesis.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial

set_option backward.isDefEq.respectTransparency false

private theorem not_differentiableAt_radialHeightField
    {h : ℝ → ℝ} {p : PolarPoint} (hh : ¬DifferentiableAt ℝ h p.1) :
    ¬DifferentiableAt ℝ (radialHeightField h) p := by
  intro hf
  have hs : DifferentiableAt ℝ (fun r : ℝ => (r, p.2)) p.1 :=
    differentiableAt_id.prodMk (differentiableAt_const p.2)
  have hc := hf.comp p.1 hs
  exact hh (by simpa only [Function.comp_def, radialHeightField] using hc)

/-- The actual radial partial of a radial lift is the ordinary derivative,
including the standard value zero at a nondifferentiable point. -/
theorem radialPartial_radialHeightField_total (h : ℝ → ℝ) (p : PolarPoint) :
    radialPartial (radialHeightField h) p = deriv h p.1 := by
  by_cases hh : DifferentiableAt ℝ h p.1
  · exact radialPartial_radialHeightField hh
  · simp only [radialPartial,
      fderiv_zero_of_not_differentiableAt (not_differentiableAt_radialHeightField hh),
      zero_apply, deriv_zero_of_not_differentiableAt hh]

/-- Radial lifts have zero angular partial without a regularity assumption. -/
theorem angularPartial_radialHeightField_total (h : ℝ → ℝ) (p : PolarPoint) :
    angularPartial (radialHeightField h) p = 0 := by
  by_cases hh : DifferentiableAt ℝ h p.1
  · exact angularPartial_radialHeightField hh
  · simp only [angularPartial,
      fderiv_zero_of_not_differentiableAt (not_differentiableAt_radialHeightField hh),
      zero_apply]

theorem heightRadial_radialHeightField_total (h : ℝ → ℝ) :
    heightRadial (radialHeightField h) = radialHeightField (deriv h) :=
  funext (radialPartial_radialHeightField_total h)

theorem heightAngular_radialHeightField_total (h : ℝ → ℝ) :
    heightAngular (radialHeightField h) = fun _ => 0 := by
  funext p
  simp only [heightAngular, angularPartial_radialHeightField_total, zero_div]

/-- Every input of the actual polar coefficient formulas is radial. -/
theorem polarCoefficients_radialHeightField_angular_invariant
    (w h : ℝ → ℝ) (r θ ψ : ℝ) :
    polarLinearA w (radialHeightField h) (r, θ) =
        polarLinearA w (radialHeightField h) (r, ψ) ∧
    polarLinearB w (radialHeightField h) (r, θ) =
        polarLinearB w (radialHeightField h) (r, ψ) ∧
    polarCorrectedC w (radialHeightField h) (r, θ) =
        polarCorrectedC w (radialHeightField h) (r, ψ) := by
  have hE : profileEnergy w = radialHeightField (fun r => radialEnergy (w r)) := rfl
  simp only [polarLinearA, polarLinearB, polarCorrectedC, polarScale, polarDiscriminant,
    hE, heightRadial_radialHeightField_total, heightAngular_radialHeightField_total,
    radialPartial_radialHeightField_total, radialPartial_const, angularPartial_const,
    radialHeightField, and_self]

/-- Setting the height parameter to zero makes the original characteristic
speed independent of angle at every state, not just at the reference state. -/
theorem minusCharacteristicSpeed_zeroParameter_angular_invariant
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (x : AnnularState S) (r θ ψ : ℝ) :
    minusCharacteristicSpeed (originalCoefficients D S C (x, 0)) (r, θ) =
      minusCharacteristicSpeed (originalCoefficients D S C (x, 0)) (r, ψ) := by
  have hheight : stateHeight D S C (x, 0) =
      radialHeightField (stateRadialHeight D S C x) := by
    funext p
    simp only [stateHeight, zero_mul, add_zero, radialHeightField]
  obtain ⟨ha, hb, hc⟩ := polarCoefficients_radialHeightField_angular_invariant
    (stateProfile D S C x) (stateRadialHeight D S C x) r θ ψ
  simp only [minusCharacteristicSpeed, originalCoefficients, hheight, ha, hb, hc]

/-- Zero derivative on the open interval and continuity at its ends suffice
to keep the function equal to its left endpoint value. -/
theorem eq_left_of_hasDerivAt_zero_on_open_interval
    {f : ℝ → ℝ} {l u : ℝ} (hc : ContinuousOn f (Icc l u))
    (hd : ∀ r ∈ Ioo l u, HasDerivAt f 0 r) {r : ℝ} (hr : r ∈ Icc l u) :
    f r = f l := by
  rcases lt_or_eq_of_le hr.1 with hlr | hsame
  · obtain ⟨c, hc', heq⟩ := exists_hasDerivAt_eq_slope f (fun _ => 0) hlr
      (hc.mono (Icc_subset_Icc le_rfl hr.2))
      (fun t ht => hd t ⟨ht.1, ht.2.trans_le hr.2⟩)
    exact sub_eq_zero.mp ((div_eq_zero_iff.mp heq.symm).resolve_right (sub_pos.mpr hlr).ne')
  · simp only [hsame]

/-- Angular-independent radial speed preserves the initial angular separation,
including at the endpoints where only continuity is required. -/
theorem flow_eq_zeroAngle_add_of_radial_speed
    {F : ℝ → ℝ → ℝ} {v : ℝ → ℝ} {l u : ℝ}
    (hinit : ∀ θ, F l θ = θ)
    (hcont : ∀ θ, ContinuousOn (fun r => F r θ) (Icc l u))
    (hode : ∀ θ r, r ∈ Ioo l u → HasDerivAt (fun t => F t θ) (v r) r)
    {r : ℝ} (hr : r ∈ Icc l u) (θ : ℝ) :
    F r θ = F r 0 + θ := by
  have hconst : F r θ - F r 0 = F l θ - F l 0 :=
    eq_left_of_hasDerivAt_zero_on_open_interval ((hcont θ).sub (hcont 0))
      (fun t ht => by simpa only [sub_self] using (hode θ t ht).sub (hode 0 t ht)) hr
  rw [hinit θ, hinit 0, sub_zero] at hconst
  linarith

/-- The actual zero-parameter ordinary flow is an angular translation at each
radius in the closed component. -/
theorem ordinaryFlow_zeroParameter_eq_zeroAngle_add
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {U : Set (AnnularState S × ℝ)} (hflow : ordinaryFlowConditions D S C U)
    {x : AnnularState S} (hx : (x, 0) ∈ U) (m : ℕ)
    {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m)) (θ : ℝ) :
    C.minusFlow (x, 0) m r θ = C.minusFlow (x, 0) m r 0 + θ := by
  apply flow_eq_zeroAngle_add_of_radial_speed
    (v := fun t => minusCharacteristicSpeed (originalCoefficients D S C (x, 0)) (t, 0))
    (fun ψ => (hflow (x, 0) hx m ψ).1)
    (fun ψ => (hflow (x, 0) hx m ψ).2.1) ?_ hr θ
  intro ψ t ht
  exact ((hflow (x, 0) hx m ψ).2.2.1 t ht).congr_deriv
    (minusCharacteristicSpeed_zeroParameter_angular_invariant D S C x t
      (C.minusFlow (x, 0) m t ψ) 0)

/-- The angular Jacobian of the actual ordinary flow at zero parameter is one. -/
theorem hasDerivAt_ordinaryFlow_zeroParameter
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {U : Set (AnnularState S × ℝ)} (hflow : ordinaryFlowConditions D S C U)
    {x : AnnularState S} (hx : (x, 0) ∈ U) (m : ℕ)
    {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m)) (θ : ℝ) :
    HasDerivAt (C.minusFlow (x, 0) m r) 1 θ := by
  have heq : C.minusFlow (x, 0) m r = fun ψ => C.minusFlow (x, 0) m r 0 + ψ :=
    funext (ordinaryFlow_zeroParameter_eq_zeroAngle_add hflow hx m hr)
  rw [heq]
  exact (hasDerivAt_id θ).const_add (C.minusFlow (x, 0) m r 0)

/-- At the reference state this supplies the exact base Jacobian used in the
first-variation estimate, on the entire closed negative component. -/
theorem deriv_referenceOrdinaryFlow_eq_one
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {base : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hflow : ordinaryFlowConditions D S C (stateNeighborhood S C base ε))
    (m : ℕ) {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m)) (θ : ℝ) :
    deriv (C.minusFlow (C.referenceState, 0) m r) θ = 1 := by
  have href := reference_mem_stateNeighborhood S C base hε
  exact (hasDerivAt_ordinaryFlow_zeroParameter hflow href m hr θ).deriv

end ContinuousFlexibility.Analysis
