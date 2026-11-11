import ContinuousFlexibility.Analysis.N04bCharacteristicFirstIntegrals
import ContinuousFlexibility.Analysis.ScalarFlowSmoothness
import ContinuousFlexibility.Analysis.ScalarFlowParameterContinuity
import ContinuousFlexibility.Analysis.PeriodicScalarFlow

/-!
# Closed-component regularity of a stored actual characteristic flow

The field hypotheses concern only the scalar speed and its angular jets.
The stored flow is assumed continuous along each individual trajectory and
to solve the ODE in the open interval. FTC supplies both endpoint derivatives;
Gronwall then proves joint continuity, and uniqueness proves its period.
The actual variational formula proves a strictly positive angular derivative.
No joint regularity of the stored flow is an input.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped Topology ContDiff NNReal

set_option backward.isDefEq.respectTransparency false

/-- Raw scalar-field regularity, allowing a radial square root at either
endpoint. `angular` concerns only derivatives in the angular variable. -/
structure N04bScalarFieldRegularity (F : PolarPoint → ℝ) (a b P : ℝ) : Prop where
  ordered : a < b
  period_pos : 0 < P
  smooth : ContDiffOn ℝ ∞ F (Ioo a b ×ˢ univ)
  angular : ∀ n : ℕ, AngularRegular n
    (fun r θ => closedStripExtend ordered.le F (r, θ))
  periodic : ∀ r ∈ Icc a b, Function.Periodic (fun θ => F (r, θ)) P

/-- The actual derivative of the angular slice. At a turning radius this
does not require the full planar derivative of the speed to exist. -/
def n04bFieldAngularDerivative (F : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  deriv (fun θ => F (p.1, θ)) p.2

namespace N04bScalarFieldRegularity

variable {F : PolarPoint → ℝ} {a b P : ℝ}
  (hF : N04bScalarFieldRegularity F a b P)

include hF

theorem period_ne_zero : P ≠ 0 := hF.period_pos.ne'

theorem continuous : ContinuousOn F (Icc a b ×ˢ univ) := by
  apply (hF.angular 0).continuous.continuousOn.congr
  intro p hp
  exact (closedStripExtend_eq hF.ordered.le F hp.1).symm

theorem angular_smooth {r : ℝ} (hr : r ∈ Icc a b) :
    ContDiff ℝ ∞ (fun θ => F (r, θ)) := by
  have h := contDiff_of_angularRegular_all hF.angular r
  have he : (fun θ => closedStripExtend hF.ordered.le F (r, θ)) =
      (fun θ => F (r, θ)) := by
    funext θ
    exact closedStripExtend_eq hF.ordered.le F hr
  rw [he] at h
  exact h

theorem angular_hasDerivAt {r : ℝ} (hr : r ∈ Icc a b) (θ : ℝ) :
    HasDerivAt (fun η => F (r, η)) (n04bFieldAngularDerivative F (r, θ)) θ :=
  ((hF.angular_smooth hr).differentiable (by simp) θ).hasDerivAt

theorem angular_derivative_continuous :
    ContinuousOn (n04bFieldAngularDerivative F) (Icc a b ×ˢ univ) := by
  apply (hF.angular 1).2.2.continuous.continuousOn.congr
  intro p hp
  simp only [n04bFieldAngularDerivative, closedStripExtend,
    projIcc_of_mem hF.ordered.le hp.1]

theorem angular_derivative_regular (n : ℕ) :
    AngularRegular n (fun r θ =>
      closedStripExtend hF.ordered.le (n04bFieldAngularDerivative F) (r, θ)) :=
  (hF.angular (n + 1)).2.2

theorem angular_derivative_periodic {r : ℝ} (hr : r ∈ Icc a b) :
    Function.Periodic (fun θ => n04bFieldAngularDerivative F (r, θ)) P := by
  intro θ
  let v : ℝ → ℝ := fun η => F (r, η)
  have he : (fun η => v (η + P)) = v := funext (hF.periodic r hr)
  change deriv v (θ + P) = deriv v θ
  rw [← deriv_comp_add_const v P θ, he]

/-- Compactness of one angular period gives a uniform Lipschitz constant. -/
theorem exists_angular_lipschitz :
    ∃ K : ℝ≥0, ∀ r ∈ Icc a b, LipschitzWith K (fun θ => F (r, θ)) := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_bound_periodic_compact isCompact_Icc
    hF.period_ne_zero hF.angular_derivative_continuous
    (fun _ hr => hF.angular_derivative_periodic hr)
  refine ⟨⟨K, hK0⟩, fun r hr => ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro θ η
  simpa only [dist_eq_norm, NNReal.coe_mk] using
    (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x _ => (hF.angular_hasDerivAt hr x).hasDerivWithinAt)
      (fun x _ => hK r hr x) (mem_univ η) (mem_univ θ)

end N04bScalarFieldRegularity

/-- FTC supplies the actual derivative within the full closed interval,
at both endpoints as well as in the interior. -/
theorem n04b_hasDerivWithinAt_Icc_of_interior
    {a b : ℝ} {f d : ℝ → ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hd : ContinuousOn d (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt f (d t) t)
    {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt f (d t) (Icc a b) t := by
  let de : ℝ → ℝ := IccExtend hab.le ((Icc a b).domRestrict d)
  have hde : Continuous de := hd.domRestrict.Icc_extend'
  have heq : EqOn de d (Icc a b) := by
    intro r hr
    exact IccExtend_of_mem hab.le _ hr
  have hprimitive (r : ℝ) (hr : r ∈ Icc a b) :
      f r = f a + ∫ s in a..r, de s := by
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f' := de) hr.1
      (hf.mono (Icc_subset_Icc le_rfl hr.2))
      (fun s hs => by
        have hs' : s ∈ Ioo a b := ⟨hs.1, hs.2.trans_le hr.2⟩
        simpa only [heq ⟨hs'.1.le, hs'.2.le⟩] using hderiv s hs')
      (hde.intervalIntegrable a r)
    linarith only [hFTC]
  have hFTC : HasDerivAt (fun r => f a + ∫ s in a..r, de s) (d t) t := by
    have h := (intervalIntegral.integral_hasDerivAt_right (hde.intervalIntegrable a t)
      hde.aestronglyMeasurable.stronglyMeasurableAtFilter hde.continuousAt).const_add (f a)
    exact (h.congr_deriv (heq ht)).congr_of_eventuallyEq
      (Eventually.of_forall fun r => by simp only [Pi.add_apply])
  apply hFTC.hasDerivWithinAt.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact hprimitive r hr
  · exact hprimitive t ht

/-- A raw continuous scalar field supplies the missing endpoint ODE for
every actual stored trajectory. -/
theorem n04b_scalarFlow_hasDerivWithinAt
    {F Φ : PolarPoint → ℝ} {a b P : ℝ}
    (hF : N04bScalarFieldRegularity F a b P)
    (htrajectory : ∀ θ, ContinuousOn (fun r => Φ (r, θ)) (Icc a b))
    (hode : ∀ θ r, r ∈ Ioo a b →
      HasDerivAt (fun s => Φ (s, θ)) (F (r, Φ (r, θ))) r)
    (θ : ℝ) {r : ℝ} (hr : r ∈ Icc a b) :
    HasDerivWithinAt (fun s => Φ (s, θ)) (F (r, Φ (r, θ))) (Icc a b) r :=
  n04b_hasDerivWithinAt_Icc_of_interior hF.ordered (htrajectory θ)
    (hF.continuous.comp (continuousOn_id.prodMk (htrajectory θ))
      (fun t ht => ⟨ht, mem_univ _⟩)) (hode θ) hr

/-- Gronwall proves joint continuity of the stored family; uniqueness gives
its angular period. Neither is an assumption on that family. -/
theorem n04b_scalarFlow_continuous_periodic
    {F Φ : PolarPoint → ℝ} {a b P : ℝ}
    (hF : N04bScalarFieldRegularity F a b P)
    (hinit : ∀ θ, Φ (a, θ) = θ)
    (htrajectory : ∀ θ, ContinuousOn (fun r => Φ (r, θ)) (Icc a b))
    (hode : ∀ θ r, r ∈ Ioo a b →
      HasDerivAt (fun s => Φ (s, θ)) (F (r, Φ (r, θ))) r) :
    ContinuousOn Φ (Icc a b ×ˢ univ) ∧
      ∀ r ∈ Icc a b, ∀ θ, Φ (r, θ + P) = Φ (r, θ) + P := by
  obtain ⟨K, hK⟩ := hF.exists_angular_lipschitz
  have hderiv (θ r : ℝ) (hr : r ∈ Icc a b) :
      HasDerivWithinAt (fun s => Φ (s, θ)) (F (r, Φ (r, θ))) (Icc a b) r :=
    n04b_scalarFlow_hasDerivWithinAt hF htrajectory hode θ hr
  have hLift : ∀ r ∈ Ico a b,
      LipschitzOnWith K (fun q : ℝ × ℝ => F (r, q.2)) (univ ×ˢ univ) := by
    intro r hr
    simpa only [mul_one] using
      ((hK r ⟨hr.1, hr.2.le⟩).comp
        (LipschitzWith.prod_snd : LipschitzWith 1 (@Prod.snd ℝ ℝ))).lipschitzOnWith
  have hswap : ContinuousOn (fun q : ℝ × ℝ => Φ (q.2, q.1)) (univ ×ˢ Icc a b) :=
    continuousOn_scalarFlow_parameters_time
      (F := fun (_ : ℝ) r θ => F (r, θ))
      (u := fun θ r => Φ (r, θ)) (v := id)
      hLift (fun θ _ r hr => hderiv θ r hr) (fun θ _ => hinit θ)
      LipschitzWith.id.lipschitzOnWith
  refine ⟨hswap.comp (continuous_snd.prodMk continuous_fst).continuousOn
    (fun p hp => ⟨mem_univ _, hp.1⟩), ?_⟩
  intro r hr θ
  exact scalarFlow_period_add hK hF.periodic hinit hderiv θ hr

/-- The positive angular derivative is the exponential of the integral
of the actual angular derivative of the raw speed. -/
theorem n04b_scalarFlow_hasDerivAt_angle
    {F Φ : PolarPoint → ℝ} {a b P : ℝ}
    (hF : N04bScalarFieldRegularity F a b P)
    (hinit : ∀ θ, Φ (a, θ) = θ)
    (htrajectory : ∀ θ, ContinuousOn (fun r => Φ (r, θ)) (Icc a b))
    (hode : ∀ θ r, r ∈ Ioo a b →
      HasDerivAt (fun s => Φ (s, θ)) (F (r, Φ (r, θ))) r)
    {r : ℝ} (hr : r ∈ Icc a b) (θ : ℝ) :
    HasDerivAt (fun η => Φ (r, η))
      (Real.exp (∫ s in a..r, n04bFieldAngularDerivative F (s, Φ (s, θ)))) θ :=
  scalar_flow_hasDerivAt_exp_integral_on hF.ordered hF.angular_derivative_continuous
    (fun _ hs η => hF.angular_hasDerivAt hs η)
    (n04b_scalarFlow_continuous_periodic hF hinit htrajectory hode).1 hinit hode hr θ

theorem n04b_scalarFlow_angular_deriv_pos
    {F Φ : PolarPoint → ℝ} {a b P : ℝ}
    (hF : N04bScalarFieldRegularity F a b P)
    (hinit : ∀ θ, Φ (a, θ) = θ)
    (htrajectory : ∀ θ, ContinuousOn (fun r => Φ (r, θ)) (Icc a b))
    (hode : ∀ θ r, r ∈ Ioo a b →
      HasDerivAt (fun s => Φ (s, θ)) (F (r, Φ (r, θ))) r)
    {r : ℝ} (hr : r ∈ Icc a b) (θ : ℝ) :
    0 < deriv (fun η => Φ (r, η)) θ := by
  rw [(n04b_scalarFlow_hasDerivAt_angle hF hinit htrajectory hode hr θ).deriv]
  exact Real.exp_pos _

theorem n04b_scalarFlow_angular_deriv_continuous
    {F Φ : PolarPoint → ℝ} {a b P : ℝ}
    (hF : N04bScalarFieldRegularity F a b P)
    (hinit : ∀ θ, Φ (a, θ) = θ)
    (htrajectory : ∀ θ, ContinuousOn (fun r => Φ (r, θ)) (Icc a b))
    (hode : ∀ θ r, r ∈ Ioo a b →
      HasDerivAt (fun s => Φ (s, θ)) (F (r, Φ (r, θ))) r) :
    ContinuousOn (fun p : PolarPoint => deriv (fun θ => Φ (p.1, θ)) p.2)
      (Icc a b ×ˢ univ) :=
  scalar_flow_angular_deriv_continuousOn hF.ordered hF.angular_derivative_continuous
    (fun _ hr θ => hF.angular_hasDerivAt hr θ)
    (n04b_scalarFlow_continuous_periodic hF hinit htrajectory hode).1 hinit hode

/-- Every closed radial slice of the actual flow is smooth in its initial angle. -/
theorem n04b_scalarFlow_angular_smooth
    {F Φ : PolarPoint → ℝ} {a b P : ℝ}
    (hF : N04bScalarFieldRegularity F a b P)
    (hinit : ∀ θ, Φ (a, θ) = θ)
    (htrajectory : ∀ θ, ContinuousOn (fun r => Φ (r, θ)) (Icc a b))
    (hode : ∀ θ r, r ∈ Ioo a b →
      HasDerivAt (fun s => Φ (s, θ)) (F (r, Φ (r, θ))) r)
    {r : ℝ} (hr : r ∈ Icc a b) :
    ContDiff ℝ ∞ (fun θ => Φ (r, θ)) :=
  scalar_flow_angular_contDiff_of_angularRegular hF.ordered
    hF.angular_derivative_regular (fun _ hs θ => hF.angular_hasDerivAt hs θ)
    (n04b_scalarFlow_continuous_periodic hF hinit htrajectory hode).1 hinit hode hr

end ContinuousFlexibility.Analysis
