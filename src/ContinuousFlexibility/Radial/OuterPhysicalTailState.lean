module

public import ContinuousFlexibility.Radial.OuterNaturalPhysicalL2
public import ContinuousFlexibility.Radial.OuterFirstOrderState

/-!
# Actual physical states from the logarithmic tail equation

This module transports a smooth logarithmic state, including a growing
Dirichlet state, to the true radial Jacobi equation. The regular entrance
is included: continuity of the actual Jacobi expression extends its
interior identity to that point.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem morsePhysicalDeepTail_lift_contDiffAt
    {M : MorseChainData} {D : ReferenceData} (hD : RadialProfileGeometry D)
    {right : Bool} {j start : ℕ} {entrance η K : ℝ} {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ ∞ u
      (Iio (morsePhysicalDeepTail M D right j start entrance η K).endpoint))
    {x : ℝ} (hx : x < (morsePhysicalDeepTail M D right j start entrance η K).endpoint) :
    ContDiffAt ℝ ∞ (tailPhysicalLift D right j u) (tailPhysicalRadius right x) := by
  have hend : 0 < tailPhysicalEndpoint D right := by
    cases right
    · exact hD.1
    · exact hD.1.trans hD.2.1
  apply contDiffAt_tailPhysicalLift hend.ne' (tailPhysicalRadius_pos right x)
  simpa only [tailPhysicalLog_radius] using hu.contDiffAt (isOpen_Iio.mem_nhds hx)

/-- A smooth logarithmic state yields the actual second-order equation.
No square-integrability condition is imposed on this state. -/
theorem morsePhysicalDeepTail_state_radialJacobi
    {M : MorseChainData} {D : ReferenceData} (hD : RadialProfileGeometry D)
    {right : Bool} {j start : ℕ} {entrance η K : ℝ}
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    {u v : ℝ → ℝ}
    (hu : ContDiffOn ℝ ∞ u
      (Iio (morsePhysicalDeepTail M D right j start entrance η K).endpoint))
    (hsys : TailFirstOrderSystem
      (morsePhysicalDeepTail M D right j start entrance η K).p
      (morsePhysicalDeepTail M D right j start entrance η K).Λ u v
      (Ico (morsePhysicalDeepTail M D right j start entrance η K).entrance
        (morsePhysicalDeepTail M D right j start entrance η K).endpoint))
    {x : ℝ} (hx : x ∈ Ioo
      (morsePhysicalDeepTail M D right j start entrance η K).entrance
      (morsePhysicalDeepTail M D right j start entrance η K).endpoint) :
    radialJacobi ((j : ℝ) ^ 2) D.w (tailPhysicalLift D right j u)
      (tailPhysicalRadius right x) = 0 := by
  let T := morsePhysicalDeepTail M D right j start entrance η K
  let s : ℝ := if right then 1 else -1
  let R := tailPhysicalEndpoint D right
  have hs : s * s = 1 := by cases right <;> norm_num [s]
  have hR : 0 < R := by
    cases right
    · exact hD.1
    · exact hD.1.trans hD.2.1
  have hradius : tailPhysicalRadius right = fun y => exp (s * y) := by
    funext y
    cases right <;> simp [tailPhysicalRadius, s]
  have hp : ∀ y ∈ Ioo T.entrance T.endpoint,
      T.p y = (exp (s * y) / R) ^ (2 * (j : ℝ) ^ 2) *
        D.w (exp (s * y)) / exp (s * y) := by
    intro y _
    simpa only [hradius, R] using
      morsePhysicalDeepTail_density_eq M D right j start entrance η K y
  have hpx : T.p x ≠ 0 := (deepTail_pos hT x ⟨hx.1.le, hx.2⟩).ne'
  have hw₀ : D.w (exp (s * x)) ≠ 0 := by
    intro hz
    have hh := hp x hx
    rw [hz, mul_zero, zero_div] at hh
    exact hpx hh
  have hUV : ∀ y ∈ Ioo T.entrance T.endpoint,
      tailPhysicalLift D right j u (exp (s * y)) =
        (exp (s * y) / R) ^ ((j : ℝ) ^ 2) * u y := by
    intro y _
    simpa only [hradius, R] using tailPhysicalLift_radius D right j u y
  have hsource := radialJacobi_signed_physical_source_at hs hR hx
    (hD.2.2.1.1.differentiable (by simp) (exp (s * x))) hw₀
    ((hu.contDiffAt (isOpen_Iio.mem_nhds hx.2)).of_le (by simp)) hp hUV
  have hequation := tailFirstOrderSystem_equation isOpen_Ioo
    (fun y hy => (deepTail_pos hT y (Ioo_subset_Ico_self hy)).ne')
    (hsys.mono Ioo_subset_Ico_self) x hx
  have heq : deriv (fun y => T.p y * deriv u y) x = -T.Λ * T.p x * u x := by
    linarith only [hequation]
  have hzero : -(T.p x)⁻¹ * deriv (fun y => T.p y * deriv u y) x -
      (j : ℝ) ^ 2 * ((j : ℝ) ^ 2 - 1) * u x = 0 := by
    rw [heq]
    change -(T.p x)⁻¹ * (-((j : ℝ) ^ 2 * ((j : ℝ) ^ 2 - 1)) * T.p x * u x) -
      (j : ℝ) ^ 2 * ((j : ℝ) ^ 2 - 1) * u x = 0
    field_simp [hpx] <;> ring
  rw [hzero, mul_zero] at hsource
  simpa only [hradius] using hsource

/-- The same actual equation holds at the included regular entrance. -/
theorem morsePhysicalDeepTail_state_radialJacobi_Ico
    {M : MorseChainData} {D : ReferenceData} (hD : RadialProfileGeometry D)
    {right : Bool} {j start : ℕ} {entrance η K : ℝ}
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    {u v : ℝ → ℝ}
    (hu : ContDiffOn ℝ ∞ u
      (Iio (morsePhysicalDeepTail M D right j start entrance η K).endpoint))
    (hsys : TailFirstOrderSystem
      (morsePhysicalDeepTail M D right j start entrance η K).p
      (morsePhysicalDeepTail M D right j start entrance η K).Λ u v
      (Ico (morsePhysicalDeepTail M D right j start entrance η K).entrance
        (morsePhysicalDeepTail M D right j start entrance η K).endpoint))
    {x : ℝ} (hx : x ∈ Ico
      (morsePhysicalDeepTail M D right j start entrance η K).entrance
      (morsePhysicalDeepTail M D right j start entrance η K).endpoint) :
    radialJacobi ((j : ℝ) ^ 2) D.w (tailPhysicalLift D right j u)
      (tailPhysicalRadius right x) = 0 := by
  let T := morsePhysicalDeepTail M D right j start entrance η K
  rcases eq_or_lt_of_le hx.1 with hxeq | hxgt
  · subst x
    have hU := morsePhysicalDeepTail_lift_contDiffAt hD hu hT.1
    have hw : ContDiffAt ℝ ∞ D.w (tailPhysicalRadius right T.entrance) :=
      hD.2.2.1.1.contDiffAt
    have hflux : ContDiffAt ℝ ∞
        (fun r => D.w r * deriv (tailPhysicalLift D right j u) r)
        (tailPhysicalRadius right T.entrance) :=
      hw.mul (hU.derivWithin (m := ∞) (by simp))
    have hJ : ContinuousAt
        (radialJacobi ((j : ℝ) ^ 2) D.w (tailPhysicalLift D right j u))
        (tailPhysicalRadius right T.entrance) :=
      (hflux.derivWithin (m := ∞) (by simp)).continuousAt.sub
        (((continuousAt_const.mul (hw.derivWithin (m := ∞) (by simp)).continuousAt).div
          continuousAt_id (tailPhysicalRadius_pos right T.entrance).ne').mul hU.continuousAt)
    have hc := hJ.comp (continuous_tailPhysicalRadius right).continuousAt
    have hz : (fun y => radialJacobi ((j : ℝ) ^ 2) D.w
        (tailPhysicalLift D right j u) (tailPhysicalRadius right y)) =ᶠ[𝓝[>] T.entrance]
        fun _ => 0 := by
      filter_upwards [Ioo_mem_nhdsGT hT.1] with y hy
      exact morsePhysicalDeepTail_state_radialJacobi hD hT hu hsys hy
    exact tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' hz.symm)
  · exact morsePhysicalDeepTail_state_radialJacobi hD hT hu hsys ⟨hxgt, hx.2⟩

/-- The transported state consists of the actual radial value and the
actual scaled flux w u'/λ, with both derivative identities at the entrance. -/
theorem morsePhysicalDeepTail_state_firstOrder_at
    {M : MorseChainData} {D : ReferenceData} (hD : RadialProfileGeometry D)
    {right : Bool} {j start : ℕ} {entrance η K lam : ℝ} (hlam : lam ≠ 0)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start entrance η K))
    {u v : ℝ → ℝ}
    (hu : ContDiffOn ℝ ∞ u
      (Iio (morsePhysicalDeepTail M D right j start entrance η K).endpoint))
    (hsys : TailFirstOrderSystem
      (morsePhysicalDeepTail M D right j start entrance η K).p
      (morsePhysicalDeepTail M D right j start entrance η K).Λ u v
      (Ico (morsePhysicalDeepTail M D right j start entrance η K).entrance
        (morsePhysicalDeepTail M D right j start entrance η K).endpoint))
    {x : ℝ} (hx : x ∈ Ico
      (morsePhysicalDeepTail M D right j start entrance η K).entrance
      (morsePhysicalDeepTail M D right j start entrance η K).endpoint) :
    HasDerivAt (tailPhysicalLift D right j u)
        (lam / D.w (tailPhysicalRadius right x) *
          (tailPhysicalFlux D right j u (tailPhysicalRadius right x) / lam))
        (tailPhysicalRadius right x) ∧
      HasDerivAt (fun r => tailPhysicalFlux D right j u r / lam)
        (((j : ℝ) ^ 2 * deriv D.w (tailPhysicalRadius right x) /
          (lam * tailPhysicalRadius right x)) *
            tailPhysicalLift D right j u (tailPhysicalRadius right x))
        (tailPhysicalRadius right x) := by
  have hU := morsePhysicalDeepTail_lift_contDiffAt hD hu hx.2
  have hw₀ : D.w (tailPhysicalRadius right x) ≠ 0 :=
    (hD.2.2.2.2.1 _ (morsePhysicalDeepTail_radius_mem_core hD hT hx)).ne'
  constructor
  · apply (hU.differentiableAt (by simp)).hasDerivAt.congr_deriv
    unfold tailPhysicalFlux
    field_simp [hw₀, hlam] <;> ring
  · have hd := hasDerivAt_flux_of_radialJacobi_eq_zero
      (hD.2.2.1.1.differentiable (by simp) _)
      ((hU.derivWithin (m := ∞) (by simp)).differentiableAt (by simp))
      (morsePhysicalDeepTail_state_radialJacobi_Ico hD hT hu hsys hx)
    exact (hd.div_const lam).congr_deriv (by ring)

end ContinuousFlexibility.Radial
