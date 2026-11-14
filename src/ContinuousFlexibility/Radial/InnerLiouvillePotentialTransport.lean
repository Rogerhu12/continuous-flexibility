module

public import ContinuousFlexibility.Radial.InnerLiouvillePhysicalRepresentatives
public import ContinuousFlexibility.Radial.InnerLiouvilleCoefficients
public import ContinuousFlexibility.Radial.InnerRadialPotentialMultiplier

/-!
# The actual signed potential under source and field transport

The physical multiplication operator is constructed in the actual
radial measure. Conjugating it by the field lift and its adjoint gives
the model coefficient -j² rho on the retained interval. Positivity of
the physical weight is derived from the same local profile identity.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff InnerProductSpace

theorem innerLiouville_radial_weight_pos_closed (D : ReferenceData)
    {R s : ℝ → ℝ} {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam)
    (hR : ContDiff ℝ ∞ R)
    (hp : ∀ x ∈ Icc a b, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x)
    (hw : ∀ x ∈ Icc a b, D.w (R x) = lam * s x ^ 2 * deriv R x) :
    ∀ r ∈ Icc (R a) (R b), 0 < D.w r := by
  have hm := (morseCell_strictMonoOn hR (fun x hx => (hp x hx).2.1)).monotoneOn
  rw [← ContinuousOn.image_Icc_of_monotoneOn hab hR.continuous.continuousOn hm]
  rintro _ ⟨x, hx, rfl⟩
  rw [hw x hx]
  exact mul_pos (mul_pos hlam (sq_pos_of_pos (hp x hx).2.2)) (hp x hx).2.1

variable (D : ReferenceData) {R s : ℝ → ℝ} {a b lam : ℝ}
  (hab : a ≤ b) (hlam : 0 < lam) (hR : ContDiff ℝ ∞ R)
  (hs : ContDiff ℝ ∞ s)
  (hp : ∀ x ∈ Icc a b, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x)
  (hcore : Ioo (R a) (R b) ⊆ radialCore D)
  (hw : ∀ x ∈ Icc a b, D.w (R x) = lam * s x ^ 2 * deriv R x)
  (U : ℝ) (hU : 0 ≤ U)
  (hv : ∀ x ∈ Icc a b, |deriv R x / R x| ≤ U)
  (hDw : ContDiff ℝ ∞ D.w) (j : ℝ)
  (hpos : ∀ r ∈ Icc (R a) (R b), 0 < D.w r)

theorem innerLiouvilleSource_potential_field_ae (f : RadialL2) :
    (innerLiouvilleSource D hab hlam hR hs hp hcore hw U hU hv
      (innerRadialPotentialMultiplier D hDw j hpos
        (innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv f)) : ℝ → ℝ) =ᵐ[volume]
      (Ioo a b).indicator (fun x => (-j ^ 2 * liouvilleRho R s x) * f x) := by
  have hpot := innerLiouvilleInterval_pullback_ae D hab hlam hR hs hp hcore hw
    (ae_restrict_of_ae
      (innerRadialPotentialMultiplier_ae D hDw j hpos
        (innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv f)))
  filter_upwards
    [innerLiouvilleSource_ae D hab hlam hR hs hp hcore hw U hU hv
      (innerRadialPotentialMultiplier D hDw j hpos
        (innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv f)),
      ae_imp_of_ae_restrict hpot,
      ae_imp_of_ae_restrict
        (innerLiouvilleFieldLift_pullback_ae D hab hlam hR hs hp hcore hw U hU hv f)]
    with x hsrc hpot' hf
  rw [hsrc]
  by_cases hx : x ∈ Ioo a b
  · have hx' := Ioo_subset_Icc_self hx
    have hm := morseCell_strictMonoOn hR (fun y hy => (hp y hy).2.1)
    have hRx : R x ∈ Ioo (R a) (R b) :=
      ⟨hm (left_mem_Icc.mpr hab) hx' hx.1,
        hm hx' (right_mem_Icc.mpr hab) hx.2⟩
    have hweight : (fun y => D.w (R y)) =ᶠ[𝓝 x]
        (fun y => lam * s y ^ 2 * deriv R y) := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      exact hw y (Ioo_subset_Icc_self hy)
    have hc := innerLiouville_radialPotential_pullback hlam.ne'
      (hR.differentiable (by simp) x) (hs.differentiable (by simp) x)
      ((contDiff_infty_iff_deriv.mp hR).2.differentiable (by simp) x)
      (hDw.differentiable (by simp) (R x)) (hp x hx').1.ne'
      (hp x hx').2.1.ne' (hp x hx').2.2.ne' hweight j
    rw [indicator_of_mem hx, indicator_of_mem hx, hpot' hx,
      innerRadialPotentialCoefficient, indicator_of_mem hRx, hf hx]
    calc
      _ = (12 * (deriv R x / R x) ^ 2 *
          ((j ^ 2 / 12) * (R x * deriv D.w (R x) / D.w (R x)))) * f x := by
        field_simp [(Real.sqrt_pos.mpr hlam).ne', (hp x hx').2.2.ne']
        <;> ring
      _ = _ := by rw [hc]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx]

/-- The potential term can be paired in model L² without any
assumed symmetry of the physical operator. -/
theorem innerLiouvillePotential_pairing (f P : RadialL2) :
    ⟪innerRadialPotentialMultiplier D hDw j hpos
        (innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv f),
      innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv P⟫_ℝ =
      ⟪f, innerLiouvilleSource D hab hlam hR hs hp hcore hw U hU hv
        (innerRadialPotentialMultiplier D hDw j hpos
          (innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv P))⟫_ℝ := by
  have h := ContinuousLinearMap.adjoint_inner_right
    (innerRadialPotentialMultiplier D hDw j hpos)
    (innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv f)
    (innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv P)
  rw [innerRadialPotentialMultiplier_adjoint D hDw j hpos] at h
  calc
    _ = ⟪innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv f,
        innerRadialPotentialMultiplier D hDw j hpos
          (innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv P)⟫_ℝ := h.symm
    _ = _ := by
      rw [real_inner_comm,
        ← innerLiouvilleSource_inner D hab hlam hR hs hp hcore hw U hU hv,
        real_inner_comm]

end ContinuousFlexibility.Radial
