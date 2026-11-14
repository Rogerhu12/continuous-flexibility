module

public import ContinuousFlexibility.Radial.DeepTailInitialEdge
public import ContinuousFlexibility.Radial.DeepTailJacobiBounds
public import ContinuousFlexibility.Radial.TailActualSolutionNodes

/-!
# Actual initial-edge bounds for classical tail states

The initial Poisson flux matrix controls the actual Dirichlet state.
Its positive off-diagonal coefficient is at least the reciprocal
resistance. All comparisons concern the given state on the original
closed interval, including its two endpoint fluxes.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set MeasureTheory
open ContinuousFlexibility.Statements

/-- A physical Poisson column is a first-order state on the open edge. -/
theorem outer_poisson_column_firstOrder {p : ℝ → ℝ} {a b Λ η : ℝ}
    {hab : a ≤ b} (B : TailPhysicalPoissonData p a b Λ η hab)
    (hpos : ∀ x ∈ Icc a b, 0 < p x) (right : Bool) :
    TailFirstOrderSystem p Λ (B.u right)
      (fun x => p x * deriv (B.u right) x) (Ioo a b) := by
  intro x hx
  constructor
  · apply (B.differentiable right x).hasDerivAt.congr_deriv
    field_simp [(hpos x (Ioo_subset_Icc_self hx)).ne'] <;> ring
  · simpa only [neg_mul] using B.equation right x hx

/-- The initial flux of an actual zero-left-value state is the positive
Poisson coupling times its right endpoint value. -/
theorem outer_poisson_dirichlet_flux {p u v : ℝ → ℝ} {a b Λ η : ℝ}
    (hab : a < b) (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ x ∈ Icc a b, 0 < p x)
    (B : TailPhysicalPoissonData p a b Λ η hab.le)
    (hsys : TailFirstOrderSystem p Λ u v (Icc a b)) (hua : u a = 0) :
    v a = B.offDiagonal * u b := by
  have h := tailFirstOrderSystem_wronskian_const_Icc
    (HasDerivAt.continuousOn (fun x hx => (hsys x hx).1))
    (HasDerivAt.continuousOn (fun x hx => (hsys x hx).2))
    (B.differentiable false).continuous.continuousOn
    (hp.mul (B.derivative_continuous false).continuousOn)
    (hsys.mono Ioo_subset_Icc_self) (outer_poisson_column_firstOrder B hpos false)
    (show b ∈ Icc a b from ⟨hab.le, le_rfl⟩)
  change u b * (p b * deriv (B.u false) b) - v b * B.u false b =
    u a * (p a * deriv (B.u false) a) - v a * B.u false a at h
  rw [B.right_endpoint false, B.left_endpoint false, hua,
    B.right_flux_false hab hp] at h
  simp only [Bool.false_eq_true, ite_false, mul_zero, zero_mul, mul_one, sub_zero,
    zero_sub] at h
  nlinarith only [h]

/-- An actual Dirichlet state is bounded at the other endpoint by its
initial flux times the complete resistance. -/
theorem outer_poisson_dirichlet_value_le_resistance
    {p u v : ℝ → ℝ} {a b Λ η : ℝ}
    (hab : a < b) (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ x ∈ Icc a b, 0 < p x) (hΛ : 0 ≤ Λ)
    (B : TailPhysicalPoissonData p a b Λ η hab.le)
    (hsys : TailFirstOrderSystem p Λ u v (Icc a b)) (hua : u a = 0) :
    |u b| ≤ |v a| * (∫ x in a..b, (p x)⁻¹) := by
  have hchart : tailResistanceChart (tailClampedDensity p a b hab.le) a b =
      ∫ x in a..b, (p x)⁻¹ :=
    tailClampedResistanceChart_eq hab.le ⟨hab.le, le_rfl⟩
  have hR : 0 < ∫ x in a..b, (p x)⁻¹ := by
    rw [← hchart]
    exact tailClampedResistanceLength_pos hab hp hpos
  have hc : 0 < B.offDiagonal := B.offDiagonal_pos hab hp hpos hΛ
  have hfree : (∫ x in a..b, (p x)⁻¹)⁻¹ ≤ B.offDiagonal := by
    rw [TailPhysicalPoissonData.offDiagonal, hchart]
    exact le_add_of_nonneg_right
      (mul_nonneg hΛ (B.massPairing_nonneg hab hp hpos false true))
  have hflux := outer_poisson_dirichlet_flux hab hp hpos B hsys hua
  calc
    |u b| = |v a| / B.offDiagonal := by
      rw [hflux, abs_mul, abs_of_pos hc]
      field_simp [hc.ne']
    _ ≤ |v a| / (∫ x in a..b, (p x)⁻¹)⁻¹ :=
      div_le_div_of_nonneg_left (abs_nonneg _) (inv_pos.mpr hR) hfree
    _ = _ := div_inv_eq_mul _ _

/-- The actual state inherits the two-endpoint Poisson bound. -/
theorem outer_poisson_actual_state_bound {p u v : ℝ → ℝ} {a b Λ η : ℝ}
    (hab : a < b) (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ x ∈ Icc a b, 0 < p x) (hη : η ≤ 1 / 2)
    (B : TailPhysicalPoissonData p a b Λ η hab.le)
    (hsys : TailFirstOrderSystem p Λ u v (Icc a b))
    {x : ℝ} (hx : x ∈ Icc a b) :
    |u x| ≤ 2 * (|u a| + |u b|) := by
  have hu : ContinuousOn u (Icc a b) :=
    HasDerivAt.continuousOn (fun y hy => (hsys y hy).1)
  have hv : ContinuousOn v (Icc a b) :=
    HasDerivAt.continuousOn (fun y hy => (hsys y hy).2)
  have hdu : ContinuousOn (deriv u) (Icc a b) :=
    (hv.div hp (fun y hy => (hpos y hy).ne')).congr
      (fun y hy => (hsys y hy).1.deriv)
  have hflux := tailFirstOrderSystem_hasDerivAt_flux isOpen_Ioo
    (fun y hy => (hpos y (Ioo_subset_Icc_self hy)).ne')
    (hsys.mono Ioo_subset_Icc_self)
  have heq := B.eq_interpolate hab hp hpos hu hdu
    (fun y hy => (hsys y (Ioo_subset_Icc_self hy)).1.differentiableAt.hasDerivAt)
    (fun y hy => by simpa only [neg_mul] using hflux y hy)
  have hη1 : η < 1 := hη.trans_lt (by norm_num)
  have hbound := B.interpolate_bound hab hp hpos hη1 (u a) (u b) hx
  rw [← heq hx] at hbound
  have hfactor : 1 / (1 - η) ≤ (2 : ℝ) :=
    (div_le_iff₀ (sub_pos.mpr hη1)).mpr (by linarith only [hη])
  calc
    _ ≤ (|u a| + |u b|) / (1 - η) := hbound
    _ = (|u a| + |u b|) * (1 / (1 - η)) := by ring
    _ ≤ (|u a| + |u b|) * 2 :=
      mul_le_mul_of_nonneg_left hfactor (add_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := mul_comm _ _

/-- The optional initial edge controls the actual Dirichlet value in
both entrance geometries. No normalization of its flux is required. -/
theorem outer_tail_initial_dirichlet_value_le_resistance {T : DeepTailData}
    (hT : DeepTailHypotheses T) {u v : ℝ → ℝ}
    (hsys : TailFirstOrderSystem T.p T.Λ u v (Ico T.entrance T.endpoint))
    (hua : u T.entrance = 0) :
    |u (T.node 0)| ≤ |v T.entrance| * tailInitialResistance T := by
  rcases hT.2.2.2.1 with heq | hgap
  · simp only [tailInitialResistance, heq, hua, abs_zero,
      intervalIntegral.integral_same, mul_zero, le_refl]
  · have hsub := deepTail_Icc_subset hT le_rfl (deepTail_node_lt_endpoint hT 0)
    obtain ⟨B⟩ := exists_deepTail_initialPoissonData hT hgap.1
    exact outer_poisson_dirichlet_value_le_resistance hgap.1
      ((deepTail_contDiffOn hT).continuousOn.mono hsub)
      (fun x hx => deepTail_pos hT x (hsub hx)) hT.2.2.1.le B (hsys.mono hsub) hua

/-- The complete initial interval inherits the same actual endpoint
interpolation estimate, including when the interval has zero length. -/
theorem outer_tail_initial_state_bound {T : DeepTailData}
    (hT : DeepTailHypotheses T) (hη : T.η ≤ 1 / 2) {u v : ℝ → ℝ}
    (hsys : TailFirstOrderSystem T.p T.Λ u v (Ico T.entrance T.endpoint))
    {x : ℝ} (hx : x ∈ Icc T.entrance (T.node 0)) :
    |u x| ≤ 2 * (|u T.entrance| + |u (T.node 0)|) := by
  rcases hT.2.2.2.1 with heq | hgap
  · have hxe : x = T.entrance := le_antisymm (hx.2.trans_eq heq) hx.1
    rw [hxe, heq]
    nlinarith only [abs_nonneg (u T.entrance)]
  · have hsub := deepTail_Icc_subset hT le_rfl (deepTail_node_lt_endpoint hT 0)
    obtain ⟨B⟩ := exists_deepTail_initialPoissonData hT hgap.1
    exact outer_poisson_actual_state_bound hgap.1
      ((deepTail_contDiffOn hT).continuousOn.mono hsub)
      (fun x hx => deepTail_pos hT x (hsub hx)) hη B (hsys.mono hsub) hx

end ContinuousFlexibility.Radial

