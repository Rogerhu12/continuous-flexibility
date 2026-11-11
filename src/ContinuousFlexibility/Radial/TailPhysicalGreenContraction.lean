import ContinuousFlexibility.Radial.TailPhysicalGreenContinuity

/-!
# Contraction of the physical-edge Green integral

A diagonal majorant bounds the actual integral operator on the fixed
physical interval.  Consequently the same quantitative smallness used
in resistance coordinates gives one common contraction constant in the
parameter-independent space of continuous physical-edge functions.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped NNReal

section KernelBound

variable {P : Type*} [TopologicalSpace P] {a b : ℝ} (hab : a ≤ b)
  (κ : P → ℝ → ℝ → ℝ)
  (hκ : Continuous (fun z : (P × ℝ) × ℝ => κ z.1.1 z.1.2 z.2))

/-- A scalar diagonal majorant controls the operator difference in the
supremum norm. -/
theorem norm_tailContinuousKernelAction_sub_le (σ : P) (w : ℝ → ℝ)
    (hw : Continuous w) (hw₀ : ∀ t ∈ Icc a b, 0 ≤ w t)
    (hbound : ∀ x ∈ Icc a b, ∀ t ∈ Icc a b, |κ σ x t| ≤ w t)
    (u v : C(Icc a b, ℝ)) :
    ‖tailContinuousKernelAction hab κ hκ σ u - tailContinuousKernelAction hab κ hκ σ v‖ ≤
      (∫ t in a..b, w t) * ‖u - v‖ := by
  have hδ₀ : 0 ≤ ∫ t in a..b, w t := intervalIntegral.integral_nonneg hab hw₀
  apply (ContinuousMap.norm_le _ (mul_nonneg hδ₀ (norm_nonneg _))).mpr
  intro x
  rw [ContinuousMap.sub_apply, tailContinuousKernelAction_apply,
    tailContinuousKernelAction_apply]
  have hk : Continuous (κ σ x) :=
    hκ.comp ((continuous_const.prodMk continuous_const).prodMk continuous_id)
  have hu : Continuous (IccExtend hab u) := u.continuous.Icc_extend'
  have hv : Continuous (IccExtend hab v) := v.continuous.Icc_extend'
  rw [← intervalIntegral.integral_sub ((hk.mul hu).intervalIntegrable a b)
    ((hk.mul hv).intervalIntegrable a b)]
  have heq : (fun t => κ σ x t * IccExtend hab u t - κ σ x t * IccExtend hab v t) =
      (fun t => κ σ x t * IccExtend hab (u - v) t) := by
    funext t
    simp only [IccExtend_apply, ContinuousMap.sub_apply, mul_sub]
  rw [heq]
  have huv : Continuous (IccExtend hab (u - v)) := (u - v).continuous.Icc_extend'
  calc
    ‖∫ t in a..b, κ σ x t * IccExtend hab (u - v) t‖ ≤
        ∫ t in a..b, ‖κ σ x t * IccExtend hab (u - v) t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ t in a..b, w t * ‖u - v‖ := by
      apply intervalIntegral.integral_mono_on hab
        ((hk.mul huv).norm.intervalIntegrable a b)
        ((hw.mul continuous_const).intervalIntegrable a b)
      intro t ht
      have huvt : |IccExtend hab (u - v) t| ≤ ‖u - v‖ := by
        rw [IccExtend_of_mem hab (u - v) ht]
        simpa only [Real.norm_eq_abs] using (u - v).norm_coe_le_norm ⟨t, ht⟩
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hbound x x.property t ht) huvt (abs_nonneg _) (hw₀ t ht)
    _ = (∫ t in a..b, w t) * ‖u - v‖ := intervalIntegral.integral_mul_const _ _

/-- Any uniform bound below one for the diagonal integral is a common
contraction constant for all boundary-data Green equations. -/
theorem tailContinuousKernelStep_contracting (K : ℝ≥0) (hK : K < 1)
    (σ : P) (w : ℝ → ℝ) (hw : Continuous w) (hw₀ : ∀ t ∈ Icc a b, 0 ≤ w t)
    (hbound : ∀ x ∈ Icc a b, ∀ t ∈ Icc a b, |κ σ x t| ≤ w t)
    (hsmall : (∫ t in a..b, w t) ≤ K) (base : C(Icc a b, ℝ)) :
    ContractingWith K (fun u => base + tailContinuousKernelAction hab κ hκ σ u) := by
  refine ⟨hK, LipschitzWith.of_dist_le_mul fun u v => ?_⟩
  rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub]
  exact (norm_tailContinuousKernelAction_sub_le hab κ hκ σ w hw hw₀ hbound u v).trans
    (mul_le_mul_of_nonneg_right hsmall (norm_nonneg _))

end KernelBound

theorem tailClampedResistance_memIcc {p : ℝ → ℝ} {a b x : ℝ} (hab : a ≤ b)
    (hp : ContinuousOn p (Icc a b)) (hpos : ∀ t ∈ Icc a b, 0 < p t)
    (hx : x ∈ Icc a b) :
    tailResistanceChart (tailClampedDensity p a b hab) a x ∈
      Icc 0 (tailResistanceChart (tailClampedDensity p a b hab) a b) := by
  have hmono := (tailResistanceChart_strictMono
    (tailClampedDensity_continuous hab hp) (tailClampedDensity_pos hab hpos) a).monotone
  have ha := hmono hx.1
  simp only [tailResistanceChart, intervalIntegral.integral_same] at ha
  exact ⟨ha, hmono hx.2⟩

theorem tailPhysicalGreenWeight_nonneg {p : ℝ → ℝ} {a b Λ x t : ℝ} (hab : a < b)
    (hp : ContinuousOn p (Icc a b)) (hpos : ∀ y ∈ Icc a b, 0 < p y)
    (hΛ : 0 ≤ Λ) (hx : x ∈ Icc a b) (ht : t ∈ Icc a b) :
    0 ≤ tailPhysicalGreenWeight p a b hab.le Λ x t := by
  apply mul_nonneg
  · exact tailEdgeGreen_nonneg (tailClampedResistanceLength_pos hab hp hpos)
      (tailClampedResistance_memIcc hab.le hp hpos hx)
      (tailClampedResistance_memIcc hab.le hp hpos ht)
  · exact mul_nonneg hΛ (tailClampedDensity_pos hab.le hpos t).le

/-- The physical Green kernel has the same diagonal majorant as the
resistance-coordinate kernel. -/
theorem tailPhysicalGreenWeight_le_diagonal {p : ℝ → ℝ} {a b Λ x t : ℝ} (hab : a < b)
    (hp : ContinuousOn p (Icc a b)) (hpos : ∀ y ∈ Icc a b, 0 < p y)
    (hΛ : 0 ≤ Λ) (hx : x ∈ Icc a b) (ht : t ∈ Icc a b) :
    |tailPhysicalGreenWeight p a b hab.le Λ x t| ≤
      tailPhysicalGreenWeight p a b hab.le Λ t t := by
  rw [abs_of_nonneg (tailPhysicalGreenWeight_nonneg hab hp hpos hΛ hx ht)]
  apply mul_le_mul_of_nonneg_right
  · exact tailEdgeGreen_le_diagonal (tailClampedResistanceLength_pos hab hp hpos)
      (tailClampedResistance_memIcc hab.le hp hpos ht)
  · exact mul_nonneg hΛ (tailClampedDensity_pos hab.le hpos t).le

/-- The actual mass-weighted physical Green equation contracts with a
uniform bound on its diagonal integral. -/
theorem tailPhysicalGreenStep_contracting {P : Type*} [TopologicalSpace P]
    {a b : ℝ} (p : P → ℝ → ℝ) (hab : a < b) (Λ : P → ℝ)
    (hp : Continuous (fun z : P × Icc a b => p z.1 z.2))
    (hpos : ∀ σ x, x ∈ Icc a b → 0 < p σ x)
    (hΛcont : Continuous Λ) (hΛ : ∀ σ, 0 ≤ Λ σ)
    (K : ℝ≥0) (hK : K < 1)
    (hsmall : ∀ σ, (∫ t in a..b,
      tailPhysicalGreenWeight (p σ) a b hab.le (Λ σ) t t) ≤ K)
    (σ : P) (base : C(Icc a b, ℝ)) :
    let κ := fun σ x t => tailPhysicalGreenWeight (p σ) a b hab.le (Λ σ) x t
    let hκ := continuous_tailPhysicalGreenWeight_family p hab hp hpos hΛcont
    ContractingWith K (fun u => base + tailContinuousKernelAction hab.le κ hκ σ u) := by
  dsimp only
  let κ := fun σ x t => tailPhysicalGreenWeight (p σ) a b hab.le (Λ σ) x t
  have hκ := continuous_tailPhysicalGreenWeight_family p hab hp hpos hΛcont
  have hpσ : ContinuousOn (p σ) (Icc a b) := by
    apply continuousOn_iff_continuous_restrict.mpr
    exact hp.comp (continuous_const.prodMk continuous_id)
  apply tailContinuousKernelStep_contracting hab.le κ hκ K hK σ
    (fun t => κ σ t t)
  · exact hκ.comp ((continuous_const.prodMk continuous_id).prodMk continuous_id)
  · intro t ht
    exact tailPhysicalGreenWeight_nonneg hab hpσ (hpos σ) (hΛ σ) ht ht
  · intro x hx t ht
    exact tailPhysicalGreenWeight_le_diagonal hab hpσ (hpos σ) (hΛ σ) hx ht
  · exact hsmall σ

end ContinuousFlexibility.Radial
