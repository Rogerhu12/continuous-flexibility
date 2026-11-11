import ContinuousFlexibility.Radial.DeepTailPoissonContinuity
import ContinuousFlexibility.Radial.DeepTailEdgeComparison
import ContinuousFlexibility.Radial.DeepTailInterpolation
import ContinuousFlexibility.Radial.TailJacobiSmallness
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Actual Poisson and Jacobi bounds on deep edges

All coefficients are integrals of the actual Poisson functions.  The
estimates use deliberately generous constants: the left mass contributes
at least half its mass to the diagonal, while each off-diagonal is at
most twice the reciprocal resistance.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology
open ContinuousFlexibility.Statements

theorem tailPhysicalHeight_continuous {p : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hp : ContinuousOn p (Icc a b)) (hpos : ∀ x ∈ Icc a b, 0 < p x) (right : Bool) :
    Continuous (tailPhysicalHeight p a b hab right) := by
  have hS : Continuous (tailResistanceChart (tailClampedDensity p a b hab) a) :=
    continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_tailResistanceChart (tailClampedDensity_continuous hab hp)
        (tailClampedDensity_pos hab hpos) a x).continuousAt
  cases right
  · exact (continuous_const.sub hS).div_const _
  · exact hS.div_const _

theorem tailPhysicalHeight_mem {p : ℝ → ℝ} {a b x : ℝ} (hab : a < b)
    (hp : ContinuousOn p (Icc a b)) (hpos : ∀ t ∈ Icc a b, 0 < p t)
    (right : Bool) (hx : x ∈ Icc a b) :
    tailPhysicalHeight p a b hab.le right x ∈ Icc 0 1 := by
  have hS := tailClampedResistance_memIcc hab.le hp hpos hx
  have hL := tailClampedResistanceLength_pos hab hp hpos
  cases right
  · exact ⟨div_nonneg (sub_nonneg.mpr hS.2) hL.le,
      (div_le_one hL).mpr (sub_le_self _ hS.1)⟩
  · exact ⟨div_nonneg hS.1 hL.le, (div_le_one hL).mpr hS.2⟩

theorem tailPhysicalHeight_product {p : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hp : ContinuousOn p (Icc a b)) (hpos : ∀ t ∈ Icc a b, 0 < p t) (x : ℝ) :
    tailPhysicalHeight p a b hab.le false x * tailPhysicalHeight p a b hab.le true x *
        tailResistanceChart (tailClampedDensity p a b hab.le) a b =
      tailPhysicalGreenKernel p a b hab.le x x := by
  have hL := (tailClampedResistanceLength_pos hab hp hpos).ne'
  simp only [tailPhysicalHeight, tailPhysicalGreenKernel, Bool.false_eq_true,
    ite_false, ite_true, tailEdgeGreen_self, sub_zero]
  field_simp [hL] <;> ring

/-- One-sided order at a common entrance value orders the two ordinary
derivatives there. -/
theorem tailEdge_deriv_le_of_right_order {a b f' g' : ℝ} {f g : ℝ → ℝ}
    (hab : a < b) (hf : HasDerivAt f f' a) (hg : HasDerivAt g g' a)
    (ha : f a = g a) (hfg : ∀ x ∈ Ioo a b, f x ≤ g x) : f' ≤ g' := by
  apply le_of_tendsto_of_tendsto
    (hf.tendsto_slope.mono_left (nhdsGT_le_nhdsNE a))
    (hg.tendsto_slope.mono_left (nhdsGT_le_nhdsNE a))
  filter_upwards [Ioo_mem_nhdsGT hab] with x hx
  rw [slope_def_field, slope_def_field, ha]
  exact div_le_div_of_nonneg_right (sub_le_sub_right (hfg x hx) _) (sub_nonneg.mpr hx.1.le)

namespace TailPhysicalPoissonData

variable {p : ℝ → ℝ} {a b Λ η : ℝ} (hab : a < b)
  (B : TailPhysicalPoissonData p a b Λ η hab.le)

theorem basis_nonneg (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ t ∈ Icc a b, 0 < p t) (right : Bool) {x : ℝ} (hx : x ∈ Icc a b) :
    0 ≤ B.u right x :=
  (tailPhysicalHeight_mem hab hp hpos right hx).1.trans (B.bounds right x hx).1

theorem basis_le_twice_height (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ t ∈ Icc a b, 0 < p t) (hη : η ≤ 1 / 2) (right : Bool)
    {x : ℝ} (hx : x ∈ Icc a b) :
    B.u right x ≤ 2 * tailPhysicalHeight p a b hab.le right x := by
  have hn := (tailPhysicalHeight_mem hab hp hpos right hx).1
  apply (B.bounds right x hx).2.trans
  apply (div_le_iff₀ (show 0 < 1 - η by linarith)).mpr
  nlinarith

theorem massPairing_nonneg (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ t ∈ Icc a b, 0 < p t) (left right : Bool) :
    0 ≤ ∫ x in a..b, p x * tailPhysicalHeight p a b hab.le left x * B.u right x := by
  apply intervalIntegral.integral_nonneg hab.le
  intro x hx
  exact mul_nonneg (mul_nonneg (hpos x hx).le
    (tailPhysicalHeight_mem hab hp hpos left hx).1) (B.basis_nonneg hab hp hpos right hx)

theorem offDiagonal_pos (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ t ∈ Icc a b, 0 < p t) (hΛ : 0 ≤ Λ) : 0 < B.offDiagonal := by
  exact add_pos_of_pos_of_nonneg (inv_pos.mpr (tailClampedResistanceLength_pos hab hp hpos))
    (mul_nonneg hΛ (B.massPairing_nonneg hab hp hpos false true))

/-- The Poisson comparison gives the off-diagonal estimate by taking the
right derivative at the entrance; this avoids an additional integral bound. -/
theorem offDiagonal_le_two_div_length (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ t ∈ Icc a b, 0 < p t) (hη : η ≤ 1 / 2) :
    B.offDiagonal ≤ 2 / tailResistanceChart (tailClampedDensity p a b hab.le) a b := by
  let L := tailResistanceChart (tailClampedDensity p a b hab.le) a b
  have hL : 0 < L := tailClampedResistanceLength_pos hab hp hpos
  have hpa : 0 < p a := hpos a ⟨le_rfl, hab.le⟩
  have hH : HasDerivAt (fun x => 2 * tailPhysicalHeight p a b hab.le true x)
      (2 * ((p a)⁻¹ / L)) a :=
    ((hasDerivAt_tailClampedResistanceChart hab.le hp hpos ⟨le_rfl, hab.le⟩).div_const L).const_mul 2
  have hd : deriv (B.u true) a ≤ 2 * ((p a)⁻¹ / L) := by
    apply tailEdge_deriv_le_of_right_order hab (B.differentiable true a).hasDerivAt hH
    · simp only [B.left_endpoint, ite_true, tailPhysicalHeight, tailResistanceChart,
        intervalIntegral.integral_same, zero_div, mul_zero]
    · intro x hx
      exact B.basis_le_twice_height hab hp hpos hη true (Ioo_subset_Icc_self hx)
  calc
    B.offDiagonal = p a * deriv (B.u true) a := B.left_flux_true.symm
    _ ≤ p a * (2 * ((p a)⁻¹ / L)) := mul_le_mul_of_nonneg_left hd hpa.le
    _ = 2 / L := by field_simp [hpa.ne', hL.ne'] <;> ring

theorem leftDiagonal_le_inv (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ t ∈ Icc a b, 0 < p t) (hΛ : 0 ≤ Λ) :
    B.leftDiagonal ≤ (tailResistanceChart (tailClampedDensity p a b hab.le) a b)⁻¹ :=
  sub_le_self _ (mul_nonneg hΛ (B.massPairing_nonneg hab hp hpos false false))

theorem rightDiagonal_le_inv (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ t ∈ Icc a b, 0 < p t) (hΛ : 0 ≤ Λ) :
    B.rightDiagonal ≤ (tailResistanceChart (tailClampedDensity p a b hab.le) a b)⁻¹ :=
  sub_le_self _ (mul_nonneg hΛ (B.massPairing_nonneg hab hp hpos true true))

theorem interpolate_left_flux (A Z : ℝ) :
    p a * deriv (B.interpolate A Z) a = -B.leftDiagonal * A + B.offDiagonal * Z := by
  rw [B.interpolate_deriv]
  calc
    _ = A * (p a * deriv (B.u false) a) + Z * (p a * deriv (B.u true) a) := by ring
    _ = _ := by rw [B.left_flux_false, B.left_flux_true]; ring

theorem interpolate_right_flux (hp : ContinuousOn p (Icc a b)) (A Z : ℝ) :
    p b * deriv (B.interpolate A Z) b = -B.offDiagonal * A + B.rightDiagonal * Z := by
  rw [B.interpolate_deriv]
  calc
    _ = A * (p b * deriv (B.u false) b) + Z * (p b * deriv (B.u true) b) := by ring
    _ = _ := by rw [B.right_flux_false hab hp, B.right_flux_true]; ring

/-- A short resistance coordinate on the mass part keeps the left
Poisson function uniformly away from zero there. -/
theorem leftDiagonal_le_inv_sub_half_mass {c : ℝ} (hc : c ∈ Icc a b)
    (hp : ContinuousOn p (Icc a b)) (hpos : ∀ t ∈ Icc a b, 0 < p t)
    (hΛ : 0 ≤ Λ)
    (hshort : 4 * tailResistanceChart (tailClampedDensity p a b hab.le) a c ≤
      tailResistanceChart (tailClampedDensity p a b hab.le) a b) :
    B.leftDiagonal ≤ (tailResistanceChart (tailClampedDensity p a b hab.le) a b)⁻¹ -
      Λ * (∫ x in a..c, p x) / 2 := by
  let S := tailResistanceChart (tailClampedDensity p a b hab.le) a
  have hL : 0 < S b := tailClampedResistanceLength_pos hab hp hpos
  have hmono : Monotone S := (tailResistanceChart_strictMono
    (tailClampedDensity_continuous hab.le hp) (tailClampedDensity_pos hab.le hpos) a).monotone
  let f := fun x => p x * tailPhysicalHeight p a b hab.le false x * B.u false x
  have hf : ContinuousOn f (Icc a b) :=
    (hp.mul (tailPhysicalHeight_continuous hab.le hp hpos false).continuousOn).mul
      (B.differentiable false).continuous.continuousOn
  have hpac := hp.mono (Icc_subset_Icc le_rfl hc.2)
  have hfac := hf.mono (Icc_subset_Icc le_rfl hc.2)
  have hfcb := hf.mono (Icc_subset_Icc hc.1 le_rfl)
  have hhalf : (∫ x in a..c, p x) / 2 ≤ ∫ x in a..c, f x := by
    rw [← intervalIntegral.integral_div_const]
    apply intervalIntegral.integral_mono_on hc.1
      ((hpac.div_const 2).intervalIntegrable_of_Icc hc.1)
      (hfac.intervalIntegrable_of_Icc hc.1)
    intro x hx
    have hx' : x ∈ Icc a b := ⟨hx.1, hx.2.trans hc.2⟩
    have hH : (3 / 4 : ℝ) ≤ tailPhysicalHeight p a b hab.le false x := by
      change (3 / 4 : ℝ) ≤ (S b - S x) / S b
      apply (le_div_iff₀ hL).mpr
      have hm := hmono hx.2
      dsimp only [S] at hm ⊢
      linarith only [hm, hshort]
    have hU := (B.bounds false x hx').1
    have hHU : (1 / 2 : ℝ) ≤
        tailPhysicalHeight p a b hab.le false x * B.u false x := by
      have hh := mul_le_mul_of_nonneg_left hU
        (show 0 ≤ tailPhysicalHeight p a b hab.le false x by linarith only [hH])
      nlinarith only [hH, hh,
        sq_nonneg (tailPhysicalHeight p a b hab.le false x - 3 / 4)]
    have hh := mul_le_mul_of_nonneg_left hHU (hpos x hx').le
    change p x / 2 ≤ p x * tailPhysicalHeight p a b hab.le false x * B.u false x
    nlinarith only [hh]
  have hgap : 0 ≤ ∫ x in c..b, f x := by
    apply intervalIntegral.integral_nonneg hc.2
    intro x hx
    have hx' : x ∈ Icc a b := ⟨hc.1.trans hx.1, hx.2⟩
    exact mul_nonneg (mul_nonneg (hpos x hx').le
      (tailPhysicalHeight_mem hab hp hpos false hx').1) (B.basis_nonneg hab hp hpos false hx')
  have hfull : (∫ x in a..c, p x) / 2 ≤ ∫ x in a..b, f x := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hfac.intervalIntegrable_of_Icc hc.1) (hfcb.intervalIntegrable_of_Icc hc.2)]
    linarith only [hhalf, hgap]
  have hh := mul_le_mul_of_nonneg_left hfull hΛ
  change _ - Λ * (∫ x in a..b, f x) ≤ _
  nlinarith only [hh]

/-- Either actual Poisson basis has square at most four on a small edge. -/
theorem basis_square_le_four_mass (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ t ∈ Icc a b, 0 < p t) (hη : η ≤ 1 / 2) (right : Bool) :
    (∫ x in a..b, p x * B.u right x ^ 2) ≤ 4 * ∫ x in a..b, p x := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hab.le
    ((hp.mul ((B.differentiable right).continuous.continuousOn.pow 2)).intervalIntegrable_of_Icc hab.le)
    ((hp.const_mul 4).intervalIntegrable_of_Icc hab.le)
  intro x hx
  have hU₀ := B.basis_nonneg hab hp hpos right hx
  have hU := B.basis_le_twice_height hab hp hpos hη right hx
  have hH := (tailPhysicalHeight_mem hab hp hpos right hx).2
  have hs : B.u right x ^ 2 ≤ 4 := by
    have hh := pow_le_pow_left₀ hU₀ (show B.u right x ≤ 2 by linarith only [hU, hH]) 2
    norm_num at hh
    exact hh
  have hh := mul_le_mul_of_nonneg_left hs (hpos x hx).le
  change p x * B.u right x ^ 2 ≤ 4 * p x
  nlinarith only [hh]

/-- The right basis is small on the preceding mass interval, so its
square integral is charged to the next mass rather than to the previous one. -/
theorem right_basis_square_bound {c : ℝ} (hc : c ∈ Icc a b)
    (hp : ContinuousOn p (Icc a b)) (hpos : ∀ t ∈ Icc a b, 0 < p t)
    (hη : η ≤ 1 / 2) :
    (∫ x in a..b, p x * B.u true x ^ 2) ≤
      4 * (tailPhysicalHeight p a b hab.le true c * (∫ x in a..c, p x) +
        ∫ x in c..b, p x) := by
  let H := tailPhysicalHeight p a b hab.le true
  have hL := tailClampedResistanceLength_pos hab hp hpos
  have hmono : Monotone H := by
    intro x y hxy
    apply div_le_div_of_nonneg_right _ hL.le
    exact (tailResistanceChart_strictMono (tailClampedDensity_continuous hab.le hp)
      (tailClampedDensity_pos hab.le hpos) a).monotone hxy
  have hf : ContinuousOn (fun x => p x * B.u true x ^ 2) (Icc a b) :=
    hp.mul ((B.differentiable true).continuous.continuousOn.pow 2)
  have hfac := hf.mono (Icc_subset_Icc le_rfl hc.2)
  have hfcb := hf.mono (Icc_subset_Icc hc.1 le_rfl)
  have hpac := hp.mono (Icc_subset_Icc le_rfl hc.2)
  have hpcb := hp.mono (Icc_subset_Icc hc.1 le_rfl)
  have hs (x : ℝ) (hx : x ∈ Icc a b) : B.u true x ^ 2 ≤ 4 * H x := by
    have hu₀ := B.basis_nonneg hab hp hpos true hx
    have hu := B.basis_le_twice_height hab hp hpos hη true hx
    have hh := tailPhysicalHeight_mem hab hp hpos true hx
    have hsq := pow_le_pow_left₀ hu₀ hu 2
    change B.u true x ^ 2 ≤ 4 * H x
    dsimp only [H] at *
    nlinarith only [hsq, hh.1, hh.2, mul_nonneg hh.1 (sub_nonneg.mpr hh.2)]
  have hm : (∫ x in a..c, p x * B.u true x ^ 2) ≤
      (4 * H c) * ∫ x in a..c, p x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hc.1
      (hfac.intervalIntegrable_of_Icc hc.1)
      ((hpac.const_mul (4 * H c)).intervalIntegrable_of_Icc hc.1)
    intro x hx
    have hx' : x ∈ Icc a b := ⟨hx.1, hx.2.trans hc.2⟩
    have hh := mul_le_mul_of_nonneg_left
      ((hs x hx').trans (mul_le_mul_of_nonneg_left (hmono hx.2) (by norm_num)))
      (hpos x hx').le
    nlinarith only [hh]
  have hg : (∫ x in c..b, p x * B.u true x ^ 2) ≤ 4 * ∫ x in c..b, p x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hc.2
      (hfcb.intervalIntegrable_of_Icc hc.2)
      ((hpcb.const_mul 4).intervalIntegrable_of_Icc hc.2)
    intro x hx
    have hx' : x ∈ Icc a b := ⟨hc.1.trans hx.1, hx.2⟩
    have hh := mul_le_mul_of_nonneg_left
      ((hs x hx').trans (mul_le_mul_of_nonneg_left
        (tailPhysicalHeight_mem hab hp hpos true hx').2 (by norm_num))) (hpos x hx').le
    nlinarith only [hh]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hfac.intervalIntegrable_of_Icc hc.1) (hfcb.intervalIntegrable_of_Icc hc.2)]
  change _ ≤ 4 * (H c * _ + _)
  nlinarith only [hm, hg]

end TailPhysicalPoissonData

end ContinuousFlexibility.Radial
