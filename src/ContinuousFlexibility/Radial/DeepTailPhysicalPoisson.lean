module

public import ContinuousFlexibility.Radial.DeepTailEdgeCoordinates
public import ContinuousFlexibility.Radial.TailPhysicalGreenContinuity
public import ContinuousFlexibility.Radial.DeepTailEdgeUniqueness

/-!
# Poisson functions on the original tail edge

The resistance-coordinate Poisson functions are pulled back by the actual
integral of the reciprocal density. The resulting functions retain their
physical integral equation, endpoint fluxes, and differential equation.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology

/-- The two actual Poisson functions on one physical edge. Every identity
in this structure is in the original coordinate, with the original density. -/
structure TailPhysicalPoissonData (p : ℝ → ℝ) (a b Λ η : ℝ) (hab : a ≤ b) where
  u : Bool → ℝ → ℝ
  differentiable : ∀ right, Differentiable ℝ (u right)
  derivative_continuous : ∀ right, Continuous (deriv (u right))
  left_endpoint : ∀ right, u right a = if right then 0 else 1
  right_endpoint : ∀ right, u right b = if right then 1 else 0
  equation : ∀ right x, x ∈ Ioo a b →
    HasDerivAt (fun y => p y * deriv (u right) y) (-(Λ * p x * u right x)) x
  bounds : ∀ right x, x ∈ Icc a b →
    tailPhysicalHeight p a b hab right x ≤ u right x ∧
      u right x ≤ tailPhysicalHeight p a b hab right x / (1 - η)
  integral : ∀ right x, x ∈ Icc a b → u right x =
    tailPhysicalHeight p a b hab right x +
      ∫ t in a..b, tailPhysicalGreenWeight p a b hab Λ x t * u right t
  left_flux : ∀ right, p a * deriv (u right) a =
    (if right then 1 else -1) / tailResistanceChart (tailClampedDensity p a b hab) a b +
      Λ * ∫ t in a..b, p t * tailPhysicalHeight p a b hab false t * u right t
  right_flux : ∀ right, p b * deriv (u right) b =
    (if right then 1 else -1) / tailResistanceChart (tailClampedDensity p a b hab) a b -
      Λ * ∫ t in a..b, p t * tailPhysicalHeight p a b hab true t * u right t

/-- The compact-edge contraction theorem constructs these functions for
the original density. The bound may use any larger uniform contraction
constant, which is useful for families of edges. -/
theorem exists_tailPhysicalPoissonData {p : ℝ → ℝ} {a b Λ η : ℝ}
    (hab : a < b) (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ x ∈ Icc a b, 0 < p x) (hΛ : 0 ≤ Λ) (hη : η < 1)
    (hsmall : tailEdgeDiagonalSize
      ((tailResistanceChart_strictMono (tailClampedDensity_continuous hab.le hp)
        (tailClampedDensity_pos hab.le hpos) a) hab)
      (tailClampedEdgePotential hab.le hp hpos Λ) ≤ η) :
    Nonempty (TailPhysicalPoissonData p a b Λ η hab.le) := by
  let P := tailClampedDensity p a b hab.le
  let S := tailResistanceChart P a
  let ρ := tailResistanceDensity P a
  let q := tailClampedEdgePotential hab.le hp hpos Λ
  have hPc : Continuous P := tailClampedDensity_continuous hab.le hp
  have hPp : ∀ x, 0 < P x := tailClampedDensity_pos hab.le hpos
  have hS : StrictMono S := tailResistanceChart_strictMono hPc hPp a
  have hSc : Continuous S :=
    continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_tailResistanceChart hPc hPp a x).continuousAt
  have hS0 : S a = 0 := intervalIntegral.integral_same
  have hL : 0 < S b := by simpa only [hS0] using hS hab
  have hq (s) : 0 ≤ q s :=
    mul_nonneg hΛ (tailClampedResistanceDensity_pos hab.le hpos s).le
  have hδ : tailEdgeDiagonalSize (hS hab) q < 1 := hsmall.trans_lt hη
  have hs (x : ℝ) (hx : x ∈ Icc a b) : S x ∈ Icc (S a) (S b) :=
    ⟨hS.monotone hx.1, hS.monotone hx.2⟩
  choose U hU hDU hUa hUb hODE hBound hFA hFB hIntegral using
    (fun right : Bool => exists_tailEdgePoisson_classical_integral (hS hab) hq hδ right)
  have hheight (right : Bool) (x : ℝ) :
      (if right then tailEdgeRightHeight (S a) (S b)
        else tailEdgeLeftHeight (S a) (S b)) (S x) =
      tailPhysicalHeight p a b hab.le right x := by
    cases right <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, tailEdgeLeftHeight,
        tailEdgeRightHeight, hS0, sub_zero, tailPhysicalHeight] <;> rfl
  have hheight_nonneg (right : Bool) (x : ℝ) (hx : x ∈ Icc a b) :
      0 ≤ tailPhysicalHeight p a b hab.le right x := by
    rw [← hheight right x]
    cases right
    · exact div_nonneg (sub_nonneg.mpr (hs x hx).2) (sub_nonneg.mpr (hS hab).le)
    · exact div_nonneg (sub_nonneg.mpr (hs x hx).1) (sub_nonneg.mpr (hS hab).le)
  have hpair (right : Bool) (e : ℝ → ℝ) (he : Continuous e) :
      (∫ s in S a..S b, e s * IccExtend (hS hab).le q s * U right s) =
      Λ * ∫ x in a..b, p x * e (S x) * U right (S x) := by
    calc
      _ = Λ * ∫ s in S a..S b, ρ s * (e s * U right s) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le (hS hab).le]
        intro s ht
        dsimp only
        rw [IccExtend_of_mem (hS hab).le q ht]
        change e s * (Λ * ρ s) * U right s = _
        ring
      _ = Λ * ∫ x in a..b, p x * (e (S x) * U right (S x)) := by
        exact congrArg (fun z : ℝ => Λ * z)
          (tailClampedResistance_mass_change (V := fun s => e s * U right s)
            hab.le hp hpos (he.mul (hU right).continuous)
            ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩)
      _ = _ := by
        congr 1
        apply intervalIntegral.integral_congr
        intro x _
        dsimp only
        ring
  have hleft : Continuous (tailEdgeLeftHeight (S a) (S b)) :=
    (continuous_const.sub continuous_id).div_const _
  have hright : Continuous (tailEdgeRightHeight (S a) (S b)) :=
    (continuous_id.sub continuous_const).div_const _
  refine ⟨{
    u := fun right => U right ∘ S
    differentiable := fun right => (hU right).comp
      (fun x => (hasDerivAt_tailResistanceChart hPc hPp a x).differentiableAt)
    derivative_continuous := ?_
    left_endpoint := ?_
    right_endpoint := ?_
    equation := ?_
    bounds := ?_
    integral := ?_
    left_flux := ?_
    right_flux := ?_
  }⟩
  · intro right
    have hd : deriv (U right ∘ S) = fun x => deriv (U right) (S x) * (P x)⁻¹ := by
      funext x
      exact ((hU right (S x)).hasDerivAt.comp x
        (hasDerivAt_tailResistanceChart hPc hPp a x)).deriv
    rw [hd]
    exact ((hDU right).continuous.comp hSc).mul (hPc.inv₀ fun x => (hPp x).ne')
  · intro right
    change U right (S a) = _
    rw [hUa right]
    cases right <;> simp [tailEdgeLeftHeight, tailEdgeRightHeight, (sub_pos.mpr (hS hab)).ne']
  · intro right
    change U right (S b) = _
    rw [hUb right]
    cases right <;> simp [tailEdgeLeftHeight, tailEdgeRightHeight, (sub_pos.mpr (hS hab)).ne']
  · intro right x hx
    have hxx : x ∈ Icc a b := Ioo_subset_Icc_self hx
    have heq : (fun y => p y * deriv (U right ∘ S) y) =ᶠ[𝓝 x]
        (fun y => deriv (U right) (S y)) :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds hx) fun y hy =>
        tailClampedResistance_flux hab.le hp hpos (hU right) (Ioo_subset_Icc_self hy)
    have hd := (hODE right (S x) (hs x hxx)).comp x
      (hasDerivAt_tailClampedResistanceChart hab.le hp hpos hxx)
    have hqx : q ⟨S x, hs x hxx⟩ = Λ * p x ^ 2 := by
      change Λ * ρ (S x) = _
      exact congrArg (fun z : ℝ => Λ * z)
        (tailClampedResistanceDensity_chart hab.le hp hpos hxx)
    apply (hd.congr_of_eventuallyEq heq).congr_deriv
    rw [hqx]
    change -(Λ * p x ^ 2 * U right (S x)) * (p x)⁻¹ = -(Λ * p x * U right (S x))
    field_simp [(hpos x hxx).ne'] <;> ring
  · intro right x hx
    have hb := hBound right (S x) (hs x hx)
    rw [hheight right x] at hb
    refine ⟨hb.1, hb.2.trans ?_⟩
    exact div_le_div_of_nonneg_left (hheight_nonneg right x hx)
      (sub_pos.mpr hη) (sub_le_sub_left hsmall 1)
  · intro right x hx
    have h := hIntegral right (S x) (hs x hx)
    rw [hheight right x] at h
    change U right (S x) = _
    rw [h]
    congr 1
    have hG : Continuous (tailEdgeGreen (S a) (S b) (S x)) := by
      unfold tailEdgeGreen
      exact (((continuous_const.min continuous_id).sub continuous_const).mul
        (continuous_const.sub (continuous_const.max continuous_id))).div_const _
    rw [hpair right _ hG, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hab.le]
    intro t ht
    dsimp only [tailPhysicalGreenWeight, tailPhysicalGreenKernel, Function.comp_apply]
    rw [tailClampedDensity_eq_of_mem hab.le ht]
    change Λ * (p t * tailEdgeGreen (S a) (S b) (S x) (S t) * U right (S t)) =
      tailEdgeGreen 0 (S b) (S x) (S t) * (Λ * p t) * U right (S t)
    rw [hS0]
    ring
  · intro right
    rw [tailClampedResistance_flux hab.le hp hpos (hU right) ⟨le_rfl, hab.le⟩,
      hFA right, hpair right _ hleft]
    have hint : (∫ x in a..b, p x * tailEdgeLeftHeight (S a) (S b) (S x) * U right (S x)) =
        ∫ x in a..b, p x * tailPhysicalHeight p a b hab.le false x * (U right ∘ S) x := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only [Function.comp_apply]
      rw [← hheight false x]
      rfl
    rw [hint]
    cases right <;> simp only [Bool.false_eq_true, ite_false, ite_true, hS0, sub_zero,
      neg_div, one_div] <;> rfl
  · intro right
    rw [tailClampedResistance_flux hab.le hp hpos (hU right) ⟨hab.le, le_rfl⟩,
      hFB right, hpair right _ hright]
    have hint : (∫ x in a..b, p x * tailEdgeRightHeight (S a) (S b) (S x) * U right (S x)) =
        ∫ x in a..b, p x * tailPhysicalHeight p a b hab.le true x * (U right ∘ S) x := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only [Function.comp_apply]
      rw [← hheight true x]
      rfl
    rw [hint]
    cases right <;> simp only [Bool.false_eq_true, ite_false, ite_true, hS0, sub_zero,
      neg_div, one_div] <;> rfl

end ContinuousFlexibility.Radial
