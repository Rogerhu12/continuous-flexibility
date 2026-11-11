import ContinuousFlexibility.Radial.TailEdgePerturbedGreen

/-!
# Weighted mass estimate for the Dirichlet edge solution

The exact differential equation gives the energy identity. The Green
diagonal controls the weighted mass form, yielding the operator estimate
on continuous forcing in the mass norm.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped ContDiff

private theorem tailEdge_mass_bound {a b Λ : ℝ} {density f u : ℝ → ℝ}
    (hab : a < b) (hΛ : 0 < Λ) (hdensity : Continuous density) (hdensity₀ : ∀ s ∈ Icc a b, 0 ≤ density s)
    (hf : Continuous f) (hu : ContDiff ℝ 1 u) (ha : u a = 0) (hb : u b = 0)
    (hode : ∀ s ∈ Icc a b, HasDerivAt (deriv u) (-(density s * f s + Λ * density s * u s)) s)
    (hsmall : Λ * (∫ s in a..b, density s * tailEdgeGreen a b s s) < 1) :
    let D := ∫ s in a..b, density s * tailEdgeGreen a b s s
    (∫ s in a..b, density s * u s ^ 2) ≤
      (D / (1 - Λ * D)) ^ 2 * ∫ s in a..b, density s * f s ^ 2 := by
  dsimp only
  let D := ∫ s in a..b, density s * tailEdgeGreen a b s s
  let E := ∫ s in a..b, deriv u s ^ 2
  let U := ∫ s in a..b, density s * u s ^ 2
  let F := ∫ s in a..b, density s * f s ^ 2
  let J := ∫ s in a..b, density s * f s * u s
  let κ := D / (1 - Λ * D)
  have hk : 0 < 1 - Λ * D := sub_pos.mpr hsmall
  have hEint : IntervalIntegrable (fun s => deriv u s ^ 2) volume a b :=
    ((hu.continuous_deriv (by simp)).pow 2).intervalIntegrable a b
  have hUint : IntervalIntegrable (fun s => density s * u s ^ 2) volume a b :=
    (hdensity.mul (hu.continuous.pow 2)).intervalIntegrable a b
  have hFint : IntervalIntegrable (fun s => density s * f s ^ 2) volume a b :=
    (hdensity.mul (hf.pow 2)).intervalIntegrable a b
  have hJint : IntervalIntegrable (fun s => density s * f s * u s) volume a b :=
    ((hdensity.mul hf).mul hu.continuous).intervalIntegrable a b
  have hEnergy : E = J + Λ * U := by
    let P : ℝ → ℝ := fun s => u s * deriv u s
    let e : ℝ → ℝ := fun s => deriv u s ^ 2 - density s * f s * u s - Λ * (density s * u s ^ 2)
    have hP (s : ℝ) (hs : s ∈ uIcc a b) : HasDerivAt P (e s) s := by
      have hs' : s ∈ Icc a b := by simpa only [uIcc_of_le hab.le] using hs
      convert ((hu.differentiable (by simp) s).hasDerivAt.mul (hode s hs')) using 1
      dsimp only [e]
      ring
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hP
      ((hEint.sub hJint).sub (hUint.const_mul Λ))
    change (∫ s in a..b, (deriv u s ^ 2 - density s * f s * u s) - Λ * (density s * u s ^ 2)) =
      P b - P a at hFTC
    rw [intervalIntegral.integral_sub (hEint.sub hJint) (hUint.const_mul Λ),
      intervalIntegral.integral_sub hEint hJint, intervalIntegral.integral_const_mul] at hFTC
    simpa only [P, ha, hb, zero_mul, sub_zero, sub_sub, sub_eq_zero] using hFTC
  have hUE : U ≤ D * E := by
    have he := tailEdge_weighted_energy_bound hab hΛ.le hu ha hb hdensity.continuousOn hdensity₀
    change Λ * U ≤ (Λ * D) * E at he
    exact le_of_mul_le_mul_left (by simpa only [mul_assoc] using he) hΛ
  have hUJ : U ≤ κ * J := by
    rw [hEnergy] at hUE
    have h : U * (1 - Λ * D) ≤ D * J := by nlinarith only [hUE]
    exact (le_div_iff₀ hk).mpr h |>.trans_eq (by dsimp only [κ]; ring)
  have hsq : 0 ≤ U - (2 * κ) * J + κ ^ 2 * F := by
    have hpos := intervalIntegral.integral_nonneg (μ := volume) hab.le (f := fun s => density s * (u s - κ * f s) ^ 2)
      (fun s hs => mul_nonneg (hdensity₀ s hs) (sq_nonneg _))
    have heq : (fun s => density s * (u s - κ * f s) ^ 2) =
        fun s => (density s * u s ^ 2 - (2 * κ) * (density s * f s * u s)) + κ ^ 2 * (density s * f s ^ 2) := by
      funext s
      ring
    rw [heq, intervalIntegral.integral_add (hUint.sub (hJint.const_mul _)) (hFint.const_mul _),
      intervalIntegral.integral_sub hUint (hJint.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hpos
    exact hpos
  change U ≤ κ ^ 2 * F
  linarith only [hUJ, hsq]

/-- Every continuous forcing has an actual classical Dirichlet solution with
the sharp diagonal-based bound in the weighted mass norm. -/
theorem exists_tailEdge_dirichlet_mass_bound {a b Λ : ℝ} {density f : ℝ → ℝ}
    (hab : a < b) (hΛ : 0 < Λ) (hdensity : Continuous density) (hdensity₀ : ∀ s ∈ Icc a b, 0 ≤ density s)
    (hf : Continuous f)
    (hsmall : Λ * (∫ s in a..b, density s * tailEdgeGreen a b s s) < 1) :
    let D := ∫ s in a..b, density s * tailEdgeGreen a b s s
    ∃ u : ℝ → ℝ,
      ContDiff ℝ 1 u ∧ u a = 0 ∧ u b = 0 ∧
      (∀ s ∈ Icc a b, HasDerivAt (deriv u) (-(density s * f s + Λ * density s * u s)) s) ∧
      (∫ s in a..b, density s * u s ^ 2) ≤
        (D / (1 - Λ * D)) ^ 2 * ∫ s in a..b, density s * f s ^ 2 := by
  dsimp only
  let q : TailEdgeContinuous a b :=
    ⟨fun s => Λ * density s, (continuous_const.mul hdensity).comp continuous_subtype_val⟩
  have hq (s : Icc a b) : 0 ≤ q s := mul_nonneg hΛ.le (hdensity₀ s s.property)
  have hδ : tailEdgeDiagonalSize hab q < 1 := by
    have heq : tailEdgeDiagonalSize hab q = Λ * ∫ s in a..b, density s * tailEdgeGreen a b s s := by
      rw [tailEdgeDiagonalSize, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le hab.le]
      intro s hs
      change tailEdgeGreen a b s s * IccExtend hab.le q s = _
      rw [IccExtend_of_mem hab.le q hs]
      change tailEdgeGreen a b s s * (Λ * density s) = Λ * (density s * tailEdgeGreen a b s s)
      ring
    exact heq.trans_lt hsmall
  let F : ℝ → ℝ := fun s => density s * f s
  have hF : Continuous F := hdensity.mul hf
  have hbase : Continuous (tailEdgeZeroSolve a b F) :=
    continuous_iff_continuousAt.mpr (fun s => (hasDerivAt_tailEdgeZeroSolve hF a b s).continuousAt)
  let base : TailEdgeContinuous a b := ⟨fun s => tailEdgeZeroSolve a b F s,
    hbase.comp continuous_subtype_val⟩
  obtain ⟨v, hv, _⟩ := existsUnique_tailEdgeIntegralSolution hab hq hδ base
  let g : ℝ → ℝ := IccExtend hab.le (q * v : TailEdgeContinuous a b)
  have hg : Continuous g := (q * v).continuous.Icc_extend'
  let u : ℝ → ℝ := fun s => tailEdgeZeroSolve a b F s + tailEdgeZeroSolve a b g s
  have hvu (s : ℝ) (hs : s ∈ Icc a b) : v ⟨s, hs⟩ = u s :=
    congrArg (fun v : TailEdgeContinuous a b => v ⟨s, hs⟩) hv
  have hD (s : ℝ) := (hasDerivAt_tailEdgeZeroSolve hF a b s).add
    (hasDerivAt_tailEdgeZeroSolve hg a b s)
  have hderiv : deriv u = fun s => deriv (tailEdgeZeroSolve a b F) s +
      deriv (tailEdgeZeroSolve a b g) s := by
    funext s
    rw [(hasDerivAt_tailEdgeZeroSolve hF a b s).deriv, (hasDerivAt_tailEdgeZeroSolve hg a b s).deriv]
    exact (hD s).deriv
  have hDD (s : ℝ) : HasDerivAt (deriv u) (-F s + -g s) s := by
    rw [hderiv]
    exact (hasDerivAt_deriv_tailEdgeZeroSolve hF hab s).add
      (hasDerivAt_deriv_tailEdgeZeroSolve hg hab s)
  have hu : ContDiff ℝ 1 u := contDiff_one_iff_deriv.mpr
    ⟨fun s => (hD s).differentiableAt,
      continuous_iff_continuousAt.mpr (fun s => (hDD s).continuousAt)⟩
  have ha : u a = 0 := by
    simp only [u, (tailEdgeZeroSolve_endpoints a b F).1, (tailEdgeZeroSolve_endpoints a b g).1, add_zero]
  have hb : u b = 0 := by
    simp only [u, (tailEdgeZeroSolve_endpoints a b F).2, (tailEdgeZeroSolve_endpoints a b g).2, add_zero]
  have hode (s : ℝ) (hs : s ∈ Icc a b) :
      HasDerivAt (deriv u) (-(density s * f s + Λ * density s * u s)) s := by
    have he : g s = Λ * density s * u s := by
      dsimp only [g]
      rw [IccExtend_of_mem hab.le (q * v) hs, ContinuousMap.mul_apply, hvu]
      rfl
    simpa only [F, he, neg_add_rev, add_comm] using hDD s
  exact ⟨u, hu, ha, hb, hode, tailEdge_mass_bound hab hΛ hdensity hdensity₀ hf hu ha hb hode hsmall⟩

end ContinuousFlexibility.Radial
