import ContinuousFlexibility.Radial.TailEdgePoissonComparison
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The exact outward flux matrix on one tail edge

The two Poisson heights solve the same homogeneous equation. Their endpoint
derivatives are given by the zero-potential Green formula, and conservation of
their Wronskian identifies the two off-diagonal entries.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory

/-- The bounded Poisson height has a classical representative on the full
closed edge, with endpoint derivative formulas in resistance coordinates. -/
theorem exists_tailEdgePoisson_classical_integral {a b : ℝ} (hab : a < b)
    {q : TailEdgeContinuous a b} (hq : ∀ s, 0 ≤ q s) (hδ : tailEdgeDiagonalSize hab q < 1)
    (right : Bool) :
    let l : ℝ → ℝ := if right then tailEdgeRightHeight a b else tailEdgeLeftHeight a b
    let slope : ℝ := if right then 1 / (b - a) else -(1 / (b - a))
    ∃ u : ℝ → ℝ,
      Differentiable ℝ u ∧ Differentiable ℝ (deriv u) ∧
      u a = l a ∧ u b = l b ∧
      (∀ s (hs : s ∈ Icc a b), HasDerivAt (deriv u) (-(q ⟨s, hs⟩ * u s)) s) ∧
      (∀ s ∈ Icc a b, l s ≤ u s ∧ u s ≤ l s / (1 - tailEdgeDiagonalSize hab q)) ∧
      deriv u a = slope + (∫ s in a..b, tailEdgeLeftHeight a b s * IccExtend hab.le q s * u s) ∧
      deriv u b = slope - (∫ s in a..b, tailEdgeRightHeight a b s * IccExtend hab.le q s * u s) ∧
      (∀ s ∈ Icc a b, u s = l s +
        ∫ t in a..b, tailEdgeGreen a b s t * IccExtend hab.le q t * u t) := by
  dsimp only
  let l : ℝ → ℝ := if right then tailEdgeRightHeight a b else tailEdgeLeftHeight a b
  let slope : ℝ := if right then 1 / (b - a) else -(1 / (b - a))
  obtain ⟨v, hv, hbound⟩ := exists_tailEdgePoisson_height hab hq hδ right
  let g : ℝ → ℝ := IccExtend hab.le (q * v : TailEdgeContinuous a b)
  have hg : Continuous g := (q * v).continuous.Icc_extend'
  let u : ℝ → ℝ := fun s => l s + tailEdgeZeroSolve a b g s
  have hvu (s : ℝ) (hs : s ∈ Icc a b) : v ⟨s, hs⟩ = u s := hv ⟨s, hs⟩
  have hL (s : ℝ) : HasDerivAt l slope s := by
    cases right
    · change HasDerivAt (fun x : ℝ => (b - x) / (b - a)) (-(1 / (b - a))) s
      convert ((hasDerivAt_const s b).sub (hasDerivAt_id s)).div_const (b - a) using 1
      · funext x
        rfl
      · ring
    · change HasDerivAt (fun x : ℝ => (x - a) / (b - a)) (1 / (b - a)) s
      convert ((hasDerivAt_id s).sub (hasDerivAt_const s a)).div_const (b - a) using 1
      · funext x
        rfl
      · ring
  have hD (s : ℝ) := (hL s).add (hasDerivAt_tailEdgeZeroSolve hg a b s)
  have hderiv : deriv u = fun s => slope + deriv (tailEdgeZeroSolve a b g) s := by
    funext s
    rw [(hasDerivAt_tailEdgeZeroSolve hg a b s).deriv]
    exact (hD s).deriv
  have hDD (s : ℝ) : HasDerivAt (deriv u) (-g s) s := by
    rw [hderiv]
    convert (hasDerivAt_const s slope).add (hasDerivAt_deriv_tailEdgeZeroSolve hg hab s) using 1
    exact (zero_add _).symm
  have hg_eq (s : ℝ) (hs : s ∈ Icc a b) : g s = IccExtend hab.le q s * u s := by
    dsimp only [g]
    rw [IccExtend_of_mem hab.le (q * v) hs, ContinuousMap.mul_apply, hvu,
      IccExtend_of_mem hab.le q hs]
  have hIntegral (e : ℝ → ℝ) :
      (∫ s in a..b, e s * g s) / (b - a) =
        ∫ s in a..b, (e s / (b - a)) * IccExtend hab.le q s * u s := by
    rw [div_eq_mul_inv, mul_comm, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hab.le]
    intro s hs
    change (b - a)⁻¹ * (e s * g s) = _
    rw [hg_eq s hs]
    ring
  have hends := tailEdgeZeroSolve_endpoints a b g
  have hflux := tailEdgeZeroSolve_endpoint_deriv hg a b
  refine ⟨u, fun s => (hD s).differentiableAt, fun s => (hDD s).differentiableAt,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change l a + tailEdgeZeroSolve a b g a = l a
    rw [hends.1, add_zero]
  · change l b + tailEdgeZeroSolve a b g b = l b
    rw [hends.2, add_zero]
  · intro s hs
    have h := hDD s
    rw [hg_eq s hs, IccExtend_of_mem hab.le q hs] at h
    exact h
  · intro s hs
    rw [← hvu s hs]
    exact hbound ⟨s, hs⟩
  · rw [hderiv]
    dsimp only
    rw [hflux.1]
    exact congrArg (slope + ·) (hIntegral (fun s => b - s))
  · rw [hderiv]
    dsimp only
    rw [hflux.2, neg_div, ← sub_eq_add_neg]
    exact congrArg (slope - ·) (hIntegral (fun s => s - a))
  · intro s hs
    change l s + tailEdgeZeroSolve a b g s = _
    rw [tailEdgeZeroSolve_eq_integral hg hs]
    congr 1
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hab.le]
    intro t ht
    dsimp only
    rw [hg_eq t ht]
    ring

/-- The classical Poisson height, retaining the endpoint-flux interface. -/
theorem exists_tailEdgePoisson_classical {a b : ℝ} (hab : a < b)
    {q : TailEdgeContinuous a b} (hq : ∀ s, 0 ≤ q s) (hδ : tailEdgeDiagonalSize hab q < 1)
    (right : Bool) :
    let l : ℝ → ℝ := if right then tailEdgeRightHeight a b else tailEdgeLeftHeight a b
    let slope : ℝ := if right then 1 / (b - a) else -(1 / (b - a))
    ∃ u : ℝ → ℝ,
      Differentiable ℝ u ∧ Differentiable ℝ (deriv u) ∧
      u a = l a ∧ u b = l b ∧
      (∀ s (hs : s ∈ Icc a b), HasDerivAt (deriv u) (-(q ⟨s, hs⟩ * u s)) s) ∧
      (∀ s ∈ Icc a b, l s ≤ u s ∧ u s ≤ l s / (1 - tailEdgeDiagonalSize hab q)) ∧
      deriv u a = slope + (∫ s in a..b, tailEdgeLeftHeight a b s * IccExtend hab.le q s * u s) ∧
      deriv u b = slope - (∫ s in a..b, tailEdgeRightHeight a b s * IccExtend hab.le q s * u s) := by
  obtain ⟨u, hu, hdu, ha, hb, hode, hbound, hleft, hright, _⟩ :=
    exists_tailEdgePoisson_classical_integral hab hq hδ right
  exact ⟨u, hu, hdu, ha, hb, hode, hbound, hleft, hright⟩

/-- The actual endpoint Poisson basis has the symmetric outward flux matrix
with the diagonal and off-diagonal integral formulas of the edge problem. -/
theorem exists_tailEdgeFluxMatrix {a b : ℝ} (hab : a < b)
    {q : TailEdgeContinuous a b} (hq : ∀ s, 0 ≤ q s) (hδ : tailEdgeDiagonalSize hab q < 1) :
    ∃ u₀ u₁ : ℝ → ℝ,
      Differentiable ℝ u₀ ∧ Differentiable ℝ u₁ ∧
      u₀ a = 1 ∧ u₀ b = 0 ∧ u₁ a = 0 ∧ u₁ b = 1 ∧
      (∀ s (hs : s ∈ Icc a b), HasDerivAt (deriv u₀) (-(q ⟨s, hs⟩ * u₀ s)) s ∧
        HasDerivAt (deriv u₁) (-(q ⟨s, hs⟩ * u₁ s)) s) ∧
      (∀ s ∈ Icc a b,
        (tailEdgeLeftHeight a b s ≤ u₀ s ∧
          u₀ s ≤ tailEdgeLeftHeight a b s / (1 - tailEdgeDiagonalSize hab q)) ∧
        (tailEdgeRightHeight a b s ≤ u₁ s ∧
          u₁ s ≤ tailEdgeRightHeight a b s / (1 - tailEdgeDiagonalSize hab q))) ∧
      (let c := 1 / (b - a) + (∫ s in a..b, tailEdgeLeftHeight a b s * IccExtend hab.le q s * u₁ s);
       let d₀ := 1 / (b - a) - (∫ s in a..b, tailEdgeLeftHeight a b s * IccExtend hab.le q s * u₀ s);
       let d₁ := 1 / (b - a) - (∫ s in a..b, tailEdgeRightHeight a b s * IccExtend hab.le q s * u₁ s);
       ∀ x y : ℝ,
        let u : ℝ → ℝ := fun s => x * u₀ s + y * u₁ s;
        -deriv u a = d₀ * x - c * y ∧ deriv u b = -c * x + d₁ * y) := by
  obtain ⟨u₀, h₀, hD₀, ha₀, hb₀, hode₀, hbounds₀, hflux₀, _⟩ :=
    exists_tailEdgePoisson_classical hab hq hδ false
  obtain ⟨u₁, h₁, hD₁, ha₁, hb₁, hode₁, hbounds₁, hflux₁, hflux₁b⟩ :=
    exists_tailEdgePoisson_classical hab hq hδ true
  simp [tailEdgeLeftHeight, tailEdgeRightHeight, (sub_pos.mpr hab).ne'] at ha₀ hb₀ ha₁ hb₁
  let W : ℝ → ℝ := fun s => deriv u₀ s * u₁ s - u₀ s * deriv u₁ s
  have hWdiff : Differentiable ℝ W := (hD₀.mul h₁).sub (h₀.mul hD₁)
  have hWzero (s : ℝ) (hs : s ∈ Icc a b) : deriv W s = 0 := by
    have h := ((hode₀ s hs).mul (h₁ s).hasDerivAt).sub
      ((h₀ s).hasDerivAt.mul (hode₁ s hs))
    exact h.deriv.trans (by ring)
  obtain ⟨s, hs, hW⟩ :=
    exists_deriv_eq_slope W hab hWdiff.continuous.continuousOn hWdiff.differentiableOn
  rw [hWzero s ⟨hs.1.le, hs.2.le⟩] at hW
  have hconst : W a = W b := by
    have he := (eq_div_iff (sub_pos.mpr hab).ne').mp hW
    linarith
  have hcross : deriv u₀ b = -deriv u₁ a := by
    simpa [W, ha₀, hb₀, ha₁, hb₁] using hconst.symm
  refine ⟨u₀, u₁, h₀, h₁, ha₀, hb₀, ha₁, hb₁,
    fun s hs => ⟨hode₀ s hs, hode₁ s hs⟩,
    fun s hs => ⟨hbounds₀ s hs, hbounds₁ s hs⟩, ?_⟩
  simp only [Bool.false_eq_true, ite_false, ite_true] at hflux₀ hflux₁ hflux₁b
  dsimp only
  intro x y
  have h (s : ℝ) : deriv (fun t => x * u₀ t + y * u₁ t) s =
      x * deriv u₀ s + y * deriv u₁ s :=
    (((h₀ s).hasDerivAt.const_mul x).add ((h₁ s).hasDerivAt.const_mul y)).deriv
  constructor
  · rw [h a, hflux₀, hflux₁]
    ring
  · rw [h b, hcross, hflux₁, hflux₁b]
    ring

end ContinuousFlexibility.Radial
