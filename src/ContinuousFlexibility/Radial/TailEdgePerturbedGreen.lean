module

public import ContinuousFlexibility.Radial.TailEdgeZeroGreen
public import ContinuousFlexibility.Radial.TailEdgeMassResistance
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Topology.Order.ProjIcc

/-!
# The perturbed Dirichlet problem on one resistance edge

The positive potential times the zero-potential Green operator contracts
the sup norm with constant equal to the diagonal integral. The unique
integral solution satisfies the differential equation and the prescribed
endpoint values.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped NNReal

abbrev TailEdgeContinuous (a b : ℝ) := C(Icc a b, ℝ)

private theorem continuous_tailEdgeGreen_right (a b s : ℝ) :
    Continuous (tailEdgeGreen a b s) := by
  unfold tailEdgeGreen
  exact (((continuous_const.min continuous_id).sub continuous_const).mul
    (continuous_const.sub (continuous_const.max continuous_id))).div_const _

private theorem continuous_tailEdgeGreen_diag (a b : ℝ) :
    Continuous (fun t => tailEdgeGreen a b t t) := by
  simp only [tailEdgeGreen_self]
  exact (((continuous_id.sub continuous_const).mul
    (continuous_const.sub continuous_id)).div_const _)

theorem tailEdgeGreen_le_diagonal {a b s t : ℝ} (hab : a < b)
    (ht : t ∈ Icc a b) :
    tailEdgeGreen a b s t ≤ tailEdgeGreen a b t t := by
  unfold tailEdgeGreen
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hab.le)
  rcases le_total s t with hst | hts
  · simpa only [min_eq_left hst, max_eq_right hst, min_self, max_self] using
      mul_le_mul_of_nonneg_right (sub_le_sub_right hst a) (sub_nonneg.mpr ht.2)
  · simpa only [min_eq_right hts, max_eq_left hts, min_self, max_self] using
      mul_le_mul_of_nonneg_left (sub_le_sub_left hts b) (sub_nonneg.mpr ht.1)

/-- The integral which controls one insertion of the potential into the Green kernel. -/
def tailEdgeDiagonalSize {a b : ℝ} (hab : a < b) (q : TailEdgeContinuous a b) : ℝ :=
  ∫ t in a..b, tailEdgeGreen a b t t * IccExtend hab.le q t

private theorem tailEdgeDiagonalSize_nonneg {a b : ℝ} (hab : a < b)
    {q : TailEdgeContinuous a b} (hq : ∀ t, 0 ≤ q t) :
    0 ≤ tailEdgeDiagonalSize hab q := by
  apply intervalIntegral.integral_nonneg hab.le
  intro t ht
  rw [IccExtend_of_mem hab.le q ht]
  exact mul_nonneg (tailEdgeGreen_nonneg hab ht ht) (hq ⟨t, ht⟩)

private theorem continuous_tailEdgeZeroSolve {g : ℝ → ℝ} (hg : Continuous g)
    (a b : ℝ) : Continuous (tailEdgeZeroSolve a b g) :=
  continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_tailEdgeZeroSolve hg a b x).continuousAt

private def tailEdgeZeroOn {a b : ℝ} (g : ℝ → ℝ) (hg : Continuous g) :
    TailEdgeContinuous a b :=
  ⟨fun s => tailEdgeZeroSolve a b g s, (continuous_tailEdgeZeroSolve hg a b).comp
    continuous_subtype_val⟩

/-- One Green step with the actual potential (q=Lambdaomega) on the edge. -/
def tailEdgeGreenAction {a b : ℝ} (hab : a < b)
    (q u : TailEdgeContinuous a b) : TailEdgeContinuous a b :=
  tailEdgeZeroOn (IccExtend hab.le (q * u)) (q * u).continuous.Icc_extend'

theorem tailEdgeGreenAction_apply {a b : ℝ} (hab : a < b)
    (q u : TailEdgeContinuous a b) (s : Icc a b) :
    tailEdgeGreenAction hab q u s =
      ∫ t in a..b, tailEdgeGreen a b s t * IccExtend hab.le (q * u) t :=
  tailEdgeZeroSolve_eq_integral (q * u).continuous.Icc_extend' s.property

private theorem tailEdgeGreenAction_sub {a b : ℝ} (hab : a < b)
    (q u v : TailEdgeContinuous a b) :
    tailEdgeGreenAction hab q (u - v) = tailEdgeGreenAction hab q u - tailEdgeGreenAction hab q v := by
  ext s
  change tailEdgeGreenAction hab q (u - v) s =
    tailEdgeGreenAction hab q u s - tailEdgeGreenAction hab q v s
  rw [tailEdgeGreenAction_apply, tailEdgeGreenAction_apply, tailEdgeGreenAction_apply]
  have heq : (fun t => tailEdgeGreen a b s t * IccExtend hab.le (q * (u - v)) t) =
      (fun t => tailEdgeGreen a b s t * IccExtend hab.le (q * u) t -
        tailEdgeGreen a b s t * IccExtend hab.le (q * v) t) := by
    funext t
    simp only [IccExtend_apply, ContinuousMap.mul_apply, ContinuousMap.sub_apply, mul_sub]
  rw [heq]
  exact intervalIntegral.integral_sub
    (((continuous_tailEdgeGreen_right a b s).mul (q * u).continuous.Icc_extend').intervalIntegrable a b)
    (((continuous_tailEdgeGreen_right a b s).mul (q * v).continuous.Icc_extend').intervalIntegrable a b)

theorem norm_tailEdgeGreenAction_le {a b : ℝ} (hab : a < b)
    {q : TailEdgeContinuous a b} (hq : ∀ t, 0 ≤ q t) (u : TailEdgeContinuous a b) :
    ‖tailEdgeGreenAction hab q u‖ ≤ tailEdgeDiagonalSize hab q * ‖u‖ := by
  apply (ContinuousMap.norm_le (tailEdgeGreenAction hab q u)
    (mul_nonneg (tailEdgeDiagonalSize_nonneg hab hq) (norm_nonneg u))).mpr
  intro s
  rw [tailEdgeGreenAction_apply]
  let f : ℝ → ℝ := fun t => tailEdgeGreen a b s t * IccExtend hab.le (q * u) t
  let w : ℝ → ℝ := fun t => tailEdgeGreen a b t t * IccExtend hab.le q t
  change ‖∫ t in a..b, f t‖ ≤ (∫ t in a..b, w t) * ‖u‖
  have hf : Continuous f :=
    (continuous_tailEdgeGreen_right a b s).mul (q * u).continuous.Icc_extend'
  have hw : Continuous w := (continuous_tailEdgeGreen_diag a b).mul q.continuous.Icc_extend'
  rw [← intervalIntegral.integral_mul_const]
  refine (intervalIntegral.norm_integral_le_integral_norm hab.le).trans
    (intervalIntegral.integral_mono_on hab.le (hf.norm.intervalIntegrable a b)
      ((hw.mul continuous_const).intervalIntegrable a b) ?_)
  intro t ht
  have htq := hq ⟨t, ht⟩
  have hkn := tailEdgeGreen_nonneg hab s.property ht
  have hdn := tailEdgeGreen_nonneg hab ht ht
  have hu : |u ⟨t, ht⟩| ≤ ‖u‖ := by
    simpa only [Real.norm_eq_abs] using u.norm_coe_le_norm ⟨t, ht⟩
  dsimp only [f, w]
  rw [IccExtend_of_mem hab.le (q * u) ht, IccExtend_of_mem hab.le q ht, ContinuousMap.mul_apply,
    Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hkn, abs_of_nonneg htq]
  rw [← mul_assoc]
  exact mul_le_mul
    (mul_le_mul_of_nonneg_right (tailEdgeGreen_le_diagonal hab ht) htq)
    hu (abs_nonneg _) (mul_nonneg hdn htq)

/-- The Green iteration contracts with the actual diagonal integral. -/
theorem tailEdgeGreenStep_contracting {a b : ℝ} (hab : a < b)
    {q : TailEdgeContinuous a b} (hq : ∀ t, 0 ≤ q t) (hδ : tailEdgeDiagonalSize hab q < 1)
    (base : TailEdgeContinuous a b) :
    ContractingWith ⟨tailEdgeDiagonalSize hab q, tailEdgeDiagonalSize_nonneg hab hq⟩
      (fun u => base + tailEdgeGreenAction hab q u) := by
  refine ⟨?_, LipschitzWith.of_dist_le_mul (fun u v => ?_)⟩
  · exact_mod_cast hδ
  · rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← tailEdgeGreenAction_sub]
    exact norm_tailEdgeGreenAction_le hab hq (u - v)

/-- The actual perturbed integral equation has a unique continuous solution. -/
theorem existsUnique_tailEdgeIntegralSolution {a b : ℝ} (hab : a < b)
    {q : TailEdgeContinuous a b} (hq : ∀ t, 0 ≤ q t) (hδ : tailEdgeDiagonalSize hab q < 1)
    (base : TailEdgeContinuous a b) :
    ∃! u : TailEdgeContinuous a b, u = base + tailEdgeGreenAction hab q u := by
  let F : TailEdgeContinuous a b → TailEdgeContinuous a b := fun u =>
    base + tailEdgeGreenAction hab q u
  have hF := tailEdgeGreenStep_contracting hab hq hδ base
  let u := ContractingWith.fixedPoint F hF
  have hu : F u = u := hF.fixedPoint_isFixedPt
  refine ⟨u, hu.symm, fun v hv => ?_⟩
  exact hF.fixedPoint_unique hv.symm

private def tailEdgeAffine (a b left right s : ℝ) : ℝ :=
  (left * (b - s) + right * (s - a)) / (b - a)

private theorem hasDerivAt_tailEdgeAffine (a b left right s : ℝ) :
    HasDerivAt (tailEdgeAffine a b left right) ((right - left) / (b - a)) s := by
  have hL := ((hasDerivAt_const s b).sub (hasDerivAt_id s)).const_mul left
  have hR := ((hasDerivAt_id s).sub (hasDerivAt_const s a)).const_mul right
  convert ((hL.add hR).div_const (b - a)) using 1
  · funext x
    rfl
  · ring

/-- The integral solution gives an actual classical solution for every
continuous source and both prescribed boundary values. -/
theorem exists_tailEdge_perturbed_boundary {a b : ℝ} (hab : a < b)
    {q : TailEdgeContinuous a b} (hq : ∀ t, 0 ≤ q t) (hδ : tailEdgeDiagonalSize hab q < 1)
    {f : ℝ → ℝ} (hf : Continuous f) (left right : ℝ) :
    ∃ u : ℝ → ℝ, Differentiable ℝ u ∧ u a = left ∧ u b = right ∧
      ∀ s (hs : s ∈ Icc a b), HasDerivAt (deriv u) (-(f s + q ⟨s, hs⟩ * u s)) s := by
  let l := tailEdgeAffine a b left right
  have hL : Continuous l := continuous_iff_continuousAt.mpr
    (fun s => (hasDerivAt_tailEdgeAffine a b left right s).continuousAt)
  let base : TailEdgeContinuous a b :=
    ⟨fun s => l s + tailEdgeZeroSolve a b f s,
      (hL.add (continuous_tailEdgeZeroSolve hf a b)).comp continuous_subtype_val⟩
  obtain ⟨v, hv, _⟩ := existsUnique_tailEdgeIntegralSolution hab hq hδ base
  let g := IccExtend hab.le (q * v)
  have hg : Continuous g := (q * v).continuous.Icc_extend'
  let u : ℝ → ℝ := fun s => l s + tailEdgeZeroSolve a b f s + tailEdgeZeroSolve a b g s
  have hvu (s : Icc a b) : v s = u s :=
    congrArg (fun v : TailEdgeContinuous a b => v s) hv
  have hD (s : ℝ) := (((hasDerivAt_tailEdgeAffine a b left right s).add
    (hasDerivAt_tailEdgeZeroSolve hf a b s)).add (hasDerivAt_tailEdgeZeroSolve hg a b s))
  refine ⟨u, fun s => (hD s).differentiableAt, ?_, ?_, fun s hs => ?_⟩
  · simp [u, l, tailEdgeAffine, (tailEdgeZeroSolve_endpoints a b f).1,
      (tailEdgeZeroSolve_endpoints a b g).1, (sub_pos.mpr hab).ne']
  · simp [u, l, tailEdgeAffine, (tailEdgeZeroSolve_endpoints a b f).2,
      (tailEdgeZeroSolve_endpoints a b g).2, (sub_pos.mpr hab).ne']
  · have hderiv (x : ℝ) : deriv u x =
        (right - left) / (b - a) + deriv (tailEdgeZeroSolve a b f) x +
          deriv (tailEdgeZeroSolve a b g) x := by
      rw [(hasDerivAt_tailEdgeZeroSolve hf a b x).deriv,
        (hasDerivAt_tailEdgeZeroSolve hg a b x).deriv]
      exact (hD x).deriv
    rw [funext hderiv]
    have he : g s = q ⟨s, hs⟩ * u s := by
      dsimp only [g]
      rw [IccExtend_of_mem hab.le (q * v) hs, ContinuousMap.mul_apply, hvu]
    convert (((hasDerivAt_const s ((right - left) / (b - a))).add
      (hasDerivAt_deriv_tailEdgeZeroSolve hf hab s)).add
      (hasDerivAt_deriv_tailEdgeZeroSolve hg hab s)) using 1
    rw [he]
    ring

end ContinuousFlexibility.Radial
