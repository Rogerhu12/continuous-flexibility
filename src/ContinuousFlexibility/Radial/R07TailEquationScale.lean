import ContinuousFlexibility.Radial.R07NaturalLineNormalization
import ContinuousFlexibility.Radial.R07NaturalTailScale

/-!
# Scalar invariance of the normalized R06 natural line

Multiplying the density by a positive constant scales both terms in the
natural equation and its weighted measure.  The normalized entrance slope
is therefore unchanged, by the actual natural-line uniqueness in R06.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

theorem deepTailMeasure_scale {T S : Statements.DeepTailData}
    (he : S.entrance = T.entrance) (hb : S.endpoint = T.endpoint)
    {scale : ℝ} (hs : 0 ≤ scale)
    (hp : EqOn S.p (fun x => scale * T.p x) (Ioo T.entrance T.endpoint)) :
    Statements.deepTailMeasure S = ENNReal.ofReal scale • Statements.deepTailMeasure T := by
  unfold Statements.deepTailMeasure
  rw [he, hb]
  calc
    _ = (volume.restrict (Ioo T.entrance T.endpoint)).withDensity
        (ENNReal.ofReal scale • (fun x => ENNReal.ofReal (T.p x))) := by
      apply withDensity_congr_ae
      filter_upwards [ae_restrict_mem isOpen_Ioo.measurableSet] with x hx
      simp only [Pi.smul_apply, smul_eq_mul, hp hx, ENNReal.ofReal_mul hs]
    _ = _ := withDensity_smul' _ _ ENNReal.ofReal_ne_top

theorem memLp_deepTailMeasure_scale_iff {T S : Statements.DeepTailData}
    (he : S.entrance = T.entrance) (hb : S.endpoint = T.endpoint)
    {scale : ℝ} (hs : 0 < scale)
    (hp : EqOn S.p (fun x => scale * T.p x) (Ioo T.entrance T.endpoint))
    (u : ℝ → ℝ) :
    MemLp u 2 (Statements.deepTailMeasure S) ↔ MemLp u 2 (Statements.deepTailMeasure T) := by
  have hforward := deepTailMeasure_scale he hb hs.le hp
  have hpinv : EqOn T.p (fun x => scale⁻¹ * S.p x) (Ioo S.entrance S.endpoint) := by
    intro x hx
    have hx' : x ∈ Ioo T.entrance T.endpoint := by simpa only [he, hb] using hx
    dsimp only
    rw [hp hx', ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
  have hreverse := deepTailMeasure_scale he.symm hb.symm (inv_pos.mpr hs).le hpinv
  constructor
  · intro hu
    rw [hreverse]
    exact hu.smul_measure ENNReal.ofReal_ne_top
  · intro hu
    rw [hforward]
    exact hu.smul_measure ENNReal.ofReal_ne_top

theorem tailNaturalEquation_scale_iff {T S : Statements.DeepTailData}
    (he : S.entrance = T.entrance) (hb : S.endpoint = T.endpoint) (hΛ : S.Λ = T.Λ)
    {scale : ℝ} (hs : 0 < scale)
    (hp : EqOn S.p (fun x => scale * T.p x) (Ioo T.entrance T.endpoint))
    (u : ℝ → ℝ) :
    Statements.TailNaturalEquation S u ↔ Statements.TailNaturalEquation T u := by
  have hode (x : ℝ) (hx : x ∈ Ioo T.entrance T.endpoint) :
      deriv (fun y => S.p y * deriv u y) x + S.Λ * S.p x * u x =
        scale * (deriv (fun y => T.p y * deriv u y) x + T.Λ * T.p x * u x) := by
    have hflux : (fun y => S.p y * deriv u y) =ᶠ[𝓝 x]
        fun y => scale * (T.p y * deriv u y) := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      dsimp only
      rw [hp hy]
      ring
    rw [hflux.deriv_eq, deriv_const_mul_field, hΛ, hp hx]
    ring
  have hmem := memLp_deepTailMeasure_scale_iff he hb hs hp u
  unfold Statements.TailNaturalEquation
  rw [he, hb, hmem]
  constructor
  · rintro ⟨hu, huOn, huLp, hEq⟩
    refine ⟨hu, huOn, huLp, fun x hx => ?_⟩
    have hz : scale * (deriv (fun y => T.p y * deriv u y) x + T.Λ * T.p x * u x) = 0 :=
      (hode x hx).symm.trans (hEq x hx)
    exact (mul_eq_zero.mp hz).resolve_left hs.ne'
  · rintro ⟨hu, huOn, huLp, hEq⟩
    refine ⟨hu, huOn, huLp, fun x hx => ?_⟩
    rw [hode x hx, hEq x hx, mul_zero]

/-- A positive density scaling leaves the normalized natural entrance slope
exactly unchanged, not merely projectively equivalent. -/
theorem tailNatural_normalized_deriv_scale {T S : Statements.DeepTailData}
    (he : S.entrance = T.entrance) (hb : S.endpoint = T.endpoint) (hΛ : S.Λ = T.Λ)
    {scale : ℝ} (hs : 0 < scale)
    (hp : EqOn S.p (fun x => scale * T.p x) (Ioo T.entrance T.endpoint))
    (hgap : T.entrance < T.endpoint) (hline : Statements.TailNaturalLineAndKernel T)
    {u v : ℝ → ℝ} (hu : Statements.TailNaturalEquation T u) (hu₀ : u T.entrance = 1)
    (hv : Statements.TailNaturalEquation S v) (hv₀ : v S.entrance = 1) :
    deriv v S.entrance = deriv u T.entrance := by
  have hv' := (tailNaturalEquation_scale_iff he hb hΛ hs hp v).mp hv
  have hv₀' : v T.entrance = 1 := by simpa only [he] using hv₀
  simpa only [he] using (tailNaturalLine_normalized_unique hgap hline hu hu₀ hv' hv₀').2

end ContinuousFlexibility.Radial
