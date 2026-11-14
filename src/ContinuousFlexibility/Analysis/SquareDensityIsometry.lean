module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# An actual isometry for a positive square density

Multiplication by a positive measurable function is an isometry between
the two appropriate L2 spaces. No boundedness of that function or of its
reciprocal is required: the measure changes with its square.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace

set_option backward.isDefEq.respectTransparency false

/-- The measure with the square of a real amplitude as density. -/
def squareDensityMeasure (μ : Measure ℝ) (a : ℝ → ℝ) : Measure ℝ :=
  μ.withDensity (fun x => ENNReal.ofReal (a x ^ 2))

theorem squareDensity_absolutelyContinuous (μ : Measure ℝ) {a : ℝ → ℝ}
    (ha : Measurable a) (hpos : ∀ x, 0 < a x) :
    μ ≪ squareDensityMeasure μ a := by
  apply withDensity_absolutelyContinuous' (ha.pow_const 2).ennreal_ofReal.aemeasurable
  exact Filter.Eventually.of_forall (fun x =>
    ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (hpos x))))

theorem squareDensity_ae_eq (μ : Measure ℝ) {a : ℝ → ℝ}
    (ha : Measurable a) (hpos : ∀ x, 0 < a x) {f g : ℝ → ℝ}
    (hfg : f =ᵐ[squareDensityMeasure μ a] g) : f =ᵐ[μ] g :=
  (squareDensity_absolutelyContinuous μ ha hpos).ae_eq hfg

theorem squareDensity_memLp_iff (μ : Measure ℝ) {a : ℝ → ℝ}
    (ha : Measurable a) (hpos : ∀ x, 0 < a x) (f : ℝ → ℝ) :
    MemLp f 2 (squareDensityMeasure μ a) ↔ MemLp (fun x => a x * f x) 2 μ := by
  have hd := (ha.pow_const 2).ennreal_ofReal
  have hfinite : ∀ᵐ x ∂μ, ENNReal.ofReal (a x ^ 2) < (∞ : ℝ≥0∞) := by simp
  constructor
  · intro hf
    have hfm := AEStronglyMeasurable.mono_ac (squareDensity_absolutelyContinuous μ ha hpos)
      hf.aestronglyMeasurable
    apply (memLp_two_iff_integrable_sq (ha.aestronglyMeasurable.mul hfm)).mpr
    have h := (integrable_withDensity_iff_integrable_smul' hd hfinite).mp hf.integrable_sq
    convert h using 1
    funext x
    rw [ENNReal.toReal_ofReal (sq_nonneg (a x))]
    simp only [smul_eq_mul, Pi.mul_apply]
    ring
  · intro hf
    have hfm : AEStronglyMeasurable f μ := by
      have h := ha.inv.aestronglyMeasurable.mul hf.aestronglyMeasurable
      convert h using 1
      funext x
      exact (inv_mul_cancel_left₀ (hpos x).ne' (f x)).symm
    have hfd : AEStronglyMeasurable f (squareDensityMeasure μ a) :=
      AEStronglyMeasurable.mono_ac (withDensity_absolutelyContinuous μ _) hfm
    apply (memLp_two_iff_integrable_sq hfd).mpr
    apply (integrable_withDensity_iff_integrable_smul' hd hfinite).mpr
    convert hf.integrable_sq using 1
    funext x
    rw [ENNReal.toReal_ofReal (sq_nonneg (a x))]
    simp only [smul_eq_mul, Pi.mul_apply]
    ring

private theorem realL2_norm_sq {μ : Measure ℝ} (f : Lp ℝ 2 μ) :
    ‖f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext x
  simp only [RCLike.inner_apply, conj_trivial]
  ring

private theorem realToLp_norm_sq {μ : Measure ℝ} {f : ℝ → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [realL2_norm_sq]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

/-- Multiplication by the amplitude, defined on L2 classes. -/
def squareDensityIsometry (μ : Measure ℝ) {a : ℝ → ℝ}
    (ha : Measurable a) (hpos : ∀ x, 0 < a x) :
    Lp ℝ 2 (squareDensityMeasure μ a) →ₗᵢ[ℝ] Lp ℝ 2 μ where
  toFun u := ((squareDensity_memLp_iff μ ha hpos u).mp (Lp.memLp u)).toLp _
  map_add' u v := by
    apply Lp.ext
    filter_upwards
      [((squareDensity_memLp_iff μ ha hpos
          ((u + v : Lp ℝ 2 (squareDensityMeasure μ a)) : ℝ → ℝ)).mp (Lp.memLp (u + v))).coeFn_toLp,
        ((squareDensity_memLp_iff μ ha hpos u).mp (Lp.memLp u)).coeFn_toLp,
        ((squareDensity_memLp_iff μ ha hpos v).mp (Lp.memLp v)).coeFn_toLp,
        Lp.coeFn_add
          (((squareDensity_memLp_iff μ ha hpos u).mp (Lp.memLp u)).toLp _)
          (((squareDensity_memLp_iff μ ha hpos v).mp (Lp.memLp v)).toLp _),
        squareDensity_ae_eq μ ha hpos (Lp.coeFn_add u v)] with x hx hu hv hs hadd
    simp only [Pi.add_apply] at hs hadd
    rw [hx, hs, hu, hv, hadd]
    ring
  map_smul' r u := by
    apply Lp.ext
    filter_upwards
      [((squareDensity_memLp_iff μ ha hpos
          ((r • u : Lp ℝ 2 (squareDensityMeasure μ a)) : ℝ → ℝ)).mp (Lp.memLp (r • u))).coeFn_toLp,
        ((squareDensity_memLp_iff μ ha hpos u).mp (Lp.memLp u)).coeFn_toLp,
        Lp.coeFn_smul r (((squareDensity_memLp_iff μ ha hpos u).mp (Lp.memLp u)).toLp _),
        squareDensity_ae_eq μ ha hpos (Lp.coeFn_smul r u)] with x hx hu hs hsmul
    simp only [Pi.smul_apply, smul_eq_mul] at hs hsmul
    simp only [RingHom.id_apply]
    rw [hx, hs, hu, hsmul]
    ring
  norm_map' u := by
    have ht := realToLp_norm_sq ((squareDensity_memLp_iff μ ha hpos u).mp (Lp.memLp u))
    have hu := realL2_norm_sq u
    change ‖u‖ ^ 2 = ∫ x, u x ^ 2 ∂(μ.withDensity (fun x => ENNReal.ofReal (a x ^ 2))) at hu
    rw [integral_withDensity_eq_integral_toReal_smul
      (ha.pow_const 2).ennreal_ofReal (by simp)] at hu
    simp only [ENNReal.toReal_ofReal (sq_nonneg (a _)), smul_eq_mul] at hu
    have hi : (∫ x, (a x * u x) ^ 2 ∂μ) = ∫ x, a x ^ 2 * u x ^ 2 ∂μ := by
      congr 1
      funext x
      ring
    rw [hi] at ht
    change ‖((squareDensity_memLp_iff μ ha hpos u).mp (Lp.memLp u)).toLp _‖ = ‖u‖
    nlinarith [norm_nonneg u,
      norm_nonneg (((squareDensity_memLp_iff μ ha hpos u).mp (Lp.memLp u)).toLp _)]

theorem squareDensityIsometry_ae (μ : Measure ℝ) {a : ℝ → ℝ}
    (ha : Measurable a) (hpos : ∀ x, 0 < a x)
    (u : Lp ℝ 2 (squareDensityMeasure μ a)) :
    squareDensityIsometry μ ha hpos u =ᵐ[μ] fun x => a x * u x :=
  ((squareDensity_memLp_iff μ ha hpos u).mp (Lp.memLp u)).coeFn_toLp

theorem squareDensityIsometry_surjective (μ : Measure ℝ) {a : ℝ → ℝ}
    (ha : Measurable a) (hpos : ∀ x, 0 < a x) :
    Function.Surjective (squareDensityIsometry μ ha hpos) := by
  intro f
  let g : ℝ → ℝ := fun x => f x / a x
  have hfg : (fun x => a x * g x) = f := by
    funext x
    dsimp only [g]
    field_simp [(hpos x).ne']
  have hg : MemLp g 2 (squareDensityMeasure μ a) := by
    apply (squareDensity_memLp_iff μ ha hpos g).mpr
    rw [hfg]
    exact Lp.memLp f
  refine ⟨hg.toLp g, ?_⟩
  apply Lp.ext
  filter_upwards [squareDensityIsometry_ae μ ha hpos (hg.toLp g),
    squareDensity_ae_eq μ ha hpos hg.coeFn_toLp] with x hx hgx
  rw [hx, hgx]
  exact congrFun hfg x

/-- The square-density change is a genuine surjective linear isometry. -/
def squareDensityEquiv (μ : Measure ℝ) {a : ℝ → ℝ}
    (ha : Measurable a) (hpos : ∀ x, 0 < a x) :
    Lp ℝ 2 (squareDensityMeasure μ a) ≃ₗᵢ[ℝ] Lp ℝ 2 μ :=
  LinearIsometryEquiv.ofSurjective (squareDensityIsometry μ ha hpos)
    (squareDensityIsometry_surjective μ ha hpos)

theorem squareDensityEquiv_ae (μ : Measure ℝ) {a : ℝ → ℝ}
    (ha : Measurable a) (hpos : ∀ x, 0 < a x)
    (u : Lp ℝ 2 (squareDensityMeasure μ a)) :
    squareDensityEquiv μ ha hpos u =ᵐ[μ] fun x => a x * u x :=
  squareDensityIsometry_ae μ ha hpos u

theorem squareDensityEquiv_symm_ae (μ : Measure ℝ) {a : ℝ → ℝ}
    (ha : Measurable a) (hpos : ∀ x, 0 < a x) (f : Lp ℝ 2 μ) :
    (squareDensityEquiv μ ha hpos).symm f =ᵐ[μ] fun x => f x / a x := by
  have h := squareDensityEquiv_ae μ ha hpos ((squareDensityEquiv μ ha hpos).symm f)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  filter_upwards [h] with x hx
  apply (eq_div_iff (hpos x).ne').mpr
  exact (mul_comm _ _).trans hx.symm

end ContinuousFlexibility.Analysis
