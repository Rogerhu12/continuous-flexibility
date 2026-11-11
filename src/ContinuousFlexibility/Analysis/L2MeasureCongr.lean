import ContinuousFlexibility.Analysis.SquareDensityIsometry
import ContinuousFlexibility.Analysis.CoordinateL2Isometry

/-!
# Exact changes of measure in L2

Equality of measures transports representatives, norms and actual integral
kernels. The equality is eliminated in the generic proofs before any
physical profile data are substituted.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory

def l2MeasureCongr {μ ν : Measure ℝ} (h : μ = ν) :
    Lp ℝ 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 ν := by
  subst ν
  exact LinearIsometryEquiv.refl ℝ _

theorem l2MeasureCongr_ae {μ ν : Measure ℝ} (h : μ = ν) (f : Lp ℝ 2 μ) :
    l2MeasureCongr h f =ᵐ[ν] f := by
  subst ν
  exact Filter.Eventually.of_forall (fun _ => rfl)

theorem ae_eq_of_measure_eq {μ ν : Measure ℝ} (h : μ = ν) {f g : ℝ → ℝ}
    (hfg : f =ᵐ[μ] g) : f =ᵐ[ν] g := by
  rw [← h]
  exact hfg

/-- A generic density change after equality of measures. The equality
is eliminated before proving the representative formula. -/
def squareDensityMeasureEquiv {μ ν : Measure ℝ} {a : ℝ → ℝ}
    (h : ν = squareDensityMeasure μ a) (ha : Measurable a) (hpos : ∀ x, 0 < a x) :
    Lp ℝ 2 ν ≃ₗᵢ[ℝ] Lp ℝ 2 μ :=
  (l2MeasureCongr h).trans (squareDensityEquiv μ ha hpos)

theorem squareDensityMeasureEquiv_ae {μ ν : Measure ℝ} {a : ℝ → ℝ}
    (h : ν = squareDensityMeasure μ a) (ha : Measurable a) (hpos : ∀ x, 0 < a x)
    (f : Lp ℝ 2 ν) :
    squareDensityMeasureEquiv h ha hpos f =ᵐ[μ] fun x => a x * f x := by
  subst ν
  exact squareDensityEquiv_ae μ ha hpos f

/-- Conjugation of an actual L2 operator by equality of its measures. -/
def l2OperatorMeasureCongr {μ ν : Measure ℝ} (h : μ = ν)
    (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  (l2MeasureCongr h).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (R.comp (l2MeasureCongr h).symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem norm_l2OperatorMeasureCongr {μ ν : Measure ℝ} (h : μ = ν)
    (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) : ‖l2OperatorMeasureCongr h R‖ = ‖R‖ := by
  subst ν
  have he : l2OperatorMeasureCongr (rfl : μ = μ) R = R := by
    apply ContinuousLinearMap.ext
    intro f
    rfl
  rw [he]

theorem l2OperatorMeasureCongr_kernel {μ ν : Measure ℝ} (h : μ = ν)
    (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (K : ℝ → ℝ → ℝ)
    (hR : ∀ f : Lp ℝ 2 μ, (R f : ℝ → ℝ) =ᵐ[μ] fun x => ∫ y, K x y * f y ∂μ)
    (f : Lp ℝ 2 ν) :
    (l2OperatorMeasureCongr h R f : ℝ → ℝ) =ᵐ[ν] fun x => ∫ y, K x y * f y ∂ν := by
  subst ν
  exact hR f

/-- Representative formulas compose without expanding the implementation
of either isometry. -/
theorem l2Equiv_trans_mul_ae {μ ν κ : Measure ℝ}
    (E : Lp ℝ 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 ν) (F : Lp ℝ 2 ν ≃ₗᵢ[ℝ] Lp ℝ 2 κ)
    (f : Lp ℝ 2 μ) (a p : ℝ → ℝ)
    (hE : (E f : ℝ → ℝ) =ᵐ[κ] p)
    (hF : (F (E f) : ℝ → ℝ) =ᵐ[κ] fun x => a x * E f x) :
    ((E.trans F) f : ℝ → ℝ) =ᵐ[κ] fun x => a x * p x := by
  filter_upwards [hE, hF] with x hx hy
  exact hy.trans (congrArg (fun t => a x * t) hx)

/-- Explicit function fields keep compositions of measure-cast isometries
from unfolding their equality proofs during representative calculations. -/
def l2EquivCompose {μ ν κ : Measure ℝ}
    (E : Lp ℝ 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 ν) (F : Lp ℝ 2 ν ≃ₗᵢ[ℝ] Lp ℝ 2 κ) :
    Lp ℝ 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 κ where
  toFun := fun f => F (E f)
  invFun := fun f => E.symm (F.symm f)
  left_inv := fun f => (congrArg E.symm (F.symm_apply_apply (E f))).trans (E.symm_apply_apply f)
  right_inv := fun f => (congrArg F (E.apply_symm_apply (F.symm f))).trans (F.apply_symm_apply f)
  map_add' := by intro f g; rw [map_add, map_add]
  map_smul' := by intro c f; rw [map_smul, map_smul, RingHom.id_apply]
  norm_map' := fun f => (F.norm_map (E f)).trans (E.norm_map f)

theorem l2EquivCompose_apply {μ ν κ : Measure ℝ}
    (E : Lp ℝ 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 ν) (F : Lp ℝ 2 ν ≃ₗᵢ[ℝ] Lp ℝ 2 κ)
    (f : Lp ℝ 2 μ) : l2EquivCompose E F f = F (E f) := rfl

/-- An existence certificate exposes the exact composition formula
without reducing concrete equality casts hidden inside the factors. -/
theorem exists_l2EquivCompose_apply {μ ν κ : Measure ℝ}
    (E : Lp ℝ 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 ν) (F : Lp ℝ 2 ν ≃ₗᵢ[ℝ] Lp ℝ 2 κ) :
    ∃ H : Lp ℝ 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 κ, ∀ f, H f = F (E f) :=
  ⟨l2EquivCompose E F, l2EquivCompose_apply E F⟩

/-- Preserve an isometry together with its equality specification while
keeping its concrete measure casts out of later function reduction. -/
def l2EquivSeal {μ ν : Measure ℝ} (E : Lp ℝ 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 ν) :
    Lp ℝ 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 ν :=
  Classical.choose (show ∃ F : Lp ℝ 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 ν, F = E from ⟨E, rfl⟩)

theorem l2EquivSeal_eq {μ ν : Measure ℝ} (E : Lp ℝ 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 ν) :
    l2EquivSeal E = E :=
  Classical.choose_spec (show ∃ F : Lp ℝ 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 ν, F = E from ⟨E, rfl⟩)

end ContinuousFlexibility.Analysis

