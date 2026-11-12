import ContinuousFlexibility.Analysis.N07bPiecewiseCanonicalLift

/-! # Linearity of actual canonical source representatives -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open MeasureTheory ContinuousFlexibility.Statements

variable {S : PhysicalSpacesData} {K : CanonicalData S} {V : VolumeModelData S K}
  {z : AnnularState S × ℝ} {γ t : ℝ} {s : ℕ}

theorem n07b_canonicalSource_add_fields (f g : PolarPoint → ℝ) (m : ℕ) :
    canonicalSource S K z m (fun x => f x + g x) =
      fun p => canonicalSource S K z m f p + canonicalSource S K z m g p := by
  funext p
  dsimp only [canonicalSource]
  ring

theorem n07b_canonicalSource_const_mul_field (a : ℝ) (f : PolarPoint → ℝ) (m : ℕ) :
    canonicalSource S K z m (fun x => a * f x) =
      fun p => a * canonicalSource S K z m f p := by
  funext p
  dsimp only [canonicalSource]
  ring

/-- Addition is in the prescribed volume model, with actual L² representatives. -/
theorem n07b_canonicalSourceLift_add_ae
    {F G : V.level γ t s} {f g : PolarPoint → ℝ}
    (hF : ∀ m, (V.forget γ t s F m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] canonicalSource S K z m f)
    (hG : ∀ m, (V.forget γ t s G m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] canonicalSource S K z m g) :
    ∀ m, (V.forget γ t s (F + G) m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] canonicalSource S K z m (fun x => f x + g x) := by
  intro m
  rw [map_add, Pi.add_apply, n07b_canonicalSource_add_fields]
  filter_upwards [Lp.coeFn_add (V.forget γ t s F m) (V.forget γ t s G m), hF m, hG m]
    with p hp hfp hgp
  simpa only [Pi.add_apply, hfp, hgp] using hp

theorem n07b_canonicalSourceLift_smul_ae
    {F : V.level γ t s} {f : PolarPoint → ℝ}
    (hF : ∀ m, (V.forget γ t s F m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] canonicalSource S K z m f) (a : ℝ) :
    ∀ m, (V.forget γ t s (a • F) m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] canonicalSource S K z m (fun x => a * f x) := by
  intro m
  rw [map_smul, Pi.smul_apply, n07b_canonicalSource_const_mul_field]
  filter_upwards [Lp.coeFn_smul a (V.forget γ t s F m), hF m] with p hp hfp
  simpa only [Pi.smul_apply, smul_eq_mul, hfp] using hp

end ContinuousFlexibility.Analysis
