module

public import ContinuousFlexibility.Radial.InnerLiouvillePoissonTransport
public import ContinuousFlexibility.Radial.InnerLiouvilleLeadingTransport
public import ContinuousFlexibility.Radial.InnerLocalizedWeights

/-!
# Actual weights commute with Liouville transport by pullback

Both sides below are the already constructed operators on their actual
Lp quotients. This lets the leading buffer keep its own cut weight and
its small local velocity, while the same remainder pays only its cell's
weight ratio.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff

variable (D : ReferenceData) {R s : ℝ → ℝ} {a b lam : ℝ}
  (hab : a ≤ b) (hlam : 0 < lam) (hR : ContDiff ℝ ∞ R)
  (hs : ContDiff ℝ ∞ s)
  (hp : ∀ x ∈ Icc a b, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x)
  (hcore : Ioo (R a) (R b) ⊆ radialCore D)
  (hw : ∀ x ∈ Icc a b, D.w (R x) = lam * s x ^ 2 * deriv R x)
  (U : ℝ) (hU : 0 ≤ U)
  (hv : ∀ x ∈ Icc a b, |deriv R x / R x| ≤ U)

theorem innerLiouvilleFieldLift_weight
    (W : ℝ → ℝ) (hW : Measurable W) (CW : ℝ) (hWC : ∀ r, |W r| ≤ CW)
    (f : Lp ℝ 2 volume) :
    innerWeightMultiplier (radialHilbertMeasure D) W hW CW hWC
      (innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv f) =
    innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv
      (innerWeightMultiplier volume (fun x => W (R x))
        (hW.comp hR.continuous.measurable) CW (fun x => hWC (R x)) f) := by
  let A := innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv
  let MW := innerWeightMultiplier (radialHilbertMeasure D) W hW CW hWC
  let MR := innerWeightMultiplier volume (fun x => W (R x))
    (hW.comp hR.continuous.measurable) CW (fun x => hWC (R x))
  have hlocal : (MW (A f) : ℝ → ℝ) =ᵐ[
      (radialHilbertMeasure D).restrict (Ioo (R a) (R b))] (A (MR f) : ℝ → ℝ) := by
    apply innerLiouvilleInterval_pushforward_ae D hab hlam hR hs hp hcore hw
      ((Lp.memLp (MW (A f))).restrict _).aestronglyMeasurable
      ((Lp.memLp (A (MR f))).restrict _).aestronglyMeasurable
    have hmul := innerLiouvilleInterval_pullback_ae D hab hlam hR hs hp hcore hw
      (ae_restrict_of_ae
        (innerWeightMultiplier_ae (radialHilbertMeasure D) W hW CW hWC (A f)))
    filter_upwards [hmul,
      innerLiouvilleFieldLift_pullback_ae D hab hlam hR hs hp hcore hw U hU hv f,
      innerLiouvilleFieldLift_pullback_ae D hab hlam hR hs hp hcore hw U hU hv (MR f),
      ae_restrict_of_ae (innerWeightMultiplier_ae volume (fun x => W (R x))
        (hW.comp hR.continuous.measurable) CW (fun x => hWC (R x)) f)] with
        x hmul' hleft hright hmodel
    change MW (A f) (R x) = A (MR f) (R x)
    rw [hmul', hleft, hright, hmodel]
    ring
  have hleft := innerWeightMultiplier_supported (radialHilbertMeasure D) W hW CW hWC
    (Ioo (R a) (R b)) (A f)
      (innerLiouvilleFieldLift_support_ae D hab hlam hR hs hp hcore hw U hU hv f)
  have hright := innerLiouvilleFieldLift_support_ae D hab hlam hR hs hp hcore hw U hU hv (MR f)
  apply Lp.ext
  filter_upwards [ae_imp_of_ae_restrict hlocal, hleft, hright] with r hlocal' hl hr
  by_cases hri : r ∈ Ioo (R a) (R b)
  · exact hlocal' hri
  · rw [hl hri, hr hri]

/-- The cell weight comparison is applied only on the supported model
field. No global condition number enters this transport estimate. -/
theorem innerLiouvilleFieldLift_weighted_cell_bound
    (W : ℝ → ℝ) (hW : Measurable W) (CW : ℝ) (hWC : ∀ r, |W r| ≤ CW)
    (f : Lp ℝ 2 volume)
    (hf : ∀ᵐ x ∂volume, x ∉ Ioo a b → f x = 0)
    {B : ℝ} (hlocal : ∀ x ∈ Ioo a b, |W (R x)| ≤ B) :
    ‖innerWeightMultiplier (radialHilbertMeasure D) W hW CW hWC
      (innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv f)‖ ≤
        (Real.sqrt 12 * U) * B * ‖f‖ := by
  rw [innerLiouvilleFieldLift_weight D hab hlam hR hs hp hcore hw U hU hv]
  have hinput := innerWeightMultiplier_norm_le_on_support volume (fun x => W (R x))
    (hW.comp hR.continuous.measurable) CW (fun x => hWC (R x)) (Ioo a b) f hf hlocal
  calc
    _ ≤ (Real.sqrt 12 * U) *
        ‖innerWeightMultiplier volume (fun x => W (R x))
          (hW.comp hR.continuous.measurable) CW (fun x => hWC (R x)) f‖ :=
      innerLiouvilleFieldLift_norm_apply_le D hab hlam hR hs hp hcore hw U hU hv _
    _ ≤ (Real.sqrt 12 * U) * (B * ‖f‖) :=
      mul_le_mul_of_nonneg_left hinput (mul_nonneg (Real.sqrt_nonneg 12) hU)
    _ = _ := (mul_assoc _ _ _).symm

/-- On an entire leading buffer the actual physical multiplier is exactly
its cut value, before taking the local velocity bound. -/
theorem innerLiouvilleFieldLift_weighted_buffer_bound
    (W : ℝ → ℝ) (hW : Measurable W) (CW : ℝ) (hWC : ∀ r, |W r| ≤ CW)
    (f : Lp ℝ 2 volume) (buffer : Set ℝ)
    (hf : ∀ᵐ x ∂volume, x ∉ buffer → f x = 0)
    (w : ℝ) (hconstant : ∀ x ∈ buffer, W (R x) = w)
    {Ucap : ℝ} (hcap : 0 ≤ Ucap)
    (hbuffer : ∀ x ∈ buffer, |deriv R x / R x| ≤ Ucap) :
    ‖innerWeightMultiplier (radialHilbertMeasure D) W hW CW hWC
      (innerLiouvilleFieldLift D hab hlam hR hs hp hcore hw U hU hv f)‖ ≤
        |w| * (Real.sqrt 12 * Ucap * ‖f‖) := by
  rw [innerLiouvilleFieldLift_weight D hab hlam hR hs hp hcore hw U hU hv,
    innerWeightMultiplier_eq_smul_of_support volume (fun x => W (R x))
      (hW.comp hR.continuous.measurable) CW (fun x => hWC (R x))
      buffer f hf w hconstant, map_smul, norm_smul, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg w)
  apply innerLiouvilleFieldLift_norm_le_of_buffer D hab hlam hR hs hp hcore hw U hU hv
    f buffer hcap _ hbuffer
  filter_upwards [hf] with x hx
  intro hne
  by_contra hnot
  exact hne (hx hnot)

end ContinuousFlexibility.Radial
