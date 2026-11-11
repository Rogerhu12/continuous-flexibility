import ContinuousFlexibility.Radial.IntervalWeakPrimitiveStrict
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp

/-!
# One-dimensional weak divergence regularity

On a closed interval where the smooth leading coefficient does not vanish,
an integrable distributional solution of `(w u')' = g` has a globally C1
representative. Its flux on the interval is a constant plus the integral
primitive of `g`, and is therefore absolutely continuous.

Only smooth compact tests whose topological support lies strictly inside
the interval are used. The proof constructs compact primitives of
zero weighted-mean tests and then applies the weak fundamental theorem.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff

/-- Dividing a smooth test by a smooth coefficient is globally smooth
if the coefficient does not vanish on the topological support of the test.
The coefficient only needs to be smooth on an open neighborhood of that support. -/
theorem contDiff_div_of_tsupport_subset
    {U : Set ℝ} (hU : IsOpen U) {φ w : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hw : ContDiffOn ℝ ∞ w U)
    (hφs : tsupport φ ⊆ U) (hwn : ∀ x ∈ U, w x ≠ 0) :
    ContDiff ℝ ∞ (fun x => φ x / w x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport φ
  · exact hφ.contDiffAt.div
      (hw.contDiffAt (hU.mem_nhds (hφs hx))) (hwn x (hφs hx))
  · apply ContDiffAt.congr_of_eventuallyEq
      (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℝ)) x)
    filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hx] with y hy
    have hy0 : φ y = 0 := image_eq_zero_of_notMem_tsupport hy
    simp only [hy0, zero_div]

/-- Division does not enlarge the topological support of the numerator. -/
theorem tsupport_div_subset (φ w : ℝ → ℝ) :
    tsupport (fun x => φ x / w x) ⊆ tsupport φ := by
  simpa only [div_eq_mul_inv] using
    (tsupport_mul_subset_left (f := φ) (g := fun x => (w x)⁻¹))

/-- Division by an arbitrary real function preserves compact support
of the numerator. -/
theorem hasCompactSupport_div_right {φ : ℝ → ℝ}
    (hφ : HasCompactSupport φ) (w : ℝ → ℝ) :
    HasCompactSupport (fun x => φ x / w x) := by
  convert (hφ.mul_right (f' := fun x => (w x)⁻¹)) using 1
  funext x
  simp only [Pi.mul_apply, div_eq_mul_inv]

/-- A function supported in an open finite interval has the same integral
over that interval and over the whole line. -/
theorem intervalIntegral_eq_integral_of_support_subset
    {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hfs : Function.support f ⊆ Ioo a b) :
    (∫ x in a..b, f x) = ∫ x : ℝ, f x := by
  rw [intervalIntegral.integral_of_le hab]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  by_contra hn
  exact hx ⟨(hfs hn).1, (hfs hn).2.le⟩

/-- An integrated weak divergence equation determines a continuous weak
first derivative, up to one flux constant. -/
theorem exists_weakDeriv_of_integrated_divergence
    {a b : ℝ} (hab : a < b) {u H w : ℝ → ℝ}
    (hu : IntervalIntegrable u volume a b)
    (hH : ContinuousOn H (Icc a b))
    (hw : ContDiff ℝ ∞ w)
    (hwn : ∀ x ∈ Icc a b, w x ≠ 0)
    (hweak : ∀ ψ : ℝ → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b →
      (∫ x in a..b, u x * deriv (fun y => w y * deriv ψ y) x) =
        -(∫ x in a..b, H x * deriv ψ x)) :
    ∃ C : ℝ, ∀ φ : ℝ → ℝ,
      ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ x in a..b, u x * deriv φ x) =
        -(∫ x in a..b, ((H x - C) / w x) * φ x) := by
  have hwn' : ∀ x ∈ Ioo a b, w x ≠ 0 :=
    fun x hx => hwn x (mem_Icc_of_Ioo hx)
  have hquot (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
      (hφs : tsupport φ ⊆ Ioo a b) :
      ContDiff ℝ ∞ (fun x => φ x / w x) :=
    contDiff_div_of_tsupport_subset isOpen_Ioo hφ hw.contDiffOn hφs hwn'
  have hHi : IntervalIntegrable H volume a b :=
    hH.intervalIntegrable_of_Icc hab.le
  let J (φ : ℝ → ℝ) : ℝ :=
    (∫ x in a..b, u x * deriv φ x) +
      ∫ x in a..b, H x * (φ x / w x)
  have hkernel (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
      (hcφ : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo a b)
      (hφzero : (∫ x : ℝ, φ x / w x) = 0) : J φ = 0 := by
    obtain ⟨ψ, hψ, hcψ, hψs, hdψ⟩ :=
      compactPrimitive_tsupport_in_interval hab (hquot φ hφ hφs)
        (hasCompactSupport_div_right hcφ w)
        ((tsupport_div_subset φ w).trans hφs) hφzero
    have hcancel : (fun x => w x * deriv ψ x) = φ := by
      funext x
      rw [hdψ]
      by_cases hx : φ x = 0
      · simp only [hx, zero_div, mul_zero]
      · have hn := hwn' x (hφs (subset_tsupport φ hx))
        field_simp [hn] <;> ring
    have hh := hweak ψ hψ hcψ hψs
    rw [hcancel, hdψ] at hh
    dsimp only [J]
    linarith only [hh]
  let B : ContDiffBump ((a + b) / 2) :=
    { rIn := (b - a) / 8
      rOut := (b - a) / 4
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  let η : ℝ → ℝ := B.normed volume
  have hη : ContDiff ℝ ∞ η := B.contDiff_normed
  have hcη : HasCompactSupport η := B.hasCompactSupport_normed
  have hηone : (∫ x : ℝ, η x) = 1 := B.integral_normed
  have hηs : tsupport η ⊆ Ioo a b := by
    intro x hx
    change x ∈ tsupport (B.normed volume) at hx
    rw [B.tsupport_normed_eq] at hx
    have hd := Metric.mem_closedBall.mp hx
    rw [Real.dist_eq] at hd
    change |x - (a + b) / 2| ≤ (b - a) / 4 at hd
    have hd' := abs_le.mp hd
    exact ⟨by linarith [hd'.1], by linarith [hd'.2]⟩
  let η₀ (x : ℝ) : ℝ := w x * η x
  have hη₀ : ContDiff ℝ ∞ η₀ := hw.mul hη
  have hcη₀ : HasCompactSupport η₀ := hcη.mul_left
  have hη₀s : tsupport η₀ ⊆ Ioo a b :=
    tsupport_mul_subset_right.trans hηs
  have hη₀q : (fun x => η₀ x / w x) = η := by
    funext x
    by_cases hx : η x = 0
    · simp only [η₀, hx, mul_zero, zero_div]
    · have hn := hwn' x (hηs (subset_tsupport η hx))
      dsimp only [η₀]
      field_simp [hn] <;> ring
  have hη₀qI : Integrable (fun x => η₀ x / w x) volume := by
    rw [hη₀q]
    exact hη.continuous.integrable_of_hasCompactSupport hcη
  have hη₀qone : (∫ x : ℝ, η₀ x / w x) = 1 := by
    rw [hη₀q, hηone]
  have hJsub (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
      (hφs : tsupport φ ⊆ Ioo a b) (m : ℝ) :
      J (fun x => φ x - m * η₀ x) = J φ - m * J η₀ := by
    have hdφ : Continuous (deriv φ) :=
      (contDiff_infty_iff_deriv.mp hφ).2.continuous
    have hdη₀ : Continuous (deriv η₀) :=
      (contDiff_infty_iff_deriv.mp hη₀).2.continuous
    have hφq : Continuous (fun x => φ x / w x) :=
      (hquot φ hφ hφs).continuous
    have hη₀qc : Continuous (fun x => η₀ x / w x) :=
      (hquot η₀ hη₀ hη₀s).continuous
    have hd (x : ℝ) :
        deriv (fun y => φ y - m * η₀ y) x =
          deriv φ x - m * deriv η₀ x :=
      ((hφ.differentiable (by simp) x).hasDerivAt.sub
        ((hη₀.differentiable (by simp) x).hasDerivAt.const_mul m)).deriv
    have hfirst :
        (∫ x in a..b, u x * deriv (fun y => φ y - m * η₀ y) x) =
          (∫ x in a..b, u x * deriv φ x) -
            m * ∫ x in a..b, u x * deriv η₀ x := by
      calc
        _ = ∫ x in a..b, u x * deriv φ x - m * (u x * deriv η₀ x) := by
          apply intervalIntegral.integral_congr
          intro x hx
          dsimp only
          rw [hd]
          ring
        _ = _ := by
          rw [intervalIntegral.integral_sub
            (hu.mul_continuousOn hdφ.continuousOn)
            ((hu.mul_continuousOn hdη₀.continuousOn).const_mul m),
            intervalIntegral.integral_const_mul]
    have hsecond :
        (∫ x in a..b, H x * ((φ x - m * η₀ x) / w x)) =
          (∫ x in a..b, H x * (φ x / w x)) -
            m * ∫ x in a..b, H x * (η₀ x / w x) := by
      calc
        _ = ∫ x in a..b, H x * (φ x / w x) -
            m * (H x * (η₀ x / w x)) := by
          apply intervalIntegral.integral_congr
          intro x hx
          simp only [div_eq_mul_inv]
          ring
        _ = _ := by
          rw [intervalIntegral.integral_sub
            (hHi.mul_continuousOn hφq.continuousOn)
            ((hHi.mul_continuousOn hη₀qc.continuousOn).const_mul m),
            intervalIntegral.integral_const_mul]
    dsimp only [J]
    rw [hfirst, hsecond]
    ring
  let C : ℝ := J η₀
  refine ⟨C, ?_⟩
  intro φ hφ hcφ hφs
  let m : ℝ := ∫ x : ℝ, φ x / w x
  let ζ (x : ℝ) : ℝ := φ x - m * η₀ x
  have hζ : ContDiff ℝ ∞ ζ := hφ.sub (contDiff_const.mul hη₀)
  have hcζ : HasCompactSupport ζ := hcφ.sub hcη₀.mul_left
  have hζs : tsupport ζ ⊆ Ioo a b := by
    have hs : Function.support ζ ⊆ tsupport φ ∪ tsupport η₀ := by
      intro x hx
      by_contra hn
      have hφ0 : φ x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hn (Or.inl h))
      have hη₀0 : η₀ x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hn (Or.inr h))
      exact hx (by simp only [ζ, hφ0, hη₀0, mul_zero, sub_zero])
    have ht : tsupport ζ ⊆ tsupport φ ∪ tsupport η₀ :=
      closure_minimal hs ((isClosed_tsupport φ).union (isClosed_tsupport η₀))
    intro x hx
    rcases ht hx with hx | hx
    · exact hφs hx
    · exact hη₀s hx
  have hφq := hquot φ hφ hφs
  have hφqI : Integrable (fun x => φ x / w x) volume :=
    hφq.continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_div_right hcφ w)
  have hζzero : (∫ x : ℝ, ζ x / w x) = 0 := by
    calc
      _ = ∫ x : ℝ, φ x / w x - m * (η₀ x / w x) := by
        apply integral_congr_ae
        apply Eventually.of_forall
        intro x
        dsimp only [ζ]
        simp only [div_eq_mul_inv]
        ring
      _ = (∫ x : ℝ, φ x / w x) - m * (∫ x : ℝ, η₀ x / w x) := by
        rw [integral_sub hφqI (hη₀qI.const_mul m), integral_const_mul]
      _ = 0 := by
        rw [hη₀qone, mul_one]
        exact sub_self m
  have hz := hkernel ζ hζ hcζ hζs hζzero
  change J (fun x => φ x - m * η₀ x) = 0 at hz
  rw [hJsub φ hφ hφs m] at hz
  have hmoment : J φ = m * C := by
    dsimp only [C]
    linarith only [hz]
  have hmass : (∫ x in a..b, φ x / w x) = m :=
    intervalIntegral_eq_integral_of_support_subset hab.le
      ((subset_tsupport _).trans ((tsupport_div_subset φ w).trans hφs))
  have hfinal :
      (∫ x in a..b, ((H x - C) / w x) * φ x) =
        (∫ x in a..b, H x * (φ x / w x)) - m * C := by
    calc
      _ = ∫ x in a..b, H x * (φ x / w x) - C * (φ x / w x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        simp only [div_eq_mul_inv]
        ring
      _ = (∫ x in a..b, H x * (φ x / w x)) -
          C * (∫ x in a..b, φ x / w x) := by
        rw [intervalIntegral.integral_sub
          (hHi.mul_continuousOn hφq.continuous.continuousOn)
          ((hφq.continuous.intervalIntegrable a b).const_mul C),
          intervalIntegral.integral_const_mul]
      _ = _ := by rw [hmass, mul_comm C m]
  dsimp only [J] at hmoment
  rw [hfinal]
  linarith only [hmoment]

/-- A continuous weak derivative on a closed interval yields a globally C1
representative with that derivative throughout the closed interval.
The original integrable function need not have pointwise boundary values. -/
theorem exists_contDiff_representative_of_continuous_weakDeriv
    {a b : ℝ} (hab : a < b) {u V : ℝ → ℝ}
    (hu : IntervalIntegrable u volume a b)
    (hV : ContinuousOn V (Icc a b))
    (hweak : ∀ φ : ℝ → ℝ,
      ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ x in a..b, u x * deriv φ x) =
        -(∫ x in a..b, V x * φ x)) :
    ∃ v : ℝ → ℝ,
      ContDiff ℝ 1 v ∧
      u =ᵐ[volume.restrict (Ioo a b)] v ∧
      ∀ x ∈ Icc a b, deriv v x = V x := by
  obtain ⟨c, hc⟩ :=
    exists_ae_intervalPrimitive_of_weakDeriv_tsupport hab hu
      (hV.intervalIntegrable_of_Icc hab.le) hweak
  let clamp (x : ℝ) : ℝ := max a (min b x)
  have hclamp : Continuous clamp :=
    continuous_const.max (continuous_const.min continuous_id)
  have hclamp_mem (x : ℝ) : clamp x ∈ Icc a b := by
    exact ⟨le_max_left _ _, max_le hab.le (min_le_left _ _)⟩
  have hclamp_eq {x : ℝ} (hx : x ∈ Icc a b) : clamp x = x := by
    simp only [clamp, min_eq_right hx.2, max_eq_right hx.1]
  let W (x : ℝ) : ℝ := V (clamp x)
  have hW : Continuous W := hV.comp_continuous hclamp hclamp_mem
  have hWV (x : ℝ) (hx : x ∈ Icc a b) : W x = V x := by
    dsimp only [W]
    rw [hclamp_eq hx]
  let v (x : ℝ) : ℝ := c + ∫ t in a..x, W t
  have hv (x : ℝ) : HasDerivAt v (W x) x :=
    (hW.integral_hasStrictDerivAt a x).hasDerivAt.const_add c
  have hdv : deriv v = W := funext (fun x => (hv x).deriv)
  refine ⟨v, ?_, ?_, ?_⟩
  · exact contDiff_one_iff_deriv.mpr
      ⟨fun x => (hv x).differentiableAt, hdv.symm ▸ hW⟩
  · filter_upwards [hc, self_mem_ae_restrict measurableSet_Ioo] with x hx hxi
    rw [hx]
    change c + (∫ t in a..x, V t) = c + ∫ t in a..x, W t
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hxi.1.le] at ht
    exact (hWV t ⟨ht.1, ht.2.trans hxi.2.le⟩).symm
  · intro x hx
    rw [hdv]
    exact hWV x hx

/-- Weak one-dimensional divergence regularity at a regular interval.
The representative is globally C1, agrees almost everywhere with the
original function in the interval, and has absolutely continuous flux
with the specified source. -/
theorem exists_contDiff_representative_of_weak_divergence
    {a b : ℝ} (hab : a < b) {u g w : ℝ → ℝ}
    (hu : IntervalIntegrable u volume a b)
    (hg : IntervalIntegrable g volume a b)
    (hw : ContDiff ℝ ∞ w)
    (hwn : ∀ x ∈ Icc a b, w x ≠ 0)
    (hweak : ∀ ψ : ℝ → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b →
      (∫ x in a..b, u x * deriv (fun y => w y * deriv ψ y) x) =
        ∫ x in a..b, g x * ψ x) :
    ∃ v : ℝ → ℝ, ∃ C : ℝ,
      ContDiff ℝ 1 v ∧
      u =ᵐ[volume.restrict (Ioo a b)] v ∧
      (∀ x ∈ Icc a b,
        w x * deriv v x = C + ∫ t in a..x, g t) ∧
      AbsolutelyContinuousOnInterval (fun x => w x * deriv v x) a b ∧
      (deriv (fun x => w x * deriv v x) =ᵐ[volume.restrict (Ioo a b)] g) := by
  let H (x : ℝ) : ℝ := ∫ t in a..x, g t
  have hHac : AbsolutelyContinuousOnInterval H a b :=
    hg.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
  have hH : ContinuousOn H (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using hHac.continuousOn
  have hweakH : ∀ ψ : ℝ → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b →
      (∫ x in a..b, u x * deriv (fun y => w y * deriv ψ y) x) =
        -(∫ x in a..b, H x * deriv ψ x) := by
    intro ψ hψ hcψ hψs
    have hψb : ψ b = 0 := by
      by_contra hn
      exact (lt_irrefl b) (hψs (subset_tsupport ψ hn)).2
    have hPweak :
        (∫ x in a..b, H x * deriv ψ x) =
          -(∫ x in a..b, g x * ψ x) := by
      simpa only [H, hψb, mul_zero, zero_sub] using
        intervalPrimitive_integral_mul_deriv hg
          ((hψ.of_le (by simp)).contDiffOn)
    rw [hweak ψ hψ hcψ hψs, hPweak, neg_neg]
  obtain ⟨C, hC⟩ :=
    exists_weakDeriv_of_integrated_divergence hab hu hH hw hwn hweakH
  have hV : ContinuousOn (fun x => (H x - C) / w x) (Icc a b) :=
    (hH.sub continuousOn_const).div hw.continuous.continuousOn hwn
  obtain ⟨v, hv, huv, hdv⟩ :=
    exists_contDiff_representative_of_continuous_weakDeriv hab hu hV hC
  have hflux (x : ℝ) (hx : x ∈ Icc a b) :
      w x * deriv v x = -C + H x := by
    rw [hdv x hx]
    have hn := hwn x hx
    field_simp [hn]
    <;> ring
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => -C) a b :=
    (contDiffOn_const : ContDiffOn ℝ 1 (fun _ : ℝ => -C) (uIcc a b)).absolutelyContinuousOnInterval
  have hPac : AbsolutelyContinuousOnInterval (fun x => -C + H x) a b :=
    hconst.add hHac
  have hfluxac : AbsolutelyContinuousOnInterval (fun x => w x * deriv v x) a b := by
    apply hPac.congr
    intro x hx
    rw [uIcc_of_le hab.le] at hx
    exact (hflux x hx).symm
  refine ⟨v, -C, hv, huv, hflux, hfluxac, ?_⟩
  apply (ae_restrict_iff' measurableSet_Ioo).mpr
  filter_upwards [hg.ae_hasDerivAt_integral] with x hx hxi
  have hxi' : x ∈ uIcc a b := by
    simpa only [uIcc_of_le hab.le] using mem_Icc_of_Ioo hxi
  have hderiv : HasDerivAt (fun y => -C + H y) (g x) x :=
    (hx hxi' a (by simp)).const_add (-C)
  have heq : (fun y => w y * deriv v y) =ᶠ[𝓝 x] (fun y => -C + H y) := by
    filter_upwards [isOpen_Ioo.mem_nhds hxi] with y hy
    exact hflux y (mem_Icc_of_Ioo hy)
  exact (hderiv.congr_of_eventuallyEq heq).deriv

end ContinuousFlexibility.Radial
