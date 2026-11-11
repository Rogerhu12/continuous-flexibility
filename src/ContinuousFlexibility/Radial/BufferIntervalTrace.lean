import ContinuousFlexibility.Radial.BufferIntervalForm
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Continuous representatives of the actual weak energy domain

A weak first derivative in Lebesgue `L²` determines an absolutely continuous
representative. The proof uses an actual integral primitive, integration by
parts for absolutely continuous functions, and compact smooth tests.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

theorem bufferCompactPrimitive {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (hzero : (∫ x : ℝ, g x) = 0) :
    ∃ P : ℝ → ℝ, ContDiff ℝ ∞ P ∧ HasCompactSupport P ∧ deriv P = g := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  let a : ℝ := -|R| - 1
  let b : ℝ := |R| + 1
  let P (x : ℝ) := ∫ t in a..x, g t
  have hP (x : ℝ) : HasDerivAt P (g x) x :=
    (hg.continuous.integral_hasStrictDerivAt a x).hasDerivAt
  have hd : deriv P = g := funext (fun x => (hP x).deriv)
  have hgzero (x : ℝ) (hx : x ∉ Ioc a b) : g x = 0 := by
    by_contra h
    have hs : x ∈ tsupport g := subset_closure (show x ∈ Function.support g from h)
    have hbound : |x| ≤ R := by
      simpa only [Real.dist_eq, sub_zero] using Metric.mem_closedBall.mp (hR hs)
    have h := abs_le.mp (hbound.trans (le_abs_self R))
    exact hx ⟨by dsimp [a]; linarith [h.1], by dsimp [b]; linarith [h.2]⟩
  refine ⟨P, contDiff_infty_iff_deriv.mpr ⟨fun x => (hP x).differentiableAt, hd.symm ▸ hg⟩,
    ?_, hd⟩
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc a b))
  intro x hx
  change (∫ t in a..x, g t) = 0
  by_cases hxa : x < a
  · have hI : (∫ t in Ioc x a, g t) = 0 := by
      calc
        _ = ∫ _ in Ioc x a, (0 : ℝ) := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro t ht
          exact hgzero t (fun hm => (not_lt_of_ge ht.2) hm.1)
        _ = _ := by simp
    rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le hxa.le, hI, neg_zero]
  · have hax : a ≤ x := le_of_not_gt hxa
    have hbx : b < x := lt_of_not_ge (fun h => hx ⟨hax, h⟩)
    have hout (t : ℝ) (ht : t ∉ Ioc a x) : g t = 0 :=
      hgzero t (fun hm => ht ⟨hm.1, hm.2.trans hbx.le⟩)
    rw [intervalIntegral.integral_of_le hax]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero hout).trans hzero

private def bufferUnitBump : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The compact-test definition detects a constant, without any pointwise
regularity assumption on the function being tested. -/
theorem buffer_ae_constant_of_weak_deriv_zero {F : ℝ → ℝ}
    (hF : LocallyIntegrable F volume)
    (hzero : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x : ℝ, F x * deriv φ x) = 0) :
    ∃ c : ℝ, F =ᵐ[volume] fun _ => c := by
  let η : ℝ → ℝ := bufferUnitBump.normed volume
  have hη : ContDiff ℝ ∞ η := bufferUnitBump.contDiff_normed
  have hcη : HasCompactSupport η := bufferUnitBump.hasCompactSupport_normed
  have hη₁ : (∫ x : ℝ, η x) = 1 := bufferUnitBump.integral_normed
  let c : ℝ := ∫ x : ℝ, F x * η x
  refine ⟨c, ?_⟩
  apply ae_eq_of_integral_contDiff_smul_eq hF continuous_const.locallyIntegrable
  intro φ hφ hc
  let M : ℝ := ∫ x : ℝ, φ x
  let g (x : ℝ) := φ x - M * η x
  have hg : ContDiff ℝ ∞ g := hφ.sub (contDiff_const.mul hη)
  have hcg : HasCompactSupport g := hc.sub (hcη.mul_left (f := fun _ => M))
  have hφI : Integrable φ volume := hφ.continuous.integrable_of_hasCompactSupport hc
  have hηI : Integrable η volume := hη.continuous.integrable_of_hasCompactSupport hcη
  have hgzero : (∫ x : ℝ, g x) = 0 := by
    change (∫ x : ℝ, φ x - M * η x) = 0
    rw [integral_sub hφI (hηI.const_mul M), integral_const_mul, hη₁, mul_one]
    exact sub_self _
  obtain ⟨P, hP, hcP, hdP⟩ := bufferCompactPrimitive hg hcg hgzero
  have hPg := hzero P hP hcP
  rw [hdP] at hPg
  have hFφ : Integrable (fun x => F x * φ x) volume := by
    simpa only [smul_eq_mul] using hF.integrable_smul_right_of_hasCompactSupport hφ.continuous hc
  have hFη : Integrable (fun x => F x * η x) volume := by
    simpa only [smul_eq_mul] using hF.integrable_smul_right_of_hasCompactSupport hη.continuous hcη
  have hsplit : (∫ x : ℝ, F x * g x) = (∫ x : ℝ, F x * φ x) - M * c := by
    calc
      _ = ∫ x : ℝ, F x * φ x - M * (F x * η x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        dsimp [g]
        ring
      _ = _ := by rw [integral_sub hFφ (hFη.const_mul M), integral_const_mul]
  rw [hsplit] at hPg
  calc
    _ = ∫ x : ℝ, F x * φ x := by simp only [smul_eq_mul, mul_comm]
    _ = M * c := sub_eq_zero.mp hPg
    _ = _ := by simp only [smul_eq_mul, integral_mul_const, M]

theorem buffer_locallyIntegrable_intervalIntegrable {f : ℝ → ℝ}
    (hf : LocallyIntegrable f volume) (a b : ℝ) : IntervalIntegrable f volume a b :=
  intervalIntegrable_iff.mpr <|
    (hf.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc

theorem bufferPrimitive_continuous {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) (a : ℝ) :
    Continuous (fun x => ∫ t in a..x, f t) :=
  intervalIntegral.continuous_primitive (buffer_locallyIntegrable_intervalIntegrable hf) a

/-- The actual integral primitive has the expected weak derivative. -/
theorem bufferPrimitive_weak_derivative {f : ℝ → ℝ} (hf : LocallyIntegrable f volume)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x : ℝ, (∫ t in (0 : ℝ)..x, f t) * deriv φ x) = -(∫ x : ℝ, f x * φ x) := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  let a : ℝ := -|R| - 1
  let b : ℝ := |R| + 1
  let P (x : ℝ) := ∫ t in (0 : ℝ)..x, f t
  have ha : a < 0 := by dsimp [a]; linarith [abs_nonneg R]
  have hb : 0 < b := by dsimp [b]; linarith [abs_nonneg R]
  have hab : a < b := ha.trans hb
  have hsupport : tsupport φ ⊆ Ioo a b := by
    intro x hx
    have hbound : |x| ≤ R := by
      simpa only [Real.dist_eq, sub_zero] using Metric.mem_closedBall.mp (hR hx)
    have h := abs_le.mp (hbound.trans (le_abs_self R))
    exact ⟨by dsimp [a]; linarith [h.1], by dsimp [b]; linarith [h.2]⟩
  have hφzero (x : ℝ) (hx : x ∉ Ioo a b) : φ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hm => hx (hsupport hm))
  have hφ'zero (x : ℝ) (hx : x ∉ Ioo a b) : deriv φ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hm => hx (hsupport (tsupport_deriv_subset hm)))
  have hφa : φ a = 0 := hφzero a (by simp)
  have hφb : φ b = 0 := hφzero b (by simp)
  have hP : AbsolutelyContinuousOnInterval P a b :=
    (buffer_locallyIntegrable_intervalIntegrable hf a b).absolutelyContinuousOnInterval_intervalIntegral
      (by rw [uIcc_of_le hab.le]; exact ⟨ha.le, hb.le⟩)
  have hφac : AbsolutelyContinuousOnInterval φ a b :=
    (hφ.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).contDiffOn.absolutelyContinuousOnInterval
  have hibp := hP.integral_mul_deriv_eq_deriv_mul hφac
  rw [hφa, hφb, mul_zero, mul_zero, sub_self, zero_sub] at hibp
  have hderiv : (∫ x in a..b, deriv P x * φ x) = ∫ x in a..b, f x * φ x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hf] with x hx _
    rw [(hx 0).deriv]
  have hleft : (∫ x : ℝ, P x * deriv φ x) = ∫ x in a..b, P x * deriv φ x := by
    rw [intervalIntegral.integral_of_le hab.le]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [hφ'zero x (fun hm => hx ⟨hm.1, hm.2.le⟩), mul_zero]
  have hright : (∫ x : ℝ, f x * φ x) = ∫ x in a..b, f x * φ x := by
    rw [intervalIntegral.integral_of_le hab.le]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [hφzero x (fun hm => hx ⟨hm.1, hm.2.le⟩), mul_zero]
  rw [hleft, hibp, hderiv, ← hright]

/-- The first weak derivative supplies an actual continuous representative and
the fundamental theorem of calculus on every compact interval. -/
theorem buffer_weakDerivative_continuousRepresentative {u d : RadialL2}
    (hud : WeakRadialDerivative u d) :
    ∃ U : ℝ → ℝ, Continuous U ∧ (u : ℝ → ℝ) =ᵐ[volume] U ∧
      (∀ a b : ℝ, U b - U a = ∫ x in a..b, d x) ∧
      (∀ᵐ x : ℝ, HasDerivAt U (d x) x) := by
  have hu : LocallyIntegrable (u : ℝ → ℝ) volume :=
    (Lp.memLp u).locallyIntegrable (by norm_num)
  have hd : LocallyIntegrable (d : ℝ → ℝ) volume :=
    (Lp.memLp d).locallyIntegrable (by norm_num)
  let P (x : ℝ) := ∫ t in (0 : ℝ)..x, d t
  have hP : Continuous P := bufferPrimitive_continuous hd 0
  let F (x : ℝ) := u x - P x
  have hF : LocallyIntegrable F volume := hu.sub hP.locallyIntegrable
  have hzero : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x : ℝ, F x * deriv φ x) = 0 := by
    intro φ hφ hcφ
    have hφ' := (contDiff_infty_iff_deriv.mp hφ).2
    have huI : Integrable (fun x => u x * deriv φ x) volume := by
      simpa only [smul_eq_mul] using
        hu.integrable_smul_right_of_hasCompactSupport hφ'.continuous hcφ.deriv
    have hPI : Integrable (fun x => P x * deriv φ x) volume :=
      (hP.mul hφ'.continuous).integrable_of_hasCompactSupport hcφ.deriv.mul_left
    calc
      _ = (∫ x : ℝ, u x * deriv φ x) - ∫ x : ℝ, P x * deriv φ x := by
        rw [← integral_sub huI hPI]
        apply integral_congr_ae
        filter_upwards [] with x
        dsimp [F]
        ring
      _ = 0 := by
        rw [hud φ hφ hcφ, bufferPrimitive_weak_derivative hd φ hφ hcφ]
        exact sub_self _
  obtain ⟨c, hc⟩ := buffer_ae_constant_of_weak_deriv_zero hF hzero
  let U (x : ℝ) := c + P x
  refine ⟨U, continuous_const.add hP, ?_, ?_, ?_⟩
  · filter_upwards [hc] with x hx
    dsimp [F] at hx
    dsimp [U]
    linarith
  · intro a b
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (buffer_locallyIntegrable_intervalIntegrable hd 0 a)
      (buffer_locallyIntegrable_intervalIntegrable hd a b)
    dsimp [U, P]
    linarith
  · filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hd] with x hx
    exact (hx 0).const_add c

theorem bufferPrimitiveRepresentative_absolutelyContinuous {U d : ℝ → ℝ}
    (hd : LocallyIntegrable d volume)
    (hprim : ∀ x y : ℝ, U y - U x = ∫ t in x..y, d t) (a b : ℝ) :
    AbsolutelyContinuousOnInterval U a b := by
  have hp := (buffer_locallyIntegrable_intervalIntegrable hd a b).absolutelyContinuousOnInterval_intervalIntegral
    (c := a) left_mem_uIcc
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => U a) a b :=
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => U a)).contDiffOn.absolutelyContinuousOnInterval
  apply (hc.fun_add hp).congr
  intro x _
  have hax := hprim a x
  linarith

/-- Weak differentiation is local on open sets. This is useful for supported
variations on an interval or a half-line, and needs no trace hypothesis. -/
theorem buffer_weakDerivative_zero_on_open {u d : RadialL2}
    (hud : WeakRadialDerivative u d) {O : Set ℝ} (hO : IsOpen O)
    (hu : (u : ℝ → ℝ) =ᵐ[volume.restrict O] (fun _ => 0)) :
    (d : ℝ → ℝ) =ᵐ[volume.restrict O] (fun _ => 0) := by
  change ∀ᵐ x : ℝ ∂volume.restrict O, d x = 0
  rw [ae_restrict_iff' hO.measurableSet]
  apply hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (((Lp.memLp d).locallyIntegrable (by norm_num)).locallyIntegrableOn O)
  intro φ hφ hcφ hsφ
  have hu' := (ae_restrict_iff' hO.measurableSet).mp hu
  have htest : (∫ x : ℝ, u x * deriv φ x) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hu'] with x hx
    by_cases hxO : x ∈ O
    · rw [hx hxO, zero_mul]
    · rw [deriv_of_notMem_tsupport (fun hm => hxO (hsφ hm)), mul_zero]
  have hweak := hud φ hφ hcφ
  rw [htest] at hweak
  have hdtest : (∫ x : ℝ, d x * φ x) = 0 := by linarith
  simpa only [smul_eq_mul, mul_comm] using hdtest

theorem buffer_continuousRepresentative_unique {u : RadialL2} {U W : ℝ → ℝ}
    (hU : Continuous U) (hW : Continuous W)
    (hu : (u : ℝ → ℝ) =ᵐ[volume] U) (hw : (u : ℝ → ℝ) =ᵐ[volume] W) : U = W :=
  MeasureTheory.Measure.eq_of_ae_eq (μ := volume) (hu.symm.trans hw) hU hW

/-- A supported continuous representative vanishes also at boundary points
approached through the exterior. Thus Dirichlet traces are true point values. -/
theorem buffer_continuousRepresentative_zero_on_closure {u : RadialL2} {U : ℝ → ℝ}
    (hU : Continuous U) (hu : (u : ℝ → ℝ) =ᵐ[volume] U)
    {O : Set ℝ} (hO : IsOpen O)
    (hz : (u : ℝ → ℝ) =ᵐ[volume.restrict O] (fun _ => 0)) :
    EqOn U (fun _ => 0) (closure O) := by
  have huO : (u : ℝ → ℝ) =ᵐ[volume.restrict O] U := ae_restrict_of_ae hu
  have he : U =ᵐ[volume.restrict O] (fun _ => 0) := huO.symm.trans hz
  exact (MeasureTheory.Measure.eqOn_open_of_ae_eq (μ := volume) he hO hU.continuousOn
    continuous_const.continuousOn).closure hU continuous_const

theorem intervalEnergyClosure_zero_traces {V : ℝ → ℝ} {l h : ℝ}
    {u d q : RadialL2} (hmem : (u, d, q) ∈ closure (IntervalEnergyCore V l h))
    {U : ℝ → ℝ} (hU : Continuous U) (hu : (u : ℝ → ℝ) =ᵐ[volume] U) :
    U l = 0 ∧ U h = 0 := by
  have hs := intervalEnergyClosure_supported V l h hmem
  have hleft : (u : ℝ → ℝ) =ᵐ[volume.restrict (Iio l)] (fun _ => 0) :=
    ae_restrict_of_ae_restrict_of_subset (by
      intro x hx hx'
      exact (not_lt_of_ge hx.le) hx'.1) hs
  have hright : (u : ℝ → ℝ) =ᵐ[volume.restrict (Ioi h)] (fun _ => 0) :=
    ae_restrict_of_ae_restrict_of_subset (by
      intro x hx hx'
      exact (not_lt_of_ge hx.le) hx'.2) hs
  have hzl := buffer_continuousRepresentative_zero_on_closure hU hu isOpen_Iio hleft
  have hzh := buffer_continuousRepresentative_zero_on_closure hU hu isOpen_Ioi hright
  exact ⟨hzl (show l ∈ closure (Iio l) by rw [closure_Iio]; exact le_rfl),
    hzh (show h ∈ closure (Ioi h) by rw [closure_Ioi]; exact le_rfl)⟩

end ContinuousFlexibility.Radial
