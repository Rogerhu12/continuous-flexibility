import ContinuousFlexibility.Analysis.IntervalWeakDivergence
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integral representatives of locally integrable weak derivatives

This file proves the compact-test integration-by-parts identity for the
ordinary indefinite integral of a locally integrable function. The proof on
a bounded interval uses Fubini on a triangle; it does not assume pointwise
differentiability of an L¹ primitive. Consequently, first weak derivatives
admit their actual integral representatives.
-/

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace ContinuousFlexibility.Analysis

noncomputable section

/-- The ordinary signed integral, based at an interior point. -/
abbrev intervalLocalPrimitive (f : ℝ → ℝ) (x₀ x : ℝ) : ℝ :=
  intervalWeakPrimitive x₀ f x

theorem continuousOn_intervalLocalPrimitive {a b : ℝ} (hab : a < b)
    {f : ℝ → ℝ} (hf : LocallyIntegrableOn f (Ioo a b) volume)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Ioo a b) :
    ContinuousOn (intervalLocalPrimitive f x₀) (Ioo a b) := by
  intro x hx
  have hK : IsCompact (insert x₀ {x}) := isCompact_singleton.insert x₀
  have hKI : insert x₀ {x} ⊆ Ioo a b := by
    intro y hy
    simp only [mem_insert_iff, mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hx₀
    · exact hx
  obtain ⟨l, r, hal, hlr, hrb, hs⟩ :=
    exists_inner_interval_of_isCompact_subset_Ioo hab hK hKI
  have hxl : x ∈ Ioo l r := hs (by simp)
  have hx₀l : x₀ ∈ Ioo l r := hs (by simp)
  have hl : l ∈ Ioo a b := ⟨hal, hlr.trans hrb⟩
  have hr : r ∈ Ioo a b := ⟨hal.trans hlr, hrb⟩
  have hi := intervalIntegrable_of_locallyIntegrableOn_Ioo hf hl hr
  have hx₀cc : x₀ ∈ uIcc l r := by
    rw [uIcc_of_le hlr.le]
    exact ⟨hx₀l.1.le, hx₀l.2.le⟩
  have hcont := intervalIntegral.continuousOn_primitive_interval' hi hx₀cc
  apply (hcont.continuousAt ?_).continuousWithinAt
  rw [uIcc_of_le hlr.le]
  exact Icc_mem_nhds hxl.1 hxl.2

/-- The classical FTC for a continuous integrand needs only local
continuity on the open interval. -/
theorem hasDerivAt_intervalLocalPrimitive_of_continuousOn {a b : ℝ}
    {f : ℝ → ℝ} (hf : ContinuousOn f (Ioo a b))
    {x₀ x : ℝ} (hx₀ : x₀ ∈ Ioo a b) (hx : x ∈ Ioo a b) :
    HasDerivAt (intervalLocalPrimitive f x₀) (f x) x := by
  have hsub : uIcc x₀ x ⊆ Ioo a b := by
    intro y hy
    exact ⟨(lt_min hx₀.1 hx.1).trans_le hy.1,
      hy.2.trans_lt (max_lt hx₀.2 hx.2)⟩
  exact intervalIntegral.integral_hasDerivAt_right (hf.mono hsub).intervalIntegrable
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hf x hx)
    (hf.continuousAt (isOpen_Ioo.mem_nhds hx))

/-- Fubini gives integration by parts for a merely integrable primitive on
a bounded interval. No derivative of the primitive is invoked. -/
theorem integral_intervalLocalPrimitive_mul_deriv_of_contDiff_one {l r : ℝ}
    {f ψ : ℝ → ℝ} (hf : IntegrableOn f (Ioc l r) volume)
    (hψ : ContDiff ℝ 1 ψ) :
    (∫ x in Ioc l r, intervalLocalPrimitive f l x * deriv ψ x) =
      ψ r * (∫ x in Ioc l r, f x) - ∫ x in Ioc l r, f x * ψ x := by
  let μ : Measure ℝ := volume.restrict (Ioc l r)
  let P : ℝ → ℝ := fun x => ∫ y in l..x, f y ∂μ
  let W : Set (ℝ × ℝ) := {p | p.2 ≤ p.1}
  let K (x y : ℝ) : ℝ := W.indicator (fun p => deriv ψ p.1 * f p.2) (x, y)
  have hW : MeasurableSet W := measurableSet_le measurable_snd measurable_fst
  have hψ' : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  have hψ'i : Integrable (deriv ψ) μ := hψ'.integrableOn_Ioc
  have hfi : Integrable f μ := hf
  have hK : Integrable (Function.uncurry K) (μ.prod μ) :=
    (hψ'i.mul_prod hfi).indicator hW
  have hmem : ∀ᵐ x ∂μ, x ∈ Ioc l r := ae_restrict_mem measurableSet_Ioc
  have hP (x : ℝ) (hx : x ∈ Ioc l r) :
      P x = intervalLocalPrimitive f l x := by
    change (∫ y in l..x, f y ∂μ) = ∫ y in l..x, f y
    rw [intervalIntegral.integral_of_le hx.1.le,
      intervalIntegral.integral_of_le hx.1.le]
    change (∫ y, f y ∂(volume.restrict (Ioc l r)).restrict (Ioc l x)) = _
    rw [Measure.restrict_restrict_of_subset (Ioc_subset_Ioc_right hx.2)]
  have hleft (x : ℝ) (hx : x ∈ Ioc l r) :
      (∫ y, K x y ∂μ) = P x * deriv ψ x := by
    have hfun : K x = (Iic x).indicator (fun y => deriv ψ x * f y) := by
      funext y
      by_cases hy : y ≤ x <;> simp [K, W, hy]
    rw [hfun, integral_indicator measurableSet_Iic, integral_const_mul]
    change deriv ψ x * (∫ y, f y ∂μ.restrict (Iic x)) =
      (∫ y in l..x, f y ∂μ) * deriv ψ x
    rw [intervalIntegral.integral_of_le hx.1.le]
    have hr : μ.restrict (Iic x) = μ.restrict (Ioc l x) := by
      dsimp only [μ]
      rw [Measure.restrict_restrict measurableSet_Iic,
        Measure.restrict_restrict_of_subset (Ioc_subset_Ioc_right hx.2)]
      have hs : Iic x ∩ Ioc l r = Ioc l x := by
        ext y
        simp only [mem_inter_iff, mem_Iic, mem_Ioc]
        exact ⟨fun h => ⟨h.2.1, h.1⟩,
          fun h => ⟨h.2, h.1, h.2.trans hx.2⟩⟩
      rw [hs]
    rw [hr, mul_comm]
  have hright (y : ℝ) (hy : y ∈ Ioc l r) :
      (∫ x, K x y ∂μ) = f y * (ψ r - ψ y) := by
    have hfun : (fun x => K x y) = (Ici y).indicator (fun x => f y * deriv ψ x) := by
      funext x
      by_cases hx : y ≤ x <;> simp [K, W, hx, mul_comm]
    rw [hfun, integral_indicator measurableSet_Ici, integral_const_mul]
    have hr : μ.restrict (Ici y) = volume.restrict (Ioc y r) := by
      dsimp only [μ]
      rw [Measure.restrict_restrict measurableSet_Ici]
      have hs : Ici y ∩ Ioc l r = Icc y r := by
        ext x
        simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
        exact ⟨fun h => ⟨h.1, h.2.2⟩,
          fun h => ⟨h.1, hy.1.trans_le h.1, h.2⟩⟩
      rw [hs, ← restrict_Ioc_eq_restrict_Icc]
    rw [hr, ← intervalIntegral.integral_of_le hy.2,
      intervalIntegral.integral_deriv_eq_sub
        (fun x _ => hψ.differentiable (by simp) x)
        (hψ'.intervalIntegrable _ _)]
  have hprod : Integrable (fun x => f x * ψ x) μ :=
    hf.mul_continuousOn_of_subset hψ.continuous.continuousOn
      measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self
  calc
    (∫ x in Ioc l r, intervalLocalPrimitive f l x * deriv ψ x) =
        ∫ x, P x * deriv ψ x ∂μ :=
      integral_congr_ae (hmem.mono fun x hx => by
        change intervalLocalPrimitive f l x * deriv ψ x = P x * deriv ψ x
        rw [hP x hx])
    _ = ∫ x, (∫ y, K x y ∂μ) ∂μ :=
      integral_congr_ae (hmem.mono fun x hx => (hleft x hx).symm)
    _ = ∫ y, (∫ x, K x y ∂μ) ∂μ := integral_integral_swap hK
    _ = ∫ y, f y * (ψ r - ψ y) ∂μ :=
      integral_congr_ae (hmem.mono hright)
    _ = _ := by
      simp_rw [mul_sub]
      rw [integral_sub (hfi.mul_const (ψ r)) hprod, integral_mul_const, mul_comm]

/-- Smooth-test specialization of the bounded-interval primitive identity. -/
theorem integral_intervalLocalPrimitive_mul_deriv {l r : ℝ}
    {f ψ : ℝ → ℝ} (hf : IntegrableOn f (Ioc l r) volume)
    (hψ : ContDiff ℝ ∞ ψ) :
    (∫ x in Ioc l r, intervalLocalPrimitive f l x * deriv ψ x) =
      ψ r * (∫ x in Ioc l r, f x) - ∫ x in Ioc l r, f x * ψ x :=
  integral_intervalLocalPrimitive_mul_deriv_of_contDiff_one hf (hψ.of_le (by simp))

/-- The indefinite integral of a locally integrable function has that
function as its first weak derivative against all interior smooth tests. -/
theorem integral_intervalLocalPrimitive_mul_deriv_Ioo_of_contDiff_one {a b : ℝ} (hab : a < b)
    {f : ℝ → ℝ} (hf : LocallyIntegrableOn f (Ioo a b) volume)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Ioo a b) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ioo a b) :
    (∫ x, intervalLocalPrimitive f x₀ x * deriv ψ x) =
      -(∫ x, f x * ψ x) := by
  have hK : IsCompact (tsupport ψ ∪ {x₀}) := hψc.isCompact.union isCompact_singleton
  have hKI : tsupport ψ ∪ {x₀} ⊆ Ioo a b := by
    intro x hx
    rcases hx with hx | hx
    · exact hψs hx
    · rcases mem_singleton_iff.mp hx with rfl
      exact hx₀
  obtain ⟨l, r, hal, hlr, hrb, hs⟩ :=
    exists_inner_interval_of_isCompact_subset_Ioo hab hK hKI
  have hψlr : tsupport ψ ⊆ Ioo l r := fun _ hx => hs (Or.inl hx)
  have hx₀lr : x₀ ∈ Ioo l r := hs (Or.inr (mem_singleton x₀))
  have hl : l ∈ Ioo a b := ⟨hal, hlr.trans hrb⟩
  have hr : r ∈ Ioo a b := ⟨hal.trans hlr, hrb⟩
  have hIcc : Icc l r ⊆ Ioo a b :=
    fun _ hx => ⟨hal.trans_le hx.1, hx.2.trans_lt hrb⟩
  have hfi : IntegrableOn f (Ioc l r) volume :=
    (intervalIntegrable_of_locallyIntegrableOn_Ioo hf hl hr).1
  have hφr : ψ r = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hh => (lt_irrefl r) (hψlr hh).2)
  have hφl : ψ l = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hh => (lt_irrefl l) (hψlr hh).1)
  have hψd : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  have hψdi : IntegrableOn (deriv ψ) (Ioc l r) volume :=
    hψd.integrableOn_Ioc
  have hψint : (∫ x in Ioc l r, deriv ψ x) = 0 := by
    rw [← intervalIntegral.integral_of_le hlr.le,
      intervalIntegral.integral_deriv_eq_sub
        (fun x _ => hψ.differentiable (by simp) x)
        (hψd.intervalIntegrable _ _), hφr, hφl, sub_self]
  have hPcont := continuousOn_intervalLocalPrimitive hab hf hl
  have hPprod : IntegrableOn
      (fun x => intervalLocalPrimitive f l x * deriv ψ x) (Ioc l r) volume :=
    (((hPcont.mono hIcc).mul hψd.continuousOn).integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  let C : ℝ := intervalLocalPrimitive f x₀ l
  have hsplit (x : ℝ) (hx : x ∈ Ioc l r) :
      intervalLocalPrimitive f x₀ x = C + intervalLocalPrimitive f l x := by
    have hxI : x ∈ Ioo a b := hIcc ⟨hx.1.le, hx.2⟩
    exact (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_of_locallyIntegrableOn_Ioo hf hx₀ hl)
      (intervalIntegrable_of_locallyIntegrableOn_Ioo hf hl hxI)).symm
  have hsψ : Function.support ψ ⊆ Ioc l r :=
    fun _ hx => ⟨(hψlr (subset_tsupport ψ hx)).1,
      (hψlr (subset_tsupport ψ hx)).2.le⟩
  have hsψd : Function.support (deriv ψ) ⊆ Ioc l r :=
    fun _ hx => ⟨(hψlr (support_deriv_subset hx)).1,
      (hψlr (support_deriv_subset hx)).2.le⟩
  have hleft :
      (∫ x, intervalLocalPrimitive f x₀ x * deriv ψ x) =
        ∫ x in Ioc l r, intervalLocalPrimitive f x₀ x * deriv ψ x := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : deriv ψ x = 0 := by
      by_contra hh
      exact hx (hsψd hh)
    rw [hz, mul_zero]
  have hright : (∫ x in Ioc l r, f x * ψ x) = ∫ x, f x * ψ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : ψ x = 0 := by
      by_contra hh
      exact hx (hsψ hh)
    rw [hz, mul_zero]
  rw [hleft]
  calc
    (∫ x in Ioc l r, intervalLocalPrimitive f x₀ x * deriv ψ x) =
        ∫ x in Ioc l r,
          C * deriv ψ x + intervalLocalPrimitive f l x * deriv ψ x := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      change intervalLocalPrimitive f x₀ x * deriv ψ x =
        C * deriv ψ x + intervalLocalPrimitive f l x * deriv ψ x
      rw [hsplit x hx, add_mul]
    _ = C * (∫ x in Ioc l r, deriv ψ x) +
        ∫ x in Ioc l r, intervalLocalPrimitive f l x * deriv ψ x := by
      rw [integral_add (hψdi.const_mul C) hPprod, integral_const_mul]
    _ = -(∫ x in Ioc l r, f x * ψ x) := by
      rw [hψint, mul_zero, zero_add, integral_intervalLocalPrimitive_mul_deriv_of_contDiff_one hfi hψ,
        hφr, zero_mul, zero_sub]
    _ = -(∫ x, f x * ψ x) := by rw [hright]

/-- Smooth-test specialization of the local primitive identity. -/
theorem integral_intervalLocalPrimitive_mul_deriv_Ioo {a b : ℝ} (hab : a < b)
    {f : ℝ → ℝ} (hf : LocallyIntegrableOn f (Ioo a b) volume)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Ioo a b) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ioo a b) :
    (∫ x, intervalLocalPrimitive f x₀ x * deriv ψ x) =
      -(∫ x, f x * ψ x) :=
  integral_intervalLocalPrimitive_mul_deriv_Ioo_of_contDiff_one hab hf hx₀
    (hψ.of_le (by simp)) hψc hψs

/-- A locally integrable first weak derivative determines an actual
indefinite-integral representative, up to one additive constant. -/
theorem exists_ae_eq_primitive_of_weak_derivative_Ioo {a b : ℝ} (hab : a < b)
    {u f : ℝ → ℝ} (hu : LocallyIntegrableOn u (Ioo a b) volume)
    (hf : LocallyIntegrableOn f (Ioo a b) volume) (x₀ : ℝ) (hx₀ : x₀ ∈ Ioo a b)
    (hw : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b → (∫ x, u x * deriv ψ x) = -(∫ x, f x * ψ x)) :
    ∃ c : ℝ, u =ᵐ[volume.restrict (Ioo a b)]
      (fun x => c + intervalLocalPrimitive f x₀ x) := by
  have hPcont := continuousOn_intervalLocalPrimitive hab hf hx₀
  have hPi : LocallyIntegrableOn (intervalLocalPrimitive f x₀) (Ioo a b) volume :=
    hPcont.locallyIntegrableOn measurableSet_Ioo
  have hsub : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b →
        (∫ x, (u x - intervalLocalPrimitive f x₀ x) * deriv ψ x) = 0 := by
    intro ψ hψ hψc hψs
    have hψd := (contDiff_infty_iff_deriv.mp hψ).2
    have hψds : tsupport (deriv ψ) ⊆ Ioo a b := tsupport_deriv_subset.trans hψs
    have huψ : Integrable (fun x => u x * deriv ψ x) :=
      integrable_mul_test_of_locallyIntegrableOn_Ioo hu hψd.continuous hψc.deriv hψds
    have hPψ : Integrable (fun x => intervalLocalPrimitive f x₀ x * deriv ψ x) :=
      integrable_mul_test_of_locallyIntegrableOn_Ioo hPi hψd.continuous hψc.deriv hψds
    simp_rw [sub_mul]
    rw [integral_sub huψ hPψ, hw ψ hψ hψc hψs,
      integral_intervalLocalPrimitive_mul_deriv_Ioo hab hf hx₀ hψ hψc hψs, sub_self]
  obtain ⟨c, hc⟩ :=
    exists_ae_eq_add_const_of_integral_sub_mul_deriv_eq_zero_Ioo hab hu hPi hsub
  refine ⟨c, ?_⟩
  filter_upwards [hc] with x hx
  simpa only [add_comm] using hx

end

end ContinuousFlexibility.Analysis
