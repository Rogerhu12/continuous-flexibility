module

public import ContinuousFlexibility.Radial.OuterWholeKernelRepresentation
public import ContinuousFlexibility.Radial.OuterFundamentalKernel
public import ContinuousFlexibility.Radial.OuterFirstOrderRegularity

/-!
# One canonical Green kernel on the whole outer interval

The constructed core/deep operator is identified with the single normalized
min/max kernel.  Row integrability is proved from the compact core, the
actual Poisson vector and the deep Dirichlet rows.  No bounded whole
integral operator or whole inverse is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter
open ContinuousFlexibility.Analysis

variable (μ : Measure ℝ) {a c b : ℝ} (hac : a ≤ c)
  [IsFiniteMeasure (compactIntervalMeasure μ a c)]

include hac in
theorem integrable_outer_compact_kernel_row (lam : ℝ) (U V : ℝ → ℝ)
    (hU : ContinuousOn U (Icc a c)) (hV : ContinuousOn V (Icc a c))
    (f : Lp ℝ 2 μ) (x : Icc a c) :
    Integrable (fun y => outerGreenKernel lam U V (x : ℝ) y * f y)
      (μ.restrict (Icc a c)) := by
  have hv := measurePreserving_compactInterval_val μ a c
  apply (hv.integrable_comp_emb (MeasurableEmbedding.subtype_coe measurableSet_Icc)).mp
  have h := integrable_outerKernel_row (compactIntervalMeasure μ a c)
    (outerContinuousGreenKernel lam (outerCoreRestriction U hU) (outerCoreRestriction V hV))
    (l2CompactIntervalEquiv μ hac (l2Restrict μ (Icc a c) f)) x
  refine h.congr ?_
  filter_upwards [outer_compact_source_coeFn μ hac f] with y hy
  dsimp only [Function.comp_apply]
  rw [outerContinuousGreenKernel_apply, outerGreenKernel_core_restriction, hy]

theorem outer_ae_deep_interval
    (hμ : ∀ᵐ x ∂μ, x ∈ Ico a b) :
    ∀ᵐ x ∂μ.restrict (Icc a c)ᶜ, x ∈ Ico c b := by
  filter_upwards [hμ.filter_mono ae_restrict_le,
    ae_restrict_mem measurableSet_Icc.compl] with x hx hxc
  have hcx : c < x := lt_of_not_ge (fun h => hxc ⟨hx.1, h⟩)
  exact ⟨hcx.le, hx.2⟩

variable {alpha beta P ZP Q ZQ : ℝ → ℝ}
  (F : OuterFundamentalStatePair alpha beta P ZP Q ZQ a c b)

theorem OuterFundamentalStatePair.continuousOn_core (hcb : c < b) :
    ContinuousOn F.U (Icc a c) ∧ ContinuousOn F.V (Icc a c) :=
  ⟨F.U_system.continuousOn.1.mono (fun _ hx => ⟨hx.1, hx.2.trans_lt hcb⟩),
    F.V_system.continuousOn.1.mono (fun _ hx => ⟨hx.1, hx.2.trans_lt hcb⟩)⟩

/-- The actual whole operator built from the constructed homogeneous pair. -/
def OuterFundamentalStatePair.greenOperator (hcb : c < b) (lam : ℝ)
    (D : Lp ℝ 2 (μ.restrict (Icc a c)ᶜ) →L[ℝ] Lp ℝ 2 (μ.restrict (Icc a c)ᶜ))
    (p : Lp ℝ 2 (μ.restrict (Icc a c)ᶜ)) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  outerIntervalGreenOperator μ hac lam F.U F.V
    (F.continuousOn_core hcb).1 (F.continuousOn_core hcb).2 D p

theorem OuterFundamentalStatePair.kernel_core_tail
    {x y lam : ℝ} (hcb : c < b) (hPc : P c = 1)
    (hx : x ∈ Icc a c) (hy : y ∈ Ico c b) :
    outerGreenKernel lam F.U F.V x y = (F.V c / lam) * F.U x * P y :=
  outerGreenKernel_core_tail hx.2 hy.1 (F.V_tail_factor hcb hPc y hy)

theorem OuterFundamentalStatePair.kernel_tail_core
    {x y lam : ℝ} (hcb : c < b) (hPc : P c = 1)
    (hx : x ∈ Ico c b) (hy : y ∈ Icc a c) :
    outerGreenKernel lam F.U F.V x y = (F.V c / lam) * P x * F.U y := by
  rw [outerGreenKernel_symm]
  rw [F.kernel_core_tail hcb hPc hy hx]
  ring

private theorem outer_poisson_source_integrable
    (p : Lp ℝ 2 (μ.restrict (Icc a c)ᶜ))
    (hp : (p : ℝ → ℝ) =ᵐ[μ.restrict (Icc a c)ᶜ] P) (f : Lp ℝ 2 μ) :
    Integrable (fun y => P y * f y) (μ.restrict (Icc a c)ᶜ) := by
  have hP : MemLp P 2 (μ.restrict (Icc a c)ᶜ) := (memLp_congr_ae hp).mp (Lp.memLp p)
  change Integrable (P * (f : ℝ → ℝ)) (μ.restrict (Icc a c)ᶜ)
  exact hP.integrable_mul ((Lp.memLp f).restrict (Icc a c)ᶜ)

private theorem outer_integrable_of_core_tail {g : ℝ → ℝ}
    (hc : Integrable g (μ.restrict (Icc a c)))
    (ht : Integrable g (μ.restrict (Icc a c)ᶜ)) : Integrable g μ := by
  have h := hc.add_measure ht
  rwa [Measure.restrict_add_restrict_compl measurableSet_Icc] at h

include hac in
/-- Core rows of the full canonical kernel are integrable against every L² source. -/
theorem OuterFundamentalStatePair.integrable_kernel_core
    {lam x : ℝ} (hcb : c < b) (hPc : P c = 1)
    (hμ : ∀ᵐ x ∂μ, x ∈ Ico a b)
    (p : Lp ℝ 2 (μ.restrict (Icc a c)ᶜ))
    (hp : (p : ℝ → ℝ) =ᵐ[μ.restrict (Icc a c)ᶜ] P)
    (f : Lp ℝ 2 μ) (hx : x ∈ Icc a c) :
    Integrable (fun y => outerGreenKernel lam F.U F.V x y * f y) μ := by
  apply outer_integrable_of_core_tail μ (a := a) (c := c)
  · exact integrable_outer_compact_kernel_row μ hac lam F.U F.V
      (F.continuousOn_core hcb).1 (F.continuousOn_core hcb).2 f ⟨x, hx⟩
  · refine ((outer_poisson_source_integrable μ p hp f).const_mul
      ((F.V c / lam) * F.U x)).congr ?_
    filter_upwards [outer_ae_deep_interval μ hμ] with y hy
    rw [F.kernel_core_tail hcb hPc hx hy]
    ring

include hac in
/-- The core part of the single full integral agrees with the actual core block. -/
theorem OuterFundamentalStatePair.kernel_integral_core
    {lam x : ℝ} (hcb : c < b) (hPc : P c = 1)
    (hμ : ∀ᵐ x ∂μ, x ∈ Ico a b)
    (p : Lp ℝ 2 (μ.restrict (Icc a c)ᶜ))
    (hp : (p : ℝ → ℝ) =ᵐ[μ.restrict (Icc a c)ᶜ] P)
    (f : Lp ℝ 2 μ) (hx : x ∈ Icc a c) :
    (∫ y, outerGreenKernel lam F.U F.V x y * f y ∂μ) =
      (∫ y in Icc a c, outerGreenKernel lam F.U F.V x y * f y ∂μ) +
        (F.V c / lam) * F.U x * (∫ y in (Icc a c)ᶜ, P y * f y ∂μ) := by
  rw [← integral_add_compl measurableSet_Icc (F.integrable_kernel_core μ hac
    hcb hPc hμ p hp f hx)]
  congr 1
  calc
    _ = ∫ y in (Icc a c)ᶜ, ((F.V c / lam) * F.U x) * (P y * f y) ∂μ := by
      apply integral_congr_ae
      filter_upwards [outer_ae_deep_interval μ hμ] with y hy
      rw [F.kernel_core_tail hcb hPc hx hy]
      ring
    _ = _ := integral_const_mul _ _

include hac in
/-- Deep rows are integrable by the actual Dirichlet row and the Poisson vector. -/
theorem OuterFundamentalStatePair.integrable_kernel_deep
    {lam x : ℝ} (hlam : lam ≠ 0) (hcb : c < b) (hPc : P c = 1) (hQc : Q c = 0)
    (hflux : ZQ c = 1 / lam) (hμ : ∀ᵐ x ∂μ, x ∈ Ico a b)
    (p : Lp ℝ 2 (μ.restrict (Icc a c)ᶜ))
    (hp : (p : ℝ → ℝ) =ᵐ[μ.restrict (Icc a c)ᶜ] P)
    (f : Lp ℝ 2 μ) (hx : x ∈ Ico c b)
    (hrow : MemLp (fun y => Q (min x y) * P (max x y)) 2 (μ.restrict (Icc a c)ᶜ)) :
    Integrable (fun y => outerGreenKernel lam F.U F.V x y * f y) μ := by
  have hPf := outer_poisson_source_integrable μ p hp f
  have hD : Integrable (fun y => (Q (min x y) * P (max x y)) * f y)
      (μ.restrict (Icc a c)ᶜ) := by
    change Integrable ((fun y => Q (min x y) * P (max x y)) * (f : ℝ → ℝ)) _
    exact hrow.integrable_mul ((Lp.memLp f).restrict (Icc a c)ᶜ)
  apply outer_integrable_of_core_tail μ (a := a) (c := c)
  · refine ((integrable_outer_core_product μ hac F.U
      (F.continuousOn_core hcb).1 f).const_mul ((F.V c / lam) * P x)).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    rw [F.kernel_tail_core hcb hPc hx hy]
    ring
  · refine (hD.add (hPf.const_mul (outerGreenKernel lam F.U F.V c c * P x))).congr ?_
    filter_upwards [outer_ae_deep_interval μ hμ] with y hy
    simp only [Pi.add_apply]
    rw [F.green_tail_decomposition_unit_flux hlam hac hcb hPc hQc hflux hx hy]
    ring

include hac in
/-- The two deep blocks are exactly the deep restriction of the single integral. -/
theorem OuterFundamentalStatePair.kernel_integral_deep
    {lam x : ℝ} (hlam : lam ≠ 0) (hcb : c < b) (hPc : P c = 1) (hQc : Q c = 0)
    (hflux : ZQ c = 1 / lam) (hμ : ∀ᵐ x ∂μ, x ∈ Ico a b)
    (p : Lp ℝ 2 (μ.restrict (Icc a c)ᶜ))
    (hp : (p : ℝ → ℝ) =ᵐ[μ.restrict (Icc a c)ᶜ] P)
    (f : Lp ℝ 2 μ) (hx : x ∈ Ico c b)
    (hrow : MemLp (fun y => Q (min x y) * P (max x y)) 2 (μ.restrict (Icc a c)ᶜ)) :
    (∫ y, outerGreenKernel lam F.U F.V x y * f y ∂μ) =
      (F.V c / lam) * P x * (∫ y in Icc a c, F.U y * f y ∂μ) +
        (∫ y in (Icc a c)ᶜ, Q (min x y) * P (max x y) * f y ∂μ) +
        (F.U c * F.V c / lam) * P x * (∫ y in (Icc a c)ᶜ, P y * f y ∂μ) := by
  have hPf := outer_poisson_source_integrable μ p hp f
  have hD : Integrable (fun y => (Q (min x y) * P (max x y)) * f y)
      (μ.restrict (Icc a c)ᶜ) := by
    change Integrable ((fun y => Q (min x y) * P (max x y)) * (f : ℝ → ℝ)) _
    exact hrow.integrable_mul ((Lp.memLp f).restrict (Icc a c)ᶜ)
  rw [← integral_add_compl measurableSet_Icc
    (F.integrable_kernel_deep μ hac hlam hcb hPc hQc hflux hμ p hp f hx hrow)]
  have hcore : (∫ y in Icc a c, outerGreenKernel lam F.U F.V x y * f y ∂μ) =
      (F.V c / lam) * P x * (∫ y in Icc a c, F.U y * f y ∂μ) := by
    calc
      _ = ∫ y in Icc a c, ((F.V c / lam) * P x) * (F.U y * f y) ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
        rw [F.kernel_tail_core hcb hPc hx hy]
        ring
      _ = _ := integral_const_mul _ _
  have htail : (∫ y in (Icc a c)ᶜ, outerGreenKernel lam F.U F.V x y * f y ∂μ) =
      (∫ y in (Icc a c)ᶜ, Q (min x y) * P (max x y) * f y ∂μ) +
        (F.U c * F.V c / lam) * P x * (∫ y in (Icc a c)ᶜ, P y * f y ∂μ) := by
    calc
      _ = ∫ y in (Icc a c)ᶜ, Q (min x y) * P (max x y) * f y +
          ((F.U c * F.V c / lam) * P x) * (P y * f y) ∂μ := by
        apply integral_congr_ae
        filter_upwards [outer_ae_deep_interval μ hμ] with y hy
        rw [F.green_tail_decomposition_unit_flux hlam hac hcb hPc hQc hflux hx hy,
          outerGreenKernel_self]
        ring
      _ = _ := by rw [integral_add hD
        (hPf.const_mul ((F.U c * F.V c / lam) * P x)), integral_const_mul]
  rw [hcore, htail]
  ring

/-- The constructed full operator has the actual canonical Green integral
as representative for every L² source. -/
theorem OuterFundamentalStatePair.greenOperator_ae_eq_integral
    {lam : ℝ} (hlam : lam ≠ 0) (hcb : c < b) (hPc : P c = 1) (hQc : Q c = 0)
    (hflux : ZQ c = 1 / lam) (hμ : ∀ᵐ x ∂μ, x ∈ Ico a b)
    (D : Lp ℝ 2 (μ.restrict (Icc a c)ᶜ) →L[ℝ] Lp ℝ 2 (μ.restrict (Icc a c)ᶜ))
    (p : Lp ℝ 2 (μ.restrict (Icc a c)ᶜ))
    (hp : (p : ℝ → ℝ) =ᵐ[μ.restrict (Icc a c)ᶜ] P)
    (hrow : ∀ x ∈ Ico c b,
      MemLp (fun y => Q (min x y) * P (max x y)) 2 (μ.restrict (Icc a c)ᶜ))
    (hD : ∀ f : Lp ℝ 2 (μ.restrict (Icc a c)ᶜ), (D f : ℝ → ℝ) =ᵐ[
      μ.restrict (Icc a c)ᶜ] fun x =>
        ∫ y in (Icc a c)ᶜ, Q (min x y) * P (max x y) * f y ∂μ)
    (f : Lp ℝ 2 μ) :
    (F.greenOperator μ hac hcb lam D p f : ℝ → ℝ) =ᵐ[μ] fun x =>
      ∫ y, outerGreenKernel lam F.U F.V x y * f y ∂μ := by
  apply ae_of_ae_restrict_of_ae_restrict_compl (Icc a c)
  · filter_upwards [outerIntervalGreenOperator_core_rep μ hac lam F.U F.V P
      (F.continuousOn_core hcb).1 (F.continuousOn_core hcb).2 D p hp f,
      ae_restrict_mem measurableSet_Icc] with x hx hxc
    exact hx.trans (F.kernel_integral_core μ hac hcb hPc hμ p hp f hxc).symm
  · have hDsource : (D (l2Restrict μ (Icc a c)ᶜ f) : ℝ → ℝ) =ᵐ[
        μ.restrict (Icc a c)ᶜ] fun x =>
        ∫ y in (Icc a c)ᶜ, Q (min x y) * P (max x y) * f y ∂μ := by
      filter_upwards [hD (l2Restrict μ (Icc a c)ᶜ f)] with x hx
      refine hx.trans (integral_congr_ae ?_)
      filter_upwards [l2Restrict_coeFn μ (Icc a c)ᶜ f] with y hy
      rw [hy]
    filter_upwards [outerIntervalGreenOperator_tail_rep μ hac lam F.U F.V P
      (F.continuousOn_core hcb).1 (F.continuousOn_core hcb).2 D p hp f,
      hDsource, outer_ae_deep_interval μ hμ] with x hx hDx hxc
    change outerIntervalGreenOperator μ hac lam F.U F.V
      (F.continuousOn_core hcb).1 (F.continuousOn_core hcb).2 D p f x = _
    rw [hx, hDx]
    exact (F.kernel_integral_deep μ hac hlam hcb hPc hQc hflux hμ p hp f hxc (hrow x hxc)).symm

end ContinuousFlexibility.Radial
