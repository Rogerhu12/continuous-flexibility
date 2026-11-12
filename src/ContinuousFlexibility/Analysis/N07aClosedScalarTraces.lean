import ContinuousFlexibility.Radial.WeakDivergenceRegularity
import ContinuousFlexibility.Statements.Radial
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.Positivity

/-!
# Closed scalar traces of one weak-divergence solution

The side values and side derivative values are continuous up to their own
closed interval. Equality with one C¹ scalar representative identifies both
endpoint traces without a smooth extension through the cut.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped Topology ContDiff

/-- A continuous closed side and its continuous first derivative coincide with
the value and derivative of a C1 representative of the same open-interval class.
The closed derivative is identified from true derivatives strictly inside the
interval, then extended to both endpoints by continuity. -/
theorem n07a_closedScalarJets_eq_of_ae_C1
    {a b : ℝ} (hab : a < b) {A B v : ℝ → ℝ}
    (hA : ContinuousOn A (Icc a b))
    (hB : ContinuousOn B (Icc a b))
    (hAB : ∀ x ∈ Ioo a b, HasDerivAt A (B x) x)
    (hv : ContDiff ℝ 1 v)
    (hAv : A =ᵐ[volume.restrict (Ioo a b)] v) :
    EqOn A v (Icc a b) ∧ EqOn B (deriv v) (Icc a b) := by
  have hAvOpen : EqOn A v (Ioo a b) :=
    Measure.eqOn_Ioo_of_ae_eq volume hAv
      (hA.mono Ioo_subset_Icc_self) hv.continuous.continuousOn
  have hBvOpen : EqOn B (deriv v) (Ioo a b) := by
    intro x hx
    have hnear : v =ᶠ[𝓝 x] A := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      exact (hAvOpen hy).symm
    exact ((hAB x hx).congr_of_eventuallyEq hnear).deriv.symm
  exact ⟨hAvOpen.of_subset_closure hA hv.continuous.continuousOn
      Ioo_subset_Icc_self (closure_Ioo hab.ne).symm.subset,
    hBvOpen.of_subset_closure hB hv.continuous_deriv_one.continuousOn
      Ioo_subset_Icc_self (closure_Ioo hab.ne).symm.subset⟩

/-- The two closed scalar side integrals have equal value and radial-derivative
traces whenever they represent one C1 scalar function on the open halves. -/
theorem n07a_closedScalar_firstTraces_match
    {l c r : ℝ} (hlc : l < c) (hcr : c < r)
    {AL AR BL BR v : ℝ → ℝ}
    (hAL : ContinuousOn AL (Icc l c))
    (hAR : ContinuousOn AR (Icc c r))
    (hBL : ContinuousOn BL (Icc l c))
    (hBR : ContinuousOn BR (Icc c r))
    (hDL : ∀ x ∈ Ioo l c, HasDerivAt AL (BL x) x)
    (hDR : ∀ x ∈ Ioo c r, HasDerivAt AR (BR x) x)
    (hv : ContDiff ℝ 1 v)
    (hL : AL =ᵐ[volume.restrict (Ioo l c)] v)
    (hR : AR =ᵐ[volume.restrict (Ioo c r)] v) :
    AL c = AR c ∧ BL c = BR c := by
  obtain ⟨hL₀, hL₁⟩ := n07a_closedScalarJets_eq_of_ae_C1 hlc hAL hBL hDL hv hL
  obtain ⟨hR₀, hR₁⟩ := n07a_closedScalarJets_eq_of_ae_C1 hcr hAR hBR hDR hv hR
  exact ⟨(hL₀ ⟨hlc.le, le_rfl⟩).trans (hR₀ ⟨le_rfl, hcr.le⟩).symm,
    (hL₁ ⟨hlc.le, le_rfl⟩).trans (hR₁ ⟨le_rfl, hcr.le⟩).symm⟩

/-- Feed the actual projected weak-divergence equation directly into the
closed-side trace lemma. The forcing is only interval integrable. -/
theorem n07a_closedScalar_firstTraces_match_of_weak_divergence
    {l c r : ℝ} (hlc : l < c) (hcr : c < r)
    {u g w AL AR BL BR : ℝ → ℝ}
    (hu : IntervalIntegrable u volume l r)
    (hg : IntervalIntegrable g volume l r)
    (hw : ContDiff ℝ ∞ w)
    (hwn : ∀ x ∈ Icc l r, w x ≠ 0)
    (hweak : ∀ ψ : ℝ → ℝ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo l r →
      (∫ x in l..r, u x * deriv (fun y => w y * deriv ψ y) x) =
        ∫ x in l..r, g x * ψ x)
    (hAL : ContinuousOn AL (Icc l c))
    (hAR : ContinuousOn AR (Icc c r))
    (hBL : ContinuousOn BL (Icc l c))
    (hBR : ContinuousOn BR (Icc c r))
    (hDL : ∀ x ∈ Ioo l c, HasDerivAt AL (BL x) x)
    (hDR : ∀ x ∈ Ioo c r, HasDerivAt AR (BR x) x)
    (hL : AL =ᵐ[volume.restrict (Ioo l c)] u)
    (hR : AR =ᵐ[volume.restrict (Ioo c r)] u) :
    AL c = AR c ∧ BL c = BR c := by
  obtain ⟨v, C, hv, huv, hflux, hac, hdflux⟩ :=
    exists_contDiff_representative_of_weak_divergence
      (hlc.trans hcr) hu hg hw hwn hweak
  have hleft : Ioo l c ⊆ Ioo l r :=
    fun _ hx => ⟨hx.1, hx.2.trans hcr⟩
  have hright : Ioo c r ⊆ Ioo l r :=
    fun _ hx => ⟨hlc.trans hx.1, hx.2⟩
  exact n07a_closedScalar_firstTraces_match hlc hcr hAL hAR hBL hBR hDL hDR hv
    (hL.trans (ae_restrict_of_ae_restrict_of_subset hleft huv))
    (hR.trans (ae_restrict_of_ae_restrict_of_subset hright huv))

/-- A continuous periodic function whose squared integral over one positive
period is zero vanishes everywhere. This is elementary positivity, with no
Fourier completeness or coefficient reconstruction. -/
theorem n07a_periodic_eq_zero_of_integral_sq_eq_zero
    {J : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hJ : Continuous J) (hJp : Function.Periodic J T)
    (hzero : (∫ θ in (0 : ℝ)..T, J θ ^ 2) = 0) :
    ∀ θ, J θ = 0 := by
  have hI : Integrable (fun θ => J θ ^ 2)
      (volume.restrict (Ioc (0 : ℝ) T)) :=
    ((hJ.pow 2).intervalIntegrable 0 T).1
  rw [intervalIntegral.integral_of_le hT.le] at hzero
  have hsq : (fun θ => J θ ^ 2) =ᵐ[volume.restrict (Ioc (0 : ℝ) T)] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun θ => sq_nonneg (J θ)) hI).mp hzero
  have hae : J =ᵐ[volume.restrict (Ioc (0 : ℝ) T)] 0 := by
    filter_upwards [hsq] with θ hθ
    exact sq_eq_zero_iff.mp hθ
  have hclosed : EqOn J (fun _ => 0) (Ioc (0 : ℝ) T) :=
    Measure.eqOn_Ioc_of_ae_eq volume hae hJ.continuousOn continuousOn_const
  intro θ
  let t := toIocMod hT 0 θ
  obtain ⟨ht, k, hk⟩ := (toIocMod_eq_iff hT).mp
    (show toIocMod hT 0 θ = t from rfl)
  have ht' : t ∈ Ioc (0 : ℝ) T := by simpa only [zero_add] using ht
  rw [hk, (hJp.zsmul k) t]
  exact hclosed ht'

/-- A smooth periodic jump annihilating every smooth periodic angular test
is zero: choose the jump itself as the test. -/
theorem n07a_periodic_eq_zero_of_smooth_angular_pairings
    {J : ℝ → ℝ}
    (hJ : ContDiff ℝ ∞ J)
    (hJp : Function.Periodic J (2 * Real.pi))
    (hpair : ∀ β : ℝ → ℝ,
      ContDiff ℝ ∞ β → Function.Periodic β (2 * Real.pi) →
      radialAngularMean (fun θ => J θ * β θ) = 0) :
    ∀ θ, J θ = 0 := by
  have hmean : radialAngularMean (fun θ => J θ ^ 2) = 0 := by
    simpa only [pow_two] using hpair J hJ hJp
  unfold radialAngularMean at hmean
  have hden : (2 * Real.pi)⁻¹ ≠ 0 := by positivity
  have hzero : (∫ θ in (0 : ℝ)..2 * Real.pi, J θ ^ 2) = 0 :=
    (mul_eq_zero.mp hmean).resolve_left hden
  exact n07a_periodic_eq_zero_of_integral_sq_eq_zero
    (by positivity) hJ.continuous hJp hzero

end ContinuousFlexibility.Analysis
