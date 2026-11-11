import ContinuousFlexibility.Analysis.StateNeighborhood
import Mathlib.Topology.Algebra.Support

/-!
# The normalization support avoids every interior critical root

The support condition in `RadialTrueBorder` alone does not separate its
closed support from the roots. The stronger N01 profile-germ condition
does: vary only the real metric-control coordinate by a nonzero small
number. The actual profile is then `w * exp(t * chi)`, so its required
agreement with the positive reference profile forces `chi` to vanish
on a neighborhood of each interior critical root.

The reference column also vanishes off this same closed support, by
locality of its actual derivatives. Thus `tsupport chi` is an actual
compact forbidden set for later endpoint cutoff choices.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

private theorem pairGrading_metric_shift
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (n : ℕ) (x : E × (ℝ × F)) (t : ℝ) :
    pairGrading p (pairGrading realGrading q) n
      ((x.1, (x.2.1 + t, x.2.2)) - x) = |t| := by
  simp only [pairGrading_apply, Prod.fst_sub, Prod.snd_sub, sub_self,
    add_sub_cancel_left, map_zero, realGrading, coe_normSeminorm,
    Real.norm_eq_abs, zero_add, add_zero]

private def normalizationMetricShift (S : PhysicalSpacesData)
    (x : AnnularState S) (t : ℝ) : AnnularState S :=
  (x.1, (x.2.1 + t, x.2.2))

private theorem stateGrading_normalizationMetricShift (S : PhysicalSpacesData)
    (x : AnnularState S) (t : ℝ) (n : ℕ) :
    stateGrading S n (normalizationMetricShift S x t - x) = |t| :=
  pairGrading_metric_shift (heightPairGrading S)
    (pairGrading (S.circle (3 / 4 : ℝ)).grading (S.circle (3 / 4 : ℝ)).grading)
    n x t

private theorem stateProfile_normalizationMetricShift
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (href : referenceStateConditions D S C) (t : ℝ) :
    stateProfile D S C (normalizationMetricShift S C.referenceState t) =
      fun r => D.w r * Real.exp (t * D.chi r) := by
  have hκ : C.referenceState.2.2.1 = 0 := href.2.2.2.1
  have hν : C.referenceState.2.1 = 0 := href.2.2.1
  have hk (m : ℕ) :
      stateKappa S (normalizationMetricShift S C.referenceState t) m = 0 := by
    change angularMean ((S.circle (3 / 4 : ℝ)).decode C.referenceState.2.2.1 m) = 0
    rw [hκ, map_zero]
    simp only [angularMean, Pi.zero_apply, intervalIntegral.integral_zero, mul_zero]
  funext r
  change D.w r * Real.exp ((C.referenceState.2.1 + t) * D.chi r +
    ∑' m, stateKappa S (normalizationMetricShift S C.referenceState t) m *
      C.control m r) = D.w r * Real.exp (t * D.chi r)
  simp only [hν, zero_add, hk, zero_mul, tsum_zero, add_zero]

/-- The actual N01 germ condition forces the metric control to vanish
on a neighborhood of every interior critical root. -/
theorem n01_chi_eventuallyEq_zero_at_critical
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    {r : ℝ} (hr : r ∈ Ioo D.a D.b) (hcritical : deriv D.w r = 0) :
    D.chi =ᶠ[𝓝 r] fun _ => 0 := by
  have hε : 0 < ε := hN.2.1
  have href : referenceStateConditions D S C := hN.2.2.1
  let t : ℝ := ε / 2
  have ht : 0 < t := half_pos hε
  have hz :
      (normalizationMetricShift S C.referenceState t, (0 : ℝ)) ∈
        stateNeighborhood S C base ε := by
    change stateGrading S base
      (normalizationMetricShift S C.referenceState t - C.referenceState) < ε ∧
        |(0 : ℝ)| < ε
    rw [stateGrading_normalizationMetricShift, abs_of_pos ht, abs_zero]
    exact ⟨half_lt_self hε, hε⟩
  have hroot : stateProfile D S C (normalizationMetricShift S C.referenceState t) =ᶠ[𝓝 r]
      D.w :=
    hN.2.2.2.2.2.2.2.2.2.2.1
      (normalizationMetricShift S C.referenceState t, 0) hz r hr hcritical
  rw [stateProfile_normalizationMetricShift href t] at hroot
  obtain ⟨_, hD⟩ := hN.1.1
  have hwpos : ∀ x ∈ Ioo D.a D.b, 0 < D.w x := hD.1.2.2.2.2.1
  filter_upwards [hroot, isOpen_Ioo.mem_nhds hr] with x hx hxi
  have he : Real.exp (t * D.chi x) = 1 :=
    mul_left_cancel₀ (hwpos x hxi).ne' (hx.trans (mul_one (D.w x)).symm)
  have hzero : t * D.chi x = 0 := Real.exp_eq_one_iff.mp he
  exact (mul_eq_zero.mp hzero).resolve_left ht.ne'

theorem n01_critical_not_mem_tsupport_chi
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    {r : ℝ} (hr : r ∈ Ioo D.a D.b) (hcritical : deriv D.w r = 0) :
    r ∉ tsupport D.chi :=
  notMem_tsupport_iff_eventuallyEq.mpr
    (n01_chi_eventuallyEq_zero_at_critical hN hr hcritical)

/-- Locality of the two actual derivatives in the reference column. -/
theorem referenceColumn_eq_zero_of_not_mem_tsupport_chi
    (D : ReferenceData) {r : ℝ} (hr : r ∉ tsupport D.chi) :
    referenceColumn D r = 0 := by
  have hχ : D.chi =ᶠ[𝓝 r] fun _ => 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hr
  have hw : (fun x => D.w x * D.chi x) =ᶠ[𝓝 r] fun _ => 0 := by
    filter_upwards [hχ] with x hx
    simp only [hx, mul_zero]
  have hflux : (fun x => D.w x * D.chi x * deriv D.phi x) =ᶠ[𝓝 r] fun _ => 0 := by
    filter_upwards [hχ] with x hx
    simp only [hx, mul_zero, zero_mul]
  change deriv (fun x => D.w x * D.chi x * deriv D.phi x) r -
    4 * deriv (fun x => D.w x * D.chi x) r / r * D.phi r = 0
  rw [hflux.deriv_eq, hw.deriv_eq]
  simp only [deriv_const, mul_zero, zero_div, zero_mul, sub_zero]

theorem support_referenceColumn_subset_tsupport_chi (D : ReferenceData) :
    Function.support (referenceColumn D) ⊆ tsupport D.chi := by
  intro r hr
  by_contra hnot
  exact hr (referenceColumn_eq_zero_of_not_mem_tsupport_chi D hnot)

/-- The forbidden set is compact, contains the actual normalization
column, and misses every interior critical root. -/
theorem n01_normalization_support_compact_and_avoids_critical
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε) :
    IsCompact (tsupport D.chi) ∧
      Function.support (referenceColumn D) ⊆ tsupport D.chi ∧
      ∀ r ∈ Ioo D.a D.b, deriv D.w r = 0 → r ∉ tsupport D.chi :=
  ⟨hN.1.2.2.2.1.2.1, support_referenceColumn_subset_tsupport_chi D,
    fun _ hr hc => n01_critical_not_mem_tsupport_chi hN hr hc⟩

/-- A genuine root collar can therefore be chosen disjoint from the
same closed support used for normalization. -/
theorem n01_exists_root_collar_disjoint_normalization_support
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    {r : ℝ} (hr : r ∈ Ioo D.a D.b) (hcritical : deriv D.w r = 0) :
    ∃ δ : ℝ, 0 < δ ∧ Disjoint (Metric.ball r δ) (tsupport D.chi) := by
  have hnot := n01_critical_not_mem_tsupport_chi hN hr hcritical
  have hn : (tsupport D.chi)ᶜ ∈ 𝓝 r :=
    (isClosed_tsupport D.chi).isOpen_compl.mem_nhds hnot
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp hn
  exact ⟨δ, hδ, Set.disjoint_left.mpr fun x hx hs => hsub hx hs⟩

end ContinuousFlexibility.Analysis
