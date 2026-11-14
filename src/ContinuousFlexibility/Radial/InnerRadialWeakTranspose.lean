module

public import ContinuousFlexibility.Radial.InnerRadialDomainPairing
public import ContinuousFlexibility.Radial.InnerRadialSmoothTestDomain
public import ContinuousFlexibility.Radial.InnerRadialH1Support
public import ContinuousFlexibility.Radial.ModeTestIntegrability
public import ContinuousFlexibility.Radial.ModeRegionalPairing

/-!
# Transposing the actual physical weak graph

The genuine H¹ integration-by-parts identity moves the derivative onto
one smooth test. The actual signed-potential relation then gives the
Jacobi operator in the frozen modal convention. All identities are in
the original radial L² measure, for arbitrary weak field coordinates.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace BigOperators

/-- A supported L² field cannot distinguish a local representative of
a smooth test from its global representative. -/
theorem innerRadial_supported_test_inner {D : ReferenceData} {a b : ℝ}
    {F T P : RadialModeL2 D} {ψ : ℝ → ℝ}
    (hF : ∀ᵐ r ∂radialHilbertMeasure D, r ∉ Ioo a b → F r = 0)
    (hT : (T : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] (Ioo a b).indicator ψ)
    (hP : (P : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] ψ) :
    ⟪F, T⟫_ℝ = ⟪F, P⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hF, hT, hP] with r hf ht hp
  rw [ht, hp]
  by_cases hr : r ∈ Ioo a b
  · rw [indicator_of_mem hr]
  · rw [hf hr, inner_zero_left, inner_zero_left]

/-- The weak derivative and signed potential give the actual Jacobi
test, with the canonical physical trace as the sole boundary term. -/
theorem innerRadialH1Domain_jacobi_test {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hw : ContDiff ℝ ∞ D.w)
    {a b : ℝ} (hab : a < b) (ha : 0 < a)
    (hcore : Ioo a b ⊆ radialCore D) (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    {j : ℕ} {q T : InnerRadialH1Pair D} {V : RadialModeL2 D}
    (hq : q ∈ innerRadialH1Domain D hw.continuous ha hcore hpos)
    (hV : InnerRadialPotentialClass D (j : ℝ) a b q.1 V)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hTu : (T.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] (Ioo a b).indicator ψ)
    (hTd : (T.2 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (Ioo a b).indicator (innerGapGradientField ψ)) :
    ⟪q.2, T.2⟫_ℝ + ⟪V, T.1⟫_ℝ +
      ⟪q.1, (matchingJacobiTest_memLp hD hψ j).toLp (matchingJacobiTest D j ψ)⟫_ℝ =
      (D.w b * deriv ψ b) * innerRadialH1Trace D hw.continuous ha hcore hpos q 1 -
        (D.w a * deriv ψ a) * innerRadialH1Trace D hw.continuous ha hcore hpos q 0 := by
  let p : ℝ → ℝ := fun r => D.w r * deriv ψ r
  have hp : ContDiff ℝ ∞ p := hw.mul (contDiff_infty_iff_deriv.mp hψ).2
  let TG := innerRadialTraceGradientTest D hw.continuous ha hcore hpos p
    hp.continuous.continuousOn
  let TV := innerRadialTraceValueTest D hw.continuous ha hcore hpos p
    (innerDirichlet_deriv_continuousOn (fun _ _ => hp.contDiffAt))
  let J : RadialModeL2 D :=
    (matchingJacobiTest_memLp hD hψ j).toLp (matchingJacobiTest D j ψ)
  have hTG : (TG : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (Ioo a b).indicator (fun r => (sqrt 12 * r / (12 * D.w r)) * p r) := by
    exact innerRadialIntervalToLp_ae D hw.continuous ha hcore _ _ _
  have hTV : (TV : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (Ioo a b).indicator (fun r => (r ^ 2 / (12 * D.w r)) * deriv p r) := by
    exact innerRadialIntervalToLp_ae D hw.continuous ha hcore _ _ _
  have hJ : (J : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] matchingJacobiTest D j ψ :=
    MemLp.coeFn_toLp _
  have hgrad : TG = T.2 := by
    apply Lp.ext
    filter_upwards [hTG, hTd] with r ht htd
    rw [ht, htd]
    by_cases hr : r ∈ Ioo a b
    · rw [indicator_of_mem hr, indicator_of_mem hr]
      have hw0 := (hpos r (Ioo_subset_Icc_self hr)).ne'
      have hs0 : sqrt (12 : ℝ) ≠ 0 := (sqrt_pos.mpr (by norm_num)).ne'
      have hs : (sqrt (12 : ℝ)) ^ 2 = 12 := sq_sqrt (by norm_num)
      dsimp only [p, innerGapGradientField]
      calc
        _ = ((sqrt 12) ^ 2 / 12) * (r / sqrt 12) * deriv ψ r := by
          field_simp [hw0, hs0]
          <;> ring
        _ = _ := by rw [hs]; norm_num
    · rw [indicator_of_notMem hr, indicator_of_notMem hr]
  have hvalue : ⟪q.1, TV⟫_ℝ = ⟪q.1, J⟫_ℝ + ⟪V, T.1⟫_ℝ := by
    rw [L2.inner_def, L2.inner_def, L2.inner_def,
      ← integral_add (L2.integrable_inner (𝕜 := ℝ) q.1 J) (L2.integrable_inner V T.1)]
    apply integral_congr_ae
    filter_upwards [hTV, hJ, hV, hTu,
      innerRadialH1Domain_supported D hw.continuous ha hcore hpos hq]
      with r htv hj hv htu hsupport
    rw [htv, hj, hv, htu]
    by_cases hr : r ∈ Ioo a b
    · simp only [indicator_of_mem hr, RCLike.inner_apply, conj_trivial,
        matchingJacobiTest, matchingDensity, radialJacobi, p]
      have hr0 := (ha.trans hr.1).ne'
      have hw0 := (hpos r (Ioo_subset_Icc_self hr)).ne'
      field_simp [hr0, hw0]
      <;> ring
    · simp only [indicator_of_notMem hr, hsupport hr, inner_zero_left, inner_zero_right,
        zero_add]
  have h := innerRadialH1Domain_firstOrder_pairing D hw.continuous hab ha hcore hpos hp hq
  change ⟪q.2, TG⟫_ℝ + ⟪q.1, TV⟫_ℝ = _ at h
  rw [hgrad, hvalue] at h
  change ⟪q.2, T.2⟫_ℝ + ⟪V, T.1⟫_ℝ + ⟪q.1, J⟫_ℝ = _
  simpa only [p, add_assoc, add_left_comm, add_comm] using h

/-- The genuine matched weak graph gives transposed Jacobi testing.
The source sum and the field sum are the actual physical coordinates.
Only raw support and representative identities occur as additional inputs. -/
theorem innerRadialChainWeakGraph_transpose {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hw : ContDiff ℝ ∞ D.w) {n j : ℕ}
    (G : InnerRadialChainGeometry D n) {bordered : Bool} {central : Fin (n + 1)}
    {column : RadialModeL2 D} {q T : Fin (n + 1) → InnerRadialH1Pair D}
    {v f : Fin (n + 1) → RadialModeL2 D} {c d : ℝ}
    (hgraph : InnerRadialChainWeakGraph D hw.continuous G bordered (j : ℝ)
      central column q v f c d)
    (hf : ∀ k, ∀ᵐ r ∂radialHilbertMeasure D,
      r ∉ Ioo (G.left k) (G.right k) → f k r = 0)
    (hcolumn : ∀ᵐ r ∂radialHilbertMeasure D,
      r ∉ Ioo (G.left central) (G.right central) → column r = 0)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hleft : ψ (G.left 0) = 0) (hright : ψ (G.right (Fin.last n)) = 0)
    (hTu : ∀ k, ((T k).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (Ioo (G.left k) (G.right k)).indicator ψ)
    (hTd : ∀ k, ((T k).2 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (Ioo (G.left k) (G.right k)).indicator (innerGapGradientField ψ)) :
    ⟪∑ k, (q k).1,
      (matchingJacobiTest_memLp hD hψ j).toLp (matchingJacobiTest D j ψ)⟫_ℝ -
      c * ⟪column, (matching_memLp_of_continuousOn hD hψ.continuous.measurable
        hψ.continuous.continuousOn 2).toLp ψ⟫_ℝ =
      -⟪∑ k, f k, (matching_memLp_of_continuousOn hD hψ.continuous.measurable
        hψ.continuous.continuousOn 2).toLp ψ⟫_ℝ := by
  let P : RadialModeL2 D := (matching_memLp_of_continuousOn hD hψ.continuous.measurable
    hψ.continuous.continuousOn 2).toLp ψ
  let J : RadialModeL2 D :=
    (matchingJacobiTest_memLp hD hψ j).toLp (matchingJacobiTest D j ψ)
  have hP : (P : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] ψ := MemLp.coeFn_toLp _
  have htest := innerRadialChain_smooth_test_mem D hw.continuous G hψ hleft hright hTu hTd
  have heq := hgraph.2.2.2 T htest
  obtain ⟨ξ, hξ⟩ := (innerRadialChainDomain_trace_iff D hw.continuous G q).mp hgraph.1
  have hsum : (∑ k, (⟪(q k).2, (T k).2⟫_ℝ + ⟪v k, (T k).1⟫_ℝ)) +
      (∑ k, ⟪(q k).1, J⟫_ℝ) = 0 := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ k, ((D.w (G.right k) * deriv ψ (G.right k)) *
          innerChainBoundaryRestriction n k ξ 1 -
          (D.w (G.left k) * deriv ψ (G.left k)) *
            innerChainBoundaryRestriction n k ξ 0) := by
        apply Finset.sum_congr rfl
        intro k _
        exact (innerRadialH1Domain_jacobi_test hD hw (G.left_lt_right k)
          (G.left_pos k) (G.in_core k) (G.weight_pos k) (hξ k).1
          (hgraph.2.1 k) hψ (hTu k) (hTd k)).trans
          (congrArg (fun z : Fin 2 → ℝ => (D.w (G.right k) * deriv ψ (G.right k)) * z 1 -
            (D.w (G.left k) * deriv ψ (G.left k)) * z 0) (hξ k).2)
      _ = 0 := innerRadialChainBoundary_pairing_sum G ξ (fun r => D.w r * deriv ψ r)
  have hc : (∑ k : Fin (n + 1), c * ⟪if k = central then column else 0, (T k).1⟫_ℝ) =
      c * ⟪column, P⟫_ℝ := by
    rw [Finset.sum_eq_single central]
    · rw [if_pos rfl, innerRadial_supported_test_inner hcolumn (hTu central) hP]
    · intro k _ hk
      simp only [if_neg hk, inner_zero_left, mul_zero]
    · intro hc
      exact (hc (Finset.mem_univ central)).elim
  have hforce : (∑ k, ⟪f k, (T k).1⟫_ℝ) = ∑ k, ⟪f k, P⟫_ℝ :=
    Finset.sum_congr rfl (fun k _ => innerRadial_supported_test_inner (hf k) (hTu k) hP)
  simp only [innerRadialChainResidual, innerRadialWeakResidual_apply,
    Finset.sum_sub_distrib, Finset.sum_add_distrib] at heq
  rw [hc, hforce] at heq
  change ⟪∑ k, (q k).1, J⟫_ℝ - c * ⟪column, P⟫_ℝ = -⟪∑ k, f k, P⟫_ℝ
  rw [sum_inner, sum_inner]
  rw [Finset.sum_add_distrib] at hsum
  linarith only [heq, hsum]

/-- The physical column density gives the frozen scalar pairing. This
uses its actual representative, not an assumed adjoint identity. -/
theorem innerRadialColumn_inner_eq {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {column : RadialModeL2 D}
    (hcolumn : (column : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      fun r => referenceColumn D r / matchingDensity D r)
    (U : RadialModeL2 D) :
    ⟪column, U⟫_ℝ = ∫ r in D.a..D.b, referenceColumn D r * U r := by
  rw [matchingMode_inner_eq_integral hD]
  apply matchingInterval_congr_ae hD
  apply (radialHilbertMeasure_ae_iff hD).mpr
  filter_upwards [(radialHilbertMeasure_ae_iff hD).mp hcolumn,
    ae_restrict_mem (show MeasurableSet (radialCore D) from measurableSet_Ioo)]
    with r hc hr
  rw [hc]
  field_simp [(matchingDensity_pos hD hr).ne']

/-- The actual weak graph has the transposed integral equation for every
smooth zero-endpoint test, including tests not compactly supported in
the open chain. This stronger conclusion will recover the endpoint values. -/
theorem innerRadialChainWeakGraph_jacobi_integral {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hw : ContDiff ℝ ∞ D.w) {n j : ℕ}
    (G : InnerRadialChainGeometry D n) {bordered : Bool} {central : Fin (n + 1)}
    {column : RadialModeL2 D} {q : Fin (n + 1) → InnerRadialH1Pair D}
    {v f : Fin (n + 1) → RadialModeL2 D} {c d : ℝ}
    (hgraph : InnerRadialChainWeakGraph D hw.continuous G bordered (j : ℝ)
      central column q v f c d)
    (hf : ∀ k, ∀ᵐ r ∂radialHilbertMeasure D,
      r ∉ Ioo (G.left k) (G.right k) → f k r = 0)
    (hcs : ∀ᵐ r ∂radialHilbertMeasure D,
      r ∉ Ioo (G.left central) (G.right central) → column r = 0)
    (hc : (column : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      fun r => referenceColumn D r / matchingDensity D r)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hleft : ψ (G.left 0) = 0) (hright : ψ (G.right (Fin.last n)) = 0) :
    (∫ r in D.a..D.b, (∑ k, (q k).1) r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r) -
      c * (∫ r in D.a..D.b, referenceColumn D r * ψ r) =
      -(∫ r in D.a..D.b, matchingDensity D r * (∑ k, f k) r * ψ r) := by
  let T : Fin (n + 1) → InnerRadialH1Pair D := fun k =>
    (innerRadialIntervalToLp D hw.continuous (G.left_pos k) (G.in_core k)
      (fun r hr => (G.weight_pos k r (Ioo_subset_Icc_self hr)).le) ψ
      hψ.continuous.continuousOn,
     innerRadialIntervalToLp D hw.continuous (G.left_pos k) (G.in_core k)
      (fun r hr => (G.weight_pos k r (Ioo_subset_Icc_self hr)).le)
      (innerGapGradientField ψ) (innerGapGradientField_continuous hψ).continuousOn)
  have hTu (k) : ((T k).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (Ioo (G.left k) (G.right k)).indicator ψ :=
    innerRadialIntervalToLp_ae D hw.continuous (G.left_pos k) (G.in_core k)
      (fun r hr => (G.weight_pos k r (Ioo_subset_Icc_self hr)).le) ψ
      hψ.continuous.continuousOn
  have hTd (k) : ((T k).2 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (Ioo (G.left k) (G.right k)).indicator (innerGapGradientField ψ) :=
    innerRadialIntervalToLp_ae D hw.continuous (G.left_pos k) (G.in_core k)
      (fun r hr => (G.weight_pos k r (Ioo_subset_Icc_self hr)).le)
      (innerGapGradientField ψ) (innerGapGradientField_continuous hψ).continuousOn
  have he := innerRadialChainWeakGraph_transpose hD hw G hgraph hf hcs hψ hleft hright hTu hTd
  let hP := matching_memLp_of_continuousOn hD hψ.continuous.measurable
    hψ.continuous.continuousOn 2
  have hcol : ⟪column, hP.toLp ψ⟫_ℝ =
      ∫ r in D.a..D.b, referenceColumn D r * ψ r := by
    rw [innerRadialColumn_inner_eq hD hc]
    apply matchingInterval_congr_ae hD
    filter_upwards [hP.coeFn_toLp] with r hr
    rw [hr]
  rw [matchingJacobi_integral_eq_inner hD _ hψ j,
    matchingSource_integral_eq_inner hD _ hP, ← hcol]
  exact he

/-- In particular, the actual physical weak graph satisfies the original
modal differential equation on the whole open inner interval. -/
theorem innerRadialChainWeakGraph_modeLocalEquation {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hw : ContDiff ℝ ∞ D.w) {n j : ℕ}
    (G : InnerRadialChainGeometry D n) {bordered : Bool} {central : Fin (n + 1)}
    {column : RadialModeL2 D} {q : Fin (n + 1) → InnerRadialH1Pair D}
    {v f : Fin (n + 1) → RadialModeL2 D} {c d : ℝ}
    (hgraph : InnerRadialChainWeakGraph D hw.continuous G bordered (j : ℝ)
      central column q v f c d)
    (hf : ∀ k, ∀ᵐ r ∂radialHilbertMeasure D,
      r ∉ Ioo (G.left k) (G.right k) → f k r = 0)
    (hcs : ∀ᵐ r ∂radialHilbertMeasure D,
      r ∉ Ioo (G.left central) (G.right central) → column r = 0)
    (hc : (column : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      fun r => referenceColumn D r / matchingDensity D r) :
    ModeLocalEquation D j (Ioo (G.left 0) (G.right (Fin.last n)))
      (∑ k, (q k).1, c) (∑ k, f k, d) := by
  intro ψ hψ _ hs
  exact innerRadialChainWeakGraph_jacobi_integral hD hw G hgraph hf hcs hc hψ
    (by by_contra h; exact (lt_irrefl _) (hs h).1)
    (by by_contra h; exact (lt_irrefl _) (hs h).2)

end ContinuousFlexibility.Radial
