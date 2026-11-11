import ContinuousFlexibility.Radial.ModeWeakGreen
import ContinuousFlexibility.Radial.ModeRegionalPairing
import ContinuousFlexibility.Radial.MatchingWeakGluing
import ContinuousFlexibility.Radial.MatchingTraceCalculus

/-!
# Green's boundary form for the outer weak realization

A plateau cutoff contains both matching cuts and stays strictly inside
the radial core. The remaining test is an admissible outer weak test.
Thus only finite regular intervals are integrated by parts, even when
the original test approaches either degenerate endpoint.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace
open ContinuousFlexibility.Statements

theorem matching_homogeneous_green_on_compact {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {j : ℕ} {J : Set ℝ} {U : RadialModePair D}
    (hEq : ModeLocalEquation D j J U 0) (hs : U.2 = 0)
    {u φ : ℝ → ℝ} (hu : (U.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u)
    {l h : ℝ} (hlh : l < h) (hsub : Icc l h ⊆ radialCore D)
    (hJ : Ioo l h ⊆ J) (hreg : ContDiffOn ℝ 1 u (Icc l h))
    (hφ : ContDiff ℝ ∞ φ) :
    (∫ x in l..h, u x * radialJacobi ((j : ℝ) ^ 2) D.w φ x) =
      (u h * (D.w h * deriv φ h) -
        φ h * (D.w h * derivWithin u (Icc l h) h)) -
      (u l * (D.w l * deriv φ l) -
        φ l * (D.w l * derivWithin u (Icc l h) l)) := by
  have hg := modeLocalEquation_green_on_compact hD hB hEq hu
    hlh hsub hJ hreg (hφ.of_le (by simp)).contDiffOn
  simp only [Prod.fst_zero] at hg
  have hzero :
      (∫ x in l..h, u x * radialJacobi ((j : ℝ) ^ 2) D.w φ x -
        (U.2 * referenceColumn D x -
          matchingDensity D x * (0 : RadialModeL2 D) x) * φ x) =
      ∫ x in l..h, u x * radialJacobi ((j : ℝ) ^ 2) D.w φ x := by
    apply matchingSubinterval_congr_ae hD hlh.le hsub
    filter_upwards [Lp.coeFn_zero ℝ 2 (radialHilbertMeasure D)] with x hx
    simp only [hs, hx, Pi.zero_apply, zero_mul, mul_zero, sub_zero]
  have hφh := (hφ.differentiable (by simp) h).derivWithin
    (uniqueDiffOn_Icc hlh h ⟨hlh.le, le_rfl⟩)
  have hφl := (hφ.differentiable (by simp) l).derivWithin
    (uniqueDiffOn_Icc hlh l ⟨le_rfl, hlh.le⟩)
  rw [hzero, hφh, hφl] at hg
  exact hg

/-- The finite outer boundary form for every original smooth weak test. -/
theorem matchingOuter_green_test {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D)
    {M : RadialMatchingData D} (hM : MatchingLocalRealizations D M)
    (ha : D.a < M.innerLeft) (hm : M.innerLeft < M.innerRight)
    (hb : M.innerRight < D.b)
    {U : RadialModePair D} (hfix : M.sourceOuter U = U)
    (hEq : ModeLocalEquation D M.frequency (matchingOuterRegion D M) U 0)
    {u : ℝ → ℝ} (hu : (U.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u)
    (hreg : ContDiffOn ℝ 1 u (Ioc D.a M.innerLeft ∪ Ico M.innerRight D.b))
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : Function.support ψ ⊆ radialCore D) :
    (∫ x in D.a..D.b, U.1 x * radialJacobi ((M.frequency : ℝ) ^ 2) D.w ψ x) =
      (u M.innerLeft * (D.w M.innerLeft * deriv ψ M.innerLeft) -
        ψ M.innerLeft * (D.w M.innerLeft *
          derivWithin u (closure (matchingOuterRegion D M)) M.innerLeft)) -
      (u M.innerRight * (D.w M.innerRight * deriv ψ M.innerRight) -
        ψ M.innerRight * (D.w M.innerRight *
          derivWithin u (closure (matchingOuterRegion D M)) M.innerRight)) := by
  let l : ℝ := (D.a + M.innerLeft) / 2
  let r : ℝ := (M.innerRight + D.b) / 2
  have hal : D.a < l := by dsimp only [l]; linarith
  have hll : l < M.innerLeft := by dsimp only [l]; linarith
  have hrr : M.innerRight < r := by dsimp only [r]; linarith
  have hrb : r < D.b := by dsimp only [r]; linarith
  have hlr : l < r := hll.trans (hm.trans hrr)
  have hab : D.a < D.b := ha.trans (hm.trans hb)
  have hsub : Icc l r ⊆ radialCore D := by
    intro x hx
    exact ⟨hal.trans_le hx.1, hx.2.trans_lt hrb⟩
  have hsubL : Icc l M.innerLeft ⊆ radialCore D :=
    (Icc_subset_Icc le_rfl (hm.trans hrr).le).trans hsub
  have hsubR : Icc M.innerRight r ⊆ radialCore D :=
    (Icc_subset_Icc (hll.trans hm).le le_rfl).trans hsub
  have hsubI : Icc M.innerLeft M.innerRight ⊆ radialCore D :=
    (Icc_subset_Icc hll.le hrr.le).trans hsub
  have hscalar : U.2 = 0 := by
    simpa only [hfix] using (hM.2.2.2.1 U).2.1
  obtain ⟨η, hη, hcη, hsη, heη⟩ :=
    exists_matching_interval_cutoff hll hm.le hrr
  let φ : ℝ → ℝ := fun x => η x * ψ x
  let χ : ℝ → ℝ := fun x => ψ x - φ x
  have hφ : ContDiff ℝ ∞ φ := hη.mul hψ
  have hχ : ContDiff ℝ ∞ χ := hψ.sub hφ
  have hφsupp : Function.support φ ⊆ Function.support η := by
    intro x hx hηx
    exact hx (by simp only [φ, hηx, zero_mul])
  have hcφ : HasCompactSupport φ := hcη.mono hφsupp
  have htφ : tsupport φ ⊆ Ioo l r := (closure_mono hφsupp).trans hsη
  have hcχ : HasCompactSupport χ := hcψ.mono (by
    intro x hx hψx
    exact hx (by simp only [χ, φ, hψx, mul_zero, sub_self]))
  have heφ (x : ℝ) (hx : x ∈ Icc M.innerLeft M.innerRight) :
      φ =ᶠ[𝓝 x] ψ := by
    filter_upwards [heη x hx] with y hy
    simp only [φ, hy, one_mul]
  have hsχ : Function.support χ ⊆ matchingOuterRegion D M := by
    intro x hx
    have hψx : ψ x ≠ 0 := by
      intro hz
      exact hx (by simp only [χ, φ, hz, mul_zero, sub_self])
    have hcore := hsψ hψx
    by_cases hleft : x < M.innerLeft
    · exact Or.inl ⟨hcore.1, hleft⟩
    · have hright : M.innerRight < x := by
        by_contra hn
        have hxI : x ∈ Icc M.innerLeft M.innerRight :=
          ⟨le_of_not_gt hleft, le_of_not_gt hn⟩
        exact hx (by simp only [χ, (heφ x hxI).eq_of_nhds, sub_self])
      exact Or.inr ⟨hright, hcore.2⟩
  have hχzero :
      (∫ x in D.a..D.b, U.1 x *
        radialJacobi ((M.frequency : ℝ) ^ 2) D.w χ x) = 0 := by
    rw [matchingJacobi_integral_eq_inner hD U.1 hχ M.frequency]
    have he := (modeLocalEquation_iff_inner hD M.frequency
      (matchingOuterRegion D M) U 0).mp hEq χ hχ hcχ hsχ
    simpa only [hscalar, Prod.fst_zero, inner_zero_left, zero_mul,
      sub_zero, neg_zero] using he
  have hreduce :
      (∫ x in D.a..D.b, U.1 x * radialJacobi ((M.frequency : ℝ) ^ 2) D.w ψ x) =
      ∫ x in D.a..D.b, U.1 x * radialJacobi ((M.frequency : ℝ) ^ 2) D.w φ x := by
    have he : ψ = fun x => χ x + φ x := by funext x; dsimp only [χ]; ring
    rw [he]
    simp only [matching_radialJacobi_add (matchingProfileGeometry hD).2.2.1.1 hχ hφ,
      mul_add]
    rw [intervalIntegral.integral_add
      (matchingJacobi_intervalIntegrable hD U.1 hχ M.frequency)
      (matchingJacobi_intervalIntegrable hD U.1 hφ M.frequency), hχzero, zero_add]
  let f : ℝ → ℝ := fun x => U.1 x * radialJacobi ((M.frequency : ℝ) ^ 2) D.w φ x
  have hfsupp : Function.support f ⊆ Ioo l r := by
    intro x hx
    apply htφ
    apply matchingJacobi_support_subset hD hφ M.frequency
    intro hz
    exact hx (by simp only [f, hz, mul_zero])
  have hlocal : (∫ x in D.a..D.b, f x) = ∫ x in l..r, f x :=
    matchingInterval_eq_subinterval (Ioo_subset_Icc_self.trans hsub) hfsupp
  have hint : IntervalIntegrable f volume D.a D.b :=
    matchingJacobi_intervalIntegrable hD U.1 hφ M.frequency
  have hint' (p q : ℝ) (hap : D.a ≤ p) (hpq : p ≤ q) (hqb : q ≤ D.b) :
      IntervalIntegrable f volume p q := by
    apply hint.mono_set
    rw [uIcc_of_le hpq, uIcc_of_le hab.le]
    exact Icc_subset_Icc hap hqb
  have hmid : (∫ x in M.innerLeft..M.innerRight, f x) = 0 := by
    have hs : (U.1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
        (fun x => if x ∈ Ioo M.innerLeft M.innerRight then 0 else U.1 x) := by
      simpa only [hfix] using (hM.2.2.2.1 U).2.2.2
    have hs' := ae_restrict_of_ae_restrict_of_subset
      (Ioo_subset_Icc_self.trans hsubI) ((radialHilbertMeasure_ae_iff hD).mp hs)
    rw [intervalIntegral.integral_of_le hm.le, integral_Ioc_eq_integral_Ioo]
    calc
      _ = ∫ _x in Ioo M.innerLeft M.innerRight, (0 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [hs', ae_restrict_mem measurableSet_Ioo] with x hx hxI
        simp only [f, hx, if_pos hxI, zero_mul]
      _ = 0 := by simp
  have hsplit : (∫ x in l..r, f x) =
      (∫ x in l..M.innerLeft, f x) + ∫ x in M.innerRight..r, f x := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hint' l M.innerRight hal.le (hll.trans hm).le hb.le)
      (hint' M.innerRight r (ha.trans hm).le hrr.le hrb.le),
      ← intervalIntegral.integral_add_adjacent_intervals
        (hint' l M.innerLeft hal.le hll.le (hm.trans hb).le)
        (hint' M.innerLeft M.innerRight ha.le hm.le hb.le),
      hmid, add_zero]
  have hrep (p q : ℝ) (hpq : p ≤ q) (hp : Icc p q ⊆ radialCore D) :
      (∫ x in p..q, f x) =
        ∫ x in p..q, u x * radialJacobi ((M.frequency : ℝ) ^ 2) D.w φ x := by
    apply matchingSubinterval_congr_ae hD hpq hp
    filter_upwards [hu] with x hx
    simp only [f, hx]
  have hL := matching_homogeneous_green_on_compact hD hB hEq hscalar hu hll hsubL
    (fun x hx => Or.inl ⟨hal.trans hx.1, hx.2⟩)
    (hreg.mono (fun x hx => Or.inl ⟨hal.trans_le hx.1, hx.2⟩)) hφ
  have hR := matching_homogeneous_green_on_compact hD hB hEq hscalar hu hrr hsubR
    (fun x hx => Or.inr ⟨hx.1, hx.2.trans hrb⟩)
    (hreg.mono (fun x hx => Or.inr ⟨hx.1, hx.2.trans_lt hrb⟩)) hφ
  have hφl : φ l = 0 := image_eq_zero_of_notMem_tsupport
    (fun ht => (lt_irrefl l) (htφ ht).1)
  have hdφl : deriv φ l = 0 := deriv_of_notMem_tsupport
    (fun ht => (lt_irrefl l) (htφ ht).1)
  have hφr : φ r = 0 := image_eq_zero_of_notMem_tsupport
    (fun ht => (lt_irrefl r) (htφ ht).2)
  have hdφr : deriv φ r = 0 := deriv_of_notMem_tsupport
    (fun ht => (lt_irrefl r) (htφ ht).2)
  have hφL := heφ M.innerLeft ⟨le_rfl, hm.le⟩
  have hφR := heφ M.innerRight ⟨hm.le, le_rfl⟩
  rw [hreduce]
  change (∫ x in D.a..D.b, f x) = _
  rw [hlocal, hsplit, hrep l M.innerLeft hll.le hsubL,
    hrep M.innerRight r hrr.le hsubR, hL, hR,
    hφl, hdφl, hφr, hdφr,
    hφL.eq_of_nhds, hφR.eq_of_nhds, hφL.deriv_eq, hφR.deriv_eq,
    matchingOuter_derivWithin_left ha hm hb hal hll u,
    matchingOuter_derivWithin_right ha hm hb hrr hrb u]
  ring

end ContinuousFlexibility.Radial
