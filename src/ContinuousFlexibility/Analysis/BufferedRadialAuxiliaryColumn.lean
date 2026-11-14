module

public import ContinuousFlexibility.Analysis.PhysicalSpacesAuxiliaryColumn
public import ContinuousFlexibility.Analysis.N04PositiveNormalizationBuffer

/-!
# A genuine radial auxiliary column in the normalization buffer

The negative derivative of a smooth left cutoff has physical integral
one. Its transition is placed strictly inside one chosen positive
normalization interval. The same height model encodes this exact radial
function, so replacing the auxiliary column preserves Q and every
Through03 field while giving the displayed AuxiliaryColumnGauge.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

theorem exists_radial_auxiliaryColumn_on_interval
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {l u : ℝ} {N : Set ℝ} (hlu : l < u)
    (hcore : Icc l u ⊆ radialCore D) (hN : Icc l u ⊆ N) :
    ∃ ψ : (S.height (3 / 4 : ℝ)).Space,
      HasCompactRadialSupport D ((S.height (3 / 4 : ℝ)).decode ψ) ∧
      S.Q ψ = 1 ∧
      (∀ p : PolarPoint, (S.height (3 / 4 : ℝ)).decode ψ p =
        (S.height (3 / 4 : ℝ)).decode ψ (p.1, 0)) ∧
      (∀ p : PolarPoint, (S.height (3 / 4 : ℝ)).decode ψ p ≠ 0 → p.1 ∈ N) := by
  let χ : ℝ → ℝ := spacesLeftCutoff l u
  let g : ℝ → ℝ := fun r => -deriv χ r
  have hχ : ContDiff ℝ ∞ χ := spacesLeftCutoff_contDiff l u
  have hg : ContDiff ℝ ∞ g := (contDiff_infty_iff_deriv.mp hχ).2.neg
  have hzero (r : ℝ) (hr : r ∉ Icc l u) : g r = 0 := by
    change -deriv (spacesLeftCutoff l u) r = 0
    rw [spacesLeftCutoff_deriv_eq_zero hlu hr, neg_zero]
  have hmember : HeightMember D T (3 / 4 : ℝ) (fun p : PolarPoint => g p.1) :=
    spaces_heightMember_of_compact_radial hT hg isCompact_Icc hcore hzero _
  have hal : D.a < l := (hcore ⟨le_rfl, hlu.le⟩).1
  have hub : u < D.b := (hcore ⟨hlu.le, le_rfl⟩).2
  have hleft : χ D.a = 1 := spacesLeftCutoff_eq_one hlu hal.le
  have hright : χ D.b = 0 := spacesLeftCutoff_eq_zero hlu hub.le
  have hint : physicalSourceIntegral D (fun p : PolarPoint => g p.1) = 1 := by
    rw [spaces_physicalSourceIntegral_radial]
    change (∫ r in D.a..D.b, -deriv χ r) = 1
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_deriv_eq_sub
      (fun r _ => hχ.differentiable (by simp) r)
      ((contDiff_infty_iff_deriv.mp hχ).2.continuous.intervalIntegrable D.a D.b),
      hleft, hright]
    norm_num
  obtain ⟨hheight, _, _, _, _, _, _, hQ, _⟩ := hS
  obtain ⟨ψ, hψ⟩ := (hheight (3 / 4)).2.2.2.2.1 _ hmember
  refine ⟨ψ, ?_, ?_, ?_, ?_⟩
  · exact ⟨Icc l u, isCompact_Icc, hcore,
      fun r hr θ => (congrFun hψ (r, θ)).trans (hzero r hr)⟩
  · rw [hQ ψ, hψ]
    exact hint
  · intro p
    exact (congrFun hψ p).trans (congrFun hψ (p.1, 0)).symm
  · intro p hp
    apply hN
    by_contra hout
    exact hp ((congrFun hψ p).trans (hzero p.1 hout))

theorem exists_radial_auxiliaryColumn_in_positiveBuffer
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hD : RadialProfileGeometry D) {F : Set ℝ}
    (B : N04PositiveNormalizationBuffer D.a D.b (deriv D.w) F) :
    ∃ ψ : (S.height (3 / 4 : ℝ)).Space,
      HasCompactRadialSupport D ((S.height (3 / 4 : ℝ)).decode ψ) ∧
      S.Q ψ = 1 ∧
      (∀ p : PolarPoint, (S.height (3 / 4 : ℝ)).decode ψ p =
        (S.height (3 / 4 : ℝ)).decode ψ (p.1, 0)) ∧
      (∀ p : PolarPoint, (S.height (3 / 4 : ℝ)).decode ψ p ≠ 0 → p.1 ∈ B.region) := by
  have hdw : Continuous (deriv D.w) := hD.2.2.1.1.continuous_deriv (by simp)
  obtain ⟨a, b, ha, hab, hb, hpos⟩ := spaces_exists_positive_deriv_interval hD
  have haP : a ∈ n04PositiveRegion D.a D.b (deriv D.w) :=
    ⟨⟨ha, hab.trans hb⟩, hpos a ⟨le_rfl, hab.le⟩⟩
  obtain ⟨i, _, _⟩ := (n04PositiveComponent_existsUnique_mem_iff a).2 haP
  have hi := B.ordered i
  obtain ⟨l, hnl, hlr⟩ := exists_between hi.2.2.1
  obtain ⟨u, hlu, hun⟩ := exists_between hlr
  have hregion : Icc l u ⊆ B.region := by
    intro r hr
    exact mem_iUnion.mpr ⟨i, ⟨hnl.trans_le hr.1, hr.2.trans_lt hun⟩⟩
  have hcore : Icc l u ⊆ radialCore D :=
    fun r hr => (B.region_subset_positive hdw (hregion hr)).1
  exact exists_radial_auxiliaryColumn_on_interval hT hS hlu hcore hregion

/-- The auxiliary gauge is supplied by an actual new column, rather than
being imposed on the arbitrary old normalizer. All Through03 data are
the fieldwise copies above; only the displayed auxiliary source changes. -/
theorem exists_buffered_auxiliaryColumnGauge_replacement
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    {F : Set ℝ} (B : N04PositiveNormalizationBuffer D.a D.b (deriv D.w) F)
    (K : CanonicalData S) (hregion : K.normalizationRegion = B.region) :
    ∃ ψ : (S.height (3 / 4 : ℝ)).Space,
      IsPhysicalSpaces D T (physicalSpacesReplaceAuxiliaryColumn S ψ) ∧
      NonlinearPropertiesThrough03 D T (physicalSpacesReplaceAuxiliaryColumn S ψ)
        (geometryReplaceAuxiliaryColumn C ψ) (returnReplaceAuxiliaryColumn R ψ)
        (correctionReplaceAuxiliaryColumn L ψ) base loss ε ∧
      CanonicalGeometry.AuxiliaryColumnGauge (physicalSpacesReplaceAuxiliaryColumn S ψ)
        (canonicalReplaceAuxiliaryColumn K ψ) := by
  obtain ⟨_, hprofile⟩ := hN.1.1.1.1
  have hD : RadialProfileGeometry D := hprofile.1
  obtain ⟨ψ, hcompact, hnormal, hradial, hsupport⟩ :=
    exists_radial_auxiliaryColumn_in_positiveBuffer hT hS hD B
  refine ⟨ψ, isPhysicalSpaces_replaceAuxiliaryColumn hT hS ψ hcompact hnormal,
    nonlinearThrough03_replaceAuxiliaryColumn hN ψ, hradial, ?_⟩
  intro p hp
  change p.1 ∈ K.normalizationRegion
  rw [hregion]
  exact hsupport p hp

end ContinuousFlexibility.Analysis
