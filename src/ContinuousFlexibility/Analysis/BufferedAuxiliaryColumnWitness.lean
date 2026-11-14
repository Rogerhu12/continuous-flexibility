module

public import ContinuousFlexibility.Analysis.BufferedRadialAuxiliaryColumn

/-!
# Retaining the actual auxiliary column's single-component support

The interval and positive component are selected before the column is
encoded in the unchanged height space.  The same column then supplies
the replacement spaces, their true Q normalization, and every support
statement.  No new choice is made after passing to the replacement data.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

theorem exists_radial_auxiliaryColumn_single_positive_buffer
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hD : RadialProfileGeometry D) {F : Set ℝ}
    (B : N04PositiveNormalizationBuffer D.a D.b (deriv D.w) F) :
    ∃ (i : N04PositiveComponent D.a D.b (deriv D.w)) (l u : ℝ)
      (ψ : (S.height (3 / 4 : ℝ)).Space),
      l < u ∧ Icc l u ⊆ Ioo (B.normalizationLeft i) (B.normalizationRight i) ∧
      HasCompactRadialSupport D ((S.height (3 / 4 : ℝ)).decode ψ) ∧
      S.Q ψ = 1 ∧
      (∀ p : PolarPoint, (S.height (3 / 4 : ℝ)).decode ψ p =
        (S.height (3 / 4 : ℝ)).decode ψ (p.1, 0)) ∧
      (∀ p : PolarPoint, (S.height (3 / 4 : ℝ)).decode ψ p ≠ 0 → p.1 ∈ Icc l u) := by
  have hdw : Continuous (deriv D.w) := hD.2.2.1.1.continuous_deriv (by simp)
  obtain ⟨a, b, ha, hab, hb, hpos⟩ := spaces_exists_positive_deriv_interval hD
  have haP : a ∈ n04PositiveRegion D.a D.b (deriv D.w) :=
    ⟨⟨ha, hab.trans hb⟩, hpos a ⟨le_rfl, hab.le⟩⟩
  obtain ⟨i, _, _⟩ := (n04PositiveComponent_existsUnique_mem_iff a).2 haP
  obtain ⟨l, hnl, hlr⟩ := exists_between (B.ordered i).2.2.1
  obtain ⟨u, hlu, hun⟩ := exists_between hlr
  have hinterval : Icc l u ⊆ Ioo (B.normalizationLeft i) (B.normalizationRight i) :=
    fun _ hr => ⟨hnl.trans_le hr.1, hr.2.trans_lt hun⟩
  have hregion : Icc l u ⊆ B.region :=
    fun r hr => mem_iUnion.mpr ⟨i, hinterval hr⟩
  have hcore : Icc l u ⊆ radialCore D :=
    fun r hr => (B.region_subset_positive hdw (hregion hr)).1
  obtain ⟨ψ, hcompact, hnormal, hradial, hsupport⟩ :=
    exists_radial_auxiliaryColumn_on_interval (N := Icc l u) hT hS hlu hcore Subset.rfl
  exact ⟨i, l, u, ψ, hlu, hinterval, hcompact, hnormal, hradial, hsupport⟩

/-- All conclusions concern one fixed new column in the same height
model.  Its interval and component remain available for the subsequent
reference-atom estimates on the actual replacement atlas. -/
theorem exists_buffered_auxiliaryColumn_replacement_with_witness
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S}
    {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hA : CanonicalGeometry D S C K base ε)
    {F : Set ℝ} (B : N04PositiveNormalizationBuffer D.a D.b (deriv D.w) F)
    (hregion : K.normalizationRegion = B.region) :
    ∃ (i : N04PositiveComponent D.a D.b (deriv D.w)) (l u : ℝ)
      (ψ : (S.height (3 / 4 : ℝ)).Space),
      l < u ∧ Icc l u ⊆ Ioo (B.normalizationLeft i) (B.normalizationRight i) ∧
      IsPhysicalSpaces D T (physicalSpacesReplaceAuxiliaryColumn S ψ) ∧
      NonlinearPropertiesThrough03 D T (physicalSpacesReplaceAuxiliaryColumn S ψ)
        (geometryReplaceAuxiliaryColumn C ψ) (returnReplaceAuxiliaryColumn R ψ)
        (correctionReplaceAuxiliaryColumn L ψ) base loss ε ∧
      CanonicalGeometry D (physicalSpacesReplaceAuxiliaryColumn S ψ)
        (geometryReplaceAuxiliaryColumn C ψ) (canonicalReplaceAuxiliaryColumn K ψ) base ε ∧
      CanonicalGeometry.AuxiliaryColumnGauge (physicalSpacesReplaceAuxiliaryColumn S ψ)
        (canonicalReplaceAuxiliaryColumn K ψ) ∧
      (physicalSpacesReplaceAuxiliaryColumn S ψ).Q
        (physicalSpacesReplaceAuxiliaryColumn S ψ).psi = 1 ∧
      HasCompactRadialSupport D ((S.height (3 / 4 : ℝ)).decode ψ) ∧
      (∀ p : PolarPoint, (S.height (3 / 4 : ℝ)).decode ψ p ≠ 0 → p.1 ∈ Icc l u) ∧
      (∀ p : PolarPoint, (S.height (3 / 4 : ℝ)).decode ψ p ≠ 0 → p.1 ∈ i.val) := by
  obtain ⟨_, hprofile⟩ := hN.1.1.1.1
  have hD : RadialProfileGeometry D := hprofile.1
  have hdw : Continuous (deriv D.w) := hD.2.2.1.1.continuous_deriv (by simp)
  obtain ⟨i, l, u, ψ, hlu, hinterval, hcompact, hnormal, hradial, hsupport⟩ :=
    exists_radial_auxiliaryColumn_single_positive_buffer hT hS hD B
  have hregionSupport (p : PolarPoint)
      (hp : (S.height (3 / 4 : ℝ)).decode ψ p ≠ 0) : p.1 ∈ B.region :=
    mem_iUnion.mpr ⟨i, hinterval (hsupport p hp)⟩
  have hgauge : CanonicalGeometry.AuxiliaryColumnGauge
      (physicalSpacesReplaceAuxiliaryColumn S ψ) (canonicalReplaceAuxiliaryColumn K ψ) := by
    refine ⟨hradial, fun p hp => ?_⟩
    change p.1 ∈ K.normalizationRegion
    rw [hregion]
    exact hregionSupport p hp
  refine ⟨i, l, u, ψ, hlu, hinterval,
    isPhysicalSpaces_replaceAuxiliaryColumn hT hS ψ hcompact hnormal,
    nonlinearThrough03_replaceAuxiliaryColumn hN ψ,
    canonicalGeometry_replaceAuxiliaryColumn hA ψ,
    hgauge, hnormal, hcompact, hsupport, ?_⟩
  intro p hp
  have hn := hinterval (hsupport p hp)
  have ho := B.ordered i
  exact (n04PositiveComponent_mem_iff hdw i).mpr
    ⟨(ho.1.trans ho.2.1).trans hn.1,
      hn.2.trans (ho.2.2.2.1.trans ho.2.2.2.2)⟩

end ContinuousFlexibility.Analysis
