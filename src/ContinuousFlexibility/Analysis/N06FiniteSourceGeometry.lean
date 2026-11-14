module

public import ContinuousFlexibility.Analysis.N06FiniteLocalSourceColumns
public import ContinuousFlexibility.Analysis.N06PhysicalPeriodicity
public import ContinuousFlexibility.Analysis.CanonicalStripGeometry
public import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Actual canonical source fields and finite physical support

Smoothness and symmetry of the source transform follow from the original
chart, height and Jacobian clauses. Physical radial support can meet only
the explicitly listed intersecting pieces. Finiteness of that set is an
input about the atlas; it is not inferred from the frozen N04 clauses.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff Topology BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

theorem n06_contDiffOn_planeJacobian
    {F : PolarPoint → PolarPoint} {U : Set PolarPoint}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) :
    ContDiffOn ℝ ∞ (planeJacobian F) U := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ F) U :=
    hF.fderiv_of_isOpen hU (by simp)
  have hR : ContDiffOn ℝ ∞ (fun p => fderiv ℝ F p (1, 0)) U :=
    hD.clm_apply contDiffOn_const
  have hA : ContDiffOn ℝ ∞ (fun p => fderiv ℝ F p (0, 1)) U :=
    hD.clm_apply contDiffOn_const
  exact (hR.fst.mul hA.snd).sub (hR.snd.mul hA.fst)

section CanonicalSource

variable {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
  {K : CanonicalData S} {base : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

theorem n06_canonicalSource_contDiffOn
    (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f (annularOpen D)) (m : ℕ) :
    ContDiffOn ℝ ∞ (canonicalSource S K z m f) (canonicalOpen S K m) := by
  have hdomains := hK.domains z hz hs m
  obtain ⟨_, hGmap, _, _, hF, hG, hH, hgood⟩ :=
    hK.charts z hz hs m
  have hsub : physicalPieceOpen S K z m ⊆ annularOpen D := hdomains.2.2.1
  have hJ := n06_contDiffOn_planeJacobian hdomains.1 hF
  have hJne : ∀ p ∈ physicalPieceOpen S K z m, planeJacobian (K.chart z m) p ≠ 0 :=
    fun p hp => (hgood p hp).2.1
  have hweight := (hH.mul (hf.mono hsub)).div (hJ.abs hJne)
    (fun p hp => abs_ne_zero.mpr (hJne p hp))
  exact hweight.comp hG hGmap

theorem n06_canonicalSource_periodicOn
    (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {f : PolarPoint → ℝ}
    (hf : ∀ p ∈ annularOpen D, f (p + (0, Real.pi)) = f p)
    (m : ℕ) {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    canonicalSource S K z m f (p + (0, Real.pi)) = canonicalSource S K z m f p := by
  have hc := hK.charts z hz hs m
  have hd := hK.domains z hz hs m
  have hq := hc.2.1 hp
  have hqD : K.inverseChart z m p ∈ annularOpen D := hd.2.2.1 hq
  have hshift : ∀ q ∈ physicalPieceOpen S K z m, q + (0, Real.pi) ∈
      physicalPieceOpen S K z m := fun q hq => (hd.2.2.2.1 q).mpr hq
  have hG := inverseChart_periodic_of_chart_periodic_on hc.2.1 hshift hc.2.2.1
    hc.2.2.2.1 (fun q hq => (hc.2.2.2.2.2.2.2 q hq).2.2.1) hp
  have hH := (hc.2.2.2.2.2.2.2 _ hq).2.2.2
  have hJ := n06_planeJacobian_chart_lift_on hd.1 hc.2.2.2.2.1 hshift
    (fun q hq => (hc.2.2.2.2.2.2.2 q hq).2.2.1) hq
  change K.height z m (K.inverseChart z m (p + (0, Real.pi))) *
      f (K.inverseChart z m (p + (0, Real.pi))) /
      |planeJacobian (K.chart z m) (K.inverseChart z m (p + (0, Real.pi)))| = _
  rw [hG, hH, hf _ hqD, hJ]
  rfl

theorem n06_canonicalSource_evenOn
    (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {f : PolarPoint → ℝ}
    (hf : ∀ p ∈ annularOpen D, f (p.1, -p.2) = f p)
    (m : ℕ) {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    canonicalSource S K z m f (p.1, -p.2) = canonicalSource S K z m f p := by
  have hq := (hK.charts z hz hs m).2.1 hp
  have hqD : K.inverseChart z m p ∈ annularOpen D :=
    (hK.domains z hz hs m).2.2.1 hq
  have hsym := hK.reflection z hz hs m _ hq
  have hG := hK.inverseReflection z hz hs m p hp
  change K.height z m (K.inverseChart z m (p.1, -p.2)) *
      f (K.inverseChart z m (p.1, -p.2)) /
      |planeJacobian (K.chart z m) (K.inverseChart z m (p.1, -p.2))| = _
  rw [hG, hsym.2.1, hf _ hqD, hsym.2.2]
  rfl

theorem n06_canonicalSource_reflectionOn
    (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {f : PolarPoint → ℝ}
    (hpF : ∀ p ∈ annularOpen D, f (p + (0, Real.pi)) = f p)
    (heF : ∀ p ∈ annularOpen D, f (p.1, -p.2) = f p)
    (m : ℕ) {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    canonicalSource S K z m f (p.1, Real.pi - p.2) = canonicalSource S K z m f p := by
  have hn : (p.1, -p.2) ∈ canonicalOpen S K m := ⟨hp.1, mem_univ _⟩
  have ht := n06_canonicalSource_periodicOn hK hz hs hpF m hn
  have he := n06_canonicalSource_evenOn hK hz hs heF m hp
  have hshift : (p.1, -p.2) + (0, Real.pi) = (p.1, Real.pi - p.2) := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, add_zero] <;> ring
  rw [hshift] at ht
  exact ht.trans he

/-- A physical source that vanishes off J has zero canonical source on
every physical piece disjoint from J. The inverse is used only on its
actual open canonical domain. -/
theorem n06_canonicalSource_zero_of_disjoint_radialSupport
    (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {J : Set ℝ} {f : PolarPoint → ℝ}
    (hf : ∀ r, r ∉ J → ∀ θ, f (r, θ) = 0)
    {m : ℕ}
    (hm : ¬(physicalPieceOpen S K z m ∩ (J ×ˢ (univ : Set ℝ))).Nonempty)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    canonicalSource S K z m f p = 0 := by
  have hq := (hK.charts z hz hs m).2.1 hp
  have hnot : (K.inverseChart z m p).1 ∉ J :=
    fun hJ => hm ⟨_, hq, hJ, mem_univ _⟩
  have hzero := hf _ hnot (K.inverseChart z m p).2
  simp only [canonicalSource, Prod.eta] at hzero ⊢
  rw [hzero, mul_zero, zero_div]

end CanonicalSource

/-- At the reference state the actual support-piece set is exactly the
original set of intersecting radial intervals. This only uses the
reference-domain clause; no current domain is identified with a strip. -/
theorem n06_referenceSourcePieces_eq_referenceIntervals
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hK : N04PartA D S C K base ε) (J : Set ℝ) :
    {m : ℕ | (physicalPieceOpen S K (C.referenceState, 0) m ∩
        (J ×ˢ (univ : Set ℝ))).Nonempty} =
      {m : ℕ | (Ioo (K.physicalLeft m) (K.physicalRight m) ∩ J).Nonempty} := by
  ext m
  change (physicalPieceOpen S K (C.referenceState, 0) m ∩
    (J ×ˢ (univ : Set ℝ))).Nonempty ↔ _
  rw [hK.referenceDomain m]
  constructor
  · rintro ⟨p, hp, hpJ⟩
    exact ⟨p.1, hp.1, hpJ.1⟩
  · rintro ⟨r, hr, hrJ⟩
    exact ⟨(r, 0), ⟨hr, mem_univ _⟩, hrJ, mem_univ _⟩

/-- The finite-index hypothesis records exactly the physical pieces met
by J. All remaining inputs concern actual fields and their finite angular
jets, and the output belongs to the original source level. -/
theorem n06Volume_exists_finite_canonical_source
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S} {V : VolumeModelData S K}
    {base : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (γ t : ℝ) (b : ℕ) {J : Set ℝ}
    (hfinite : Set.Finite {m : ℕ |
      (physicalPieceOpen S K z m ∩ (J ×ˢ (univ : Set ℝ))).Nonempty})
    {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (hp : ∀ p ∈ annularOpen D, f (p + (0, Real.pi)) = f p)
    (he : ∀ p ∈ annularOpen D, f (p.1, -p.2) = f p)
    (hsupport : ∀ r, r ∉ J → ∀ θ, f (r, θ) = 0)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ m ∈ hfinite.toFinset, ∀ j, j ≤ b → ∀ p ∈ canonicalOpen S K m,
      |mixedDerivative 0 j (canonicalSource S K z m f) p| ≤ δ) :
    ∃ F : V.level γ t b,
      (∀ m, (V.forget γ t b F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalSource S K z m f) ∧
      ‖F‖ ≤ (n06WeakAngularMultiplierCost b *
        n06FiniteSourceCost T S K γ t b hfinite.toFinset) * δ := by
  apply n06Volume_exists_finite_local_source hD hT hV γ t b hfinite.toFinset
    (fun m => canonicalSource S K z m f)
    (n06_canonicalSource_contDiffOn hK hz hs hf)
    (fun m _ hq => n06_canonicalSource_periodicOn hK hz hs hp m hq)
    (fun m _ hq => n06_canonicalSource_reflectionOn hK hz hs hp he m hq)
    _ hδ hbound
  intro m hm p hpU
  apply n06_canonicalSource_zero_of_disjoint_radialSupport hK hz hs hsupport _ hpU
  intro hmeet
  exact hm (hfinite.mem_toFinset.mpr hmeet)

end ContinuousFlexibility.Statements
