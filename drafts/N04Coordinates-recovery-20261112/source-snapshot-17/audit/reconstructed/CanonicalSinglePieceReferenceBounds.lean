import ContinuousFlexibility.Analysis.CanonicalAuxiliaryNormalization
import ContinuousFlexibility.Analysis.PhysicalTransmissionTrace
import ContinuousFlexibility.Analysis.N07bAtlasEnergy
import ContinuousFlexibility.Analysis.N07bCanonicalAngularPullback
import ContinuousFlexibility.Analysis.N07aAngularReferenceCoordinates
import ContinuousFlexibility.Analysis.N08RadialFamilyMaterialJets

/-!
# Reference source jets for one compact physical support interval

The actual reference inverse and the actual radial chart send the fixed
physical support into a compact subset of its canonical unit interval.
All other pieces have zero source, by disjointness of the real reference
intervals. Compactness therefore gives one bound at each finite order,
without a uniform estimate on the other charts or their inverse jets.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open CanonicalGeometry
open scoped Topology ContDiff BigOperators

def canonicalReferenceUnitSource (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S)
    (m : ℕ) (f : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  canonicalSource S K (C.referenceState, 0) m f (canonicalUnitPoint K m p)

private theorem auxiliary_unitPoint_mem {S : PhysicalSpacesData} {K : CanonicalData S}
    {m : ℕ} (hlen : K.left m < K.right m) {p : PolarPoint} (hp : p ∈ unitStrip) :
    canonicalUnitPoint K m p ∈ canonicalOpen S K m := by
  have hl := mul_pos (sub_pos.mpr hlen) hp.1.1
  have hu := mul_lt_of_lt_one_right (sub_pos.mpr hlen) hp.1.2
  refine ⟨?_, mem_univ _⟩
  dsimp only [canonicalUnitPoint]
  constructor <;> linarith

private theorem compact_radial_unit_mixed_bound
    {g : PolarPoint → ℝ} {E : Set ℝ}
    (hg : ContDiffOn ℝ ∞ g unitStrip)
    (hradial : ∀ p ∈ unitStrip, g p = g (p.1, 0))
    (hE : IsCompact E) (hsub : E ⊆ Ioo (0 : ℝ) 1)
    (hzero : ∀ p ∈ unitStrip, p.1 ∉ E → g p = 0) (i j : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ unitStrip, |mixedDerivative i j g p| ≤ B := by
  have hcont : ContinuousOn (mixedDerivative i j g) (E ×ˢ ({0} : Set ℝ)) :=
    (contDiffOn_mixedDerivative (isOpen_Ioo.prod isOpen_univ) hg i j).continuousOn.mono
      (fun p hp => ⟨hsub hp.1, mem_univ _⟩)
  obtain ⟨M, hM⟩ := (hE.prod isCompact_singleton).exists_bound_of_continuousOn hcont
  refine ⟨max M 0, le_max_right _ _, fun p hp => ?_⟩
  by_cases hpE : p.1 ∈ E
  · have he : EqOn g (fun q : PolarPoint => g (q.1, 0)) unitStrip := hradial
    have hjets := mixedDerivative_eqOn_of_isOpen
      (isOpen_Ioo.prod isOpen_univ) he i j
    have heq : mixedDerivative i j g p = mixedDerivative i j g (p.1, 0) := by
      calc
        _ = mixedDerivative i j (fun q : PolarPoint => g (q.1, 0)) p := hjets hp
        _ = mixedDerivative i j (fun q : PolarPoint => g (q.1, 0)) (p.1, 0) := by
          simp only [n08_mixedDerivative_radial]
        _ = _ := (hjets (x := (p.1, 0)) ⟨hp.1, mem_univ _⟩).symm
    have hb : |mixedDerivative i j g (p.1, 0)| ≤ M := by
      simpa only [Real.norm_eq_abs] using hM (p.1, 0) ⟨hpE, mem_singleton 0⟩
    rw [heq]
    exact hb.trans (le_max_left _ _)
  · have hV : IsOpen (unitStrip ∩ (Eᶜ ×ˢ (univ : Set ℝ))) :=
      (isOpen_Ioo.prod isOpen_univ).inter (hE.isClosed.isOpen_compl.prod isOpen_univ)
    have he : EqOn g (fun _ : PolarPoint => (0 : ℝ))
        (unitStrip ∩ (Eᶜ ×ˢ (univ : Set ℝ))) :=
      fun q hq => hzero q hq.1 hq.2.1
    have hd := (mixedDerivative_eqOn_of_isOpen hV he i j)
      (x := p) ⟨hp, hpE, mem_univ _⟩
    have hz : mixedDerivative i j g p = 0 := by
      simpa only [mixedDerivative, iteratedDeriv_fun_const_zero] using hd
    simpa only [hz, abs_zero] using (le_max_right M 0)

theorem canonicalReferenceUnitSource_singlePiece_bounds
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S}
    {base : ℕ} {ε : ℝ} (hA : CanonicalGeometry D S C K base ε)
    (hz₀ : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hs₀ : stateSector S C.referenceState) (hR : ReferenceRadial S C K)
    (f : PolarPoint → ℝ) (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (hfradial : ∀ p, f p = f (p.1, 0))
    (m₀ : ℕ) {l u : ℝ}
    (hinterval : Icc l u ⊆ Ioo (K.physicalLeft m₀) (K.physicalRight m₀))
    (hsupport : ∀ p, f p ≠ 0 → p.1 ∈ Icc l u) :
    (∀ m, ContDiffOn ℝ ∞ (canonicalReferenceUnitSource S C K m f) unitStrip ∧
      ∀ p ∈ unitStrip, canonicalReferenceUnitSource S C K m f (p + (0, Real.pi)) =
        canonicalReferenceUnitSource S C K m f p) ∧
    ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m i j p, p ∈ unitStrip → i + j ≤ s →
      |mixedDerivative i j (canonicalReferenceUnitSource S C K m f) p| ≤ B := by
  let g : ℕ → PolarPoint → ℝ := fun m => canonicalReferenceUnitSource S C K m f
  have hunit (m : ℕ) : ContDiff ℝ ∞ (canonicalUnitPoint K m) :=
    (contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk contDiff_snd
  have hmem (m : ℕ) {p : PolarPoint} (hp : p ∈ unitStrip) :=
    auxiliary_unitPoint_mem (hA.referenceBounds m).2.1 hp
  have hgs (m : ℕ) : ContDiffOn ℝ ∞ (g m) unitStrip :=
    (n07b_contDiffOn_canonicalSource_of_open hA hz₀ hs₀ m
      (hf.mono (hA.domains (C.referenceState, 0) hz₀ hs₀ m).2.2.1)).comp
        (hunit m).contDiffOn (fun p hp => hmem m hp)
  have hrad (m : ℕ) (p : PolarPoint) (hp : p ∈ unitStrip) : g m p = g m (p.1, 0) := by
    have hc := hA.charts (C.referenceState, 0) hz₀ hs₀ m
    have hmap : MapsTo (K.inverseChart (C.referenceState, 0) m)
        (canonicalOpen S K m) (referencePhysicalPieceOpen S K m) := by
      simpa only [hA.referenceDomain] using hc.2.1
    have hF : ContDiffOn ℝ ∞ (K.chart (C.referenceState, 0) m)
        (referencePhysicalPieceOpen S K m) := by
      simpa only [hA.referenceDomain] using hc.2.2.2.2.1
    have hr : K.left m + (K.right m - K.left m) * p.1 ∈ Ioo (K.left m) (K.right m) :=
      (hmem m hp).1
    change canonicalSource S K (C.referenceState, 0) m f
        (K.left m + (K.right m - K.left m) * p.1, p.2) =
      canonicalSource S K (C.referenceState, 0) m f
        (K.left m + (K.right m - K.left m) * p.1, 0)
    rw [n07a_canonicalSource_reference_row hR m hmap hF f hr p.2,
      n07a_canonicalSource_reference_row hR m hmap hF f hr 0,
      hfradial (((K.inverseChart (C.referenceState, 0) m
        (K.left m + (K.right m - K.left m) * p.1, 0)).1), p.2)]
  have hother (m : ℕ) (hm : m ≠ m₀) : EqOn (g m) (fun _ => (0 : ℝ)) unitStrip := by
    intro p hp
    let x := K.inverseChart (C.referenceState, 0) m (canonicalUnitPoint K m p)
    have hx : x ∈ referencePhysicalPieceOpen S K m := by
      rw [← hA.referenceDomain m]
      exact (hA.charts (C.referenceState, 0) hz₀ hs₀ m).2.1 (hmem m hp)
    have hfx : f x = 0 := by
      by_contra hn
      exact Set.disjoint_left.mp (n07b_physicalIntervals_pairwiseDisjoint hA hm)
        hx.1 (hinterval (hsupport x hn))
    change K.height (C.referenceState, 0) m x * f x /
      |planeJacobian (K.chart (C.referenceState, 0) m) x| = 0
    rw [hfx, mul_zero, zero_div]
  let ξ : ℝ → ℝ := fun r =>
    ((K.chart (C.referenceState, 0) m₀ (r, 0)).1 - K.left m₀) /
      (K.right m₀ - K.left m₀)
  let E : Set ℝ := ξ '' Icc l u
  have hc₀ := hA.charts (C.referenceState, 0) hz₀ hs₀ m₀
  have hslice : MapsTo (fun r : ℝ => (r, (0 : ℝ))) (Icc l u)
      (physicalPieceOpen S K (C.referenceState, 0) m₀) := by
    intro r hr
    rw [hA.referenceDomain m₀]
    exact ⟨hinterval hr, mem_univ _⟩
  have hξ : ContinuousOn ξ (Icc l u) :=
    ((((hc₀.2.2.2.2.1.continuousOn).comp
      (continuous_id.prodMk continuous_const).continuousOn hslice).fst).sub
        continuousOn_const).div_const _
  have hE : IsCompact E := isCompact_Icc.image_of_continuousOn hξ
  have hlen : 0 < K.right m₀ - K.left m₀ := sub_pos.mpr (hA.referenceBounds m₀).2.1
  have hsub : E ⊆ Ioo (0 : ℝ) 1 := by
    rintro r ⟨t, ht, rfl⟩
    have hc := hc₀.1 (hslice ht)
    change 0 < ((K.chart (C.referenceState, 0) m₀ (t, 0)).1 - K.left m₀) /
        (K.right m₀ - K.left m₀) ∧
      ((K.chart (C.referenceState, 0) m₀ (t, 0)).1 - K.left m₀) /
        (K.right m₀ - K.left m₀) < 1
    exact ⟨div_pos (sub_pos.mpr hc.1.1) hlen, (div_lt_one hlen).mpr (by linarith [hc.1.2])⟩
  have hzero (p : PolarPoint) (hp : p ∈ unitStrip) (hpE : p.1 ∉ E) : g m₀ p = 0 := by
    let x := K.inverseChart (C.referenceState, 0) m₀ (canonicalUnitPoint K m₀ p)
    have hx : x ∈ referencePhysicalPieceOpen S K m₀ := by
      rw [← hA.referenceDomain m₀]
      exact hc₀.2.1 (hmem m₀ hp)
    have hfx : f x = 0 := by
      by_contra hn
      have hfirst : (K.chart (C.referenceState, 0) m₀ (x.1, 0)).1 =
          K.left m₀ + (K.right m₀ - K.left m₀) * p.1 :=
        (congrArg Prod.fst (hR.1 m₀ x hx).1).symm.trans
          (congrArg Prod.fst (hc₀.2.2.2.1 (canonicalUnitPoint K m₀ p) (hmem m₀ hp)))
      apply hpE
      refine ⟨x.1, hsupport x hn, ?_⟩
      change ((K.chart (C.referenceState, 0) m₀ (x.1, 0)).1 - K.left m₀) /
        (K.right m₀ - K.left m₀) = p.1
      rw [hfirst]
      field_simp [hlen.ne'] <;> ring
    change K.height (C.referenceState, 0) m₀ x * f x /
      |planeJacobian (K.chart (C.referenceState, 0) m₀) x| = 0
    rw [hfx, mul_zero, zero_div]
  refine ⟨?_, ?_⟩
  · intro m
    refine ⟨hgs m, fun p hp => ?_⟩
    have hp' : p + (0, Real.pi) ∈ unitStrip :=
      ⟨by simpa only [Prod.add_def, zero_add, add_zero] using hp.1, mem_univ _⟩
    exact (hrad m _ hp').trans (by
      simpa only [Prod.add_def, add_zero] using (hrad m p hp).symm)
  · intro s
    classical
    choose B hB0 hB using fun ij : Fin (s + 1) × Fin (s + 1) =>
      compact_radial_unit_mixed_bound (hgs m₀) (hrad m₀) hE hsub hzero ij.1.val ij.2.val
    let M : ℝ := 1 + ∑ ij, B ij
    have hM : 0 < M := add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun ij _ => hB0 ij)
    refine ⟨M, hM, fun m i j p hp hij => ?_⟩
    by_cases hm : m = m₀
    · subst m
      let ij : Fin (s + 1) × Fin (s + 1) := ⟨⟨i, by omega⟩, ⟨j, by omega⟩⟩
      have hsum : B ij ≤ ∑ q, B q := Finset.single_le_sum (fun q _ => hB0 q) (Finset.mem_univ ij)
      exact (hB ij p hp).trans (hsum.trans (le_add_of_nonneg_left zero_le_one))
    · have he := (mixedDerivative_eqOn_of_isOpen
        (isOpen_Ioo.prod isOpen_univ) (hother m hm) i j) (x := p) hp
      have hz : mixedDerivative i j (g m) p = 0 := by
        simpa only [mixedDerivative, iteratedDeriv_fun_const_zero] using he
      simpa only [hz, abs_zero] using hM.le

end ContinuousFlexibility.Analysis
