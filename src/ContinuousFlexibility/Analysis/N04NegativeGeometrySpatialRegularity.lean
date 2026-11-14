import ContinuousFlexibility.Analysis.N04NegativeGeometryReductions
import ContinuousFlexibility.Analysis.N04NegativeGeometrySpatialFields
import ContinuousFlexibility.Analysis.N06FiniteSourceGeometry

/-!
# Spatial regularity of the actual current negative atoms

All eight geometry atoms use their literal fixed unit-point formulas.
The forward fields are evaluated on the reference half, and the inverse
fields on their fixed canonical interval.  The preceding component-germ
lemma supplies the current forward fields on that reference half.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

/-- Affine unit coordinates preserve angular translation and map the
open unit strip to the prescribed radial strip. -/
theorem n04NegativeGeometry_affine_unitPoint
    (l r : ℝ) (hlr : l < r) :
    ContDiff ℝ ∞ (fun p : PolarPoint => (l + (r - l) * p.1, p.2)) ∧
      MapsTo (fun p : PolarPoint => (l + (r - l) * p.1, p.2)) unitStrip
        (Ioo l r ×ˢ (univ : Set ℝ)) ∧
      (∀ p : PolarPoint,
        (l + (r - l) * (p + (0, Real.pi)).1, (p + (0, Real.pi)).2) =
          (l + (r - l) * p.1, p.2) + (0, Real.pi)) := by
  refine ⟨(contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk contDiff_snd,
    ?_, fun p => by simp only [Prod.fst_add, Prod.snd_add, add_zero, Prod.mk_add_mk]⟩
  intro p hp
  refine ⟨⟨lt_add_of_pos_right l (mul_pos (sub_pos.mpr hlr) hp.1.1), ?_⟩, mem_univ _⟩
  have h := mul_lt_mul_of_pos_left hp.1.2 (sub_pos.mpr hlr)
  linarith only [h]

/-- Spatial calculus for the eight geometry atoms.  The forward domain
is the fixed physical interval appearing in the definition of `atom`. -/
theorem n04NegativeGeometry_atoms_spatial_of_fields
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {L : ReturnCorrectionData S}
    {K : CanonicalData S} {z : AnnularState S × ℝ} (m : ℕ)
    (hlen : K.physicalLeft m < K.physicalRight m) (hcan : K.left m < K.right m)
    (hF : ContDiffOn ℝ ∞ (K.chart z m) (referencePhysicalPieceOpen S K m))
    (hH : ContDiffOn ℝ ∞ (K.height z m) (referencePhysicalPieceOpen S K m))
    (hgood : ∀ p ∈ referencePhysicalPieceOpen S K m,
      planeJacobian (K.chart z m) p ≠ 0 ∧ 0 < K.height z m p)
    (hperiod : ∀ p ∈ referencePhysicalPieceOpen S K m,
      K.chart z m (p + (0, Real.pi)) = K.chart z m p + (0, Real.pi) ∧
        K.height z m (p + (0, Real.pi)) = K.height z m p)
    (hI : ContDiffOn ℝ ∞ (K.inverseChart z m) (canonicalOpen S K m))
    (hIperiod : ∀ p ∈ canonicalOpen S K m,
      K.inverseChart z m (p + (0, Real.pi)) = K.inverseChart z m p + (0, Real.pi))
    (a : Atom) (ha : atomIsGeometry a) :
    ContDiffOn ℝ ∞ (atom D T S C L K z m a) unitStrip ∧
      (∀ p ∈ unitStrip, atom D T S C L K z m a (p + (0, Real.pi)) =
        atom D T S C L K z m a p) := by
  have hp := n04NegativeGeometry_affine_unitPoint _ _ hlen
  have hc := n04NegativeGeometry_affine_unitPoint _ _ hcan
  have hP : ContDiff ℝ ∞ (physicalUnitPoint K m) := hp.1
  have hC : ContDiff ℝ ∞ (canonicalUnitPoint K m) := hc.1
  have hPmap : MapsTo (physicalUnitPoint K m) unitStrip (referencePhysicalPieceOpen S K m) :=
    hp.2.1
  have hCmap : MapsTo (canonicalUnitPoint K m) unitStrip (canonicalOpen S K m) := hc.2.1
  have hPshift (p : PolarPoint) : physicalUnitPoint K m (p + (0, Real.pi)) =
      physicalUnitPoint K m p + (0, Real.pi) := hp.2.2 p
  have hCshift (p : PolarPoint) : canonicalUnitPoint K m (p + (0, Real.pi)) =
      canonicalUnitPoint K m p + (0, Real.pi) := hc.2.2 p
  have hJ := (n06_contDiffOn_planeJacobian (isOpen_Ioo.prod isOpen_univ) hF).abs
    (fun p hp => (hgood p hp).1)
  have hJperiod (p : PolarPoint) (hp : p ∈ referencePhysicalPieceOpen S K m) :
      planeJacobian (K.chart z m) (p + (0, Real.pi)) = planeJacobian (K.chart z m) p :=
    n06_planeJacobian_chart_lift hF (fun q hq => (hperiod q hq).1) hp
  cases a <;> simp only [atomIsGeometry] at ha <;> dsimp only [atom]
  · refine ⟨(((hF.comp hP.contDiffOn hPmap).fst.sub contDiffOn_const).div_const _), ?_⟩
    intro p hp
    rw [hPshift, (hperiod _ (hPmap hp)).1]
    simp only [Prod.fst_add, add_zero]
  · refine ⟨((hF.comp hP.contDiffOn hPmap).snd.sub hP.contDiffOn.snd), ?_⟩
    intro p hp
    rw [hPshift, (hperiod _ (hPmap hp)).1]
    simp only [Prod.snd_add, add_sub_add_right_eq_sub]
  · refine ⟨(((hI.comp hC.contDiffOn hCmap).fst.sub contDiffOn_const).div_const _), ?_⟩
    intro p hp
    rw [hCshift, hIperiod _ (hCmap hp)]
    simp only [Prod.fst_add, add_zero]
  · refine ⟨((hI.comp hC.contDiffOn hCmap).snd.sub hC.contDiffOn.snd), ?_⟩
    intro p hp
    rw [hCshift, hIperiod _ (hCmap hp)]
    simp only [Prod.snd_add, add_sub_add_right_eq_sub]
  · refine ⟨hH.comp hP.contDiffOn hPmap, ?_⟩
    intro p hp
    rw [hPshift, (hperiod _ (hPmap hp)).2]
  · refine ⟨(hH.inv (fun p hp => (hgood p hp).2.ne')).comp hP.contDiffOn hPmap, ?_⟩
    intro p hp
    rw [hPshift, (hperiod _ (hPmap hp)).2]
  · refine ⟨hJ.comp hP.contDiffOn hPmap, ?_⟩
    intro p hp
    rw [hPshift, hJperiod _ (hPmap hp)]
  · refine ⟨(hJ.inv (fun p hp => abs_ne_zero.mpr (hgood p hp).1)).comp
      hP.contDiffOn hPmap, ?_⟩
    intro p hp
    rw [hPshift, hJperiod _ (hPmap hp)]

namespace N04RealizationGauge

/-- Actual spatial smoothness and pi-periodicity of every current
negative geometry atom, on the original neighborhood and before any
auxiliary column is chosen. -/
theorem negative_geometry_spatial (G : N04RealizationGauge)
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (z : Parameter G.W.S)
    (hz : z ∈ sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε)
    (m : ℕ) (hm : G.Neg η m) (a : Atom) (ha : atomIsGeometry a) :
    ContDiffOn ℝ ∞ (G.atomFamily η a z m) unitStrip ∧
      (∀ p ∈ unitStrip, G.atomFamily η a z m (p + (0, Real.pi)) =
        G.atomFamily η a z m p) := by
  have hj := (G.neg_iff_inl η m).mp hm
  exact hj.elim fun j hi => by
    let k := G.negativeIndex j
    have hk : G.X.e₀ k = .inl (j.1, j.2) := G.X.e₀.apply_symm_apply _
    have hz' := liftSectorParameter_mem_stateNeighborhood (C := G.W.C) hz le_rfl
    have hs := G.W.through03.1.1.2.2.1.liftSectorParameter_sector z
    have hf := n04NegativeGeometry_referenceHalf_fields
      G.W.hT G.W.hS G.W.through03 G.W.field G.X.e₀ k j.1 j.2 hk hz' hs
    have hA := n04b_actualTypedAtlas_partA
      G.W.hT G.W.hS G.W.through03 G.W.field G.X.e₀
    have haux : a ≠ .auxiliaryColumn := by
      intro he
      subst a
      cases ha
    rw [G.negative_atomFamily η z m j hi a haux]
    exact n04NegativeGeometry_atoms_spatial_of_fields
      (D := G.W.D) (T := G.W.U) (C := G.W.C) (L := G.W.L) k
      (hA.referenceBounds k).1 (hA.referenceBounds k).2.1
      hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2 a ha

end N04RealizationGauge

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negative_geometry_spatial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negative_geometry_spatial
