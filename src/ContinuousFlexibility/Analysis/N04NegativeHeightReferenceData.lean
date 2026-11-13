import ContinuousFlexibility.Analysis.N04NegativeHeightCurrentData
import ContinuousFlexibility.Analysis.N04NegativeHeightRadialFamilies
import ContinuousFlexibility.Analysis.WholeReferenceGaugeNegativeGeometryJets
import ContinuousFlexibility.Analysis.N01OriginalCoefficientGlobalJets

/-!
# Reference data for the negative-height calculation

The retained negative geometric atoms have the original sampled reference
estimates, independently of the positive fields and the auxiliary column.
The physical radial coefficient has a simpler reference bound: its actual
reference jets are uniformly bounded on the fixed annulus, and the unit
pullback uses only a bounded physical half length.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationGauge

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

variable (G : N04RealizationGauge)
  (η : (G.W.S.height (3 / 4 : ℝ)).Space)

/-- Zero sector parameter is the actual stored reference state. -/
theorem height_atomFamily_zero (a : Atom) :
    G.atomFamily η a 0 = G.atomRef η a := by
  have hlift : G.lift η (0 : Parameter (G.S η)) = G.ref η := by
    simp only [lift, ref, liftSectorParameter, Prod.fst_zero, Prod.snd_zero,
      ZeroMemClass.coe_zero, add_zero]
  funext m
  exact congrArg
    (fun z => atom G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η) z m a) hlift

theorem height_zero_mem_sector :
    (0 : Parameter (G.S η)) ∈
      sectorNeighborhood (G.S η) G.W.base G.W.ε G.W.ε := by
  exact ⟨(sectorGrading (G.S η) G.W.base).map_zero'.trans_lt G.W.ε_pos,
    (abs_zero : |(0 : ℝ)| = 0).trans_lt G.W.ε_pos⟩

/-- All eight geometric reference atoms on the selected negative pieces
have the same reference envelope, before the auxiliary column is chosen. -/
theorem negative_height_referenceData (a : Atom) (ha : atomIsGeometry a) :
    N04HeightReferenceDataOn G.W.U (G.V η).cell (G.Neg η) (G.atomRef η a) := by
  have hne : a ≠ .auxiliaryColumn := by
    intro he
    subst a
    exact ha
  have hgeometry : a = .chartRadial ∨ a = .chartAngleDefect ∨
      a = .inverseRadial ∨ a = .inverseAngleDefect ∨ a = .height ∨
      a = .heightInverse ∨ a = .jacobian ∨ a = .jacobianInverse ∨
      a = .sourceFactor ∨ a = .sourceFactorInverse := by
    cases a <;> simp_all [atomIsGeometry]
  refine ⟨fun m hm => ?_, fun s => ?_⟩
  · simpa only [G.height_atomFamily_zero η a] using
      G.negative_geometry_spatial η 0 (G.height_zero_mem_sector η) m hm a ha
  · obtain ⟨B, hB, hb⟩ :=
      n04WholeReferenceGauge_negative_geometryReferenceJets_enlargedMaterialData
        G.W.hT G.W.hS G.W.through03 G.W.field G.X.e₀ G.X.κ_pos s
    refine ⟨B, hB, ?_⟩
    intro m hm q hq i j hij
    have hraw := hb G.e G.X.cell
      (fun t => positiveReferenceCylinderChart (G.Y t))
      (fun t => positiveReferenceCylinderInverse (G.Y t))
      (fun t p => G.H t p.1) G.τ G.σ G.Q G.N
      (fun t => ⟨G.W.C.cell t, G.W.host t, G.X.optical t⟩)
      m hm a hgeometry q hq i j hij
    have he := canonicalAtom_replaceAuxiliaryColumn_of_ne
      G.W.D G.W.U G.W.S G.W.C G.W.L
      (n04RealizationAtlas G.W G.X G.e G.Y G.H G.τ G.σ G.Q G.N)
      η (G.W.C.referenceState, 0) m a hne
    change |mixedDerivative i j
      (atom G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)
        (G.W.C.referenceState, 0) m a) q| ≤ _
    rw [he]
    exact hraw

/-- The fixed physical pullback of `a` has reference data at the same
retained sample. No reciprocal-profile estimate enters this lemma. -/
theorem negative_physicalRadial_referenceData :
    N04HeightReferenceDataOn G.W.U (G.V η).cell (G.Neg η)
      (G.physicalRadialRef η) := by
  refine ⟨fun m hm => ?_, fun s => ?_⟩
  · simpa only [G.physicalRadialFamily_zero η m] using
      G.physicalRadial_spatial η 0 (G.height_zero_mem_sector η) m hm
  · obtain ⟨A, hA, hb⟩ :=
      G.W.through03.1.1.reference_coefficient_mixed_global_bound s
    let L : ℝ := max 1 (G.W.D.b - G.W.D.a)
    have hL : 1 ≤ L := le_max_left _ _
    let B : ℝ := 1 + L ^ s * A
    have hB : 0 < B := add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg (pow_nonneg (zero_le_one.trans hL) _) hA)
    refine ⟨B, hB, ?_⟩
    intro m hm q hq i j hij
    obtain ⟨t, ht⟩ := (G.neg_iff_inl η m).mp hm
    have hgeom := G.heightRadial_physicalBounds η m t ht
    let l : ℝ := (G.V η).physicalRight m - (G.V η).physicalLeft m
    have hl : 0 < l := sub_pos.mpr hgeom.2.1
    have hlL : l ≤ L := (by
      dsimp only [l]
      linarith only [hgeom.1, hgeom.2.2] : l ≤ G.W.D.b - G.W.D.a).trans
        (le_max_right _ _)
    have hpow : l ^ i ≤ L ^ s :=
      (pow_le_pow_left₀ hl.le hlL i).trans (pow_le_pow_right₀ hL (by omega))
    have hp := G.heightRadial_physicalUnitPoint_mem_annulus η m hm hq
    have hraw := hb 0 i j hij (physicalUnitPoint (G.V η) m q)
      ⟨hp.1.1.le, hp.1.2.le⟩
    have he : G.physicalRadialRef η m =
        fun y => (originalCoefficients G.W.D G.W.S G.W.C
          (G.W.C.referenceState, 0)).a
            ((G.V η).physicalLeft m + l * y.1, y.2) :=
      funext (G.physicalRadialRef_eq_original η m)
    rw [he, n07a_mixedDerivative_radialAffine, abs_mul,
      abs_of_nonneg (pow_nonneg hl.le _)]
    have hE := (G.cost_nonneg η).2.2 m
    calc
      _ ≤ L ^ s * A := mul_le_mul hpow hraw (abs_nonneg _)
        (pow_nonneg (zero_le_one.trans hL) _)
      _ ≤ B := le_add_of_nonneg_left zero_le_one
      _ ≤ B * G.W.U.E0 (G.W.U.sample ((G.V η).cell m)) ^ B :=
        le_mul_of_one_le_right hB.le (Real.one_le_rpow hE hB.le)

end ContinuousFlexibility.Analysis.N04RealizationGauge

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negative_height_referenceData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negative_height_referenceData
