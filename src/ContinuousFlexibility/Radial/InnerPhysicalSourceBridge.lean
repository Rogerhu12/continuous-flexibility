import ContinuousFlexibility.Radial.InnerPhysicalFrozenGraph
import ContinuousFlexibility.Radial.ModeInnerHilbertProjection
import Mathlib.Data.Finset.Max

/-!
# The same finite physical source in frozen modal coordinates

The union of the open pieces differs from the whole inner interval only
at its finitely many cuts. The actual radial measure has no atoms there.
Consequently the genuine supported Hilbert source is precisely the
range of the concrete frozen inner indicator, with the inactive scalar
removed in unbordered modes.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped InnerProductSpace BigOperators

theorem innerRadialChainRegion_iff_of_ne_cuts {D : ReferenceData} {n : ℕ}
    (G : InnerRadialChainGeometry D n) {r : ℝ} (hr : ∀ i, r ≠ G.cuts i) :
    r ∈ innerRadialChainRegion D G ↔ r ∈ Ioo (G.left 0) (G.right (Fin.last n)) := by
  classical
  constructor
  · intro h
    obtain ⟨k, hk⟩ := mem_iUnion.mp h
    exact innerRadialChain_piece_subset G k hk
  · intro h
    let s : Finset (Fin (n + 2)) := Finset.univ.filter (fun i => G.cuts i < r)
    have hs : s.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1⟩⟩
    let p : Fin (n + 2) := s.max' hs
    have hp : G.cuts p < r := (Finset.mem_filter.mp (s.max'_mem hs)).2
    have hpn : p.val < n + 1 := by
      by_contra hn
      have he : p = Fin.last (n + 1) := Fin.ext (by simp only [Fin.val_last]; omega)
      rw [he] at hp
      exact (not_lt_of_ge hp.le) h.2
    let k : Fin (n + 1) := ⟨p.val, hpn⟩
    have hk : k.castSucc = p := Fin.ext rfl
    have hnext : r < G.cuts k.succ := by
      by_contra hn
      have hlt : G.cuts k.succ < r :=
        lt_of_le_of_ne (le_of_not_gt hn) (hr k.succ).symm
      have hsnext : k.succ ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
      have hmax : k.succ ≤ p := s.le_max' k.succ hsnext
      change p.val + 1 ≤ p.val at hmax
      omega
    apply mem_iUnion.mpr
    refine ⟨k, ?_, hnext⟩
    change G.cuts k.castSucc < r
    rw [hk]
    exact hp

theorem innerRadialChainRegion_ae {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {n : ℕ} (G : InnerRadialChainGeometry D n) :
    ∀ᵐ r ∂radialHilbertMeasure D,
      r ∈ innerRadialChainRegion D G ↔ r ∈ Ioo (G.left 0) (G.right (Fin.last n)) := by
  filter_upwards [ae_all_iff.mpr (fun i : Fin (n + 2) => matching_ae_ne hD (G.cuts i))]
    with r hr
  exact innerRadialChainRegion_iff_of_ne_cuts G hr

theorem innerL2PieceProjection_eq_modeRegionVector (D : ReferenceData) (J : Set ℝ)
    (hJ : MeasurableSet J) (F : RadialModeL2 D) :
    innerL2PieceProjection (radialHilbertMeasure D) J F = modeRegionVector D J hJ F := by
  apply Lp.ext
  exact (innerL2PieceProjection_ae (radialHilbertMeasure D) J hJ F).trans
    (modeRegionVector_coe D J hJ F).symm

theorem mem_innerRadialPhysicalSource_whole {D : ReferenceData}
    (hD : IsAccumulatingProfile D) {n : ℕ} (G : InnerRadialChainGeometry D n)
    (bordered : Bool) (F : ModeHilbertPair D) :
    F ∈ innerSupportedAdmissibleSource (radialHilbertMeasure D)
      (innerRadialChainRegion D G) bordered ↔
      (bordered = true ∨ F.snd = 0) ∧
        modeRegionVector D (Ioo (G.left 0) (G.right (Fin.last n))) measurableSet_Ioo F.fst =
          F.fst := by
  rw [mem_innerSupportedAdmissibleSource,
    innerL2PieceProjection_eq_modeRegionVector D _ (innerRadialChainRegion_measurable D G),
    modeRegionVector_congr_set_ae D (innerRadialChainRegion_measurable D G) measurableSet_Ioo
      (innerRadialChainRegion_ae hD G)]

/-- The frozen inner source is an actual continuous linear projection.
Its scalar is retained before the mode admissibility projection. -/
def innerRadialPairSource (D : ReferenceData) {n : ℕ}
    (G : InnerRadialChainGeometry D n) : RadialModePair D →L[ℝ] RadialModePair D :=
  (modeRegionProjection D (Ioo (G.left 0) (G.right (Fin.last n))) measurableSet_Ioo).prodMap
    (ContinuousLinearMap.id ℝ ℝ)

theorem innerRadialPairSource_apply (D : ReferenceData) {n : ℕ}
    (G : InnerRadialChainGeometry D n) (F : RadialModePair D) :
    innerRadialPairSource D G F = modeInnerSource D (G.left 0) (G.right (Fin.last n)) F := by
  change (modeRegionProjection D (Ioo (G.left 0) (G.right (Fin.last n))) measurableSet_Ioo
    F.1, F.2) =
    (modeRegionVector D (Ioo (G.left 0) (G.right (Fin.last n))) measurableSet_Ioo F.1, F.2)
  rw [modeRegionProjection_apply]

theorem innerRadialPairSource_norm_le (D : ReferenceData) {n : ℕ}
    (G : InnerRadialChainGeometry D n) : ‖innerRadialPairSource D G‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro F
  rw [innerRadialPairSource_apply, one_mul]
  change max ‖modeRegionVector D (Ioo (G.left 0) (G.right (Fin.last n))) measurableSet_Ioo
    F.1‖ ‖F.2‖ ≤ max ‖F.1‖ ‖F.2‖
  exact max_le_max
    (modeRegionVector_norm_le D (Ioo (G.left 0) (G.right (Fin.last n))) measurableSet_Ioo F.1)
    le_rfl

theorem innerRadialPairSource_spec (D : ReferenceData) {n : ℕ}
    (G : InnerRadialChainGeometry D n) (F : RadialModePair D) :
    (innerRadialPairSource D G F).2 = F.2 ∧
    ((innerRadialPairSource D G F).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      (fun r => if r ∈ Ioo (G.left 0) (G.right (Fin.last n)) then F.1 r else 0) := by
  simpa only [innerRadialPairSource_apply] using
    And.intro (modeRegionSources_spec D (G.left 0) (G.right (Fin.last n)) F).1
      (modeRegionSources_spec D (G.left 0) (G.right (Fin.last n)) F).2.2.1

section ActualSource

variable {D : ReferenceData} (hD : IsAccumulatingProfile D) {n : ℕ}
  (G : InnerRadialChainGeometry D n) (bordered : Bool)

local notation "K" => innerSupportedAdmissibleSource (radialHilbertMeasure D)
  (innerRadialChainRegion D G) bordered
local notation "H" => InnerRadialPhysicalSource D G bordered
local notation "J" => Ioo (G.left 0) (G.right (Fin.last n))

/-- The concrete whole-inner restriction, with codomain the very same
physical source subspace used by the actual finite-chain inverse. -/
def innerRadialPhysicalRestriction : ModeHilbertPair D →L[ℝ] H :=
  modeSupportedHilbertRestrict D J measurableSet_Ioo bordered K
    (mem_innerRadialPhysicalSource_whole hD G bordered)

theorem innerRadialPhysicalRestriction_apply (F : RadialModePair D) :
    WithLp.ofLp (innerRadialPhysicalRestriction hD G bordered (WithLp.toLp 2 F)).val =
      (modeRegionVector D J measurableSet_Ioo F.1, if bordered then F.2 else 0) := by
  rw [innerRadialPhysicalRestriction, modeSupportedHilbertRestrict_coe,
    modeSupportedHilbertProjection_apply, WithLp.ofLp_toLp, WithLp.toLp_fst, WithLp.toLp_snd]

/-- Extend the same physical operator to the frozen max-norm pair space. -/
def innerRadialPairExtension (A : H →L[ℝ] H) : RadialModePair D →L[ℝ] RadialModePair D :=
  modeSupportedPairOperator D J measurableSet_Ioo bordered K
    (mem_innerRadialPhysicalSource_whole hD G bordered) A

theorem innerRadialPairExtension_apply (A : H →L[ℝ] H) (F : RadialModePair D) :
    innerRadialPairExtension hD G bordered A F =
      WithLp.ofLp (A (innerRadialPhysicalRestriction hD G bordered (WithLp.toLp 2 F))).val := by
  exact modeSupportedPairOperator_apply D J measurableSet_Ioo bordered K
    (mem_innerRadialPhysicalSource_whole hD G bordered) A F

theorem innerRadialPairExtension_norm_le (A : H →L[ℝ] H) :
    ‖innerRadialPairExtension hD G bordered A‖ ≤ sqrt 2 * ‖A‖ :=
  modeSupportedPairOperator_norm_le D J measurableSet_Ioo bordered K
    (mem_innerRadialPhysicalSource_whole hD G bordered) A

theorem innerRadialPairExtension_innerSource (A : H →L[ℝ] H) (F : RadialModePair D) :
    innerRadialPairExtension hD G bordered A (modeInnerSource D (G.left 0) (G.right (Fin.last n)) F) =
      innerRadialPairExtension hD G bordered A F :=
  modeSupportedPairOperator_innerSource D (G.left 0) (G.right (Fin.last n)) bordered K
    (mem_innerRadialPhysicalSource_whole hD G bordered) A F

end ActualSource

end ContinuousFlexibility.Radial
