import ContinuousFlexibility.Radial.InnerPhysicalSourceBridge
import ContinuousFlexibility.Radial.ModeInnerGreenUniqueness

/-!
# A physical weak right inverse in the frozen modal coordinates

The physical operator is arbitrary, but its right-inverse assertion
concerns the existing actual weak graph on the same supported source
space. The proved graph bridge and Green uniqueness give both frozen
inverse identities. No reverse identification of arbitrary frozen
solutions with a Sobolev domain is needed.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace BigOperators

namespace InnerRadialPhysicalInverse

section PairOperator

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n} {bordered : Bool}
  (inverse : InnerRadialPhysicalSource D G bordered →L[ℝ]
    InnerRadialPhysicalSource D G bordered)

def pairInverse (hD : IsAccumulatingProfile D) : RadialModePair D →L[ℝ] RadialModePair D :=
  innerRadialPairExtension hD G bordered inverse

theorem pairInverse_apply (hD : IsAccumulatingProfile D) (F : RadialModePair D) :
    pairInverse inverse hD F = WithLp.ofLp
      (inverse (innerRadialPhysicalRestriction hD G bordered (WithLp.toLp 2 F))).val :=
  innerRadialPairExtension_apply hD G bordered inverse F

theorem pairInverse_norm_le (hD : IsAccumulatingProfile D) :
    ‖pairInverse inverse hD‖ ≤ sqrt 2 * ‖inverse‖ :=
  innerRadialPairExtension_norm_le hD G bordered inverse

theorem pairInverse_norm_le_of_bound (hD : IsAccumulatingProfile D) {K : ℝ}
    (hK : ‖inverse‖ ≤ K) : ‖pairInverse inverse hD‖ ≤ sqrt 2 * K :=
  (pairInverse_norm_le inverse hD).trans
    (mul_le_mul_of_nonneg_left hK (sqrt_nonneg 2))

theorem pairInverse_innerSource (hD : IsAccumulatingProfile D) (F : RadialModePair D) :
    pairInverse inverse hD (modeInnerSource D (G.left 0) (G.right (Fin.last n)) F) =
      pairInverse inverse hD F :=
  innerRadialPairExtension_innerSource hD G bordered inverse F

end PairOperator

section FrozenMatching

variable {D : ReferenceData} {M : RadialMatchingData D} {n : ℕ}
  {G : InnerRadialChainGeometry D n} {central : Fin (n + 1)} {column : RadialModeL2 D}
  (inverse : InnerRadialPhysicalSource D G (decide (M.frequency = 2)) →L[ℝ]
    InnerRadialPhysicalSource D G (decide (M.frequency = 2)))
  (hD : IsAccumulatingProfile D) (hB : RadialTrueBorder D) (hw : ContDiff ℝ ∞ D.w)
  (hsolve : ∀ F, InnerRadialPhysicalWeakGraph D hw.continuous G (decide (M.frequency = 2))
    (M.frequency : ℝ) central column (inverse F) F)
  (hleft : G.left 0 = M.innerLeft) (hright : G.right (Fin.last n) = M.innerRight)
  (hab : M.innerLeft < M.innerRight)
  (hsub : Icc M.innerLeft M.innerRight ⊆ radialCore D)
  (hc : (column : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
    fun r => referenceColumn D r / matchingDensity D r)
  (hgs : Function.support (referenceColumn D) ⊆ Ioo (G.left central) (G.right central))

local notation "R" => innerRadialPhysicalRestriction hD G (decide (M.frequency = 2))
local notation "A" => pairInverse inverse hD
local notation "src" => modeInnerSource D M.innerLeft M.innerRight

include hw hsolve hB hleft hright hab hsub hc hgs

theorem pairInverse_frozen_restricted (F : RadialModePair D) :
    ModeInnerDirichletGraph D M (A F) (WithLp.ofLp (R (WithLp.toLp 2 F)).val) := by
  rw [pairInverse_apply]
  exact innerRadialPhysicalWeakGraph_frozen hD hB hw G hleft hright hab hsub hc hgs
    (hsolve (R (WithLp.toLp 2 F)))

/-- Admissible inputs keep exactly their original scalar and their
actual field restriction to the whole inner interval. -/
theorem pairInverse_right_frozen (F : RadialModePair D)
    (hF : M.frequency ≠ 2 → F.2 = 0) :
    ModeInnerDirichletGraph D M (A (src F)) (src F) := by
  have he := pairInverse_frozen_restricted inverse hD hB hw hsolve
    hleft hright hab hsub hc hgs F
  have hsrc : WithLp.ofLp (R (WithLp.toLp 2 F)).val = src F := by
    rw [innerRadialPhysicalRestriction_apply, hleft, hright]
    apply Prod.ext
    · rfl
    · change (if decide (M.frequency = 2) then F.2 else 0) = F.2
      simp only [decide_eq_true_eq]
      split_ifs with hj
      · rfl
      · exact (hF hj).symm
  rw [hsrc] at he
  have hinv : A (src F) = A F := by
    simpa only [hleft, hright] using pairInverse_innerSource inverse hD F
  rw [hinv]
  exact he

/-- The frozen Green identity gives the left inverse on every frozen
graph element, without any assumed reverse domain correspondence. -/
theorem pairInverse_left_frozen {U F : RadialModePair D}
    (hU : ModeInnerDirichletGraph D M U F) : A F = U := by
  apply modeInnerDirichletGraph_unique_of_projected_right_inverse hD hB hab hsub A
    (fun F => ?_) (fun F hF => ?_) hU
  · simpa only [hleft, hright] using pairInverse_innerSource inverse hD F
  · exact pairInverse_right_frozen inverse hD hB hw hsolve hleft hright hab hsub hc hgs F hF

def frozenRepresentative (F : RadialModePair D) : ℝ → ℝ :=
  Classical.choose (pairInverse_frozen_restricted inverse hD hB hw hsolve hleft hright
    hab hsub hc hgs F).2.2

theorem frozenRepresentative_spec (F : RadialModePair D) :
    ((A (src F)).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D]
      frozenRepresentative inverse hD hB hw hsolve hleft hright hab hsub hc hgs F ∧
    ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight) (A (src F)) (src F) ∧
    ContDiffOn ℝ 1 (frozenRepresentative inverse hD hB hw hsolve hleft hright hab hsub hc hgs F)
      (Icc M.innerLeft M.innerRight) ∧
    (∀ r ∈ matchingOuterRegion D M,
      frozenRepresentative inverse hD hB hw hsolve hleft hright hab hsub hc hgs F r = 0) ∧
    (if M.frequency = 2 then
      (∫ r in D.a..D.b, referenceColumn D r *
        frozenRepresentative inverse hD hB hw hsolve hleft hright hab hsub hc hgs F r) = F.2
     else (A (src F)).2 = 0) ∧
    (∀ i, frozenRepresentative inverse hD hB hw hsolve hleft hright hab hsub hc hgs F
      (matchingCut D M i) = 0) := by
  let u := frozenRepresentative inverse hD hB hw hsolve hleft hright hab hsub hc hgs F
  have hgraph := pairInverse_frozen_restricted inverse hD hB hw hsolve
    hleft hright hab hsub hc hgs F
  have hu : ((A F).1 : ℝ → ℝ) =ᵐ[radialHilbertMeasure D] u ∧
      ContDiffOn ℝ 1 u (Icc M.innerLeft M.innerRight) ∧
      (∀ r ∈ matchingOuterRegion D M, u r = 0) ∧
      u M.innerLeft = 0 ∧ u M.innerRight = 0 :=
    Classical.choose_spec hgraph.2.2
  have hinv : A (src F) = A F := by
    simpa only [hleft, hright] using pairInverse_innerSource inverse hD F
  have heq : ModeLocalEquation D M.frequency (Ioo M.innerLeft M.innerRight) (A F) (src F) := by
    intro ψ hψ hcompact hsupp
    have he := hgraph.1 ψ hψ hcompact hsupp
    simpa only [innerRadialPhysicalRestriction_apply, hleft, hright, modeInnerSource,
      Prod.fst_mk] using he
  have hrow : if M.frequency = 2 then
      (∫ r in D.a..D.b, referenceColumn D r * u r) = F.2 else (A F).2 = 0 := by
    by_cases hj : M.frequency = 2
    · rw [if_pos hj]
      have hs : (WithLp.ofLp (R (WithLp.toLp 2 F)).val).2 = F.2 := by
        rw [innerRadialPhysicalRestriction_apply]
        simp only [Prod.snd_mk, decide_eq_true_eq, if_pos hj]
      have hr : (∫ r in D.a..D.b, referenceColumn D r * (A F).1 r) = F.2 := by
        simpa only [if_pos hj, hs] using hgraph.2.1
      calc
        _ = ∫ r in D.a..D.b, referenceColumn D r * (A F).1 r := by
          apply matchingInterval_congr_ae hD
          filter_upwards [hu.1] with r hr
          rw [hr]
        _ = F.2 := hr
    · rw [if_neg hj]
      exact (show (A F).2 = 0 ∧ (WithLp.ofLp (R (WithLp.toLp 2 F)).val).2 = 0 by
        simpa only [if_neg hj] using hgraph.2.1).1
  rw [hinv]
  refine ⟨hu.1, heq, hu.2.1, hu.2.2.1, hrow, ?_⟩
  intro i
  by_cases hi : i = 0
  · simpa only [matchingCut, if_pos hi] using hu.2.2.2.1
  · simpa only [matchingCut, if_neg hi] using hu.2.2.2.2

end FrozenMatching

end InnerRadialPhysicalInverse

end ContinuousFlexibility.Radial
