module

public import ContinuousFlexibility.Analysis.N01cOneHighProducts
public import ContinuousFlexibility.Analysis.N01cStateSeminorms
public import ContinuousFlexibility.Analysis.TameTransfer
public import ContinuousFlexibility.Analysis.TameSmoothingCalculus

/-!
# Interpolation for the actual joint state grading

The physical height and circle smoothing operators produce smoothing
and interpolation on the actual state product.  A state neighbourhood
of radius at most one half controls the sum grading of the state and
the real parameter.  The product estimate is then normalized on one
smaller neighbourhood of the original reference state.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped BigOperators

/-- The actual height, scalar and circle components inherit smoothing
from the physical-space witnesses. -/
theorem stateGrading_hasSmoothing {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hS : IsPhysicalSpaces D T S) :
    HasSmoothing (stateGrading S) := by
  obtain ⟨_, _, _, hheight, hcircle, _⟩ := hS
  have hH : HasSmoothing (S.height (3 / 4 : ℝ)).grading :=
    (hheight (3 / 4 : ℝ)).2.1
  have hK : HasSmoothing (S.circle (3 / 4 : ℝ)).grading :=
    (hcircle (3 / 4 : ℝ)).2.1
  have hpair : HasSmoothing (heightPairGrading S) :=
    hasSmoothing_pairGrading hH hasSmoothing_realGrading
  have hcircles : HasSmoothing
      (pairGrading (S.circle (3 / 4 : ℝ)).grading
        (S.circle (3 / 4 : ℝ)).grading) :=
    hasSmoothing_pairGrading hK hK
  have htail : HasSmoothing
      (pairGrading realGrading
        (pairGrading (S.circle (3 / 4 : ℝ)).grading
          (S.circle (3 / 4 : ℝ)).grading)) :=
    hasSmoothing_pairGrading hasSmoothing_realGrading hcircles
  exact hasSmoothing_pairGrading hpair htail

/-- Adjoining the actual real parameter preserves smoothing. -/
theorem jointStateGrading_hasSmoothing {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hS : IsPhysicalSpaces D T S) :
    HasSmoothing (pairGrading (stateGrading S) realGrading) :=
  hasSmoothing_pairGrading (stateGrading_hasSmoothing hS) hasSmoothing_realGrading

/-- Interpolation follows from smoothing of the actual joint state. -/
theorem jointStateGrading_hasInterpolation {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hS : IsPhysicalSpaces D T S) :
    HasInterpolation (pairGrading (stateGrading S) realGrading) :=
  hasInterpolation_of_hasSmoothing (jointStateGrading_monotone S)
    (jointStateGrading_hasSmoothing hS)

private theorem pairGrading_displacement_apply {E : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] (p : ℕ → Seminorm ℝ E)
    (base : ℕ) (z : E × ℝ) (reference : E) :
    pairGrading p realGrading base (z - (reference, (0 : ℝ))) =
      p base (z.1 - reference) + |z.2| := by
  rw [pairGrading_apply]
  simp only [Prod.fst_sub, Prod.snd_sub,
    sub_zero, realGrading, coe_normSeminorm, Real.norm_eq_abs]

/-- The displacement grading is exactly the sum of the two quantities
already controlled by the original state neighbourhood. -/
theorem jointStateGrading_displacement_apply (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base : ℕ) (z : AnnularState S × ℝ) :
    pairGrading (stateGrading S) realGrading base (z - (C.referenceState, (0 : ℝ))) =
      stateGrading S base (z.1 - C.referenceState) + |z.2| :=
  pairGrading_displacement_apply (stateGrading S) base z C.referenceState

/-- Halving the common radius puts the actual joint displacement in
the unit low-seminorm ball used for multilinear normalization. -/
theorem jointStateGrading_displacement_lt_one {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
    (hε : ε ≤ 1 / 2) (hz : z ∈ stateNeighborhood S C base ε) :
    pairGrading (stateGrading S) realGrading base (z - (C.referenceState, (0 : ℝ))) < 1 := by
  rw [jointStateGrading_displacement_apply]
  have hsum :
      stateGrading S base (z.1 - C.referenceState) + |z.2| < ε + ε :=
    add_lt_add hz.1 hz.2
  linarith

private theorem exists_neighborhood_oneHighProductBounds
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (hinterp : HasInterpolation p)
    (center : E) (U : ℕ → ℝ → Set E)
    (hsubset : ∀ b b' ε ε', b ≤ b' → ε' ≤ ε → U b' ε' ⊆ U b ε)
    (hunit : ∀ b ε z, ε ≤ 1 / 2 → z ∈ U b ε → p b (z - center) < 1)
    (originalBase offset : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ base loss : ℕ,
      originalBase ≤ base ∧ 0 < min ε (1 / 2) ∧
      U base (min ε (1 / 2)) ⊆ U originalBase ε ∧
      ∀ k factors s : ℕ, ∃ B : ℝ, 0 ≤ B ∧
        ∀ a : Fin factors → ℕ, (∑ i, a i ≤ s) →
        ∀ select : Fin factors → Fin (k + 1),
        ∀ z ∈ U base (min ε (1 / 2)),
        ∀ A : E [×k]→L[ℝ] ℝ, ∀ K : ℝ, 0 ≤ K →
          (∀ v : Fin k → E, |A v| ≤ K * ∏ i, p (a i + offset)
            ((Fin.cons (z - center) v : Fin (k + 1) → E) (select i))) →
          ∀ v : Fin k → E, |A v| ≤ K * B *
            oneHighVariationWeight p base (s + loss) (z - center) v := by
  obtain ⟨b, loss, hbounds⟩ := exists_oneHighMultilinearProductBounds (F := ℝ)
    p hp hinterp offset
  refine ⟨max originalBase b, loss, le_max_left _ _,
    lt_min hε (by norm_num), ?_, ?_⟩
  · exact hsubset originalBase (max originalBase b) ε (min ε (1 / 2))
      (le_max_left _ _) (min_le_left _ _)
  · intro k factors s
    obtain ⟨B, hB, hBb⟩ := hbounds k factors s
    refine ⟨B, hB, ?_⟩
    intro a ha select z hz A K hK hraw v
    have hsmall : p b (z - center) ≤ 1 :=
      ((hp (le_max_right originalBase b) _).trans_lt
        (hunit (max originalBase b) (min ε (1 / 2)) z (min_le_right _ _) hz)).le
    have hraw' : ∀ w : Fin k → E, realGrading 0 (A w) ≤ K * ∏ i, p (a i + offset)
        ((Fin.cons (z - center) w : Fin (k + 1) → E) (select i)) := by
      intro w
      simpa only [realGrading, coe_normSeminorm, Real.norm_eq_abs] using hraw w
    have h := hBb a ha select (z - center) hsmall A (realGrading 0) K hK hraw' v
    have hbound : |A v| ≤ K * B *
        oneHighVariationWeight p b (s + loss) (z - center) v := by
      simpa only [realGrading, coe_normSeminorm, Real.norm_eq_abs,
        multilinearTameSize, oneHighVariationWeight] using h
    exact hbound.trans (mul_le_mul_of_nonneg_left
      (oneHighVariationWeight_mono hp (le_max_right originalBase b) le_rfl (z - center) v)
      (mul_nonneg hK hB))

/-- The original product estimates for actual state multilinear maps
give the prescribed one-high-variation expression on a common smaller
neighbourhood.  No coefficient estimate is included among the hypotheses. -/
theorem exists_stateNeighborhood_oneHighProductBounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (C : NonlinearGeometryData S)
    (originalBase offset : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ base loss : ℕ,
      originalBase ≤ base ∧
      0 < min ε (1 / 2) ∧
      stateNeighborhood S C base (min ε (1 / 2)) ⊆
        stateNeighborhood S C originalBase ε ∧
      ∀ k factors s : ℕ, ∃ B : ℝ, 0 ≤ B ∧
        ∀ a : Fin factors → ℕ, (∑ i, a i ≤ s) →
        ∀ select : Fin factors → Fin (k + 1),
        ∀ z ∈ stateNeighborhood S C base (min ε (1 / 2)),
        ∀ A : (AnnularState S × ℝ) [×k]→L[ℝ] ℝ, ∀ K : ℝ, 0 ≤ K →
          (∀ v : Fin k → AnnularState S × ℝ, |A v| ≤
            K * ∏ i, pairGrading (stateGrading S) realGrading (a i + offset)
              ((Fin.cons (z - (C.referenceState, (0 : ℝ))) v :
                Fin (k + 1) → AnnularState S × ℝ) (select i))) →
          ∀ v : Fin k → AnnularState S × ℝ, |A v| ≤ K * B *
            oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
              base (s + loss) (z - (C.referenceState, (0 : ℝ))) v :=
  exists_neighborhood_oneHighProductBounds
    (pairGrading (stateGrading S) realGrading) (jointStateGrading_monotone S)
    (jointStateGrading_hasInterpolation hS) (C.referenceState, (0 : ℝ))
    (stateNeighborhood S C)
    (fun _ _ _ _ hb hrad => stateNeighborhood_subset hb hrad)
    (fun _ _ _ hrad hz => jointStateGrading_displacement_lt_one hrad hz)
    originalBase offset hε

end ContinuousFlexibility.Statements
