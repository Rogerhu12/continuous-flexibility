module

public import ContinuousFlexibility.Analysis.N01cCosineLowGeometry

/-!
# One common neighbourhood for the actual compact flow geometry

Only the fixed physical angular order five is used to choose the base.
The quotient positivity radius is chosen once from the primitive optical
geometry. All higher flow estimates therefore share this same domain.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Blueprint

open Set MeasureTheory ContinuousFlexibility.Analysis ContinuousFlexibility.Statements
open scoped ContDiff

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

theorem n01_exists_common_cosineLowGeometry
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε) (hB : N01PartB D S C base ε)
    (hG : N01PrimitiveGeometry D T S C)
    (hSpeed : CharacteristicSpeedTameBounds D T S C base loss ε) :
    ∃ base' : ℕ, ∃ ε' : ℝ, base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧
      (∀ z ∈ stateNeighborhood S C base' ε', ∀ m r,
        r ∈ Icc (C.left m) (C.right m) →
          0 < twoRootDivided (componentOpticalSquare D S C m z)
            (C.left m) (C.right m) r) ∧
      (∀ z ∈ stateNeighborhood S C base' ε', ∀ m,
        ContDiff ℝ ∞ (fun p : PolarPoint => componentCosineSpeed D S C m (z, p))) ∧
      ∃ M : ℝ, 0 < M ∧ ∀ z ∈ stateNeighborhood S C base' ε', ∀ m,
        ∀ hGz : ContDiff ℝ ∞ (fun p : PolarPoint => componentCosineSpeed D S C m (z, p)),
        circleFlowLambda (fun p => componentCosineSpeed D S C m (z, p)) hGz
            (componentCosineSpeed_periodic hS z m) 4 0 Real.pi ≤ M ∧
        circleFlowReferenceSize (fun p => componentCosineSpeed D S C m (z, p)) hGz
            (componentCosineSpeed_periodic hS z m)
            (fun t => componentCosineSpeed D S C m ((C.referenceState, 0), (t, 0)))
            3 0 Real.pi ≤ M := by
  obtain ⟨base', hb, M₀, hM₀, hbound⟩ :=
    n01_speedDifference_fixedOrder_uniform hT hA.1.1 hSpeed 5
  obtain ⟨εq, hεq, hquotient⟩ := n01_exists_componentOpticalQuotient_positive hS hT hA hG
  let ε' : ℝ := min (min ε (1 / 2)) εq
  have hε' : 0 < ε' := lt_min (lt_min hε (by norm_num)) hεq
  have hε'ε : ε' ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have hB' : N01PartB D S C base' ε' := n01PartB_mono hB hb hε'ε
  have hpos : ∀ z ∈ stateNeighborhood S C base' ε', ∀ m r,
      r ∈ Icc (C.left m) (C.right m) →
        0 < twoRootDivided (componentOpticalSquare D S C m z)
          (C.left m) (C.right m) r := by
    intro z hz m r hr
    exact hquotient base' z (stateNeighborhood_subset le_rfl (min_le_right _ _) hz) m r hr
  have hsmooth : ∀ z ∈ stateNeighborhood S C base' ε', ∀ m,
      ContDiff ℝ ∞ (fun p : PolarPoint => componentCosineSpeed D S C m (z, p)) :=
    fun z hz m => contDiff_componentCosineSpeed hS hT hA hB' hpos hz m
  have href : (C.referenceState, 0) ∈ stateNeighborhood S C base' ε' :=
    reference_mem_stateNeighborhood S C base' hε'
  have hwidth : 0 < D.b - D.a := sub_pos.mpr
    ((hA.2.2.1.1 0).1.trans ((hA.2.2.1.1 0).2.1.trans (hA.2.2.1.1 0).2.2))
  let M : ℝ := Real.pi * (2 : ℝ) ^ 5 * ((D.b - D.a) * M₀) + 1
  have hM : 0 < M := by dsimp only [M]; positivity
  refine ⟨base', ε', hb, hε', hε'ε, hpos, hsmooth, M, hM, ?_⟩
  intro z hz m hGz
  have hGc : Continuous (fun t => componentCosineSpeed D S C m
      ((C.referenceState, 0), (t, 0))) :=
    (hsmooth _ href m).continuous.comp (continuous_id.prodMk continuous_const)
  have hbound' : ∀ i n p, n ≤ 5 → p.1 ∈ Ioo (C.left i) (C.right i) →
      |characteristicSpeedFamily D S C 0 n p z| ≤ M₀ :=
    hbound z (stateNeighborhood_subset le_rfl (min_le_left _ _) hz)
  have hfive := componentCosineSpeed_referenceSize_le hS hT hA hε' hB' hz hM₀.le
    hbound' m hGz hGc
  have hthree := componentCosineSpeed_referenceSize_le hS hT hA hε' hB' hz hM₀.le
    (s := 3) (fun i n p hn hp => hbound' i n p (hn.trans (by decide)) hp) m hGz hGc
  have hlambda := circleFlowLambda_le_referenceSize
    (fun p => componentCosineSpeed D S C m (z, p)) hGz
    (componentCosineSpeed_periodic hS z m) Real.pi_pos.le
    (hGc.intervalIntegrable 0 Real.pi) 4
  refine ⟨hlambda.trans (hfive.trans ?_), hthree.trans ?_⟩
  · exact le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)
  · have hh : Real.pi * (2 : ℝ) ^ 3 * ((D.b - D.a) * M₀) ≤
        Real.pi * (2 : ℝ) ^ 5 * ((D.b - D.a) * M₀) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by norm_num : (2 : ℝ) ^ 3 ≤ 2 ^ 5) Real.pi_pos.le)
        (mul_nonneg hwidth.le hM₀.le)
    exact hh.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))

end ContinuousFlexibility.Blueprint
