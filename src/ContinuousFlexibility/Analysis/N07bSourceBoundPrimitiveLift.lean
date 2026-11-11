import ContinuousFlexibility.Analysis.N07bSourceBoundPrimitiveGrowth

/-!
# Actual source lifts from primitive geometric jet estimates

The finite primitive geometry estimate produces the actual element of the
prescribed volume model, with a uniform norm bound on one common state
neighborhood. The source order is `b+1`. The geometric input remains
explicit: qualitative chart regularity alone is not claimed to supply it.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ENNReal

set_option backward.isDefEq.respectTransparency true

/-- Perform the square-root calculation on real numbers, before the
norm and seminorm arguments are specialized to the actual volume model. -/
private theorem source_norm_bound_of_sq
    {N K p q : ℝ} (hN : 0 ≤ N) (hK : 0 ≤ K) (hp : 0 ≤ p)
    (hpq : p ≤ q) (hbound : N ^ 2 ≤ K * p ^ 2) :
    N ≤ (Real.sqrt K + 1) * q := by
  have hq : 0 ≤ q := hp.trans hpq
  have hn : N ≤ Real.sqrt K * q := by
    apply (sq_le_sq₀ hN (mul_nonneg (Real.sqrt_nonneg K) hq)).mp
    calc
      N ^ 2 ≤ K * p ^ 2 := hbound
      _ ≤ K * q ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp hpq 2) hK
      _ = (Real.sqrt K * q) ^ 2 := by rw [mul_pow, Real.sq_sqrt hK]
  exact hn.trans (mul_le_mul_of_nonneg_right
    (le_add_of_nonneg_right zero_le_one) hq)

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {base b : ℕ} {ε : ℝ}

/-- Primitive material jets, with constants chosen before the state,
give the actual lift and its uniform source norm estimate. -/
theorem n07b_sourceLift_uniform_bound_of_primitive_growth
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hV : IsVolumeModel T S K V)
    (hK : N04PartA D S C K base ε) (hε : 0 < ε)
    (hgeom : N07bSourcePrimitiveGrowth T S C K base ε b) :
    ∃ base' : ℕ, ∃ ε' C₀ : ℝ,
      base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧ ε' ≤ (1 / 2 : ℝ) ∧ 0 < C₀ ∧
      ∀ z ∈ stateNeighborhood S C base' ε', stateSector S z.1 → ∀ f : S.Source,
        ∃ F : V.level (3 / 4 : ℝ) 0 b,
          ‖F‖ ≤ C₀ * S.sourceGrading (b + 1) f ∧
          ∀ m, (V.forget (3 / 4 : ℝ) 0 b F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
            canonicalSource S K z m ((S.height (3 / 4 : ℝ)).decode f.val) := by
  obtain ⟨base', ε', A, hb, hε', hεle, hsmall, hA, hcoeff⟩ :=
    n07b_exists_uniform_sourceCoefficient_M_bound_of_primitive hD hT hK hε hgeom
  let K₀ : ℝ := A * n07bSourcePathConstant b
  have hK₀ : 0 ≤ K₀ := mul_nonneg hA (n07bSourcePathConstant_nonneg b)
  have hC₀ : 0 < Real.sqrt K₀ + 1 :=
    add_pos_of_nonneg_of_pos (Real.sqrt_nonneg K₀) zero_lt_one
  refine ⟨base', ε', Real.sqrt K₀ + 1, hb, hε', hεle, hsmall, hC₀, ?_⟩
  intro z hz hs f
  have hzold : z ∈ stateNeighborhood S C base ε :=
    n06_stateNeighborhood_mono (C := C) hb hεle hz
  obtain ⟨F, hF, hforget⟩ := n07b_exists_sourceLift_of_M_bound
    hD hT hS hV hK hzold hs f b hA (hcoeff z hz hs)
  have hsource : physicalNorm T (3 / 4 : ℝ) (b + 1)
      ((S.height (3 / 4 : ℝ)).decode f.val) ≤ S.sourceGrading (b + 1) f := by
    change physicalNorm T (3 / 4 : ℝ) (b + 1) ((S.height (3 / 4 : ℝ)).decode f.val) ≤
      (S.height (3 / 4 : ℝ)).grading (b + 1) f.val
    exact physicalNorm_decode_le_grading (hS.1 (3 / 4 : ℝ)) f.val (b + 1)
  refine ⟨F, ?_, hforget⟩
  exact source_norm_bound_of_sq
    (p := physicalNorm T (3 / 4 : ℝ) (b + 1) ((S.height (3 / 4 : ℝ)).decode f.val))
    (norm_nonneg F) hK₀ (Real.sqrt_nonneg _) hsource hF

/-- A common `E0` growth exponent on the four genuine primitive jet fields
is sufficient; the material data turn it into the needed subpower bound. -/
theorem n07b_sourceLift_uniform_bound_of_primitive_E0
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hV : IsVolumeModel T S K V)
    (hK : N04PartA D S C K base ε) (hε : 0 < ε)
    (hgeom : N07bSourcePrimitiveE0Growth T S C K base ε b) :
    ∃ base' : ℕ, ∃ ε' C₀ : ℝ,
      base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε ∧ ε' ≤ (1 / 2 : ℝ) ∧ 0 < C₀ ∧
      ∀ z ∈ stateNeighborhood S C base' ε', stateSector S z.1 → ∀ f : S.Source,
        ∃ F : V.level (3 / 4 : ℝ) 0 b,
          ‖F‖ ≤ C₀ * S.sourceGrading (b + 1) f ∧
          ∀ m, (V.forget (3 / 4 : ℝ) 0 b F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
            canonicalSource S K z m ((S.height (3 / 4 : ℝ)).decode f.val) :=
  n07b_sourceLift_uniform_bound_of_primitive_growth hD hT hS hV hK hε
    (n07b_sourcePrimitiveGrowth_of_E0 hT hgeom)

end ContinuousFlexibility.Analysis
