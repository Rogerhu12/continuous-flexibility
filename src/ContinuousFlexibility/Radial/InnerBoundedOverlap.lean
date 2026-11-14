module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Bounded overlap for the inner interface errors

The interface error is a sum of local blocks. Its norm depends on the
number of blocks meeting a cut, rather than on the total number of cuts.
The estimate applies to the nonsymmetric blocks obtained after conjugating
by either weight. In the inner chain the overlap constant is two.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open scoped BigOperators InnerProductSpace

variable {ι : Type*} [Fintype ι]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)]
  [∀ i, InnerProductSpace ℝ (F i)] [∀ i, CompleteSpace (F i)]

/-- The local error blocks, extended to the full boundary Hilbert space. -/
def innerInterfaceBlockSum (L : ∀ i, E →L[ℝ] F i)
    (K : ∀ i, F i →L[ℝ] F i) : E →L[ℝ] E :=
  ∑ i, (L i).adjoint.comp ((K i).comp (L i))

theorem innerInterfaceBlockSum_inner (L : ∀ i, E →L[ℝ] F i)
    (K : ∀ i, F i →L[ℝ] F i) (x y : E) :
    ⟪innerInterfaceBlockSum L K x, y⟫_ℝ =
      ∑ i, ⟪K i (L i x), L i y⟫_ℝ := by
  simp only [innerInterfaceBlockSum, sum_apply, ContinuousLinearMap.comp_apply,
    sum_inner, ContinuousLinearMap.adjoint_inner_left]

/-- Cauchy--Schwarz for local restrictions with a common overlap bound. -/
theorem inner_overlap_cauchy (L : ∀ i, E →L[ℝ] F i) {d : ℝ} (hd : 0 ≤ d)
    (hL : ∀ x, ∑ i, ‖L i x‖ ^ 2 ≤ d * ‖x‖ ^ 2)
    {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ i, ‖L i x‖ * ‖L i y‖ ≤ d := by
  have hX : ∑ i, ‖L i x‖ ^ 2 ≤ d := by simpa only [hx, one_pow, mul_one] using hL x
  have hY : ∑ i, ‖L i y‖ ^ 2 ≤ d := by simpa only [hy, one_pow, mul_one] using hL y
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => ‖L i x‖) (fun i => ‖L i y‖)
  apply (sq_le_sq₀ (Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))) hd).mp
  calc
    (∑ i, ‖L i x‖ * ‖L i y‖) ^ 2 ≤
        (∑ i, ‖L i x‖ ^ 2) * ∑ i, ‖L i y‖ ^ 2 := hcs
    _ ≤ d * d := mul_le_mul hX hY (Finset.sum_nonneg (fun i _ => sq_nonneg _)) hd
    _ = d ^ 2 := (pow_two d).symm

/-- The sum of local errors costs the overlap multiplicity, independent of
the number of cells. No symmetry of the conjugated errors is assumed. -/
theorem norm_innerInterfaceBlockSum_le (L : ∀ i, E →L[ℝ] F i)
    (K : ∀ i, F i →L[ℝ] F i) {d η : ℝ} (hd : 0 ≤ d) (hη : 0 ≤ η)
    (hL : ∀ x, ∑ i, ‖L i x‖ ^ 2 ≤ d * ‖x‖ ^ 2)
    (hK : ∀ i, ‖K i‖ ≤ η) :
    ‖innerInterfaceBlockSum L K‖ ≤ d * η := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le (mul_nonneg hd hη)
  intro x y hx hy
  simp only [RCLike.re_to_real, innerInterfaceBlockSum_inner]
  calc
    (∑ i, ⟪K i (L i x), L i y⟫_ℝ) ≤
        ∑ i, η * (‖L i x‖ * ‖L i y‖) := by
      apply Finset.sum_le_sum
      intro i _
      calc
        ⟪K i (L i x), L i y⟫_ℝ ≤ ‖K i (L i x)‖ * ‖L i y‖ :=
          real_inner_le_norm _ _
        _ ≤ (η * ‖L i x‖) * ‖L i y‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact ((K i).le_opNorm (L i x)).trans
            (mul_le_mul_of_nonneg_right (hK i) (norm_nonneg _))
        _ = η * (‖L i x‖ * ‖L i y‖) := mul_assoc _ _ _
    _ = η * ∑ i, ‖L i x‖ * ‖L i y‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ η * d := mul_le_mul_of_nonneg_left (inner_overlap_cauchy L hd hL hx hy) hη
    _ = d * η := mul_comm _ _

/-- Contractive normalization by the positive reference interface preserves
the dimension-independent local-block bound. -/
theorem norm_innerInterfaceBlockSum_normalized_le
    (L : ∀ i, E →L[ℝ] F i) (K : ∀ i, F i →L[ℝ] F i)
    (A : E →L[ℝ] E) {d η : ℝ} (hd : 0 ≤ d) (hη : 0 ≤ η)
    (hL : ∀ x, ∑ i, ‖L i x‖ ^ 2 ≤ d * ‖x‖ ^ 2)
    (hK : ∀ i, ‖K i‖ ≤ η) (hA : ‖A‖ ≤ 1) :
    ‖A.comp ((innerInterfaceBlockSum L K).comp A.adjoint)‖ ≤ d * η := by
  have hAstar : ‖A.adjoint‖ ≤ 1 := by
    simpa only [LinearIsometryEquiv.norm_map] using hA
  have hblock := norm_innerInterfaceBlockSum_le L K hd hη hL hK
  calc
    _ ≤ ‖A‖ * ‖(innerInterfaceBlockSum L K).comp A.adjoint‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ((d * η) * 1) := by
      apply mul_le_mul hA _ (norm_nonneg _) zero_le_one
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul hblock hAstar (norm_nonneg _) (mul_nonneg hd hη))
    _ = d * η := by ring

end ContinuousFlexibility.Radial
