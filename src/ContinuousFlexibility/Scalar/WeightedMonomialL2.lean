import ContinuousFlexibility.Scalar.WeightedPointwise
import ContinuousFlexibility.Scalar.WeightedOneHighInterpolation
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

/-!
# Actual material-jet monomials in the cylinder L² norm

One factor carries the full material weight and the L² norm.  The remaining
factors use the quantitative cylinder evaluation bound.  A coefficient bounded
by one material envelope costs one further weighted jet, and interpolation
puts the resulting high order on only one input factor.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped BigOperators ContDiff ENNReal

set_option backward.isDefEq.respectTransparency false

/-- The literal coefficient times material weight times finite jet product. -/
def materialJetMonomial (T : MaterialData) (γ : ℝ) (A : SobolevModelData)
    {k : ℕ} (coefficient : PolarPoint → ℝ) (a b : Fin (k + 1) → ℕ) (c : ℕ)
    (u : Fin (k + 1) → A.Space) : PolarPoint → ℝ :=
  fun p => coefficient p * T.M (T.radius p.1) ^ c *
    ∏ i, mixedDerivative (a i) (b i) (materialPullback T γ (A.decode (u i))) p

/-- A genuine L² estimate for a coefficient bounded by one material envelope.
The weighted jet on factor zero carries `c + 1`; every other factor costs only
the fixed two-derivative point-evaluation shift. -/
theorem materialJetMonomial_memLp_and_norm_le
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    {k : ℕ} (a b : Fin (k + 1) → ℕ) (c : ℕ)
    {coefficient : PolarPoint → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hcoefficient : AEStronglyMeasurable coefficient materialCylinderMeasure)
    (hbound : ∀ p, |coefficient p| ≤ K * T.M (T.radius p.1))
    (u : Fin (k + 1) → A.Space) :
    MemLp (materialJetMonomial T γ A coefficient a b c u) 2 materialCylinderMeasure ∧
    (eLpNorm (materialJetMonomial T γ A coefficient a b c u)
      2 materialCylinderMeasure).toReal ≤
      (K * ∏ i ∈ Finset.univ.erase (0 : Fin (k + 1)),
        (4 * Real.sqrt Real.pi) * A.grading (a i + b i + 2) (u i)) *
        A.grading (a 0 + b 0 + (c + 1)) (u 0) := by
  classical
  let J : Fin (k + 1) → PolarPoint → ℝ := fun i =>
    mixedDerivative (a i) (b i) (materialPullback T γ (A.decode (u i)))
  let W : PolarPoint → ℝ := fun p => T.M (T.radius p.1)
  let F : PolarPoint → ℝ := weightedPhysicalJet T γ (a 0) (b 0) (c + 1) (A.decode (u 0))
  let N : Fin (k + 1) → ℝ := fun i =>
    (4 * Real.sqrt Real.pi) * A.grading (a i + b i + 2) (u i)
  let B : ℝ := K * ∏ i ∈ Finset.univ.erase (0 : Fin (k + 1)), N i
  have hN (i : Fin (k + 1)) : 0 ≤ N i := by dsimp [N]; positivity
  have hB : 0 ≤ B := mul_nonneg hK (Finset.prod_nonneg (fun i _ => hN i))
  have hJbound (i : Fin (k + 1)) (p : PolarPoint) : |J i p| ≤ N i :=
    materialPullback_decode_mixedDerivative_le_grading hT hA (u i) (a i) (b i) p
  have hJcont (i : Fin (k + 1)) : Continuous (J i) :=
    (contDiff_mixedDerivative (contDiff_materialPullback hT (hA.2.2.2.1 (u i)).1)
      (a i) (b i)).continuous
  have hW : Continuous W := by
    obtain ⟨hsmooth, _, _, _, _, _, hrad, hInv, _⟩ := hT
    exact (hsmooth T.M (by simp)).continuousOn.comp_continuous
      (hrad.continuous.comp continuous_fst) (fun p => (hInv p.1).1)
  have hW0 (p : PolarPoint) : 0 ≤ W p := by
    obtain ⟨_, hpos, _, _, _, _, _, hInv, _⟩ := hT
    exact zero_le_one.trans (hpos (T.radius p.1) (hInv p.1).1).2.2.2
  have hprodcont : Continuous (fun p => ∏ i, J i p) :=
    continuous_finsetProd Finset.univ (fun i _ => hJcont i)
  have hg : AEStronglyMeasurable
      (materialJetMonomial T γ A coefficient a b c u) materialCylinderMeasure :=
    (hcoefficient.mul (hW.pow c).aestronglyMeasurable).mul hprodcont.aestronglyMeasurable
  have hF : MemLp F 2 materialCylinderMeasure :=
    (hA.2.2.2.1 (u 0)).2.2.2.2 (a 0) (b 0) (c + 1)
  have hpoint (p : PolarPoint) :
      ‖materialJetMonomial T γ A coefficient a b c u p‖ ≤ B * ‖F p‖ := by
    have hprod0 : 0 ≤ ∏ i, |J i p| := Finset.prod_nonneg (fun i _ => abs_nonneg _)
    have htail : (∏ i ∈ Finset.univ.erase (0 : Fin (k + 1)), |J i p|) ≤
        ∏ i ∈ Finset.univ.erase (0 : Fin (k + 1)), N i :=
      Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hJbound i p)
    simp only [Real.norm_eq_abs]
    change |coefficient p * W p ^ c * ∏ i, J i p| ≤ B * |W p ^ (c + 1) * J 0 p|
    rw [abs_mul, abs_mul, Finset.abs_prod, abs_of_nonneg (pow_nonneg (hW0 p) c),
      abs_mul, abs_of_nonneg (pow_nonneg (hW0 p) (c + 1))]
    calc
      |coefficient p| * W p ^ c * (∏ i, |J i p|) ≤
          (K * W p) * W p ^ c * (∏ i, |J i p|) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hbound p) (pow_nonneg (hW0 p) c)) hprod0
      _ = (K * W p ^ (c + 1)) *
          (|J 0 p| * ∏ i ∈ Finset.univ.erase (0 : Fin (k + 1)), |J i p|) := by
        rw [pow_succ, Finset.mul_prod_erase Finset.univ
          (fun i => |J i p|) (Finset.mem_univ (0 : Fin (k + 1)))]
        ring
      _ ≤ (K * W p ^ (c + 1)) *
          (|J 0 p| * ∏ i ∈ Finset.univ.erase (0 : Fin (k + 1)), N i) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left htail (abs_nonneg _))
          (mul_nonneg hK (pow_nonneg (hW0 p) (c + 1)))
      _ = B * (W p ^ (c + 1) * |J 0 p|) := by dsimp [B]; ring
  have haepoint : ∀ᵐ p ∂materialCylinderMeasure,
      ‖materialJetMonomial T γ A coefficient a b c u p‖ ≤ B * ‖F p‖ :=
    Eventually.of_forall hpoint
  refine ⟨hF.of_le_mul hg haepoint, ?_⟩
  have he := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hg haepoint 2
  have hfinite : ENNReal.ofReal B * eLpNorm F 2 materialCylinderMeasure ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF.eLpNorm_lt_top).ne
  have hreal := ENNReal.toReal_mono hfinite he
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB] at hreal
  have hFnorm : (eLpNorm F 2 materialCylinderMeasure).toReal ≤
      A.grading (a 0 + b 0 + (c + 1)) (u 0) :=
    (weightedPhysicalJet_norm_le_physicalNorm (hA.2.2.2.1 (u 0))
      (a := a 0) (b := b 0) (c := c + 1) le_rfl).trans
        (physicalNorm_decode_le_grading hA (u 0) (a 0 + b 0 + (c + 1)))
  exact hreal.trans (mul_le_mul_of_nonneg_left hFnorm hB)

private theorem monomial_input_product_le
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) {k : ℕ}
    (a b d : Fin (k + 1) → ℕ) (c : ℕ) {K Q : ℝ} (hK : 0 ≤ K) (hQ : 0 ≤ Q)
    (hd0 : a 0 + b 0 + (c + 1) ≤ d 0 + 2)
    (hdi : ∀ i, a i + b i + 2 ≤ d i + 2) (u : Fin (k + 1) → E) :
    (K * ∏ i ∈ Finset.univ.erase (0 : Fin (k + 1)), Q * p (a i + b i + 2) (u i)) *
        p (a 0 + b 0 + (c + 1)) (u 0) ≤
      (K * ∏ i ∈ Finset.univ.erase (0 : Fin (k + 1)), Q) *
        ∏ i, p (d i + 2) (u i) := by
  classical
  have hprod :
      p (a 0 + b 0 + (c + 1)) (u 0) *
        (∏ i ∈ Finset.univ.erase (0 : Fin (k + 1)), p (a i + b i + 2) (u i)) ≤
      ∏ i, p (d i + 2) (u i) := by
    rw [← Finset.mul_prod_erase Finset.univ (fun i => p (d i + 2) (u i))
      (Finset.mem_univ (0 : Fin (k + 1)))]
    exact mul_le_mul (hp hd0 (u 0))
      (Finset.prod_le_prod₀ (fun _ _ => apply_nonneg _ _) (fun i _ => hp (hdi i) (u i)))
      (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _)) (apply_nonneg _ _)
  calc
    _ = (K * ∏ i ∈ Finset.univ.erase (0 : Fin (k + 1)), Q) *
        (p (a 0 + b 0 + (c + 1)) (u 0) *
          ∏ i ∈ Finset.univ.erase (0 : Fin (k + 1)), p (a i + b i + 2) (u i)) := by
      rw [Finset.prod_mul_distrib]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod
      (mul_nonneg hK (Finset.prod_nonneg (fun _ _ => hQ)))

/-- Every actual weighted monomial has an L² one-high-factor estimate with a
single base and loss for all positive arities.  Its coefficient is constrained
only by measurability and its pointwise material-envelope bound. -/
theorem materialJetMonomial_oneHigh
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) :
    ∃ base loss : ℕ, 2 ≤ base ∧ ∀ k s : ℕ,
      ∀ (a b : Fin (k + 1) → ℕ) (c : ℕ),
      (∑ i, (a i + b i)) + c ≤ s →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (coefficient : PolarPoint → ℝ) (K : ℝ), 0 ≤ K →
        AEStronglyMeasurable coefficient materialCylinderMeasure →
        (∀ p, |coefficient p| ≤ K * T.M (T.radius p.1)) →
        ∀ u : Fin (k + 1) → A.Space,
          MemLp (materialJetMonomial T γ A coefficient a b c u) 2 materialCylinderMeasure ∧
          (eLpNorm (materialJetMonomial T γ A coefficient a b c u)
            2 materialCylinderMeasure).toReal ≤
            K * C * ∑ i, A.grading (s + loss) (u i) *
              ∏ j ∈ Finset.univ.erase i, A.grading base (u j) := by
  classical
  have hp : Monotone A.grading := gradedSeminorm_monotone (fun n => A.level n) A.bond
  obtain ⟨base, loss, hbase, hproduct⟩ := hinterp.oneHigh_product hp
  refine ⟨base, loss + 1, hbase, ?_⟩
  intro k s a b c horder
  let d : Fin (k + 1) → ℕ := fun i => a i + b i + if i = 0 then c + 1 else 0
  have hd : (∑ i, d i) ≤ s + 1 := by
    have heq : (∑ i, d i) = (∑ i, (a i + b i)) + (c + 1) := by
      simp [d, Finset.sum_add_distrib]
    rw [heq]
    omega
  obtain ⟨C, hC, hCx⟩ := hproduct k (s + 1) d hd
  let P : ℝ := ∏ i ∈ Finset.univ.erase (0 : Fin (k + 1)), (4 * Real.sqrt Real.pi)
  have hP : 0 ≤ P := Finset.prod_nonneg (fun _ _ => by positivity)
  refine ⟨P * C, mul_nonneg hP hC, ?_⟩
  intro coefficient K hK hc hcBound u
  obtain ⟨hm, hn⟩ := materialJetMonomial_memLp_and_norm_le hT hA a b c hK hc hcBound u
  refine ⟨hm, ?_⟩
  have hd0 : a 0 + b 0 + (c + 1) ≤ d 0 + 2 := by simp [d]
  have hdi (i : Fin (k + 1)) : a i + b i + 2 ≤ d i + 2 := by
    dsimp [d]
    split_ifs <;> omega
  have hindex : s + 1 + loss = s + (loss + 1) := by omega
  have hi := hCx u
  rw [hindex] at hi
  calc
    (eLpNorm (materialJetMonomial T γ A coefficient a b c u)
        2 materialCylinderMeasure).toReal ≤
        (K * ∏ i ∈ Finset.univ.erase (0 : Fin (k + 1)),
          (4 * Real.sqrt Real.pi) * A.grading (a i + b i + 2) (u i)) *
          A.grading (a 0 + b 0 + (c + 1)) (u 0) := hn
    _ ≤ (K * P) * ∏ i, A.grading (d i + 2) (u i) :=
      monomial_input_product_le hp a b d c hK
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hd0 hdi u
    _ ≤ (K * P) * (C * ∑ i, A.grading (s + (loss + 1)) (u i) *
        ∏ j ∈ Finset.univ.erase i, A.grading base (u j)) :=
      mul_le_mul_of_nonneg_left hi (mul_nonneg hK hP)
    _ = _ := by ring

end ContinuousFlexibility.Statements
