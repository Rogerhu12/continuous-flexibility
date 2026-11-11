import ContinuousFlexibility.Scalar.WeightedDecodedProduct
import ContinuousFlexibility.Scalar.WeightedDifferentiationPullback

/-!
# Weighted jets of an even field times an angular derivative

At the sum weight the pullback is the product of the two normalized fields,
with one angular derivative on the second factor. A finite Leibniz expansion
therefore has total input order at most one more than the output order.
The actual cylinder L² monomial estimate keeps one common base and loss.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped BigOperators ContDiff ENNReal

set_option backward.isDefEq.respectTransparency false

/-- The odd physical product used by the scalar coefficient encoding. -/
def scalarAngularProduct (f g : PolarPoint → ℝ) : PolarPoint → ℝ :=
  fun p => f p * angularPartial g p

theorem materialPullback_scalarAngularProduct
    {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    (hT : IsMaterialData D T) (f : PolarPoint → ℝ) {g : PolarPoint → ℝ}
    (hg : ContDiffOn ℝ ∞ g (annularOpen D)) :
    materialPullback T (2 * γ) (scalarAngularProduct f g) =
      fun p => materialPullback T γ f p *
        angularPartial (materialPullback T γ g) p := by
  calc
    _ = fun p => materialPullback T γ f p *
        materialPullback T γ (angularPartial g) p := by
      funext p
      have hinside := hT.2.2.2.2.2.2.2.1
      have hH : 0 < T.H (T.radius p.1) := (hT.2.1 _ (hinside p.1).1).2.1
      have he : -(2 * γ) = (-γ) + (-γ) := by ring
      unfold scalarAngularProduct materialPullback
      rw [he, Real.rpow_add hH]
      ring
    _ = _ := by rw [materialPullback_angularPartial hT hg]

/-- Every weighted jet of the actual odd product has a one-high-factor
estimate. The extra angular derivative costs one fixed input order. -/
theorem scalarAngularProduct_weightedJets_oneHigh
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) :
    ∃ base loss : ℕ, 2 ≤ base ∧ ∀ s a b c : ℕ, a + b + c ≤ s →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Fin 2 → A.Space,
        MemLp
          (weightedPhysicalJet T (2 * γ) a b c
            (scalarAngularProduct (A.decode (u 0)) (A.decode (u 1))))
          2 materialCylinderMeasure ∧
        (eLpNorm
          (weightedPhysicalJet T (2 * γ) a b c
            (scalarAngularProduct (A.decode (u 0)) (A.decode (u 1))))
          2 materialCylinderMeasure).toReal ≤
          C * ∑ i, A.grading (s + loss) (u i) *
            ∏ j ∈ Finset.univ.erase i, A.grading base (u j) := by
  classical
  obtain ⟨base, loss, hbase, hmono⟩ := materialJetMonomial_oneHigh hT hA hinterp
  refine ⟨base, loss + 1, hbase, ?_⟩
  intro s a b c horder
  let e := mixedProductLeibniz 2 a b
  let bb : e.Index → Fin 2 → ℕ := fun t i => e.angular t i + if i = 1 then 1 else 0
  have htorder (t : e.Index) :
      (∑ i, (e.radial t i + bb t i)) + c ≤ s + 1 := by
    have hr := e.radial_order t
    have ha := e.angular_order t
    simp only [Fin.sum_univ_two] at hr ha
    simp [bb, Fin.sum_univ_two] <;> omega
  have hterm (t : e.Index) := hmono 1 (s + 1) (e.radial t) (bb t) c (htorder t)
  choose C hC hCt using hterm
  refine ⟨∑ t, C t, Finset.sum_nonneg (fun t _ => hC t), ?_⟩
  intro u
  let F : Fin 2 → PolarPoint → ℝ := fun i => materialPullback T γ (A.decode (u i))
  let G : Fin 2 → PolarPoint → ℝ := fun i => if i = 1 then angularPartial (F i) else F i
  have hF (i : Fin 2) : ContDiff ℝ ∞ (F i) :=
    contDiff_materialPullback hT (hA.2.2.2.1 (u i)).1
  have hG (i : Fin 2) : ContDiff ℝ ∞ (G i) := by
    by_cases hi : i = 1
    · simp only [G, if_pos hi]
      exact contDiff_iff_contDiffAt.mpr fun p =>
        contDiffAt_angularPartial (hF i).contDiffAt (by simp)
    · simpa only [G, if_neg hi] using hF i
  have hGjet (t : e.Index) (i : Fin 2) (p : PolarPoint) :
      mixedDerivative (e.radial t i) (e.angular t i) (G i) p =
        mixedDerivative (e.radial t i) (bb t i) (F i) p := by
    by_cases hi : i = 1
    · simp only [G, bb, if_pos hi]
      exact mixedDerivative_angularPartial isOpen_univ (hF i).contDiffOn
        (e.radial t i) (e.angular t i) (mem_univ p)
    · simp only [G, bb, if_neg hi, Nat.add_zero]
  have hprod : (fun p => ∏ i, G i p) =
      fun p => F 0 p * angularPartial (F 1) p := by
    funext p
    simp [Fin.prod_univ_two, G]
  let g : e.Index → PolarPoint → ℝ := fun t =>
    materialJetMonomial T γ A (fun _ => 1) (e.radial t) (bb t) c u
  have hcoeff : ∀ p : PolarPoint, |(1 : ℝ)| ≤ (1 : ℝ) * T.M (T.radius p.1) := by
    intro p
    rw [abs_one, one_mul]
    obtain ⟨_, hpos, _, _, _, _, _, hinside, _⟩ := hT
    exact (hpos _ (hinside p.1).1).2.2.2
  have ht (t : e.Index) := hCt t (fun _ => 1) 1 zero_le_one
    aestronglyMeasurable_const hcoeff u
  have htmem (t : e.Index) : MemLp (g t) 2 materialCylinderMeasure := (ht t).1
  have htnorm (t : e.Index) : (eLpNorm (g t) 2 materialCylinderMeasure).toReal ≤
      C t * ∑ i, A.grading (s + (loss + 1)) (u i) *
        ∏ j ∈ Finset.univ.erase i, A.grading base (u j) := by
    simpa only [one_mul, Nat.add_assoc, Nat.add_comm 1 loss] using (ht t).2
  have heq :
      weightedPhysicalJet T (2 * γ) a b c
        (scalarAngularProduct (A.decode (u 0)) (A.decode (u 1))) =
      ∑ t : e.Index, g t := by
    funext p
    simp only [weightedPhysicalJet, materialPullback_scalarAngularProduct hT
      (A.decode (u 0)) (hA.2.2.2.1 (u 1)).1]
    change T.M (T.radius p.1) ^ c *
      mixedDerivative a b (fun q => F 0 q * angularPartial (F 1) q) p = _
    rw [← hprod, e.formula G hG p, Finset.mul_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro t _
    change T.M (T.radius p.1) ^ c *
      (∏ i, mixedDerivative (e.radial t i) (e.angular t i) (G i) p) =
      1 * T.M (T.radius p.1) ^ c *
        ∏ i, mixedDerivative (e.radial t i) (bb t i) (F i) p
    rw [one_mul]
    exact congrArg (fun z : ℝ => T.M (T.radius p.1) ^ c * z)
      (Finset.prod_congr rfl (fun i _ => hGjet t i p))
  rw [heq]
  refine ⟨memLp_finsetSum' Finset.univ (fun t _ => htmem t), ?_⟩
  have hfinite : (∑ t : e.Index, eLpNorm (g t) 2 materialCylinderMeasure) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun t _ => (htmem t).eLpNorm_ne_top)
  have htri := ENNReal.toReal_mono hfinite
    (eLpNorm_sum_le (f := g) (s := Finset.univ) (p := 2) (μ := materialCylinderMeasure)
      (by norm_num))
  rw [ENNReal.toReal_sum (fun t _ => (htmem t).eLpNorm_ne_top)] at htri
  apply htri.trans
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun t _ => htnorm t)

end ContinuousFlexibility.Statements
