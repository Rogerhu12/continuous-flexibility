import ContinuousFlexibility.Scalar.WeightedCompositionControl
import ContinuousFlexibility.Scalar.WeightedCompositionJets

/-!
# Weighted bounds for individual scalar chain-rule terms

Positive-arity terms contain enough actual decoded jets to cancel the
outer H^(-γ). Their remaining power of H is nonnegative. The zero-arity
term uses F(0)=0 and the bounded measurable quotient F(z)/z. Both cases
are actual diagonal monomials of the normalized material jet family.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff Topology BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

def normalizedCompositionMonomial
    (T : MaterialData) (γ : ℝ) (A : SobolevModelData) (F : ℝ → ℝ)
    {n : ℕ} (a b : Fin n → ℕ) (c : ℕ)
    (g : PolarPoint → ℝ) (u : A.Space) : PolarPoint → ℝ :=
  fun p => g p * T.M (T.radius p.1) ^ c * T.H (T.radius p.1) ^ (-γ) *
    iteratedDeriv n F (A.decode u (T.radius p.1, p.2)) *
      ∏ i, mixedDerivative (a i) (b i)
        (fun q => A.decode u (T.radius q.1, q.2)) p

/-- The same base and loss control every actual scalar chain-rule term,
including the term with no derivative of the scalar function. -/
theorem normalizedCompositionMonomial_bound
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A) (hγ : 0 ≤ γ)
    {base loss : ℕ} (hbase : 2 ≤ base)
    (hdiag : (normalizedMaterialJetFamily hT hA).DiagonalEstimate base loss)
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hF0 : F 0 = 0)
    (R : ℝ) (hR : 0 ≤ R) (n s : ℕ)
    (a b : Fin n → ℕ) (c : ℕ) (horder : (∑ i, (a i + b i)) + c ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : PolarPoint → ℝ) (K : ℝ), 0 ≤ K →
      AEStronglyMeasurable g materialCylinderMeasure → (∀ p, |g p| ≤ K) →
      ∀ u : A.Space, A.grading base u ≤ R →
        MemLp (normalizedCompositionMonomial T γ A F a b c g u)
          2 materialCylinderMeasure ∧
        (eLpNorm (normalizedCompositionMonomial T γ A F a b c g u)
          2 materialCylinderMeasure).toReal ≤ K * C * A.grading (s + loss) u := by
  classical
  have hdata := hT
  obtain ⟨_, hpos, _, _, _, _, _, hinside, _⟩ := hdata
  have hH (p : PolarPoint) : 0 < T.H (T.radius p.1) := (hpos _ (hinside p.1).1).2.1
  have hM (p : PolarPoint) : 1 ≤ T.M (T.radius p.1) := (hpos _ (hinside p.1).1).2.2.2
  obtain ⟨B, hB, hrange⟩ := decodedMaterialPullback_bound_of_grading hT hA hγ hbase R hR
  cases n with
  | zero =>
    obtain ⟨L, hL, hLb⟩ := scalar_zero_value_and_quotient_bound hF hF0 hB
    obtain ⟨C, hC, hCb⟩ := hdiag R hR 0 s (fun _ : Fin 1 => 0)
      (fun _ : Fin 1 => 0) c (by simpa using horder)
    refine ⟨L * C, mul_nonneg hL hC, ?_⟩
    intro g K hK hg hgb u hu
    let U : PolarPoint → ℝ := fun p => A.decode u (T.radius p.1, p.2)
    have hU : Continuous U := (decodedMaterialPullback_contDiff hT hA u).continuous
    let coefficient : PolarPoint → ℝ := fun p => g p * (F (U p) / U p)
    have hc : AEStronglyMeasurable coefficient materialCylinderMeasure :=
      hg.mul (((hF.continuous.comp hU).measurable.div hU.measurable).aestronglyMeasurable)
    have hcb (p : PolarPoint) : |coefficient p| ≤ (K * L) * T.M (T.radius p.1) := by
      change |g p * (F (U p) / U p)| ≤ _
      rw [abs_mul]
      calc
        _ ≤ K * L :=
          mul_le_mul (hgb p) (hLb (U p) (hrange u hu p)).2 (abs_nonneg _) hK
        _ ≤ (K * L) * T.M (T.radius p.1) :=
          le_mul_of_one_le_right (mul_nonneg hK hL) (hM p)
    have h := hCb coefficient (K * L) (mul_nonneg hK hL) hc hcb u hu
    have heq : normalizedCompositionMonomial T γ A F a b c g u =
        materialFamilyMonomial (normalizedMaterialJetFamily hT hA) coefficient
          (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0) c (fun _ => u) := by
      funext p
      simp only [normalizedCompositionMonomial, materialFamilyMonomial,
        normalizedMaterialJetFamily, normalizedMaterialJet, mixedDerivative,
        iteratedDeriv_zero, Fin.prod_univ_zero, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, pow_one, mul_one]
      change g p * T.M (T.radius p.1) ^ c * T.H (T.radius p.1) ^ (-γ) * F (U p) =
        (g p * (F (U p) / U p)) * T.M (T.radius p.1) ^ c *
          (T.H (T.radius p.1) ^ (-γ) * U p)
      by_cases hz : U p = 0
      · simp only [hz, hF0, div_zero, mul_zero, zero_mul]
      · field_simp [hz]
        <;> ring
    rw [heq]
    exact ⟨h.1, h.2.trans_eq (by ring)⟩
  | succ k =>
    obtain ⟨L, hL, hLb⟩ := scalar_iteratedDeriv_bound_on_interval hF (k + 1) B
    obtain ⟨H, hH0, hHb⟩ := materialH_nonnegative_power_bounded hT
      (mul_nonneg (Nat.cast_nonneg k) hγ)
    obtain ⟨C, hC, hCb⟩ := hdiag R hR k s a b c horder
    refine ⟨L * H * C, mul_nonneg (mul_nonneg hL hH0) hC, ?_⟩
    intro g K hK hg hgb u hu
    let U : PolarPoint → ℝ := fun p => A.decode u (T.radius p.1, p.2)
    have hU : Continuous U := (decodedMaterialPullback_contDiff hT hA u).continuous
    have hn : ContDiff ℝ ∞ (iteratedDeriv (k + 1) F) := by
      rw [iteratedDeriv_eq_iterate]
      exact hF.iterate_deriv (k + 1)
    let coefficient : PolarPoint → ℝ := fun p =>
      g p * iteratedDeriv (k + 1) F (U p) * T.H (T.radius p.1) ^ ((k : ℝ) * γ)
    have hc : AEStronglyMeasurable coefficient materialCylinderMeasure :=
      (hg.mul (hn.continuous.comp hU).aestronglyMeasurable).mul
        (((contDiff_materialH_rpow hT ((k : ℝ) * γ)).comp contDiff_fst).continuous.aestronglyMeasurable)
    have hcb (p : PolarPoint) :
        |coefficient p| ≤ (K * L * H) * T.M (T.radius p.1) := by
      change |g p * iteratedDeriv (k + 1) F (U p) *
        T.H (T.radius p.1) ^ ((k : ℝ) * γ)| ≤ _
      rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (hH p) _)]
      calc
        _ ≤ K * L * H :=
          mul_le_mul
            (mul_le_mul (hgb p) (hLb (U p) (hrange u hu p)) (abs_nonneg _) hK)
            (hHb p.1) (Real.rpow_nonneg (hH p).le _) (mul_nonneg hK hL)
        _ ≤ (K * L * H) * T.M (T.radius p.1) :=
          le_mul_of_one_le_right (mul_nonneg (mul_nonneg hK hL) hH0) (hM p)
    have h := hCb coefficient (K * L * H) (mul_nonneg (mul_nonneg hK hL) hH0) hc hcb u hu
    have heq : normalizedCompositionMonomial T γ A F a b c g u =
        materialFamilyMonomial (normalizedMaterialJetFamily hT hA) coefficient
          a b c (fun _ => u) := by
      funext p
      have hjet (i : Fin (k + 1)) : mixedDerivative (a i) (b i) U p =
          T.H (T.radius p.1) ^ γ *
            normalizedMaterialJet T γ (a i) (b i) (A.decode u) p := by
        change mixedDerivative (a i) (b i) U p =
          T.H (T.radius p.1) ^ γ *
            (T.H (T.radius p.1) ^ (-γ) * mixedDerivative (a i) (b i) U p)
        rw [← mul_assoc, ← Real.rpow_add (hH p), add_neg_cancel, Real.rpow_zero, one_mul]
      have hprod : (∏ i, mixedDerivative (a i) (b i) U p) =
          (T.H (T.radius p.1) ^ γ) ^ (k + 1) *
            ∏ i, normalizedMaterialJet T γ (a i) (b i) (A.decode u) p := by
        simp_rw [hjet]
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have hpower : T.H (T.radius p.1) ^ (-γ) *
          (T.H (T.radius p.1) ^ γ) ^ (k + 1) =
            T.H (T.radius p.1) ^ ((k : ℝ) * γ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (hH p).le, ← Real.rpow_add (hH p)]
        congr 1
        push_cast
        ring
      change g p * T.M (T.radius p.1) ^ c * T.H (T.radius p.1) ^ (-γ) *
        iteratedDeriv (k + 1) F (U p) * (∏ i, mixedDerivative (a i) (b i) U p) =
          coefficient p * T.M (T.radius p.1) ^ c *
            ∏ i, normalizedMaterialJet T γ (a i) (b i) (A.decode u) p
      rw [hprod]
      calc
        _ = (g p * iteratedDeriv (k + 1) F (U p) *
            (T.H (T.radius p.1) ^ (-γ) * (T.H (T.radius p.1) ^ γ) ^ (k + 1))) *
              T.M (T.radius p.1) ^ c *
                ∏ i, normalizedMaterialJet T γ (a i) (b i) (A.decode u) p := by ring
        _ = _ := by rw [hpower]
    rw [heq]
    exact ⟨h.1, h.2.trans_eq (by ring)⟩

/-- Summing the universal finite chain rule keeps the same base and loss. -/
theorem normalizedCompositionJet_bound
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A) (hγ : 0 ≤ γ)
    {base loss : ℕ} (hbase : 2 ≤ base)
    (hdiag : (normalizedMaterialJetFamily hT hA).DiagonalEstimate base loss)
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hF0 : F 0 = 0)
    (R : ℝ) (hR : 0 ≤ R) (s a b c : ℕ) (horder : a + b + c ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : PolarPoint → ℝ) (K : ℝ), 0 ≤ K →
      AEStronglyMeasurable g materialCylinderMeasure → (∀ p, |g p| ≤ K) →
      ∀ u : A.Space, A.grading base u ≤ R →
        MemLp (fun p => g p * T.M (T.radius p.1) ^ c * T.H (T.radius p.1) ^ (-γ) *
          mixedDerivative a b (fun q => F (A.decode u (T.radius q.1, q.2))) p)
          2 materialCylinderMeasure ∧
        (eLpNorm (fun p => g p * T.M (T.radius p.1) ^ c * T.H (T.radius p.1) ^ (-γ) *
          mixedDerivative a b (fun q => F (A.decode u (T.radius q.1, q.2))) p)
          2 materialCylinderMeasure).toReal ≤ K * C * A.grading (s + loss) u := by
  classical
  let e := mixedCompositionLeibniz a b
  have ht (t : e.Index) := normalizedCompositionMonomial_bound hT hA hγ hbase hdiag hF hF0
    R hR (e.arity t) s (e.radial t) (e.angular t) c
      (by rw [Finset.sum_add_distrib, e.radial_order, e.angular_order]; exact horder)
  choose C hC hCb using ht
  refine ⟨∑ t, C t, Finset.sum_nonneg (fun t _ => hC t), ?_⟩
  intro g K hK hg hgb u hu
  let term : e.Index → PolarPoint → ℝ := fun t =>
    normalizedCompositionMonomial T γ A F (e.radial t) (e.angular t) c g u
  have hterm (t : e.Index) := hCb t g K hK hg hgb u hu
  have heq :
      (fun p => g p * T.M (T.radius p.1) ^ c * T.H (T.radius p.1) ^ (-γ) *
        mixedDerivative a b (fun q => F (A.decode u (T.radius q.1, q.2))) p) =
        ∑ t, term t := by
    funext p
    rw [e.formula F hF _ (decodedMaterialPullback_contDiff hT hA u), Finset.mul_sum,
      Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro t _
    dsimp only [term, normalizedCompositionMonomial]
    ring
  rw [heq]
  have h := scalar_finiteL2_sum_bound term (fun t => K * C t) (A.grading (s + loss) u)
    (fun t => (hterm t).1) (fun t => (hterm t).2)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  rw [Finset.mul_sum]

end ContinuousFlexibility.Statements
