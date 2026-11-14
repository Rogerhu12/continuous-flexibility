module

public import ContinuousFlexibility.Analysis.N07aMaterialDecay

/-!
# Fixed linear formulas for the actual weighted material jets

At each material point, a weighted jet is a fixed continuous linear
combination of finitely many ordinary physical jets. Applying this map
to genuine parameter towers requires no interchange of two derivatives.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff BigOperators
open ContinuousFlexibility.Statements

/-- The finite physical jet is transformed using the actual radius and
height weight, before any parameter family is chosen. -/
def n07aMaterialJetFunctional (T : MaterialData) (γ : ℝ) (a c : ℕ)
    (p : PolarPoint) : (Fin (a + 1) → ℝ) →L[ℝ] ℝ :=
  T.M (T.radius p.1) ^ c •
    ∑ i : Fin (a + 1),
      ((a.choose i.val : ℝ) *
        iteratedDeriv i.val (fun x => T.H (T.radius x) ^ (-γ)) p.1) •
      ∑ r : OrderedFinpartition (a - i.val),
        n07aRadiusJetCoefficient T r p.1 •
          ContinuousLinearMap.proj
            (⟨r.length, Nat.lt_succ_of_le (r.length_le.trans (Nat.sub_le _ _))⟩ :
              Fin (a + 1))

theorem n07aMaterialJetFunctional_apply (T : MaterialData) (γ : ℝ)
    (a c : ℕ) (p : PolarPoint) (v : Fin (a + 1) → ℝ) :
    n07aMaterialJetFunctional T γ a c p v =
      T.M (T.radius p.1) ^ c *
        ∑ i : Fin (a + 1),
          ((a.choose i.val : ℝ) *
            iteratedDeriv i.val (fun x => T.H (T.radius x) ^ (-γ)) p.1) *
          ∑ r : OrderedFinpartition (a - i.val),
            n07aRadiusJetCoefficient T r p.1 *
              v ⟨r.length, Nat.lt_succ_of_le (r.length_le.trans (Nat.sub_le _ _))⟩ := by
  simp only [n07aMaterialJetFunctional, smul_apply,
    sum_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]

/-- The linear formula is the original weighted physical jet, rather
than a separately defined formal spatial derivative. -/
theorem n07aMaterialJetFunctional_mixedDerivative
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (γ : ℝ) (a b c : ℕ) (p : PolarPoint) :
    n07aMaterialJetFunctional T γ a c p
      (fun j => mixedDerivative j.val b f (T.radius p.1, p.2)) =
      weightedPhysicalJet T γ a b c f p := by
  have hzero : ContDiff ℝ ∞ (materialPullback T 0 f) :=
    contDiff_materialPullback hT hf
  have he : materialPullback T γ f =
      fun q => T.H (T.radius q.1) ^ (-γ) * materialPullback T 0 f q := by
    funext q
    simp only [materialPullback, neg_zero, Real.rpow_zero, one_mul]
  rw [n07aMaterialJetFunctional_apply, weightedPhysicalJet, he,
    mixedDerivative_radial_mul (contDiff_materialH_rpow hT (-γ)) hzero]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [n07a_materialPullback_zero_mixedDerivative hT hf]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  exact mul_comm _ _

/-- A pointwise bound on the finite input jet gives the exact material
weight, with a constant uniform in the point and in the input vector. -/
theorem n07aMaterialJetFunctional_bound
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    (γ : ℝ) (a : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (c : ℕ) (p : PolarPoint) (W : ℝ), 0 ≤ W →
      ∀ v : Fin (a + 1) → ℝ, (∀ j, |v j| ≤ W) →
        |n07aMaterialJetFunctional T γ a c p v| ≤
          K * T.M (T.radius p.1) ^ c * T.H (T.radius p.1) ^ (-γ) * W := by
  classical
  choose B hB hBb using fun i : Fin (a + 1) =>
    iteratedDeriv_materialH_rpow_bound hT (-γ) i.val
  choose P hP hPb using fun (i : Fin (a + 1))
      (r : OrderedFinpartition (a - i.val)) =>
    n07aRadiusJetCoefficient_bounded hT r
  let Q : Fin (a + 1) → ℝ := fun i => ∑ r, P i r
  have hQ (i : Fin (a + 1)) : 0 ≤ Q i :=
    Finset.sum_nonneg (fun r _ => hP i r)
  let C : Fin (a + 1) → ℝ := fun i => (a.choose i.val : ℝ) * B i * Q i
  have hC (i : Fin (a + 1)) : 0 ≤ C i :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB i)) (hQ i)
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  intro c p W hW v hv
  have hp := (hT.2.2.2.2.2.2.2.1 p.1).1
  have hH := (hT.2.1 _ hp).2.1
  have hM : 0 ≤ T.M (T.radius p.1) := zero_le_one.trans (hT.2.1 _ hp).2.2.2
  have hHpow : 0 ≤ T.H (T.radius p.1) ^ (-γ) := Real.rpow_nonneg hH.le _
  have hinner (i : Fin (a + 1)) :
      |∑ r : OrderedFinpartition (a - i.val),
        n07aRadiusJetCoefficient T r p.1 *
          v ⟨r.length, Nat.lt_succ_of_le (r.length_le.trans (Nat.sub_le _ _))⟩| ≤ Q i * W := by
    dsimp only [Q]
    rw [Finset.sum_mul]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro r _
    rw [abs_mul]
    exact mul_le_mul (hPb i r p.1) (hv _) (abs_nonneg _) (hP i r)
  rw [n07aMaterialJetFunctional_apply, abs_mul, abs_of_nonneg (pow_nonneg hM c)]
  calc
    _ ≤ T.M (T.radius p.1) ^ c *
        ∑ i : Fin (a + 1), C i * T.H (T.radius p.1) ^ (-γ) * W := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hM c)
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)]
      calc
        _ ≤ ((a.choose i.val : ℝ) * (B i * T.H (T.radius p.1) ^ (-γ))) *
            (Q i * W) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hBb i p.1) (Nat.cast_nonneg _))
            (hinner i) (abs_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hB i) hHpow))
        _ = C i * T.H (T.radius p.1) ^ (-γ) * W := by dsimp only [C]; ring
    _ = (∑ i, C i) * T.M (T.radius p.1) ^ c * T.H (T.radius p.1) ^ (-γ) * W := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      ring

end ContinuousFlexibility.Analysis
