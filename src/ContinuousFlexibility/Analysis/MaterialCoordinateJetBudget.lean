import ContinuousFlexibility.Analysis.MaterialCoefficientMultipliers
import ContinuousFlexibility.Analysis.ReturnCoefficientLocalBounds

/-!
# The exact spatial budget under the material coordinate

All positive derivatives of the supplied radius are uniformly bounded.
At each spatial point, the material-coordinate jet through order `k`
therefore costs a constant times the ordinary jets through that same
order. The constant precedes the coefficient, the point, and its bound.
In particular neither the derivative loss nor a material weight exponent
changes when an actual coefficient tower is pulled back.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

theorem materialCoordinate_fderiv_pointwise_budget
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : PolarPoint → ℝ,
      ContDiffOn ℝ ∞ f (annularOpen D) → ∀ p : PolarPoint, ∀ K : ℝ, 0 ≤ K →
      (∀ a b : ℕ, a + b ≤ n →
        |mixedDerivative a b f (T.radius p.1, p.2)| ≤ K) →
      ‖iteratedFDeriv ℝ n (fun q => f (T.radius q.1, q.2)) p‖ ≤ C * K := by
  classical
  have hjet (i : Fin n) :=
    materialCoordinate_positive_fderiv_bounded hT (i.val + 1) (by omega)
  choose B hB hBb using hjet
  let Q : ℝ := 1 + ∑ i : Fin n, B i
  have hQ : 1 ≤ Q := le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hB i))
  have hQ₀ : 0 ≤ Q := zero_le_one.trans hQ
  let g : PolarPoint → PolarPoint := fun p => (T.radius p.1, p.2)
  have hg : ContDiff ℝ ∞ g :=
    (hT.2.2.2.2.2.2.1.comp contDiff_fst).prodMk contDiff_snd
  have hV : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hmap : MapsTo g univ (annularOpen D) :=
    fun p _ => ⟨(hT.2.2.2.2.2.2.2.1 p.1).1, mem_univ _⟩
  refine ⟨(n.factorial : ℝ) * (2 : ℝ) ^ n * Q ^ n,
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _))
      (pow_nonneg hQ₀ _), ?_⟩
  intro f hf p K hK hb
  have hout (k : ℕ) (hk : k ≤ n) :
      ‖iteratedFDerivWithin ℝ k f (annularOpen D) (g p)‖ ≤ (2 : ℝ) ^ n * K := by
    rw [iteratedFDerivWithin_of_isOpen k hV (hmap (mem_univ p))]
    have h := norm_iteratedFDeriv_le_of_mixedDerivative hV hf k
      (hmap (mem_univ p)) hK (fun a b hab => by
        simpa only [Real.norm_eq_abs] using hb a b (hab.le.trans hk))
    exact h.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk) hK)
  have hin (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
      ‖iteratedFDerivWithin ℝ k g univ p‖ ≤ Q ^ k := by
    rw [iteratedFDerivWithin_of_isOpen k isOpen_univ (mem_univ p)]
    let i : Fin n := ⟨k - 1, by omega⟩
    have hi : i.val + 1 = k := by dsimp only [i]; omega
    have hsum : B i ≤ ∑ j : Fin n, B j :=
      Finset.single_le_sum (fun j _ => hB j) (Finset.mem_univ i)
    have hj : ‖iteratedFDeriv ℝ k g p‖ ≤ B i := by
      simpa only [hi] using hBb i p
    have hbound : ‖iteratedFDeriv ℝ k g p‖ ≤ Q :=
      hj.trans (hsum.trans (by dsimp only [Q]; linarith))
    exact hbound.trans (by simpa only [pow_one] using pow_le_pow_right₀ hQ hk)
  have h := norm_iteratedFDerivWithin_comp_le hf hg.contDiffOn (n := n) (by simp)
    hV.uniqueDiffOn isOpen_univ.uniqueDiffOn hmap (mem_univ p) hout hin
  rw [iteratedFDerivWithin_of_isOpen n isOpen_univ (mem_univ p)] at h
  have h' : ‖iteratedFDeriv ℝ n (fun q => f (T.radius q.1, q.2)) p‖ ≤
      (n.factorial : ℝ) * ((2 : ℝ) ^ n * K) * Q ^ n := by
    simpa only [Function.comp_def, g] using h
  exact h'.trans_eq (by ring)

theorem materialCoordinate_mixed_pointwise_budget
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : PolarPoint → ℝ,
      ContDiffOn ℝ ∞ f (annularOpen D) → ∀ p : PolarPoint, ∀ K : ℝ, 0 ≤ K →
      (∀ a b : ℕ, a + b ≤ k →
        |mixedDerivative a b f (T.radius p.1, p.2)| ≤ K) →
      ∀ a b : ℕ, a + b ≤ k →
        |mixedDerivative a b (fun q => f (T.radius q.1, q.2)) p| ≤ C * K := by
  classical
  have hfinite (i : Fin (k + 1)) := materialCoordinate_fderiv_pointwise_budget hT i.val
  choose C hC hCb using hfinite
  refine ⟨∑ i : Fin (k + 1), C i, Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  intro f hf p K hK hb a b hab
  let i : Fin (k + 1) := ⟨a + b, by omega⟩
  have hcomp : ContDiff ℝ ∞ (fun q : PolarPoint => f (T.radius q.1, q.2)) :=
    hf.comp_contDiff ((hT.2.2.2.2.2.2.1.comp contDiff_fst).prodMk contDiff_snd)
      (fun q => ⟨(hT.2.2.2.2.2.2.2.1 q.1).1, mem_univ _⟩)
  have hjet := hCb i f hf p K hK (fun c d hcd => hb c d (hcd.trans hab))
  have hsum : C i ≤ ∑ j : Fin (k + 1), C j :=
    Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)
  exact (mixedDerivative_abs_le_norm_iteratedFDeriv isOpen_univ hcomp.contDiffOn
    a b (mem_univ p)).trans (hjet.trans (mul_le_mul_of_nonneg_right hsum hK))

/-- The material coefficient interface follows from the same ordinary
jet estimates, with the same low order, loss, and material exponent. -/
theorem coefficientMaterialOneHighBound_of_ordinary
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    (p : ℕ → Seminorm ℝ E)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E)
      (annularSmoothCoefficientSpace D))
    (n base loss d : ℕ) (V : Set E)
    (hbound : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ V, ∀ v : Fin n → E,
      ∀ a b : ℕ, a + b ≤ k → ∀ q ∈ annularOpen D,
        |mixedDerivative a b (fun y => ((A n x v).val y).1) q| ≤
          C * oneHighVariationWeight p base (k + loss) x v * T.M q.1 ^ d ∧
        |mixedDerivative a b (fun y => ((A n x v).val y).2) q| ≤
          C * oneHighVariationWeight p base (k + loss) x v * T.M q.1 ^ d) :
    CoefficientMaterialOneHighBound (T := T) p A n base loss d V := by
  intro k
  obtain ⟨C, hC, hb⟩ := hbound k
  obtain ⟨B, hB, hbudget⟩ := materialCoordinate_mixed_pointwise_budget hT k
  refine ⟨B * C, mul_nonneg hB hC, fun x hx v a b hab q => ?_⟩
  let W : ℝ := oneHighVariationWeight p base (k + loss) x v
  have hW : 0 ≤ W := multilinearTameSize_nonneg _ _ _
    (add_nonneg zero_le_one (apply_nonneg _ _)) v
  have hinside : (T.radius q.1, q.2) ∈ annularOpen D :=
    ⟨(hT.2.2.2.2.2.2.2.1 q.1).1, mem_univ _⟩
  have hM : 0 ≤ T.M (T.radius q.1) ^ d :=
    pow_nonneg (zero_le_one.trans (hT.2.1 _ hinside.1).2.2.2) d
  have hK : 0 ≤ C * W * T.M (T.radius q.1) ^ d :=
    mul_nonneg (mul_nonneg hC hW) hM
  have hfst := hbudget (fun y => ((A n x v).val y).1) (A n x v).property.fst
    q _ hK (fun c e hce => (hb x hx v c e hce _ hinside).1) a b hab
  have hsnd := hbudget (fun y => ((A n x v).val y).2) (A n x v).property.snd
    q _ hK (fun c e hce => (hb x hx v c e hce _ hinside).2) a b hab
  have heq : B * (C * W * T.M (T.radius q.1) ^ d) =
      B * C * W * T.M (T.radius q.1) ^ d := by ring
  exact ⟨hfst.trans_eq heq, hsnd.trans_eq heq⟩

end ContinuousFlexibility.Statements
