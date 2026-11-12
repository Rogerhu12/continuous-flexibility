import ContinuousFlexibility.Analysis.ReturnCoefficientLocalBounds
import ContinuousFlexibility.Analysis.ReturnCorrectionSourceNormBudget
import ContinuousFlexibility.Analysis.SourceMixedOrderInterpolation

/-!
# Fixed-loss unit-direction growth of the actual source jets

Complementary coefficient and height orders are interpolated before the
finite spatial sum is estimated. The common low order and loss are fixed
before the low-ball radii, parameter arity, and output order.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff Topology BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

private theorem oneHigh_nonneg (p : ℕ → Seminorm ℝ E) (base high : ℕ)
    {n : ℕ} (x : E) (v : Fin n → E) :
    0 ≤ oneHighVariationWeight p base high x v :=
  multilinearTameSize_nonneg _ _ _ (add_nonneg zero_le_one (apply_nonneg _ _)) v

theorem exists_symmetricDivergence_unit_growth
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ (HeightPair S))
    (hp : Monotone p) (hq : Monotone q)
    (hIp : HasInterpolation p) (hIq : HasInterpolation q)
    (hheight : ∀ s η, physicalNorm T (3 / 4 : ℝ) s
      ((S.height (3 / 4 : ℝ)).decode η.1) ≤ q s η)
    (oldBase oldLoss d requestedBase : ℕ) :
    ∃ B L : ℕ, max requestedBase oldBase ≤ B ∧
      ∀ n : ℕ,
      ∀ A : (∀ k : ℕ, E → MultilinearMap ℝ (fun _ : Fin k => E)
        (annularSmoothCoefficientSpace D)),
      ∀ V : Set E,
      CoefficientMaterialOneHighBound (T := T) p A n oldBase oldLoss d V →
      ∀ Kp Kq : ℝ, 0 ≤ Kp → 0 ≤ Kq →
      ∀ s : ℕ, B ≤ s → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ V, ∀ η : HeightPair S, ∀ v : Fin n → E × HeightPair S,
        p B x ≤ Kp → q B η ≤ Kq → (∀ i, pairGrading p q B (v i) ≤ 1) →
        physicalNorm T (3 / 4 : ℝ) s
          (symmetricDivergenceBilinear hS hT (A n x (fun i => (v i).1)) η) ≤
          C * (1 + pairGrading p q (s + L) (x, η) +
            ∑ i : Fin n, pairGrading p q (s + L) (v i)) := by
  classical
  obtain ⟨B, L, hB, hinterp⟩ := hasInterpolation_oneHigh_height_local_growth
    p q hp hq hIp hIq oldBase oldLoss (4 + d) requestedBase
  refine ⟨B, L, hB, ?_⟩
  intro n A V hcoeff Kp Kq hKp hKq s hs
  choose K hK hbK using hcoeff
  obtain ⟨I, hI, hbI⟩ := hinterp n Kp Kq hKp hKq s hs
  obtain ⟨C, hC, hbC⟩ := exists_physicalNorm_symmetricDivergenceBilinear_bound hS hT s d
  let Ksum : ℝ := ∑ k ∈ Finset.range (s + 3), K k
  have hKsum : 0 ≤ Ksum := Finset.sum_nonneg (fun k _ => hK k)
  refine ⟨C * Ksum * I, mul_nonneg (mul_nonneg hC hKsum) hI, ?_⟩
  intro x hx η v hpx hqη hv
  let Q : ℝ := 1 + pairGrading p q (s + L) (x, η) +
    ∑ i : Fin n, pairGrading p q (s + L) (v i)
  let K' (k : ℕ) : ℝ := K k * oneHighVariationWeight p oldBase (k + oldLoss) x
    (fun i => (v i).1)
  have hK' (k : ℕ) : 0 ≤ K' k := mul_nonneg (hK k) (oneHigh_nonneg _ _ _ _ _)
  have hactual := hbC (A n x (fun i => (v i).1)) K' hK'
    (fun a b r => hbK (a + b) x hx (fun i => (v i).1) a b le_rfl r) η
  have hterm (k : ℕ) (hk : k ∈ Finset.range (s + 3)) :
      K' k * physicalNorm T (3 / 4 : ℝ) (s + 4 - k + d)
        ((S.height (3 / 4 : ℝ)).decode η.1) ≤ K k * I * Q := by
    have horder : k + (s + 4 - k + d) ≤ s + (4 + d) := by
      have hk' := Finset.mem_range.mp hk
      omega
    have hi := hbI k (s + 4 - k + d) horder x η v hpx hqη hv
    calc
      _ ≤ K' k * q (s + 4 - k + d) η :=
        mul_le_mul_of_nonneg_left (hheight _ η) (hK' k)
      _ = K k * (oneHighVariationWeight p oldBase (k + oldLoss) x
          (fun i => (v i).1) * q (s + 4 - k + d) η) := mul_assoc _ _ _
      _ ≤ K k * (I * Q) := mul_le_mul_of_nonneg_left hi (hK k)
      _ = _ := (mul_assoc _ _ _).symm
  have hsum := Finset.sum_le_sum (fun k hk => hterm k hk)
  have hsum' : (∑ k ∈ Finset.range (s + 3), K' k *
      physicalNorm T (3 / 4 : ℝ) (s + 4 - k + d)
        ((S.height (3 / 4 : ℝ)).decode η.1)) ≤ Ksum * I * Q := by
    apply hsum.trans_eq
    simp only [Ksum, Finset.sum_mul]
  exact hactual.trans ((mul_le_mul_of_nonneg_left hsum' hC).trans_eq (by ring))

private theorem omitted_fiber_growth_le
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ (HeightPair S))
    (s : ℕ) {n : ℕ} (z : E × HeightPair S)
    (v : Fin (n + 1) → E × HeightPair S) (i : Fin (n + 1)) :
    1 + pairGrading p q s (z.1, (v i).2) +
        ∑ j : Fin n, pairGrading p q s (v (i.succAbove j)) ≤
      ((n : ℝ) + 1) * (1 + pairGrading p q s z +
        ∑ j : Fin (n + 1), pairGrading p q s (v j)) := by
  let W : ℝ := ∑ j : Fin (n + 1), pairGrading p q s (v j)
  have hW : 0 ≤ W := Finset.sum_nonneg (fun _ _ => apply_nonneg _ _)
  have hv (j : Fin (n + 1)) : pairGrading p q s (v j) ≤ W :=
    Finset.single_le_sum (fun k _ => apply_nonneg _ _) (Finset.mem_univ j)
  have hηi : q s (v i).2 ≤ W :=
    (le_add_of_nonneg_left (apply_nonneg (p s) (v i).1)).trans (hv i)
  have hdeleted : (∑ j : Fin n, pairGrading p q s (v (i.succAbove j))) ≤ (n : ℝ) * W := by
    have h := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hv (i.succAbove j))
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h
  have hz : 0 ≤ pairGrading p q s z := apply_nonneg _ _
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hη : 0 ≤ q s z.2 := apply_nonneg _ _
  have hpz : 0 ≤ p s z.1 := apply_nonneg _ _
  let Q : ℝ := 1 + pairGrading p q s z + W
  have hbase : 1 + pairGrading p q s (z.1, (v i).2) ≤ Q := by
    change 1 + (p s z.1 + q s (v i).2) ≤ 1 + (p s z.1 + q s z.2) + W
    linarith only [hηi, hη]
  have hWQ : W ≤ Q := le_add_of_nonneg_left (add_nonneg zero_le_one hz)
  exact (add_le_add hbase (hdeleted.trans (mul_le_mul_of_nonneg_left hWQ hn))).trans_eq
    (by dsimp only [Q, W]; ring)

theorem symmetricSourceScalarJets_norm_le_components
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (A : ∀ k : ℕ, E → MultilinearMap ℝ (fun _ : Fin k => E)
      (annularSmoothCoefficientSpace D)) (n : ℕ) (z : E × HeightPair S)
    (v : Fin (n + 1) → E × HeightPair S)
    (hmember : ∀ k (vs : Fin k → E) (η : HeightPair S),
      HeightMember D T (3 / 4 : ℝ) (symmetricDivergenceBilinear hS hT (A k z.1 vs) η))
    (s : ℕ) :
    physicalNorm T (3 / 4 : ℝ) s (symmetricSourceScalarJets hS hT A (n + 1) z v) ≤
      Real.sqrt (Fintype.card (JetIndex s) : ℝ) *
        (physicalNorm T (3 / 4 : ℝ) s
          (symmetricDivergenceBilinear hS hT (A (n + 1) z.1 (fun i => (v i).1)) z.2) +
        ∑ i : Fin (n + 1), physicalNorm T (3 / 4 : ℝ) s
          (symmetricDivergenceBilinear hS hT
            (A n z.1 (fun j => (v (i.succAbove j)).1)) (v i).2)) := by
  classical
  let F := symmetricDivergenceBilinear hS hT (A (n + 1) z.1 (fun i => (v i).1)) z.2
  let G (i : Fin (n + 1)) := symmetricDivergenceBilinear hS hT
    (A n z.1 (fun j => (v (i.succAbove j)).1)) (v i).2
  let terms : Fin (n + 2) → PolarPoint → ℝ := Fin.cons F G
  have hm (i : Fin (n + 2)) : HeightMember D T (3 / 4 : ℝ) (terms i) := by
    cases i using Fin.cases with
    | zero => exact hmember (n + 1) _ z.2
    | succ i => exact hmember n _ (v i).2
  have heq : symmetricSourceScalarJets hS hT A (n + 1) z v =
      fun p => ∑ i : Fin (n + 2), terms i p := by
    funext p
    have h := congrFun (symmetricSourceScalarJets_eq_sum hS hT A n z v) p
    simpa only [terms, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      Pi.add_apply, Finset.sum_apply, F, G] using h
  have h := physicalNorm_finset_sum_le hT Finset.univ terms
    (fun i _ => (hm i).1) (fun i _ => (hm i).2.2.2.2) s
  rw [heq]
  simpa only [terms, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, F, G] using h

theorem exists_symmetricSourceScalarJets_unit_growth
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ (HeightPair S))
    (hp : Monotone p) (hq : Monotone q)
    (hIp : HasInterpolation p) (hIq : HasInterpolation q)
    (hheight : ∀ s η, physicalNorm T (3 / 4 : ℝ) s
      ((S.height (3 / 4 : ℝ)).decode η.1) ≤ q s η)
    (oldBase oldLoss d requestedBase : ℕ) :
    ∃ B L : ℕ, max requestedBase oldBase ≤ B ∧
      ∀ n : ℕ,
      ∀ A : (∀ k : ℕ, E → MultilinearMap ℝ (fun _ : Fin k => E)
        (annularSmoothCoefficientSpace D)),
      ∀ V : Set E,
      CoefficientMaterialOneHighBound (T := T) p A n oldBase oldLoss d V →
      CoefficientMaterialOneHighBound (T := T) p A (n + 1) oldBase oldLoss d V →
      (∀ x ∈ V, ∀ k (vs : Fin k → E) (η : HeightPair S),
        HeightMember D T (3 / 4 : ℝ) (symmetricDivergenceBilinear hS hT (A k x vs) η)) →
      ∀ Kp Kq : ℝ, 0 ≤ Kp → 0 ≤ Kq →
      ∀ s : ℕ, B ≤ s → ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : E × HeightPair S, z.1 ∈ V → ∀ v : Fin (n + 1) → E × HeightPair S,
        p B z.1 ≤ Kp → q B z.2 ≤ Kq → (∀ i, pairGrading p q B (v i) ≤ 1) →
        physicalNorm T (3 / 4 : ℝ) s
          (symmetricSourceScalarJets hS hT A (n + 1) z v) ≤
          C * (1 + pairGrading p q (s + L) z +
            ∑ i : Fin (n + 1), pairGrading p q (s + L) (v i)) := by
  classical
  obtain ⟨B, L, hB, hdiv⟩ := exists_symmetricDivergence_unit_growth
    hS hT p q hp hq hIp hIq hheight oldBase oldLoss d requestedBase
  refine ⟨B, L, hB, ?_⟩
  intro n A V hlow hhigh hmember Kp Kq hKp hKq s hs
  obtain ⟨C₁, hC₁, hb₁⟩ := hdiv (n + 1) A V hhigh Kp (max Kq 1)
    hKp (zero_le_one.trans (le_max_right _ _)) s hs
  obtain ⟨C₀, hC₀, hb₀⟩ := hdiv n A V hlow Kp (max Kq 1)
    hKp (zero_le_one.trans (le_max_right _ _)) s hs
  let H : ℝ := Real.sqrt (Fintype.card (JetIndex s) : ℝ)
  let N : ℝ := (n : ℝ) + 1
  have hN : 0 ≤ N := add_nonneg (Nat.cast_nonneg _) zero_le_one
  refine ⟨H * (C₁ + N * (C₀ * N)),
    mul_nonneg (Real.sqrt_nonneg _) (add_nonneg hC₁ (mul_nonneg hN (mul_nonneg hC₀ hN))), ?_⟩
  intro z hz v hpx hqη hv
  let Q : ℝ := 1 + pairGrading p q (s + L) z +
    ∑ i : Fin (n + 1), pairGrading p q (s + L) (v i)
  have hmain := hb₁ z.1 hz z.2 v hpx (hqη.trans (le_max_left _ _)) hv
  have hlower (i : Fin (n + 1)) :
      physicalNorm T (3 / 4 : ℝ) s (symmetricDivergenceBilinear hS hT
        (A n z.1 (fun j => (v (i.succAbove j)).1)) (v i).2) ≤ C₀ * N * Q := by
    have hηi : q B (v i).2 ≤ max Kq 1 :=
      ((le_add_of_nonneg_left (apply_nonneg (p B) (v i).1)).trans (hv i)).trans
        (le_max_right _ _)
    have hi := hb₀ z.1 hz (v i).2 (fun j => v (i.succAbove j)) hpx hηi
      (fun j => hv (i.succAbove j))
    exact hi.trans ((mul_le_mul_of_nonneg_left
      (omitted_fiber_growth_le p q (s + L) z v i) hC₀).trans_eq (mul_assoc _ _ _).symm)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (n + 1)))) => hlower i)
  have hsum' : (∑ i : Fin (n + 1), physicalNorm T (3 / 4 : ℝ) s
      (symmetricDivergenceBilinear hS hT
        (A n z.1 (fun j => (v (i.succAbove j)).1)) (v i).2)) ≤ N * (C₀ * N * Q) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one, N] using hsum
  have hn := symmetricSourceScalarJets_norm_le_components hS hT A n z v (hmember z.1 hz) s
  exact hn.trans ((mul_le_mul_of_nonneg_left (add_le_add hmain hsum')
    (Real.sqrt_nonneg _)).trans_eq (by dsimp only [H, N, Q]; ring))

end ContinuousFlexibility.Statements
