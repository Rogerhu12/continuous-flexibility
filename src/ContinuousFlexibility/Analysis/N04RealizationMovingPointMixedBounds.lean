import ContinuousFlexibility.Analysis.N04RealizationHeightGraphComposition
import ContinuousFlexibility.Analysis.N04RealizationJointMixedRegularity
import ContinuousFlexibility.Analysis.N04RealizationMixedSlotBudget

/-!
# Actual mixed jets after evaluation at the moving physical point

The original state is the linear first coordinate of the genuine graph.
Only its original parameter slots enter the inverse-point parameter
budget. The physical height estimate is used once in every partition
term, so its complete height factor is retained in the coefficient C.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {U : Set E} {V Ω : Set PolarPoint}

/-- The actual moving-point graph supplies the complete mixed-jet
interface on the unchanged parameter and spatial domains. -/
def n04Realization_movingPoint_mixedRegularity
    {f : E × PolarPoint → ℝ} (F : SmoothDirections (U ×ˢ V) f)
    {φ : E × PolarPoint → PolarPoint} (Jφ : SmoothDirections (U ×ˢ Ω) φ)
    (hφ : MapsTo φ (U ×ˢ Ω) V)
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hc : Convex ℝ (U ×ˢ Ω)) :
    MixedJetRegularity U Ω (fun x q => f (x, φ (x, q))) := by
  let L : (E × PolarPoint) →L[ℝ] E := ContinuousLinearMap.fst ℝ E PolarPoint
  let G := smoothDirectionsUniformProd
    ((smoothDirectionsLinear L).restrict Jφ.open_domain (subset_univ (U ×ˢ Ω))) Jφ
  have hmap : MapsTo (fun z => (L z, φ z)) (U ×ˢ Ω) (U ×ˢ V) := by
    intro z hz
    exact ⟨by simpa only [L, ContinuousLinearMap.coe_fst'] using hz.1, hφ hz⟩
  let J : SmoothDirections (U ×ˢ Ω) (fun z => f (z.1, φ z)) :=
    (smoothDirections_realCompTVS G F hmap).congrOn (fun z _ => by
      simp only [Function.comp_apply, L, ContinuousLinearMap.coe_fst'])
  exact n04Realization_jointMixedRegularity
    (f := fun z => f (z.1, φ z)) J hU hΩ hc

/-- A finite raw inverse-point prefix and the weighted physical joint
jets bound the actual parameter jets of every required spatial mixed
derivative. The inverse prefix uses only the original parameter budget K. -/
theorem n04Realization_movingPoint_mixed_bound
    {f : E × PolarPoint → ℝ} (F : SmoothDirections (U ×ˢ V) f)
    {φ : E × PolarPoint → PolarPoint} (Jφ : SmoothDirections (U ×ˢ Ω) φ)
    (hφ : MapsTo φ (U ×ˢ Ω) V)
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hc : Convex ℝ (U ×ˢ Ω))
    (low high : Seminorm ℝ E) {C A R t : ℝ}
    (hC : 0 ≤ C) (hA : 1 ≤ A) (hR : 0 < R) (ht : 1 ≤ t)
    (K s offset : ℕ) (x : E) (hx : x ∈ U) (q : PolarPoint) (hq : q ∈ Ω)
    (houter : ∀ j : ℕ, j ≤ K + s → ∀ w : Fin j → E × PolarPoint,
      |F.D j (x, φ (x, q)) w| ≤ C * ∏ i,
        (low (w i).1 + high (w i).1 / R + t * |(w i).2.1| + t * |(w i).2.2|))
    (hinverse : ∀ n : ℕ, 0 < n → n ≤ K + s →
      ∀ w : StateAngleWord n, w.stateArity ≤ K →
      ∀ v : Fin n → E × PolarPoint,
      (∀ i, low (v i).1 ≤ 1) → (∀ i, high (v i).1 ≤ R) →
      (∀ i, ‖(v i).2‖ ≤ 1) →
      (∀ i, w.isState i = false → (v i).1 = 0) →
      (∀ i, w.isState i = true → (v i).2 = 0) →
      ‖Jφ.D n (x, q) v‖ ≤
        A * t ^ (if w.stateArity = 0 then w.angleArity - 1 else w.angleArity + offset))
    (k a b : ℕ) (hk : k ≤ K) (hab : a + b ≤ s)
    (Q : SmoothDirections U
      (fun z => mixedDerivative a b (fun y => f (z, φ (z, y))) q))
    (v : Fin k → E) (hlow : ∀ i, low (v i) ≤ 1) (hhigh : ∀ i, high (v i) ≤ R) :
    |Q.D k x v| ≤
      (∑ j : Fin (K + s + 1), (Fintype.card (OrderedFinpartition j.val) : ℝ)) *
        C * (4 * A) ^ (K + s) * t ^ (s + (offset + 1) * K) := by
  let L : (E × PolarPoint) →L[ℝ] E := ContinuousLinearMap.fst ℝ E PolarPoint
  let G := smoothDirectionsUniformProd
    ((smoothDirectionsLinear L).restrict Jφ.open_domain (subset_univ (U ×ˢ Ω))) Jφ
  have hmap : MapsTo (fun z => (L z, φ z)) (U ×ˢ Ω) (U ×ˢ V) := by
    intro z hz
    exact ⟨by simpa only [L, ContinuousLinearMap.coe_fst'] using hz.1, hφ hz⟩
  let J : SmoothDirections (U ×ˢ Ω) (fun z => f (z.1, φ z)) :=
    (smoothDirections_realCompTVS G F hmap).congrOn (fun z _ => by
      simp only [Function.comp_apply, L, ContinuousLinearMap.coe_fst'])
  let scale : E × PolarPoint → ℝ := fun w => low w.1 + high w.1 / R +
    t * |w.2.1| + t * |w.2.2|
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hscale (w : E × PolarPoint) : 0 ≤ scale w := by
    dsimp only [scale]
    positivity
  let count : ℝ := ∑ j : Fin (K + s + 1),
    (Fintype.card (OrderedFinpartition j.val) : ℝ)
  let B : ℝ := count * C * (4 * A) ^ (K + s) * t ^ (s + (offset + 1) * K)
  have h4A : 1 ≤ 4 * A := by nlinarith
  have hbound (n : ℕ) (hn : n ≤ k + a + b)
      (u : Fin n → E × PolarPoint)
      (hu : N04RealizationMixedSlots low high K R n u) : |J.D n (x, q) u| ≤ B := by
    have hnN : n ≤ K + s := by omega
    obtain ⟨w, hw, hl, hh, hp, hstate, hspatial⟩ := hu
    let κ : ∀ c : OrderedFinpartition n, Fin c.length → ℕ :=
      fun c i => (w.restrict (c.emb i)).stateArity
    let β : ∀ c : OrderedFinpartition n, Fin c.length → ℕ :=
      fun c i => (w.restrict (c.emb i)).angleArity
    have hpart (c : OrderedFinpartition n) (i : Fin c.length) : 0 < κ c i + β c i := by
      rw [show κ c i + β c i = c.partSize i from (w.restrict (c.emb i)).arity_sum]
      exact c.partSize_pos i
    have hcost (c : OrderedFinpartition n) :
        (∑ i : Fin c.length, (β c i + (offset + 1) * κ c i)) ≤ s + (offset + 1) * K :=
      n04Realization_partition_mixedSlot_cost w c offset hnN hw
    have hraw := n04Realization_realComp_weighted_power_bound G F hmap scale hscale
      hC h4A ht n (s + (offset + 1) * K) (x, q) u
      (fun c i => β c i + (offset + 1) * κ c i) hcost
      (fun j hj z => by
        simpa only [L, ContinuousLinearMap.coe_fst'] using houter j (hj.trans hnN) z) (by
        intro c i
        have hκ : κ c i ≤ K := by
          calc
            _ ≤ ∑ j, κ c j :=
              Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
            _ = w.stateArity := w.sum_restrict_stateArity c
            _ ≤ K := hw
        have hi := hinverse (c.partSize i) (c.partSize_pos i)
          ((c.partSize_le i).trans hnN) (w.restrict (c.emb i)) hκ
          (u ∘ c.emb i) (fun j => hl _) (fun j => hh _) (fun j => hp _)
          (fun j hj => hstate _ (by simpa only [StateAngleWord.isState_restrict] using hj))
          (fun j hj => hspatial _ (by simpa only [StateAngleWord.isState_restrict] using hj))
        have hLo := n04Realization_linearJet_seminorm_le L low (c.partSize_pos i)
          (x, q) (u ∘ c.emb i) zero_le_one (fun j => by
            simpa only [L, ContinuousLinearMap.coe_fst', Function.comp_apply] using hl (c.emb i j))
        have hHi := n04Realization_linearJet_seminorm_le L high (c.partSize_pos i)
          (x, q) (u ∘ c.emb i) hR.le (fun j => by
            simpa only [L, ContinuousLinearMap.coe_fst', Function.comp_apply] using hh (c.emb i j))
        have hs : low (continuousLinearJets L (c.partSize i) (x, q) (u ∘ c.emb i)) +
            high (continuousLinearJets L (c.partSize i) (x, q) (u ∘ c.emb i)) / R ≤ 2 := by
          have hd := (div_le_one hR).mpr hHi
          linarith
        have hb := n04Realization_movingGraph_slot_bound
          (fun z : E => low z + high z / R)
          (continuousLinearJets L (c.partSize i) (x, q) (u ∘ c.emb i),
            Jφ.D (c.partSize i) (x, q) (u ∘ c.emb i))
          (κ c i) (β c i) offset (hpart c i) hA ht hs hi
        simpa only [G, scale, n04Realization_linearPointGraph_D_apply] using hb)
    have hcard : (Fintype.card (OrderedFinpartition n) : ℝ) ≤ count :=
      Finset.single_le_sum
        (f := fun j : Fin (K + s + 1) => (Fintype.card (OrderedFinpartition j.val) : ℝ))
        (fun _ _ => Nat.cast_nonneg _)
        (Finset.mem_univ (⟨n, Nat.lt_succ_of_le hnN⟩ : Fin (K + s + 1)))
    have hpows := pow_le_pow_right₀ h4A hnN
    have hcount0 : 0 ≤ count := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    exact hraw.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul (mul_le_mul_of_nonneg_right hcard hC) hpows
        (pow_nonneg (zero_le_one.trans h4A) _) (mul_nonneg hcount0 hC))
      (pow_nonneg ht0 _))
  rw [n04Realization_mixedParameter_eq_joint J hU hΩ hc a b k x hx q hq Q v]
  apply n04Realization_jointMixed_bound_of_stableSlots
    (N04RealizationMixedSlots low high K R)
    (fun n u hu => n04Realization_mixedSlots_snoc low high hR.le hu (1, 0)
      (by simp only [Prod.norm_def, norm_one, norm_zero, max_eq_left zero_le_one, le_refl]))
    (fun n u hu => n04Realization_mixedSlots_snoc low high hR.le hu (0, 1)
      (by simp only [Prod.norm_def, norm_one, norm_zero, max_eq_right zero_le_one, le_refl]))
    hΩ hc x hx q hq J k a b B hbound (fun i => (v i, 0))
  exact n04Realization_mixedSlots_parameters low high hk v hlow hhigh

end ContinuousFlexibility.Analysis
