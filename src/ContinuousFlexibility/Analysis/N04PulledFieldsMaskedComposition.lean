import ContinuousFlexibility.Analysis.N04PulledFieldsMaskedExpansion
import ContinuousFlexibility.Analysis.N04RealizationMovingPointMixedBounds

/-!
# Moving-point estimates with the original physical parameter budget

The physical mixed estimate is required only through parameter order `K`,
independently of the number of spatial derivatives. The linear state
coordinate of the genuine graph vanishes on every zero-state block.
The exact masked expansion therefore retains the physical loss of the
original parameter prefix and the existing height and spatial weights.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

/-- A word with zero state count has no state-marked slot. -/
theorem n04PulledFields_isState_false_of_stateArity_zero
    {n : ℕ} (w : StateAngleWord n) (hw : w.stateArity = 0) (i : Fin n) :
    w.isState i = false := by
  have hi : (if w.isState i then 1 else 0 : ℕ) ≤ w.stateArity := by
    rw [w.stateArity_eq_sum]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  cases hflag : w.isState i with
  | false => rfl
  | true =>
      have hbad : (1 : ℕ) ≤ 0 := by
        simpa only [hflag, if_true, hw] using hi
      omega

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {U : Set E} {V Ω : Set PolarPoint}

/-- Positive jets of the genuine graph's state coordinate vanish when
all original slots of the block are spatial. -/
theorem n04PulledFields_linearStateJet_zero_of_mask
    (n : ℕ) (hn : 0 < n) (w : StateAngleWord n) (hw : w.stateArity = 0)
    (x : E × PolarPoint) (v : Fin n → E × PolarPoint)
    (hv : ∀ i, w.isState i = false → (v i).1 = 0) :
    continuousLinearJets (ContinuousLinearMap.fst ℝ E PolarPoint) n x v = 0 := by
  cases n with
  | zero => omega
  | succ n =>
      cases n with
      | zero =>
          have hzero := hv 0 (n04PulledFields_isState_false_of_stateArity_zero w hw 0)
          simpa only [continuousLinearJets,
            ContinuousMultilinearMap.ofSubsingleton_apply_apply,
            ContinuousLinearMap.coe_fst'] using hzero
      | succ n =>
          simp only [continuousLinearJets, zero_apply]

/-- The original moving-point bound with a physical parameter prefix
through `K` rather than the total spatial-and-parameter order `K + s`.
All graph towers are genuine towers of the actual composed functions. -/
theorem n04PulledFields_movingPoint_maskedMixedHeight_bound
    {f : E × PolarPoint → ℝ} (F : SmoothDirections (U ×ˢ V) f)
    {φ : E × PolarPoint → PolarPoint} (Jφ : SmoothDirections (U ×ˢ Ω) φ)
    (hφ : MapsTo φ (U ×ˢ Ω) V)
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hc : Convex ℝ (U ×ˢ Ω))
    (low high : Seminorm ℝ E) {C M H L R t : ℝ}
    (hC : 0 ≤ C) (hM : 1 ≤ M) (hH : 0 ≤ H) (hHL : H ≤ L) (hL : 1 ≤ L)
    (hR : 0 < R) (ht : 1 ≤ t)
    (K s offset : ℕ) (x : E) (hx : x ∈ U) (q : PolarPoint) (hq : q ∈ Ω)
    (A : ∀ a b j : ℕ, E [×j]→L[ℝ] ℝ)
    (hexpansion : ∀ j : ℕ, j ≤ K + s → ∀ u : Fin j → E × PolarPoint,
      F.D j (x, φ (x, q)) u =
        scalarAngularExpansion j
          (fun b k => scalarAngularExpansion k
            (fun a l => (A a b l).toMultilinearMap))
          (fun i => (((u i).1, (u i).2.1), (u i).2.2)))
    (hphysical : ∀ a b j : ℕ, a + b + j ≤ K + s → j ≤ K →
      ∀ u : Fin j → E,
      (∀ i, low (u i) ≤ 1) → (∀ i, high (u i) ≤ R) →
      |A a b j u| ≤ C * parameterHeightWeight H j * t ^ (a + b))
    (hinverse : ∀ n : ℕ, 0 < n → n ≤ K + s →
      ∀ w : StateAngleWord n, w.stateArity ≤ K →
      ∀ u : Fin n → E × PolarPoint,
      (∀ i, low (u i).1 ≤ 1) → (∀ i, high (u i).1 ≤ R) →
      (∀ i, ‖(u i).2‖ ≤ 1) →
      (∀ i, w.isState i = false → (u i).1 = 0) →
      (∀ i, w.isState i = true → (u i).2 = 0) →
      ‖Jφ.D n (x, q) u‖ ≤ M * parameterHeightWeight H w.stateArity *
        t ^ (if w.stateArity = 0 then w.angleArity - 1 else w.angleArity + offset))
    (k a b : ℕ) (hk : k ≤ K) (hab : a + b ≤ s)
    (Q : SmoothDirections U
      (fun z => mixedDerivative a b (fun y => f (z, φ (z, y))) q))
    (v : Fin k → E) (hlow : ∀ i, low (v i) ≤ 1) (hhigh : ∀ i, high (v i) ≤ R) :
    |Q.D k x v| ≤
      (∑ j : Fin (K + s + 1), (Fintype.card (OrderedFinpartition j.val) : ℝ)) *
        C * (4 * M * L) ^ (K + s) * parameterHeightWeight H k *
          t ^ (a + b + (offset + 1) * k) := by
  classical
  let π : (E × PolarPoint) →L[ℝ] E := ContinuousLinearMap.fst ℝ E PolarPoint
  let G := smoothDirectionsUniformProd
    ((smoothDirectionsLinear π).restrict Jφ.open_domain (subset_univ (U ×ˢ Ω))) Jφ
  have hmap : MapsTo (fun z => (π z, φ z)) (U ×ˢ Ω) (U ×ˢ V) := by
    intro z hz
    exact ⟨by simpa only [π, ContinuousLinearMap.coe_fst'] using hz.1, hφ hz⟩
  let J : SmoothDirections (U ×ˢ Ω) (fun z => f (z.1, φ z)) :=
    (smoothDirections_realCompTVS G F hmap).congrOn (fun z _ => by
      simp only [Function.comp_apply, π, ContinuousLinearMap.coe_fst'])
  let p : E → ℝ := fun z => low z + high z / R
  have hp (z : E) : 0 ≤ p z :=
    add_nonneg (apply_nonneg low _) (div_nonneg (apply_nonneg high _) hR.le)
  let W : ℝ := 4 * M * L
  have hW : 1 ≤ W := by dsimp only [W]; nlinarith
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hHk : 0 ≤ parameterHeightWeight H k := parameterHeightWeight_nonneg hH k
  let count : ℝ := ∑ j : Fin (K + s + 1),
    (Fintype.card (OrderedFinpartition j.val) : ℝ)
  let B : ℝ := count * C * W ^ (K + s) * parameterHeightWeight H k *
    t ^ (a + b + (offset + 1) * k)
  let P : ∀ n : ℕ, (Fin n → E × PolarPoint) → Prop :=
    fun n u => ∃ w : StateAngleWord n, w.stateArity = k ∧
      (∀ i, low (u i).1 ≤ 1) ∧ (∀ i, high (u i).1 ≤ R) ∧
      (∀ i, ‖(u i).2‖ ≤ 1) ∧
      (∀ i, w.isState i = false → (u i).1 = 0) ∧
      (∀ i, w.isState i = true → (u i).2 = 0)
  have hdata (a' b' j : ℕ) (horder : a' + b' + j ≤ K + s) (hj : j ≤ K)
      (u : Fin j → E) :
      |A a' b' j u| ≤ C * parameterHeightWeight H j * t ^ (a' + b') *
        ∏ i, p (u i) :=
    n04Realization_multilinear_twoSeminorm_bound (A a' b' j) low high
      (mul_nonneg (mul_nonneg hC (parameterHeightWeight_nonneg hH _))
        (pow_nonneg ht0 _)) hR (hphysical a' b' j horder hj) u
  have hbound (n : ℕ) (hn : n ≤ k + a + b)
      (u : Fin n → E × PolarPoint) (hu : P n u) : |J.D n (x, q) u| ≤ B := by
    have hnN : n ≤ K + s := by omega
    obtain ⟨w, hw, hl, hh, hs, hz, htang⟩ := hu
    let κ : ∀ c : OrderedFinpartition n, Fin c.length → ℕ :=
      fun c i => (w.restrict (c.emb i)).stateArity
    let β : ∀ c : OrderedFinpartition n, Fin c.length → ℕ :=
      fun c i => (w.restrict (c.emb i)).angleArity
    have hpart (c : OrderedFinpartition n) (i : Fin c.length) : 0 < κ c i + β c i := by
      rw [show κ c i + β c i = c.partSize i from (w.restrict (c.emb i)).arity_sum]
      exact c.partSize_pos i
    have hsum (c : OrderedFinpartition n) : (∑ i, κ c i) = k :=
      (w.sum_restrict_stateArity c).trans hw
    have hcost (c : OrderedFinpartition n) :
        (∑ i : Fin c.length, (β c i + (offset + 1) * κ c i)) ≤
          a + b + (offset + 1) * k :=
      n04Realization_partition_mixedSlot_cost w c offset (by omega) hw.le
    have hinv (c : OrderedFinpartition n) (i : Fin c.length) :
        ‖Jφ.D (c.partSize i) (x, q) (u ∘ c.emb i)‖ ≤
          M * parameterHeightWeight H (κ c i) *
            t ^ (if κ c i = 0 then β c i - 1 else β c i + offset) := by
      have hκ : κ c i ≤ K := by
        calc
          _ ≤ ∑ j, κ c j :=
            Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
          _ = k := hsum c
          _ ≤ K := hk
      exact hinverse (c.partSize i) (c.partSize_pos i)
        ((c.partSize_le i).trans hnN) (w.restrict (c.emb i)) hκ (u ∘ c.emb i)
        (fun j => hl _) (fun j => hh _) (fun j => hs _)
        (fun j hj => hz _ (by simpa only [StateAngleWord.isState_restrict] using hj))
        (fun j hj => htang _ (by simpa only [StateAngleWord.isState_restrict] using hj))
    have hstate (c : OrderedFinpartition n) (i : Fin c.length) :
        p (continuousLinearJets π (c.partSize i) (x, q) (u ∘ c.emb i)) ≤ 2 := by
      have hlo := n04Realization_linearJet_seminorm_le π low (c.partSize_pos i)
        (x, q) (u ∘ c.emb i) zero_le_one (fun j => by
          simpa only [π, ContinuousLinearMap.coe_fst', Function.comp_apply] using hl (c.emb i j))
      have hhi := n04Realization_linearJet_seminorm_le π high (c.partSize_pos i)
        (x, q) (u ∘ c.emb i) hR.le (fun j => by
          simpa only [π, ContinuousLinearMap.coe_fst', Function.comp_apply] using hh (c.emb i j))
      have hd := (div_le_one hR).mpr hhi
      dsimp only [p]
      linarith
    have hmask (c : OrderedFinpartition n) (i : Fin c.length) (hκ : κ c i = 0) :
        continuousLinearJets π (c.partSize i) (x, q) (u ∘ c.emb i) = 0 := by
      exact n04PulledFields_linearStateJet_zero_of_mask (c.partSize i)
        (c.partSize_pos i) (w.restrict (c.emb i)) hκ (x, q) (u ∘ c.emb i)
        (fun j hj => hz (c.emb i j)
          (by simpa only [StateAngleWord.isState_restrict] using hj))
    have hterm (c : OrderedFinpartition n) :
        |F.D c.length (x, φ (x, q))
          (fun i => G.D (c.partSize i) (x, q) (u ∘ c.emb i))| ≤
          C * W ^ (K + s) * parameterHeightWeight H k *
            t ^ (a + b + (offset + 1) * k) := by
      have hraw := n04PulledFields_doubleExpansion_maskedHeight_bound c.length 0 K p hp
        (fun a' b' j => (A a' b' j).toMultilinearMap) hC hM hH hHL hL ht
        offset (κ c) (β c) (hpart c) ((hsum c).le.trans hk)
        (fun a' b' j hj hjK z => by
          simpa only [Nat.zero_add, ContinuousMultilinearMap.coe_coe] using
            hdata a' b' j (hj.trans (c.length_le.trans hnN)) hjK z)
        (fun i =>
          ((continuousLinearJets π (c.partSize i) (x, q) (u ∘ c.emb i),
              (Jφ.D (c.partSize i) (x, q) (u ∘ c.emb i)).1),
            (Jφ.D (c.partSize i) (x, q) (u ∘ c.emb i)).2))
        (hmask c) (hstate c)
        (fun i => (show |(Jφ.D (c.partSize i) (x, q) (u ∘ c.emb i)).1| ≤
            ‖Jφ.D (c.partSize i) (x, q) (u ∘ c.emb i)‖ from by
          simpa only [Real.norm_eq_abs] using norm_fst_le
            (Jφ.D (c.partSize i) (x, q) (u ∘ c.emb i))).trans (hinv c i))
        (fun i => (show |(Jφ.D (c.partSize i) (x, q) (u ∘ c.emb i)).2| ≤
            ‖Jφ.D (c.partSize i) (x, q) (u ∘ c.emb i)‖ from by
          simpa only [Real.norm_eq_abs] using norm_snd_le
            (Jφ.D (c.partSize i) (x, q) (u ∘ c.emb i))).trans (hinv c i))
      have hraw' :
          |F.D c.length (x, φ (x, q))
            (fun i => G.D (c.partSize i) (x, q) (u ∘ c.emb i))| ≤
            C * W ^ c.length * parameterHeightWeight H k *
              t ^ (∑ i : Fin c.length, (β c i + (offset + 1) * κ c i)) := by
        rw [hexpansion c.length (c.length_le.trans hnN)]
        simpa only [G, n04Realization_linearPointGraph_D_apply, Nat.zero_add, hsum, W] using hraw
      exact hraw'.trans (mul_le_mul
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hW (c.length_le.trans hnN)) hC) hHk)
        (pow_le_pow_right₀ ht (hcost c)) (pow_nonneg ht0 _)
        (mul_nonneg (mul_nonneg hC (pow_nonneg (zero_le_one.trans hW) _)) hHk))
    have hcard : (Fintype.card (OrderedFinpartition n) : ℝ) ≤ count :=
      Finset.single_le_sum
        (f := fun j : Fin (K + s + 1) => (Fintype.card (OrderedFinpartition j.val) : ℝ))
        (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ
          (⟨n, Nat.lt_succ_of_le hnN⟩ : Fin (K + s + 1)))
    change |(smoothDirections_realCompTVS G F hmap).D n (x, q) u| ≤ B
    rw [smoothDirections_realCompTVS_D_apply]
    simp only [π, ContinuousLinearMap.coe_fst']
    calc
      _ ≤ ∑ c : OrderedFinpartition n,
          |F.D c.length (x, φ (x, q))
            (fun i => G.D (c.partSize i) (x, q) (u ∘ c.emb i))| := by
        simpa only [Real.norm_eq_abs] using norm_sum_le
          (Finset.univ : Finset (OrderedFinpartition n))
          (fun c => F.D c.length (x, φ (x, q))
            (fun i => G.D (c.partSize i) (x, q) (u ∘ c.emb i)))
      _ ≤ ∑ _c : OrderedFinpartition n,
          C * W ^ (K + s) * parameterHeightWeight H k *
            t ^ (a + b + (offset + 1) * k) :=
        Finset.sum_le_sum (fun c _ => hterm c)
      _ = (Fintype.card (OrderedFinpartition n) : ℝ) *
          (C * W ^ (K + s) * parameterHeightWeight H k *
            t ^ (a + b + (offset + 1) * k)) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ count * (C * W ^ (K + s) * parameterHeightWeight H k *
          t ^ (a + b + (offset + 1) * k)) :=
        mul_le_mul_of_nonneg_right hcard
          (mul_nonneg (mul_nonneg (mul_nonneg hC
            (pow_nonneg (zero_le_one.trans hW) _)) hHk) (pow_nonneg ht0 _))
      _ = B := by dsimp only [B]; ring
  rw [n04Realization_mixedParameter_eq_joint J hU hΩ hc a b k x hx q hq Q v]
  apply n04Realization_jointMixed_bound_of_stableSlots P
    (fun n u hu => n04Realization_mixedSlots_snoc_with_arity low high (fun j => j = k)
      hR.le hu (1, 0)
      (by simp only [Prod.norm_def, norm_one, norm_zero, max_eq_left zero_le_one, le_refl]))
    (fun n u hu => n04Realization_mixedSlots_snoc_with_arity low high (fun j => j = k)
      hR.le hu (0, 1)
      (by simp only [Prod.norm_def, norm_one, norm_zero, max_eq_right zero_le_one, le_refl]))
    hΩ hc x hx q hq J k a b B hbound (fun i => (v i, 0))
  exact n04Realization_mixedSlots_parameters_with_arity low high (fun j => j = k)
    rfl v hlow hhigh

end ContinuousFlexibility.Analysis
