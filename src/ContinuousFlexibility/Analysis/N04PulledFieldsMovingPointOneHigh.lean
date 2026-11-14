module

public import ContinuousFlexibility.Analysis.N04PulledFieldsMaskedComposition
public import ContinuousFlexibility.Analysis.N01cPhysicalGraphNormalization

/-!
# One-high normalization of the genuine moving-point jets

The spatial and parameter costs of the masked composition are charged to
one high order. The complete multilinear jet is then normalized once.
The low order and state neighborhood are unchanged; only the finite
parameter prefix enters the high-order budget.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {U : Set E} {V Ω : Set PolarPoint}

/-- Normalize the complete true mixed jet after the masked moving-point
estimate. Physical parameter derivatives are needed only through `K`.
The supplied common high index may dominate different physical and
inverse input indices without changing their shared power scale. -/
theorem n04PulledFields_movingPoint_masked_positive_oneHigh
    {f : E × PolarPoint → ℝ} (F : SmoothDirections (U ×ˢ V) f)
    {φ : E × PolarPoint → PolarPoint} (Jφ : SmoothDirections (U ×ˢ Ω) φ)
    (hφ : MapsTo φ (U ×ˢ Ω) V)
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hc : Convex ℝ (U ×ˢ Ω))
    (p : ℕ → Seminorm ℝ E) (base high : ℕ)
    {C M H L : ℝ} (hC : 0 ≤ C) (hM : 1 ≤ M)
    (hH : 0 ≤ H) (hHL : H ≤ L) (hL : 1 ≤ L)
    (K s offset top : ℕ) (hbudget : s + (offset + 1) * K ≤ top)
    (x : E) (hx : x ∈ U) (q : PolarPoint) (hq : q ∈ Ω)
    (A : ∀ a b j : ℕ, E [×j]→L[ℝ] ℝ)
    (hexpansion : ∀ j : ℕ, j ≤ K + s → ∀ u : Fin j → E × PolarPoint,
      F.D j (x, φ (x, q)) u =
        scalarAngularExpansion j
          (fun b k => scalarAngularExpansion k
            (fun a l => (A a b l).toMultilinearMap))
          (fun i => (((u i).1, (u i).2.1), (u i).2.2)))
    (hphysical : ∀ R : ℝ, 1 ≤ R → p high x ≤ R →
      ∀ a b j : ℕ, a + b + j ≤ K + s → j ≤ K →
      ∀ u : Fin j → E,
      (∀ i, p base (u i) ≤ 1) → (∀ i, p high (u i) ≤ R) →
      |A a b j u| ≤ C * parameterHeightWeight H j *
        (R ^ (1 / ((top : ℝ) + 1))) ^ (a + b))
    (hinverse : ∀ R : ℝ, 1 ≤ R → p high x ≤ R →
      ∀ n : ℕ, 0 < n → n ≤ K + s →
      ∀ w : StateAngleWord n, w.stateArity ≤ K →
      ∀ u : Fin n → E × PolarPoint,
      (∀ i, p base (u i).1 ≤ 1) → (∀ i, p high (u i).1 ≤ R) →
      (∀ i, ‖(u i).2‖ ≤ 1) →
      (∀ i, w.isState i = false → (u i).1 = 0) →
      (∀ i, w.isState i = true → (u i).2 = 0) →
      ‖Jφ.D n (x, q) u‖ ≤ M * parameterHeightWeight H w.stateArity *
        (R ^ (1 / ((top : ℝ) + 1))) ^
          (if w.stateArity = 0 then w.angleArity - 1 else w.angleArity + offset))
    (k a b : ℕ) (hk : k ≤ K) (hkpos : 0 < k) (hab : a + b ≤ s)
    (Q : SmoothDirections U
      (fun z => mixedDerivative a b (fun y => f (z, φ (z, y))) q)) :
    ∀ v : Fin k → E, |Q.D k x v| ≤
      (∑ j : Fin (K + s + 1), (Fintype.card (OrderedFinpartition j.val) : ℝ)) *
        C * (4 * M * L) ^ (K + s) * H *
          oneHighVariationWeight p base high x v := by
  let count : ℝ := ∑ j : Fin (K + s + 1),
    (Fintype.card (OrderedFinpartition j.val) : ℝ)
  let Cout : ℝ := count * C * (4 * M * L) ^ (K + s) * H
  have hcount : 0 ≤ count := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hCout : 0 ≤ Cout := mul_nonneg
    (mul_nonneg (mul_nonneg hcount hC)
      (pow_nonneg (mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans hM))
        (zero_le_one.trans hL)) _)) hH
  have hd : a + b + (offset + 1) * k ≤ top :=
    (Nat.add_le_add hab (Nat.mul_le_mul_left (offset + 1) hk)).trans hbudget
  have hexponent : (((a + b + (offset + 1) * k : ℕ) : ℝ) /
      ((top : ℝ) + 1)) ≤ 1 := spatialOrder_fraction_le_one hd
  have hn := weightedMultilinear_oneHigh_of_unitPower p base high x (Q.D k x)
    (δ := 1) (M := Cout) (exponent :=
      (((a + b + (offset + 1) * k : ℕ) : ℝ) / ((top : ℝ) + 1)))
    zero_le_one hCout hexponent (fun v hv R hR hxR hvR => by
      have ht : 1 ≤ R ^ (1 / ((top : ℝ) + 1)) :=
        Real.one_le_rpow hR (by positivity)
      have hraw := n04PulledFields_movingPoint_maskedMixedHeight_bound F Jφ hφ
        hU hΩ hc (p base) (p high) hC hM hH hHL hL
        (zero_lt_one.trans_le hR) ht K s offset x hx q hq A hexpansion
        (hphysical R hR hxR) (hinverse R hR hxR) k a b hk hab Q v hv hvR
      have hpower :
          (R ^ (1 / ((top : ℝ) + 1))) ^ (a + b + (offset + 1) * k) =
            R ^ (((a + b + (offset + 1) * k : ℕ) : ℝ) / ((top : ℝ) + 1)) := by
        rw [← Real.rpow_mul_natCast (zero_le_one.trans hR)]
        congr 1
        ring
      simpa only [one_mul, parameterHeightWeight, if_neg (Nat.ne_of_gt hkpos),
        hpower, Cout, count] using hraw)
  simpa only [one_mul, Cout, count] using hn

end ContinuousFlexibility.Analysis
