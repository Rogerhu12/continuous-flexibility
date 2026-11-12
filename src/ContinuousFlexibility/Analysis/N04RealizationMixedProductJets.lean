import ContinuousFlexibility.Scalar.WeightedProductJets
import ContinuousFlexibility.Analysis.LocalMixedProductBounds
import ContinuousFlexibility.Analysis.N07aMixedLocalCalculus
import ContinuousFlexibility.Analysis.N01cPhysicalLieProducts

/-!
# Parameter jets of spatial differential products

The existing finite Leibniz data are localized to the actual open domain.
Each original factor retains its assigned spatial order, including any
fixed derivatives already present in the operator. The genuine parameter
product estimate retains one height factor at positive parameter order.
No interpolation exponent is changed when a spatial derivative is taken.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

/-- The existing finite Leibniz expansion applies to smooth functions on
their genuine open domain. Global extensions are used only for germs. -/
theorem n04Realization_mixedProductLeibniz_on_open
    {m a b : ℕ} (e : MixedProductLeibniz m a b)
    {Ω : Set PolarPoint} (hΩ : IsOpen Ω) (f : Fin m → PolarPoint → ℝ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) Ω) {q : PolarPoint} (hq : q ∈ Ω) :
    mixedDerivative a b (fun p => ∏ i, f i p) q =
      ∑ t : e.Index, ∏ i, mixedDerivative (e.radial t i) (e.angular t i) (f i) q := by
  classical
  choose g hg he using fun i => exists_global_contDiff_germ_of_open hΩ (hf i) hq
  have hprod : (fun p => ∏ i, g i p) =ᶠ[𝓝 q] (fun p => ∏ i, f i p) := by
    filter_upwards [Filter.eventually_all.mpr he] with p hp
    exact Finset.prod_congr rfl (fun i _ => hp i)
  rw [← mixedDerivative_eq_of_germ hprod a b, e.formula g hg]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.prod_congr rfl
  intro i _
  exact mixedDerivative_eq_of_germ (he i) _ _

/-- Fixed derivative offsets are counted before the outer mixed
derivatives are distributed. -/
theorem n04Realization_mixedProduct_shifted_formula
    {m a b : ℕ} (e : MixedProductLeibniz m a b)
    (α β : Fin m → ℕ) {Ω : Set PolarPoint} (hΩ : IsOpen Ω)
    (f : Fin m → PolarPoint → ℝ) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) Ω)
    {q : PolarPoint} (hq : q ∈ Ω) :
    mixedDerivative a b (fun p => ∏ i, mixedDerivative (α i) (β i) (f i) p) q =
      ∑ t : e.Index, ∏ i,
        mixedDerivative (e.radial t i + α i) (e.angular t i + β i) (f i) q := by
  rw [n04Realization_mixedProductLeibniz_on_open e hΩ
    (fun i => mixedDerivative (α i) (β i) (f i))
    (fun i => contDiffOn_mixedDerivative hΩ (hf i) (α i) (β i)) hq]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.prod_congr rfl
  intro i _
  exact n07a_mixedDerivative_mixedDerivative_on hΩ (hf i)
    (e.radial t i) (e.angular t i) (α i) (β i) hq

private theorem n04Realization_mixedProduct_shifted_total
    {m a b : ℕ} (e : MixedProductLeibniz m a b) (α β : Fin m → ℕ) (t : e.Index) :
    (∑ i, ((e.radial t i + α i) + (e.angular t i + β i))) =
      a + b + ∑ i, (α i + β i) := by
  have he (i : Fin m) : (e.radial t i + α i) + (e.angular t i + β i) =
      (e.radial t i + e.angular t i) + (α i + β i) := by omega
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    e.radial_order, e.angular_order]

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- The finite expansion constructs the genuine tower of the actual
spatial differential product, before estimating any parameter order. -/
def n04Realization_mixedJetRegularity_shiftedProduct
    {m : ℕ} {U : Set X} {Ω : Set PolarPoint} {f : Fin m → X → PolarPoint → ℝ}
    (hU : IsOpen U) (hΩ : IsOpen Ω) (RF : ∀ i, MixedJetRegularity U Ω (f i))
    (α β : Fin m → ℕ) :
    MixedJetRegularity U Ω
      (fun x q => ∏ i, mixedDerivative (α i) (β i) (f i x) q) where
  spatial x hx := contDiffOn_prod (fun i _ =>
    contDiffOn_mixedDerivative hΩ ((RF i).spatial x hx) (α i) (β i))
  parameter a b q hq := by
    let e := mixedProductLeibniz m a b
    let J : ∀ t : e.Index, SmoothDirections U (fun x => ∏ i,
        mixedDerivative (e.radial t i + α i) (e.angular t i + β i) (f i x) q) :=
      fun t => smoothDirections_finiteProduct hU (fun i =>
        (RF i).parameter (e.radial t i + α i) (e.angular t i + β i) q hq)
    exact (smoothDirections_finiteSum hU J).congr (fun x hx =>
      (n04Realization_mixedProduct_shifted_formula e α β hΩ
        (fun i => f i x) (fun i => (RF i).spatial x hx) hq).symm)

/-- A finite spatial differential product has a genuine all-order
parameter estimate with the exact total spatial exponent. The universal
constant is selected before the domain, fields, point, or material data.
Only the finite parameter prefix appearing in the ordered partitions is
used, so later applications may retain a loss depending on that order. -/
theorem n04Realization_shiftedProduct_parameter_bound
    (m k a b : ℕ) (RH : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ α β : Fin m → ℕ,
      ∀ U : Set X, IsOpen U → ∀ Ω : Set PolarPoint, IsOpen Ω →
      ∀ f : Fin m → X → PolarPoint → ℝ,
      ∀ RF : ∀ i, MixedJetRegularity U Ω (f i),
      ∀ q (hq : q ∈ Ω), ∀ J : SmoothDirections U
        (fun x => mixedDerivative a b
          (fun p => ∏ i, mixedDerivative (α i) (β i) (f i x) p) q),
      ∀ x ∈ U, ∀ v : Fin k → X,
      ∀ s : ℕ, a + b + ∑ i, (α i + β i) ≤ s →
      ∀ H E C A R : ℝ, 0 ≤ H → H ≤ RH → 1 ≤ E → 1 ≤ C → 0 ≤ A → 1 ≤ R →
      (∀ i : Fin m, ∀ u w : ℕ, u + w ≤ s →
        ‖mixedDerivative u w (f i x) q‖ ≤
          C * E ^ A * R ^ (((u + w : ℕ) : ℝ) / ((s : ℝ) + 1))) →
      (∀ i : Fin m, ∀ u w : ℕ, ∀ (huw : u + w ≤ s)
        (d : OrderedFinpartition k) (j : Fin d.length),
        ‖((RF i).parameter u w q hq).D (d.partSize j) x (v ∘ d.emb j)‖ ≤
          H * (C * E ^ A * R ^ (((u + w : ℕ) : ℝ) / ((s : ℝ) + 1)))) →
      ‖J.D k x v‖ ≤ B * C ^ m * E ^ (A * (m : ℝ)) * parameterHeightWeight H k *
        R ^ (((a + b + ∑ i, (α i + β i) : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
  classical
  let e := mixedProductLeibniz m a b
  obtain ⟨B₀, hB₀, hb₀⟩ := exists_finiteProduct_allParameterJet_bound (X := X) m k RH
  let B : ℝ := 1 + (Fintype.card e.Index : ℝ) * B₀
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  refine ⟨B, hB, ?_⟩
  intro α β U hU Ω hΩ f RF q hq J x hx v s hs H E C A R hH hHR hE hC hA hR hbase hjet
  let terms : e.Index → X → ℝ := fun t y => ∏ i,
    mixedDerivative (e.radial t i + α i) (e.angular t i + β i) (f i y) q
  let JT : ∀ t : e.Index, SmoothDirections U (terms t) := fun t =>
    smoothDirections_finiteProduct hU (fun i =>
      (RF i).parameter (e.radial t i + α i) (e.angular t i + β i) q hq)
  let W : ℝ := C ^ m * E ^ (A * (m : ℝ)) * parameterHeightWeight H k *
    R ^ (((a + b + ∑ i, (α i + β i) : ℕ) : ℝ) / ((s : ℝ) + 1))
  have hW : 0 ≤ W := by
    dsimp only [W]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans hC) _)
        (Real.rpow_nonneg (zero_le_one.trans hE) _)) (parameterHeightWeight_nonneg hH k))
      (Real.rpow_nonneg (zero_le_one.trans hR) _)
  have ht (t : e.Index) : ‖(JT t).D k x v‖ ≤ B₀ * W := by
    let u : Fin m → ℕ := fun i => e.radial t i + α i
    let w : Fin m → ℕ := fun i => e.angular t i + β i
    let orders : Fin m → ℕ := fun i => u i + w i
    have hsum : (∑ i, orders i) = a + b + ∑ i, (α i + β i) :=
      n04Realization_mixedProduct_shifted_total e α β t
    have hi (i : Fin m) : u i + w i ≤ s :=
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans
        (hsum.le.trans hs)
    let Bi : Fin m → ℝ := fun i => C * E ^ A * R ^ ((orders i : ℝ) / ((s : ℝ) + 1))
    have hBi (i : Fin m) : 0 < Bi i :=
      mul_pos (mul_pos (zero_lt_one.trans_le hC)
        (Real.rpow_pos_of_pos (zero_lt_one.trans_le hE) _))
        (Real.rpow_pos_of_pos (zero_lt_one.trans_le hR) _)
    have hprod := hb₀
      (fun i => (RF i).parameter (u i) (w i) q hq) (JT t) x hx H hH hHR Bi hBi
      (fun i => hbase i (u i) (w i) (hi i)) v
      (fun i d j => hjet i (u i) (w i) (hi i) d j)
    have hBiProd := n01c_finiteProduct_spatialEnvelope (m := m) (L := m) le_rfl
      orders s hC hE hA hR
    rw [hsum] at hBiProd
    calc
      ‖(JT t).D k x v‖ ≤ B₀ * parameterHeightWeight H k * ∏ i, Bi i := hprod
      _ ≤ B₀ * parameterHeightWeight H k *
          (C ^ m * E ^ (A * (m : ℝ)) *
            R ^ (((a + b + ∑ i, (α i + β i) : ℕ) : ℝ) / ((s : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hBiProd
          (mul_nonneg hB₀.le (parameterHeightWeight_nonneg hH k))
      _ = B₀ * W := by dsimp only [W]; ring
  have hd := smoothDirections_D_eq_linearCombination J JT (fun _ => (1 : ℝ))
    (fun y hy => by
      simpa only [one_mul] using n04Realization_mixedProduct_shifted_formula e α β hΩ
        (fun i => f i y) (fun i => (RF i).spatial y hy) hq) k hx v
  simp only [one_mul] at hd
  rw [hd]
  calc
    ‖∑ t : e.Index, (JT t).D k x v‖ ≤ ∑ t : e.Index, ‖(JT t).D k x v‖ := norm_sum_le _ _
    _ ≤ ∑ _t : e.Index, B₀ * W := Finset.sum_le_sum (fun t _ => ht t)
    _ = ((Fintype.card e.Index : ℝ) * B₀) * W := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ B * W := mul_le_mul_of_nonneg_right (by dsimp only [B]; linarith) hW
    _ = _ := by dsimp only [W]; ring

end ContinuousFlexibility.Analysis
