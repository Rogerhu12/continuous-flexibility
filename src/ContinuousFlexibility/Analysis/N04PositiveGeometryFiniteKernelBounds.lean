module

public import ContinuousFlexibility.Analysis.N01cCompositionJetBounds
public import ContinuousFlexibility.Analysis.N01cStateAngleGraphBudget
public import ContinuousFlexibility.Analysis.SmoothDirectionsAffine

/-!
# Finite kernel composition with the original parameter height factor

Every block in the actual partition formula keeps its own parameter
arity and spatial cost. A block without a parameter direction carries
no height factor. Multiplying the blocks keeps one height factor
precisely when the original parameter arity is positive. The spatial
costs are added before any normalization to one high seminorm.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

/-- A finite product keeps the positive-parameter height gain. -/
theorem n04PositiveGeometry_parameterHeightProduct_le
    {ι : Type*} (s : Finset ι) (κ : ι → ℕ) {H L : ℝ}
    (hH : 0 ≤ H) (hHL : H ≤ L) (hL : 1 ≤ L) :
    (∏ i ∈ s, parameterHeightWeight H (κ i)) ≤
      L ^ s.card * parameterHeightWeight H (∑ i ∈ s, κ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty, Finset.card_empty, Finset.sum_empty, pow_zero,
        parameterHeightWeight, ite_true, mul_one, le_refl]
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
      calc
        _ ≤ parameterHeightWeight H (κ a) *
            (L ^ s.card * parameterHeightWeight H (∑ i ∈ s, κ i)) :=
          mul_le_mul_of_nonneg_left ih (parameterHeightWeight_nonneg hH _)
        _ = L ^ s.card * (parameterHeightWeight H (κ a) *
            parameterHeightWeight H (∑ i ∈ s, κ i)) := by ring
        _ ≤ L ^ s.card * (L * parameterHeightWeight H (κ a + ∑ i ∈ s, κ i)) :=
          mul_le_mul_of_nonneg_left
            (n01c_parameterHeightWeight_mul_le hH hHL hL _ _)
            (pow_nonneg (zero_le_one.trans hL) _)
        _ = _ := by rw [pow_succ]; ring

variable {X F G : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {U : Set X} {V : Set F} {f : X → F} {g : F → G}

/-- A genuine finite-dimensional kernel estimate. The numerical outer
envelope can depend on the component's material sample. The arity and
cost identities refer to the original slots, not to the number of
factors in an expanded product. -/
theorem n04PositiveGeometry_finiteKernel_weighted_bound
    (J : SmoothDirections U f) (hV : IsOpen V)
    (hg : ContDiffOn ℝ ∞ g V) (hmap : MapsTo f U V)
    (Q : SmoothDirections U (g ∘ f))
    (n k budget : ℕ) (x : X) (hx : x ∈ U) (v : Fin n → X)
    (κ cost : ∀ c : OrderedFinpartition n, Fin c.length → ℕ)
    (hκ : ∀ c, ∑ i, κ c i = k)
    (hcost : ∀ c, ∑ i, cost c i ≤ budget)
    {C M H L t : ℝ} (hC : 0 ≤ C) (hM : 1 ≤ M)
    (hH : 0 ≤ H) (hHL : H ≤ L) (hL : 1 ≤ L) (ht : 1 ≤ t)
    (houter : ∀ j, j ≤ n → ‖iteratedFDeriv ℝ j g (f x)‖ ≤ C)
    (hinner : ∀ c : OrderedFinpartition n, ∀ i : Fin c.length,
      ‖J.D (c.partSize i) x (v ∘ c.emb i)‖ ≤
        M * parameterHeightWeight H (κ c i) * t ^ cost c i) :
    ‖Q.D n x v‖ ≤ (Fintype.card (OrderedFinpartition n) : ℝ) *
      C * M ^ n * L ^ n * parameterHeightWeight H k * t ^ budget := by
  classical
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hprod (c : OrderedFinpartition n) :
      (∏ i : Fin c.length, ‖J.D (c.partSize i) x (v ∘ c.emb i)‖) ≤
        M ^ n * L ^ n * parameterHeightWeight H k * t ^ budget := by
    have hheight : (∏ i : Fin c.length, parameterHeightWeight H (κ c i)) ≤
        L ^ c.length * parameterHeightWeight H k := by
      simpa only [Finset.card_univ, Fintype.card_fin, hκ c] using
        n04PositiveGeometry_parameterHeightProduct_le Finset.univ (κ c) hH hHL hL
    have hMpow := pow_le_pow_right₀ hM c.length_le
    have hLpow := pow_le_pow_right₀ hL c.length_le
    have htpow := pow_le_pow_right₀ ht (hcost c)
    have hheight' := hheight.trans (mul_le_mul_of_nonneg_right hLpow
      (parameterHeightWeight_nonneg hH k))
    calc
      _ ≤ ∏ i : Fin c.length,
          M * parameterHeightWeight H (κ c i) * t ^ cost c i :=
        Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hinner c i)
      _ = M ^ c.length *
          (∏ i : Fin c.length, parameterHeightWeight H (κ c i)) *
            t ^ (∑ i, cost c i) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
          Finset.prod_pow_eq_pow_sum]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ M ^ n * (L ^ n * parameterHeightWeight H k) * t ^ budget :=
        mul_le_mul (mul_le_mul hMpow hheight'
          (Finset.prod_nonneg (fun _ _ => parameterHeightWeight_nonneg hH _))
          (pow_nonneg hM0 _)) htpow (pow_nonneg ht0 _)
          (mul_nonneg (pow_nonneg hM0 _)
            (mul_nonneg (pow_nonneg hL0 _) (parameterHeightWeight_nonneg hH _)))
      _ = _ := by ring
  let K := smoothDirections_contDiff_comp J hV hg hmap
  have heq : Q.D n x v = K.D n x v :=
    congrArg (fun A : X [×n]→L[ℝ] G => A v) (Q.unique K n x hx)
  calc
    _ = ‖K.D n x v‖ := congrArg norm heq
    _ ≤ C * ∑ c : OrderedFinpartition n,
        ∏ i : Fin c.length, ‖J.D (c.partSize i) x (v ∘ c.emb i)‖ :=
      smoothDirections_contDiff_comp_D_norm_le_of_outer_bound
        J hV hg hmap n x C houter v
    _ ≤ C * ∑ _c : OrderedFinpartition n,
        M ^ n * L ^ n * parameterHeightWeight H k * t ^ budget :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun c _ => hprod c)) hC
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end ContinuousFlexibility.Analysis
