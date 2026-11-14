module

public import ContinuousFlexibility.Analysis.N01cStateAngleGraphBudget
public import ContinuousFlexibility.Analysis.N01cPhysicalLieProducts

/-!
# A complete state-flow graph word estimate

This is the numerical estimate for one actual outer word in the genuine
ordered-partition chain formula. It multiplies the raw distributed powers
before any one-high normalization. The complete word retains one height
factor whenever the original state order is positive.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped BigOperators

theorem n01c_stateAngleGraph_term_bound
    {Y : Type*} {N : ℕ} (w : StateAngleWord N)
    (κ β : Fin N → ℕ) (offset n s : ℕ)
    (hpart : ∀ i, 0 < κ i + β i) (hκ : 0 < ∑ i, κ i)
    {C₀ C₁ E A₀ A₁ R H L δ outer : ℝ} (v : Fin N → Y × ℝ)
    (hC₀ : 0 ≤ C₀) (hC₁ : 1 ≤ C₁) (hE : 1 ≤ E)
    (hA₁ : 0 ≤ A₁) (hR : 1 ≤ R)
    (hH : 0 ≤ H) (hHL : H ≤ L) (hL : 1 ≤ L)
    (houter : δ * |outer| ≤
      C₀ * E ^ A₀ * parameterHeightWeight H w.stateArity *
        R ^ (((n + w.angleArity : ℕ) : ℝ) / ((s : ℝ) + 1)))
    (hfactor : ∀ i,
      |(v i).2| ≤ C₁ * E ^ A₁ * parameterHeightWeight H (κ i) *
        R ^ (((if κ i = 0 then β i - 1 else β i + offset : ℕ) : ℝ) /
          ((s : ℝ) + 1))) :
    δ * |outer * w.angleFactor v| ≤
      (C₀ * C₁ ^ N * L ^ N) * E ^ (A₀ + A₁ * (N : ℝ)) * H *
        R ^ (((n + (∑ i, β i) + (offset + 1) * ∑ i, κ i : ℕ) : ℝ) /
          ((s : ℝ) + 1)) := by
  let Q : ℝ := C₁ * E ^ A₁
  let orders : Fin N → ℕ := fun i => if κ i = 0 then β i - 1 else β i + offset
  let PH : ℝ := w.selectedProduct (fun i => parameterHeightWeight H (κ i))
  have hEp : 0 < E := zero_lt_one.trans_le hE
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hQ : 1 ≤ Q :=
    hC₁.trans (le_mul_of_one_le_right (zero_le_one.trans hC₁)
      (Real.one_le_rpow hE hA₁))
  have hPH : 0 ≤ PH := w.selectedProduct_nonneg
    (fun i => parameterHeightWeight_nonneg hH (κ i))
  have hprod : |w.angleFactor v| ≤
      (Q ^ w.angleArity * PH) *
        R ^ (((w.selectedSum orders : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
    rw [w.abs_angleFactor]
    have hh := w.selectedProduct_mono (fun i => abs_nonneg ((v i).2)) hfactor
    simpa only [StateAngleWord.selectedProduct_mul, StateAngleWord.selectedProduct_const,
      StateAngleWord.selectedProduct_spatialPower _ _ hRp s, Q, PH, orders, mul_pow] using hh
  have hheight : parameterHeightWeight H w.stateArity * PH ≤ L ^ N * H := by
    have hh := w.selected_heightProduct_le κ hH hHL hL 0
    have hk := w.flowParameterOrder_pos κ hκ
    simpa only [Nat.zero_add, parameterHeightWeight,
      if_neg (Nat.ne_of_gt hk), PH] using hh
  have hcount : w.angleArity ≤ N := by
    have hh := w.arity_sum
    omega
  have hconst : C₀ * E ^ A₀ * Q ^ w.angleArity ≤ C₀ * E ^ A₀ * Q ^ N :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hQ hcount)
      (mul_nonneg hC₀ (Real.rpow_nonneg hEp.le _))
  have horder := w.flowSpatialOrder_le κ β offset hpart
  have hRmono :
      R ^ (((n + w.flowSpatialOrder κ β offset : ℕ) : ℝ) / ((s : ℝ) + 1)) ≤
        R ^ (((n + (∑ i, β i) + (offset + 1) * ∑ i, κ i : ℕ) : ℝ) /
          ((s : ℝ) + 1)) := by
    apply Real.rpow_le_rpow_of_exponent_le hR
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast (show n + w.flowSpatialOrder κ β offset ≤
      n + (∑ i, β i) + (offset + 1) * ∑ i, κ i by omega)
  have hRsplit :
      R ^ (((n + w.flowSpatialOrder κ β offset : ℕ) : ℝ) / ((s : ℝ) + 1)) =
        R ^ (((n + w.angleArity : ℕ) : ℝ) / ((s : ℝ) + 1)) *
          R ^ (((w.selectedSum orders : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
    have he : n + w.flowSpatialOrder κ β offset =
        (n + w.angleArity) + w.selectedSum orders := by
      simp only [StateAngleWord.flowSpatialOrder, orders, Nat.add_assoc]
    rw [he, ← rpow_spatialOrder_mul hRp]
  have houterNonneg : 0 ≤
      C₀ * E ^ A₀ * parameterHeightWeight H w.stateArity *
        R ^ (((n + w.angleArity : ℕ) : ℝ) / ((s : ℝ) + 1)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC₀ (Real.rpow_nonneg hEp.le _))
      (parameterHeightWeight_nonneg hH _)) (Real.rpow_nonneg hRp.le _)
  have hCN : 0 ≤ C₀ * E ^ A₀ * Q ^ N :=
    mul_nonneg (mul_nonneg hC₀ (Real.rpow_nonneg hEp.le _))
      (pow_nonneg (zero_le_one.trans hQ) _)
  calc
    _ = (δ * |outer|) * |w.angleFactor v| := by rw [abs_mul]; ring
    _ ≤ (C₀ * E ^ A₀ * parameterHeightWeight H w.stateArity *
          R ^ (((n + w.angleArity : ℕ) : ℝ) / ((s : ℝ) + 1))) *
        ((Q ^ w.angleArity * PH) *
          R ^ (((w.selectedSum orders : ℕ) : ℝ) / ((s : ℝ) + 1))) :=
      mul_le_mul houter hprod (abs_nonneg _) houterNonneg
    _ = (C₀ * E ^ A₀ * Q ^ w.angleArity) *
        (parameterHeightWeight H w.stateArity * PH) *
          R ^ (((n + w.flowSpatialOrder κ β offset : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
      rw [hRsplit]
      ring
    _ ≤ (C₀ * E ^ A₀ * Q ^ N) * (L ^ N * H) *
          R ^ (((n + w.flowSpatialOrder κ β offset : ℕ) : ℝ) / ((s : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hconst hheight
          (mul_nonneg (parameterHeightWeight_nonneg hH _) hPH) hCN)
        (Real.rpow_nonneg hRp.le _)
    _ ≤ (C₀ * E ^ A₀ * Q ^ N) * (L ^ N * H) *
          R ^ (((n + (∑ i, β i) + (offset + 1) * ∑ i, κ i : ℕ) : ℝ) /
            ((s : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hRmono
        (mul_nonneg hCN (mul_nonneg (pow_nonneg (zero_le_one.trans hL) _) hH))
    _ = _ := by
      dsimp only [Q]
      rw [mul_pow, ← Real.rpow_mul_natCast hEp.le A₁ N,
        Real.rpow_add hEp]
      ring

end ContinuousFlexibility.Analysis
