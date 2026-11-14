module

public import ContinuousFlexibility.Analysis.N01cMixedPowerBounds

/-!
# Weighted finite products for the physical Lie expansion

Every radial endpoint power is attached to its own factor before the
genuine parameter product theorem is applied. The separate spatial
powers add exactly; only the finite material-envelope powers are enlarged.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- Constant nonnegative factor weights commute with all actual parameter
jets, including order zero. No individual product is normalized here. -/
theorem exists_n01c_scaled_finiteProduct_parameterJet_bound (m k : ℕ) (RH : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {U : Set X} {f : Fin m → X → ℝ},
      ∀ J : ∀ i, SmoothDirections U (f i),
      ∀ K : SmoothDirections U (fun x => ∏ i, f i x),
      ∀ x ∈ U, ∀ H : ℝ, 0 ≤ H → H ≤ RH →
      ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) →
      ∀ B : Fin m → ℝ, (∀ i, 0 < B i) →
      (∀ i, c i * ‖f i x‖ ≤ B i) →
      ∀ v : Fin k → X,
      (∀ i (d : OrderedFinpartition k) (j : Fin d.length),
        c i * ‖(J i).D (d.partSize j) x (v ∘ d.emb j)‖ ≤ H * B i) →
      (∏ i, c i) * ‖K.D k x v‖ ≤ C * parameterHeightWeight H k * ∏ i, B i := by
  obtain ⟨C, hC, hb⟩ := exists_finiteProduct_allParameterJet_bound (X := X) m k RH
  refine ⟨C, hC, ?_⟩
  intro U f J K x hx H hH hHR c hc B hB hbase v hjet
  let L : Fin m → ℝ →L[ℝ] ℝ := fun i => c i • ContinuousLinearMap.id ℝ ℝ
  let fs : Fin m → X → ℝ := fun i y => c i * f i y
  let Js : ∀ i, SmoothDirections U (fs i) :=
    fun i => smoothDirections_postcompCLM (J i) (L i)
  have hcp : 0 ≤ ∏ i, c i := Finset.prod_nonneg (fun i _ => hc i)
  let Lout : ℝ →L[ℝ] ℝ := (∏ i, c i) • ContinuousLinearMap.id ℝ ℝ
  let Ks : SmoothDirections U (fun y => ∏ i, fs i y) :=
    (smoothDirections_postcompCLM K Lout).congr (fun y _ => by
      simp only [Function.comp_apply, Lout, smul_apply, ContinuousLinearMap.id_apply,
        smul_eq_mul, fs, Finset.prod_mul_distrib])
  have hvalue (i : Fin m) : ‖fs i x‖ ≤ B i := by
    simpa only [fs, norm_mul, Real.norm_of_nonneg (hc i)] using hbase i
  have hderiv (i : Fin m) (d : OrderedFinpartition k) (j : Fin d.length) :
      ‖(Js i).D (d.partSize j) x (v ∘ d.emb j)‖ ≤ H * B i := by
    simpa only [Js, smoothDirections_postcompCLM_D_apply, L, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, norm_mul,
      Real.norm_of_nonneg (hc i)] using hjet i d j
  have hKs : ‖Ks.D k x v‖ = (∏ i, c i) * ‖K.D k x v‖ := by
    change ‖(smoothDirections_postcompCLM K Lout).D k x v‖ = _
    simp only [smoothDirections_postcompCLM_D_apply, Lout, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, norm_mul, Real.norm_of_nonneg hcp]
  simpa only [hKs, parameterHeightWeight] using
    hb Js Ks x hx H hH hHR B hB hvalue v hderiv

/-- Spatial interpolation exponents add according to the original
distribution of coordinate orders. -/
theorem n01c_finset_prod_spatialOrder {ι : Type*} (t : Finset ι)
    (orders : ι → ℕ) {R : ℝ} (hR : 0 < R) (s : ℕ) :
    (∏ i ∈ t, R ^ ((orders i : ℝ) / ((s : ℝ) + 1))) =
      R ^ (((∑ i ∈ t, orders i : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty, Nat.cast_zero, zero_div, Real.rpow_zero]
  | @insert i t hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih,
        rpow_spatialOrder_mul hR]

/-- Only the material envelope uses the upper bound on the number of
factors. The spatial exponent remains the exact sum of their orders. -/
theorem n01c_finiteProduct_spatialEnvelope {m L : ℕ} (hm : m ≤ L)
    (orders : Fin m → ℕ) (s : ℕ) {C E A R : ℝ}
    (hC : 1 ≤ C) (hE : 1 ≤ E) (hA : 0 ≤ A) (hR : 1 ≤ R) :
    (∏ i, C * E ^ A * R ^ ((orders i : ℝ) / ((s : ℝ) + 1))) ≤
      C ^ L * E ^ (A * (L : ℝ)) *
        R ^ (((∑ i, orders i : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
  have hE0 : 0 ≤ E := zero_le_one.trans hE
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hCE : 1 ≤ C * E ^ A :=
    hC.trans (le_mul_of_one_le_right (zero_le_one.trans hC) (Real.one_le_rpow hE hA))
  calc
    _ = (C * E ^ A) ^ m *
        R ^ (((∑ i, orders i : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
      rw [Finset.prod_mul_distrib, n01c_finset_prod_spatialOrder _ orders hR0 s]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ (C * E ^ A) ^ L *
        R ^ (((∑ i, orders i : ℕ) : ℝ) / ((s : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hCE hm) (Real.rpow_nonneg hR0.le _)
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast hE0 A L]

/-- The unused endpoint exponent is bounded by the fixed physical width. -/
theorem n01c_endpoint_power_raise {δ width v : ℝ} {d a : ℕ}
    (hδ : 0 ≤ δ) (hwidth : δ ≤ width) (hv : 0 ≤ v) (hd : d ≤ a) :
    δ ^ a * v ≤ (max 1 width) ^ a * (δ ^ d * v) := by
  have hscale : δ ^ a = δ ^ (a - d) * δ ^ d := by
    rw [← pow_add, Nat.sub_add_cancel hd]
  have hpow : δ ^ (a - d) ≤ (max 1 width) ^ a :=
    (pow_le_pow_left₀ hδ (hwidth.trans (le_max_right _ _)) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) (Nat.sub_le a d))
  calc
    _ = δ ^ (a - d) * (δ ^ d * v) := by rw [hscale, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right hpow (mul_nonneg (pow_nonneg hδ _) hv)

end ContinuousFlexibility.Analysis
