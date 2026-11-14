module

public import ContinuousFlexibility.Analysis.N01cParameterCalculus
public import ContinuousFlexibility.Analysis.N01cCompositionJetBounds
public import ContinuousFlexibility.Analysis.N01cMaterialAbsorption
public import ContinuousFlexibility.Analysis.N01cSpatialParameterComposition

/-!
# Finite products of genuine parameter jets

Each factor is rescaled by its own positive bound before the actual
parameter composition theorem is applied. The outer product is then
evaluated on a fixed compact cube. Rescaling the output restores each
factor bound exactly once, preserving the separate assigned spatial orders
needed by the subsequent interpolation estimate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]


/-- The product tower is the genuine finite-dimensional product composition. -/
def smoothDirections_finiteProduct {m : ℕ} {U : Set X} {f : Fin m → X → ℝ}
    (hU : IsOpen U) (J : ∀ i, SmoothDirections U (f i)) :
    SmoothDirections U (fun x => ∏ i, f i x) := by
  have hP : ContDiff ℝ ∞ (fun y : Fin m → ℝ => ∏ i, y i) :=
    contDiff_prod (fun i _ => contDiff_apply ℝ ℝ i)
  exact smoothDirections_contDiff_comp
    (u := fun x i => f i x) (g := fun y : Fin m → ℝ => ∏ i, y i)
    (smoothDirections_scalarTuple hU J) isOpen_univ hP.contDiffOn (fun _ _ => mem_univ _)

/-- A genuine positive-order parameter jet of a finite product retains one
small weight. Every individual factor bound occurs only once. -/
theorem exists_finiteProduct_parameterJet_bound (m k : ℕ) (hk : 0 < k) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {U : Set X} {f : Fin m → X → ℝ},
      ∀ J : ∀ i, SmoothDirections U (f i),
      ∀ K : SmoothDirections U (fun x => ∏ i, f i x),
      ∀ x ∈ U, ∀ H : ℝ, 0 ≤ H → H ≤ R →
      ∀ B : Fin m → ℝ, (∀ i, 0 < B i) →
      (∀ i, ‖f i x‖ ≤ B i) →
      ∀ v : Fin k → X,
      (∀ i (c : OrderedFinpartition k) (j : Fin c.length),
        ‖(J i).D (c.partSize j) x (v ∘ c.emb j)‖ ≤ H * B i) →
      ‖K.D k x v‖ ≤ C * H * ∏ i, B i := by
  classical
  let P : (Fin m → ℝ) → ℝ := fun y => ∏ i, y i
  have hP : ContDiff ℝ ∞ P :=
    contDiff_prod (fun i _ => contDiff_apply ℝ ℝ i)
  let cube : Set (Fin m → ℝ) := Icc (fun _ => -1) (fun _ => 1)
  obtain ⟨C₀, hC₀, hb₀⟩ := compact_iteratedFDeriv_bound
    (K := cube) isCompact_Icc (fun _ _ => hP.contDiffAt) k
  let C : ℝ := C₀ * (max 1 R) ^ k * Fintype.card (OrderedFinpartition k)
  have hR : 0 ≤ max 1 R := zero_le_one.trans (le_max_left _ _)
  have hC : 0 ≤ C := mul_nonneg
    (mul_nonneg hC₀.le (pow_nonneg hR _)) (Nat.cast_nonneg _)
  refine ⟨C, hC, ?_⟩
  intro U f J K x hx H hH hHR B hB hbase v hjet
  let L : Fin m → ℝ →L[ℝ] ℝ := fun i => (B i)⁻¹ • ContinuousLinearMap.id ℝ ℝ
  let u : X → Fin m → ℝ := fun y i => L i (f i y)
  let Js : ∀ i, SmoothDirections U (fun y => u y i) :=
    fun i => smoothDirections_postcompCLM (J i) (L i)
  let JT := smoothDirections_scalarTuple K.open_domain Js
  let JP := smoothDirections_contDiff_comp JT isOpen_univ hP.contDiffOn
    (fun _ _ => mem_univ _)
  have hscaledValue (i : Fin m) : ‖u x i‖ ≤ 1 := by
    calc
      ‖u x i‖ = (B i)⁻¹ * ‖f i x‖ := by
        simp only [u, L, smul_apply, ContinuousLinearMap.id_apply,
          smul_eq_mul, norm_mul, Real.norm_of_nonneg (inv_pos.mpr (hB i)).le]
      _ ≤ (B i)⁻¹ * B i :=
        mul_le_mul_of_nonneg_left (hbase i) (inv_pos.mpr (hB i)).le
      _ = 1 := inv_mul_cancel₀ (hB i).ne'
  have hcube : u x ∈ cube :=
    ⟨fun i => (abs_le.mp (by simpa only [Real.norm_eq_abs] using hscaledValue i)).1,
      fun i => (abs_le.mp (by simpa only [Real.norm_eq_abs] using hscaledValue i)).2⟩
  have hscaledJet (i : Fin m) (c : OrderedFinpartition k) (j : Fin c.length) :
      ‖(Js i).D (c.partSize j) x (v ∘ c.emb j)‖ ≤ H := by
    calc
      _ = (B i)⁻¹ * ‖(J i).D (c.partSize j) x (v ∘ c.emb j)‖ := by
        rw [smoothDirections_postcompCLM_D_apply]
        simp only [L, smul_apply, ContinuousLinearMap.id_apply,
          smul_eq_mul, norm_mul, Real.norm_of_nonneg (inv_pos.mpr (hB i)).le]
      _ ≤ (B i)⁻¹ * (H * B i) :=
        mul_le_mul_of_nonneg_left (hjet i c j) (inv_pos.mpr (hB i)).le
      _ = H := by
        calc
          _ = ((B i)⁻¹ * B i) * H := by ring
          _ = H := by rw [inv_mul_cancel₀ (hB i).ne', one_mul]
  have htuple (c : OrderedFinpartition k) (j : Fin c.length) :
      ‖JT.D (c.partSize j) x (v ∘ c.emb j)‖ ≤ H := by
    apply (pi_norm_le_iff_of_nonneg hH).mpr
    intro i
    rw [smoothDirections_scalarTuple_D_apply]
    exact hscaledJet i c j
  have hpower (c : OrderedFinpartition k) :
      H ^ c.length ≤ (max 1 R) ^ k * H :=
    (nonempty_weight_power_le hH (hHR.trans (le_max_right _ _))
      (c.length_pos hk)).trans
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (le_max_left _ _)
          ((Nat.sub_le c.length 1).trans c.length_le)) hH)
  have hpart (c : OrderedFinpartition k) :
      (∏ j : Fin c.length, ‖JT.D (c.partSize j) x (v ∘ c.emb j)‖) ≤
        (max 1 R) ^ k * H := by
    calc
      _ ≤ ∏ _j : Fin c.length, H :=
        Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => htuple c j)
      _ = H ^ c.length := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ _ := hpower c
  have hproduct : ‖JP.D k x v‖ ≤ C * H := by
    calc
      _ ≤ C₀ * ∑ c : OrderedFinpartition k,
          ∏ j : Fin c.length, ‖JT.D (c.partSize j) x (v ∘ c.emb j)‖ :=
        smoothDirections_contDiff_comp_D_norm_le_of_outer_bound
          JT isOpen_univ hP.contDiffOn (fun _ _ => mem_univ _) k x C₀
          (fun n hn => hb₀ n hn (u x) hcube) v
      _ ≤ C₀ * ∑ _c : OrderedFinpartition k, (max 1 R) ^ k * H :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun c _ => hpart c)) hC₀.le
      _ = C * H := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        dsimp only [C]
        ring
  let Lout : ℝ →L[ℝ] ℝ := (∏ i, B i) • ContinuousLinearMap.id ℝ ℝ
  have hreconstruct (y : X) : Lout (P (u y)) = ∏ i, f i y := by
    simp only [Lout, P, u, L, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [← mul_assoc, mul_inv_cancel₀ (hB i).ne', one_mul]
  let Kback : SmoothDirections U (fun y => ∏ i, f i y) :=
    (smoothDirections_postcompCLM JP Lout).congr (fun y _ => hreconstruct y)
  have heq := HasProjectiveJetsOn.unique K.open_domain
    K.hasProjectiveJetsOn Kback.hasProjectiveJetsOn k x hx
  have heval : K.D k x v = Lout (JP.D k x v) :=
    (congrArg (fun A : X [×k]→L[ℝ] ℝ => A v) heq).trans
      (smoothDirections_postcompCLM_D_apply JP Lout k x v)
  have hBprod : 0 ≤ ∏ i, B i := Finset.prod_nonneg (fun i _ => (hB i).le)
  calc
    ‖K.D k x v‖ = (∏ i, B i) * ‖JP.D k x v‖ := by
      rw [heval]
      simp only [Lout, smul_apply, ContinuousLinearMap.id_apply,
        smul_eq_mul, norm_mul, Real.norm_of_nonneg hBprod]
    _ ≤ (∏ i, B i) * (C * H) := mul_le_mul_of_nonneg_left hproduct hBprod
    _ = C * H * ∏ i, B i := by ring

/-- The order-zero multilinear map is evaluation at the actual function. -/
theorem smoothDirections_D_zero_apply {U : Set X} {f : X → ℝ}
    (J : SmoothDirections U f) {x : X} (hx : x ∈ U) (v : Fin 0 → X) :
    J.D 0 x v = f x := by
  have hv : v = Fin.elim0 := funext (fun i => i.elim0)
  rw [hv]
  exact J.zero x hx

/-- The same product estimate includes order zero, where no small weight
is required. -/
theorem exists_finiteProduct_allParameterJet_bound (m k : ℕ) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {U : Set X} {f : Fin m → X → ℝ},
      ∀ J : ∀ i, SmoothDirections U (f i),
      ∀ K : SmoothDirections U (fun x => ∏ i, f i x),
      ∀ x ∈ U, ∀ H : ℝ, 0 ≤ H → H ≤ R →
      ∀ B : Fin m → ℝ, (∀ i, 0 < B i) →
      (∀ i, ‖f i x‖ ≤ B i) →
      ∀ v : Fin k → X,
      (∀ i (c : OrderedFinpartition k) (j : Fin c.length),
        ‖(J i).D (c.partSize j) x (v ∘ c.emb j)‖ ≤ H * B i) →
      ‖K.D k x v‖ ≤ C * (if k = 0 then 1 else H) * ∏ i, B i := by
  by_cases hk : k = 0
  · subst k
    refine ⟨1, zero_lt_one, ?_⟩
    intro U f J K x hx H hH hHR B hB hbase v hjet
    rw [smoothDirections_D_zero_apply K hx v, norm_prod]
    simpa only [ite_true, one_mul] using
      Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hbase i)
  · obtain ⟨C, hC, hb⟩ :=
      exists_finiteProduct_parameterJet_bound (X := X) m k (Nat.pos_of_ne_zero hk) R
    refine ⟨1 + C, by linarith, ?_⟩
    intro U f J K x hx H hH hHR B hB hbase v hjet
    have hprod : 0 ≤ ∏ i, B i := Finset.prod_nonneg (fun i _ => (hB i).le)
    simpa only [if_neg hk] using (hb J K x hx H hH hHR B hB hbase v hjet).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left zero_le_one) hH) hprod)

/-- Finite scalar linear combinations identify the actual parameter jet. -/
theorem smoothDirections_D_eq_linearCombination
    {ι : Type*} [Fintype ι] {U : Set X} {f : X → ℝ} {g : ι → X → ℝ}
    (J : SmoothDirections U f) (K : ∀ i, SmoothDirections U (g i))
    (c : ι → ℝ) (hformula : ∀ x ∈ U, f x = ∑ i, c i * g i x)
    (k : ℕ) {x : X} (hx : x ∈ U) (v : Fin k → X) :
    J.D k x v = ∑ i, c i * (K i).D k x v := by
  let L : ι → ℝ →L[ℝ] ℝ := fun i => c i • ContinuousLinearMap.id ℝ ℝ
  let Ks : ∀ i, SmoothDirections U (fun y => c i * g i y) :=
    fun i => (smoothDirections_postcompCLM (K i) (L i)).congr (fun y _ => by
      simp only [L, smul_apply, ContinuousLinearMap.id_apply,
        Function.comp_apply, smul_eq_mul])
  let Jsum := (smoothDirections_finiteSum J.open_domain Ks).congr
    (fun y hy => (hformula y hy).symm)
  have heq := HasProjectiveJetsOn.unique J.open_domain
    J.hasProjectiveJetsOn Jsum.hasProjectiveJetsOn k x hx
  calc
    J.D k x v = Jsum.D k x v := congrArg (fun A : X [×k]→L[ℝ] ℝ => A v) heq
    _ = ∑ i, (Ks i).D k x v := smoothDirections_finiteSum_D_apply J.open_domain Ks k x v
    _ = ∑ i, c i * (K i).D k x v := by
      apply Finset.sum_congr rfl
      intro i _
      exact (smoothDirections_postcompCLM_D_apply (K i) (L i) k x v).trans
        (by simp only [L, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul])

/-- Any genuine tower of a constant scalar function has zero positive jets. -/
theorem smoothDirections_D_constant {U : Set X} {c : ℝ}
    (J : SmoothDirections U (fun _ : X => c)) {k : ℕ} (hk : 0 < k)
    {x : X} (hx : x ∈ U) (v : Fin k → X) : J.D k x v = 0 := by
  let JL := (smoothDirectionsLinear (0 : X →L[ℝ] ℝ)).restrict
    J.open_domain (subset_univ _)
  let JC := smoothDirections_contDiff_comp (g := fun _ : ℝ => c)
    JL isOpen_univ contDiff_const.contDiffOn (fun _ _ => mem_univ _)
  have heq := HasProjectiveJetsOn.unique J.open_domain
    J.hasProjectiveJetsOn JC.hasProjectiveJetsOn k x hx
  calc
    J.D k x v = JC.D k x v := congrArg (fun A : X [×k]→L[ℝ] ℝ => A v) heq
    _ = ∑ b : OrderedFinpartition k,
        iteratedFDeriv ℝ b.length (fun _ : ℝ => c) (JL.D 0 x Fin.elim0)
          (fun i => JL.D (b.partSize i) x (v ∘ b.emb i)) := by
      rw [smoothDirections_contDiff_comp_D_apply]
      apply Finset.sum_congr rfl
      intro b _
      rw [smoothDirections_D_zero_apply JL hx]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      rw [iteratedFDeriv_const_of_ne (Nat.ne_of_gt (b.length_pos hk))]
      exact ContinuousMultilinearMap.zero_apply _


end ContinuousFlexibility.Analysis
