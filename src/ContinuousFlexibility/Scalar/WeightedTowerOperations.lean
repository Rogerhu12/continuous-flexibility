import ContinuousFlexibility.Scalar.WeightedBilinearTower

/-!
# Elementary uniform-tower operations for scalar state expressions

Pairing, constants, and scalar multiplication retain actual continuous
multilinear derivatives.  Their fixed orders are independent of derivative
order and are valid on the specified original open domain.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

section Pairing

variable {E F G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]
  {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}
  {U : Set E} {f : E → F} {g : E → G}
  {b c ell m : ℕ}

def smoothDirectionsUniformProd
    (J : SmoothDirections U f) (K : SmoothDirections U g) :
    SmoothDirections U (fun x => (f x, g x)) where
  open_domain := J.open_domain
  D := fun k x => (J.D k x).prod (K.D k x)
  zero := fun x hx => by
    rw [ContinuousMultilinearMap.prod_apply, J.zero x hx, K.zero x hx]
  continuous := fun k => by
    simpa only [ContinuousMultilinearMap.prod_apply] using (J.continuous k).prodMk (K.continuous k)
  derivative := fun k x hx v w => by
    have hJ := J.derivative k x hx v w
    have hK := K.derivative k x hx v w
    unfold HasProjectiveLineDerivAt HasProjectiveCurveDerivAt at hJ hK ⊢
    simpa only [ContinuousMultilinearMap.prod_apply, Prod.smul_mk, Prod.mk_sub_mk] using
      hJ.prodMk_nhds hK

theorem UniformScalarTowerEstimate.prodMk
    {J : SmoothDirections U f} {K : SmoothDirections U g}
    (hJ : UniformScalarTowerEstimate p q U b ell f J)
    (hK : UniformScalarTowerEstimate p r U c m g K) (hp : Monotone p) :
    UniformScalarTowerEstimate p (pairGrading q r) U (max b c) (max ell m)
      (fun x => (f x, g x)) (smoothDirectionsUniformProd J K) := by
  have hj := hJ.weaken hp (le_max_left b c) (le_max_left ell m)
  have hk := hK.weaken hp (le_max_right b c) (le_max_right ell m)
  intro k s hs
  obtain ⟨C, hC, hCx⟩ := hj k s hs
  obtain ⟨D, hD, hDx⟩ := hk k s hs
  refine ⟨C + D, add_nonneg hC hD, ?_⟩
  intro x hx v
  change pairGrading q r s ((J.D k x).prod (K.D k x) v) ≤ _
  rw [ContinuousMultilinearMap.prod_apply, tamePairGrading_apply]
  exact (add_le_add (hCx x hx v) (hDx x hx v)).trans_eq (by ring)

theorem FixedNeighborhoodSmoothTame.prodMk
    (hf : FixedNeighborhoodSmoothTame p q U b ell f)
    (hg : FixedNeighborhoodSmoothTame p r U c m g) (hp : Monotone p) :
    FixedNeighborhoodSmoothTame p (pairGrading q r) U (max b c) (max ell m)
      (fun x => (f x, g x)) := by
  obtain ⟨J, hJ⟩ := hf.2
  obtain ⟨K, hK⟩ := hg.2
  exact fixedNeighborhoodSmoothTame_of_uniform (smoothDirectionsUniformProd J K) (hJ.prodMk hK hp)

end Pairing

section Constant

variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F} {U : Set E}
  {base loss : ℕ}

def scalarConstantJets (a : F) : ProjectiveJetFamily E F
  | 0, _ => ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) a
  | _ + 1, _ => 0

def smoothDirectionsUniformConst (a : F) (hU : IsOpen U) :
    SmoothDirections U (fun _ : E => a) where
  open_domain := hU
  D := scalarConstantJets a
  zero := fun _ _ => rfl
  continuous := fun k => by cases k <;> exact continuousOn_const
  derivative := fun k x _ v w => by
    cases k with
    | zero => exact hasProjectiveLineDerivAt_const a x w
    | succ k => exact hasProjectiveLineDerivAt_const (0 : F) x w

theorem uniformScalarTowerEstimate_const (a : F) (hU : IsOpen U) :
    UniformScalarTowerEstimate p q U base loss (fun _ : E => a)
      (smoothDirectionsUniformConst a hU) := by
  intro k s _
  refine ⟨q s a, apply_nonneg _ _, ?_⟩
  intro x _ v
  cases k with
  | zero =>
      change q s a ≤ q s a * tameJetSize p 0 s loss base x v
      rw [tameJetSize_zero]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (apply_nonneg (p (s + loss)) x)) (apply_nonneg (q s) a)
  | succ k =>
      change q s 0 ≤ q s a * tameJetSize p (k + 1) s loss base x v
      rw [map_zero]
      exact mul_nonneg (apply_nonneg _ _) (tameJetSize_nonneg _ _ _ _ _ _ _)

theorem fixedNeighborhoodSmoothTame_const (a : F) (hU : IsOpen U) :
    FixedNeighborhoodSmoothTame p q U base loss (fun _ : E => a) :=
  fixedNeighborhoodSmoothTame_of_uniform (smoothDirectionsUniformConst a hU)
    (uniformScalarTowerEstimate_const a hU)

theorem FixedNeighborhoodSmoothTame.congr {f g : E → F}
    (hf : FixedNeighborhoodSmoothTame p q U base loss f)
    (hfg : ∀ x ∈ U, f x = g x) :
    FixedNeighborhoodSmoothTame p q U base loss g := by
  obtain ⟨J, hJ⟩ := hf.2
  exact fixedNeighborhoodSmoothTame_of_uniform (J.congr hfg) hJ

end Constant

section ScalarMultiplication

variable {F : Type*} [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

/-- The scalar-module multiplication used for the independent real state
parameters, represented by a genuine continuous bilinear map. -/
def scalarSMulPairMultilinear : (ℝ × F) [×2]→L[ℝ] F where
  toFun v := (v 0).1 • (v 1).2
  map_update_add' := by
    intro _ v i x y
    fin_cases i <;> simp [add_smul, smul_add]
  map_update_smul' := by
    intro _ v i c x
    fin_cases i <;> simp [smul_smul, mul_comm]
  cont := ((continuous_apply 0).fst).smul ((continuous_apply 1).snd)

theorem scalarSMulPairMultilinear_apply (x y : ℝ × F) :
    bilinearJetValue (scalarSMulPairMultilinear (F := F)) x y = x.1 • y.2 := rfl

/-- Scalar multiplication has a zero-loss uniform actual tower on every
open set with bounded order-zero pair seminorm. -/
theorem fixedNeighborhoodSmoothTame_scalarSMul
    (q : ℕ → Seminorm ℝ F) {U : Set (ℝ × F)} (hU : IsOpen U)
    {R : ℝ} (hR : 0 ≤ R)
    (hxR : ∀ x ∈ U, pairGrading realGrading q 0 x ≤ R) :
    FixedNeighborhoodSmoothTame (pairGrading realGrading q) q U 0 0
      (fun x : ℝ × F => x.1 • x.2) := by
  have hB : ∀ s, 0 ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ × F,
      q s (bilinearJetValue (scalarSMulPairMultilinear (F := F)) x y) ≤
        C * (pairGrading realGrading q (s + 0) x * pairGrading realGrading q 0 y +
          pairGrading realGrading q 0 x * pairGrading realGrading q (s + 0) y) := by
    intro s _
    refine ⟨1, zero_le_one, fun x y => ?_⟩
    rw [scalarSMulPairMultilinear_apply, map_smul_eq_mul]
    simp only [one_mul, Nat.add_zero]
    have hx : ‖x.1‖ ≤ pairGrading realGrading q 0 x := by
      change ‖x.1‖ ≤ ‖x.1‖ + q 0 x.2
      exact le_add_of_nonneg_right (apply_nonneg _ _)
    have hy : q s y.2 ≤ pairGrading realGrading q s y := by
      change q s y.2 ≤ ‖y.1‖ + q s y.2
      exact le_add_of_nonneg_left (norm_nonneg _)
    exact (mul_le_mul hx hy (apply_nonneg _ _) (apply_nonneg _ _)).trans
      (le_add_of_nonneg_left (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)))
  exact fixedNeighborhoodSmoothTame_quadratic
    (scalarSMulPairMultilinear (F := F)) hB hU hR hxR

end ScalarMultiplication

end ContinuousFlexibility.Statements
