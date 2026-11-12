import ContinuousFlexibility.Analysis.TameElementaryCalculus

/-!
# Exact parameter jets of products of scalar linear functionals

The product is the diagonal of a genuine continuous bilinear map.
Its verified quadratic jet family therefore gives the first and second
directional derivatives and vanishing at every higher order. Uniqueness
identifies these formulas with any already constructed smooth directional
tower for the same actual function on its open domain.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

/-- The continuous bilinear map whose diagonal is the scalar product. -/
def scalarLinearProductBilinear (L M : E →L[ℝ] ℝ) : E [×2]→L[ℝ] ℝ where
  toFun v := L (v 0) * M (v 1)
  map_update_add' := by
    intro _ v i x y
    fin_cases i <;> simp [map_add, add_mul, mul_add]
  map_update_smul' := by
    intro _ v i c x
    fin_cases i <;> simp [map_smul, smul_eq_mul, mul_assoc, mul_left_comm]
  cont := (L.continuous.comp (continuous_apply 0)).mul
    (M.continuous.comp (continuous_apply 1))

theorem scalarLinearProductBilinear_apply (L M : E →L[ℝ] ℝ) (v : Fin 2 → E) :
    scalarLinearProductBilinear L M v = L (v 0) * M (v 1) := rfl

theorem scalarLinearProductBilinear_value (L M : E →L[ℝ] ℝ) (x y : E) :
    bilinearJetValue (scalarLinearProductBilinear L M) x y = L x * M y := by
  simp only [bilinearJetValue, scalarLinearProductBilinear_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]

/-- An actual smooth tower for the quadratic scalar product. -/
def smoothDirections_linearProduct (L M : E →L[ℝ] ℝ) :
    SmoothDirections univ (fun x => L x * M x) :=
  (smoothDirectionsOfJets isOpen_univ (quadraticJets (scalarLinearProductBilinear L M))
    (hasProjectiveJetsOn_quadratic (scalarLinearProductBilinear L M) univ)).congr
      (fun x _ => scalarLinearProductBilinear_value L M x x)

theorem smoothDirections_linearProduct_D_zero (L M : E →L[ℝ] ℝ)
    (x : E) (v : Fin 0 → E) :
    (smoothDirections_linearProduct L M).D 0 x v = L x * M x := by
  change quadraticJets (scalarLinearProductBilinear L M) 0 x v = _
  simp only [quadraticJets, ContinuousMultilinearMap.constOfIsEmpty_apply,
    quadraticJetValue, scalarLinearProductBilinear_value]

theorem smoothDirections_linearProduct_D_one (L M : E →L[ℝ] ℝ)
    (x : E) (v : Fin 1 → E) :
    (smoothDirections_linearProduct L M).D 1 x v =
      L (v 0) * M x + L x * M (v 0) := by
  change quadraticJets (scalarLinearProductBilinear L M) 1 x v = _
  simp only [quadraticJets, ContinuousMultilinearMap.ofSubsingleton_apply_apply,
    quadraticJetFirst_apply, scalarLinearProductBilinear_value]

theorem smoothDirections_linearProduct_D_two (L M : E →L[ℝ] ℝ)
    (x : E) (v : Fin 2 → E) :
    (smoothDirections_linearProduct L M).D 2 x v =
      L (v 0) * M (v 1) + L (v 1) * M (v 0) := by
  change quadraticJets (scalarLinearProductBilinear L M) 2 x v = _
  simp only [quadraticJets, quadraticJetSecond_apply, scalarLinearProductBilinear_value]

theorem smoothDirections_linearProduct_D_ge_three (L M : E →L[ℝ] ℝ)
    (n : ℕ) (x : E) (v : Fin (n + 3) → E) :
    (smoothDirections_linearProduct L M).D (n + 3) x v = 0 := by
  change quadraticJets (scalarLinearProductBilinear L M) (n + 3) x v = 0
  simp only [quadraticJets_order_ge_three, zero_apply]

section Uniqueness

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
variable {U : Set E} {f : E → ℝ}

/-- These are the derivatives of any genuine tower for the same scalar
product, including a tower obtained by finite-dimensional composition. -/
theorem scalarLinearProduct_D_eq (L M : E →L[ℝ] ℝ)
    (J : SmoothDirections U f) (hformula : ∀ x ∈ U, f x = L x * M x)
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    J.D n x v = (smoothDirections_linearProduct L M).D n x v := by
  let K := smoothDirections_linearProduct L M
  have hK : HasProjectiveJetsOn (fun x => L x * M x) K.D U := by
    refine ⟨fun y _ => K.zero y (mem_univ _), ?_, ?_⟩
    · intro k
      exact (K.continuous k).mono (fun q _ => ⟨mem_univ q.1, mem_univ q.2⟩)
    · intro k y _ w vs
      exact K.derivative k y (mem_univ _) vs w
  have he := HasProjectiveJetsOn.unique J.open_domain
    (J.congr hformula).hasProjectiveJetsOn hK n x hx
  exact congrArg (fun A : E [×n]→L[ℝ] ℝ => A v) he

theorem scalarLinearProduct_D_zero (L M : E →L[ℝ] ℝ)
    (J : SmoothDirections U f) (hformula : ∀ x ∈ U, f x = L x * M x)
    (x : E) (hx : x ∈ U) (v : Fin 0 → E) :
    J.D 0 x v = L x * M x :=
  (scalarLinearProduct_D_eq L M J hformula 0 x hx v).trans
    (smoothDirections_linearProduct_D_zero L M x v)

theorem scalarLinearProduct_D_one (L M : E →L[ℝ] ℝ)
    (J : SmoothDirections U f) (hformula : ∀ x ∈ U, f x = L x * M x)
    (x : E) (hx : x ∈ U) (v : Fin 1 → E) :
    J.D 1 x v = L (v 0) * M x + L x * M (v 0) :=
  (scalarLinearProduct_D_eq L M J hformula 1 x hx v).trans
    (smoothDirections_linearProduct_D_one L M x v)

theorem scalarLinearProduct_D_two (L M : E →L[ℝ] ℝ)
    (J : SmoothDirections U f) (hformula : ∀ x ∈ U, f x = L x * M x)
    (x : E) (hx : x ∈ U) (v : Fin 2 → E) :
    J.D 2 x v = L (v 0) * M (v 1) + L (v 1) * M (v 0) :=
  (scalarLinearProduct_D_eq L M J hformula 2 x hx v).trans
    (smoothDirections_linearProduct_D_two L M x v)

theorem scalarLinearProduct_D_ge_three (L M : E →L[ℝ] ℝ)
    (J : SmoothDirections U f) (hformula : ∀ x ∈ U, f x = L x * M x)
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin (n + 3) → E) :
    J.D (n + 3) x v = 0 :=
  (scalarLinearProduct_D_eq L M J hformula (n + 3) x hx v).trans
    (smoothDirections_linearProduct_D_ge_three L M n x v)

end Uniqueness

end ContinuousFlexibility.Analysis
