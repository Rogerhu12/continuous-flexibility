module

public import ContinuousFlexibility.Statements.RadialTargets
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Values, fluxes, and uniqueness in the matching system

The normalized state on the outer side is (-B o + A y, A o + B y).
The inner state is (x, Db x - h). A two-sided inverse of A Db - B
makes these states equal and determines both coefficient vectors.
No diagonal entry of A or B is divided by.
-/

@[expose] public section

namespace ContinuousFlexibility.Statements

open scoped BigOperators

/-- Matrix multiplication acts by composition on the boundary vectors. -/
theorem matchedBoundary_apply_product (A B : RadialMatrix)
    (v : Fin 2 → ℝ) (i : Fin 2) :
    radialMatrixApply (radialMatrixProduct A B) v i =
      radialMatrixApply A (radialMatrixApply B v) i := by
  simp only [radialMatrixApply, radialMatrixProduct, Fin.sum_univ_two]
  ring

@[simp] theorem matchedBoundary_apply_identity (v : Fin 2 → ℝ) (i : Fin 2) :
    radialMatrixApply radialMatrixIdentity v i = v i := by
  classical
  simp [radialMatrixApply, radialMatrixIdentity, ite_mul]

theorem matchedBoundary_apply_add (A B : RadialMatrix)
    (v : Fin 2 → ℝ) (i : Fin 2) :
    radialMatrixApply (fun a b => A a b + B a b) v i =
      radialMatrixApply A v i + radialMatrixApply B v i := by
  simp only [radialMatrixApply, add_mul, Finset.sum_add_distrib]

theorem matchedBoundary_apply_sub (A B : RadialMatrix)
    (v : Fin 2 → ℝ) (i : Fin 2) :
    radialMatrixApply (fun a b => A a b - B a b) v i =
      radialMatrixApply A v i - radialMatrixApply B v i := by
  simp only [radialMatrixApply, sub_mul, Finset.sum_sub_distrib]

theorem matchedBoundary_apply_diagonal (A : RadialMatrix)
    (hA : ∀ i j, i ≠ j → A i j = 0) (v : Fin 2 → ℝ) (i : Fin 2) :
    radialMatrixApply A v i = A i i * v i := by
  classical
  unfold radialMatrixApply
  refine Finset.sum_eq_single i ?_ ?_
  · intro j _ hji
    rw [hA i j hji.symm, zero_mul]
  · simp

/-- The same real orthogonal state transformation is its own inverse. -/
theorem matching_boundary_rotation_iff (a b x z o y : ℝ)
    (hnorm : a ^ 2 + b ^ 2 = 1) :
    (-b * o + a * y = x ∧ a * o + b * y = z) ↔
      (-b * x + a * z = o ∧ a * x + b * z = y) := by
  constructor
  · rintro ⟨hx, hz⟩
    constructor
    · calc
        -b * x + a * z = -b * (-b * o + a * y) + a * (a * o + b * y) := by
          rw [hx, hz]
        _ = (a ^ 2 + b ^ 2) * o := by ring
        _ = o := by rw [hnorm, one_mul]
    · calc
        a * x + b * z = a * (-b * o + a * y) + b * (a * o + b * y) := by
          rw [hx, hz]
        _ = (a ^ 2 + b ^ 2) * y := by ring
        _ = y := by rw [hnorm, one_mul]
  · rintro ⟨ho, hy⟩
    constructor
    · calc
        -b * o + a * y = -b * (-b * x + a * z) + a * (a * x + b * z) := by
          rw [ho, hy]
        _ = (a ^ 2 + b ^ 2) * x := by ring
        _ = x := by rw [hnorm, one_mul]
    · calc
        a * o + b * y = a * (-b * x + a * z) + b * (a * x + b * z) := by
          rw [ho, hy]
        _ = (a ^ 2 + b ^ 2) * z := by ring
        _ = z := by rw [hnorm, one_mul]

/-- Coordinate expansion of the matching matrix. -/
theorem matchedBoundary_system_apply (A B D : RadialMatrix)
    (hdiag : ∀ i j, i ≠ j → A i j = 0 ∧ B i j = 0)
    (x : Fin 2 → ℝ) (i : Fin 2) :
    radialMatrixApply (fun a b => radialMatrixProduct A D a b - B a b) x i =
      A i i * radialMatrixApply D x i - B i i * x i := by
  simp only [matchedBoundary_apply_sub, matchedBoundary_apply_product,
    matchedBoundary_apply_diagonal A (fun i j hij => (hdiag i j hij).1),
    matchedBoundary_apply_diagonal B (fun i j hij => (hdiag i j hij).2)]

/-- The coefficient along the outer natural line is A x + B z. -/
theorem matchedBoundary_outer_apply (A B D : RadialMatrix)
    (hdiag : ∀ i j, i ≠ j → A i j = 0 ∧ B i j = 0)
    (x h : Fin 2 → ℝ) (i : Fin 2) :
    radialMatrixApply (fun a b => A a b + radialMatrixProduct B D a b) x i -
        radialMatrixApply B h i =
      A i i * x i + B i i * (radialMatrixApply D x i - h i) := by
  simp only [matchedBoundary_apply_add, matchedBoundary_apply_product,
    matchedBoundary_apply_diagonal A (fun i j hij => (hdiag i j hij).1),
    matchedBoundary_apply_diagonal B (fun i j hij => (hdiag i j hij).2)]
  ring

/-- The coefficients in the inverse formula match values and fluxes exactly. -/
theorem matching_boundary_values_fluxes (A B D Kinv : RadialMatrix)
    (hdiag : ∀ i j, i ≠ j → A i j = 0 ∧ B i j = 0)
    (hnorm : ∀ i, A i i ^ 2 + B i i ^ 2 = 1)
    (hright : radialMatrixProduct
      (fun a b => radialMatrixProduct A D a b - B a b) Kinv = radialMatrixIdentity)
    (h o : Fin 2 → ℝ) :
    let x := radialMatrixApply Kinv (fun i => o i + radialMatrixApply A h i)
    let z := fun i => radialMatrixApply D x i - h i
    let y := fun i => radialMatrixApply
      (fun a b => A a b + radialMatrixProduct B D a b) x i - radialMatrixApply B h i
    ∀ i, -B i i * o i + A i i * y i = x i ∧
      A i i * o i + B i i * y i = z i := by
  let x := radialMatrixApply Kinv (fun i => o i + radialMatrixApply A h i)
  let z := fun i => radialMatrixApply D x i - h i
  let y := fun i => radialMatrixApply
    (fun a b => A a b + radialMatrixProduct B D a b) x i - radialMatrixApply B h i
  change ∀ i, -B i i * o i + A i i * y i = x i ∧
    A i i * o i + B i i * y i = z i
  intro i
  have hsolve :
      radialMatrixApply (fun a b => radialMatrixProduct A D a b - B a b) x i =
        o i + radialMatrixApply A h i := by
    dsimp only [x]
    rw [← matchedBoundary_apply_product, hright, matchedBoundary_apply_identity]
  rw [matchedBoundary_system_apply A B D hdiag,
    matchedBoundary_apply_diagonal A (fun i j hij => (hdiag i j hij).1)] at hsolve
  have hnormal : -B i i * x i + A i i * z i = o i := by
    dsimp only [z]
    linarith only [hsolve]
  have halong : A i i * x i + B i i * z i = y i :=
    (matchedBoundary_outer_apply A B D hdiag x h i).symm
  exact (matching_boundary_rotation_iff (A i i) (B i i) (x i) (z i)
    (o i) (y i) (hnorm i)).mpr ⟨hnormal, halong⟩

/-- Any coefficient pair with matching states has the displayed unique values. -/
theorem matching_boundary_coefficients_unique (A B D Kinv : RadialMatrix)
    (hdiag : ∀ i j, i ≠ j → A i j = 0 ∧ B i j = 0)
    (hnorm : ∀ i, A i i ^ 2 + B i i ^ 2 = 1)
    (hleft : radialMatrixProduct Kinv
      (fun a b => radialMatrixProduct A D a b - B a b) = radialMatrixIdentity)
    (h o x y : Fin 2 → ℝ)
    (hmatch : ∀ i, -B i i * o i + A i i * y i = x i ∧
      A i i * o i + B i i * y i = radialMatrixApply D x i - h i) :
    x = radialMatrixApply Kinv (fun i => o i + radialMatrixApply A h i) ∧
      y = fun i => radialMatrixApply
        (fun a b => A a b + radialMatrixProduct B D a b) x i - radialMatrixApply B h i := by
  have hrot (i : Fin 2) :
      (-B i i * x i + A i i * (radialMatrixApply D x i - h i) = o i) ∧
        (A i i * x i + B i i * (radialMatrixApply D x i - h i) = y i) :=
    (matching_boundary_rotation_iff (A i i) (B i i) (x i)
      (radialMatrixApply D x i - h i) (o i) (y i) (hnorm i)).mp (hmatch i)
  have hsystem : radialMatrixApply
      (fun a b => radialMatrixProduct A D a b - B a b) x =
        fun i => o i + radialMatrixApply A h i := by
    funext i
    rw [matchedBoundary_system_apply A B D hdiag,
      matchedBoundary_apply_diagonal A (fun i j hij => (hdiag i j hij).1)]
    linarith only [(hrot i).1]
  constructor
  · calc
      x = radialMatrixApply radialMatrixIdentity x :=
        funext fun i => (matchedBoundary_apply_identity x i).symm
      _ = radialMatrixApply (radialMatrixProduct Kinv
          (fun a b => radialMatrixProduct A D a b - B a b)) x := by rw [hleft]
      _ = radialMatrixApply Kinv (radialMatrixApply
          (fun a b => radialMatrixProduct A D a b - B a b) x) :=
        funext fun i => matchedBoundary_apply_product _ _ x i
      _ = radialMatrixApply Kinv (fun i => o i + radialMatrixApply A h i) := by
        rw [hsystem]
  · funext i
    exact (hrot i).2.symm.trans (matchedBoundary_outer_apply A B D hdiag x h i).symm

end ContinuousFlexibility.Statements
