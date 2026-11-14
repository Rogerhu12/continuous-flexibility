module

public import ContinuousFlexibility.Analysis.CircleJetAssembly

/-!
# Actual circle towers from positive-order estimates

Arity zero has no direction variables, so its realization is automatically
continuous in those variables. Base-point continuity follows from the
genuine first derivative. Thus positive-order seminorm bounds suffice;
no independent zeroth-order growth estimate is needed to assemble the tower.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ENNReal BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {T : MaterialData} {γ : ℝ} {S : CircleModelData} {U : Set E}

def CirclePositiveJetNormBounds
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (ℕ → ℝ → ℝ)) : Prop :=
  ∀ n s, ∃ p : Seminorm ℝ E, ∃ B : ℝ, Continuous p ∧ 0 ≤ B ∧
    ∀ x ∈ U, ∀ v : Fin (n + 1) → E,
      circleNorm T γ s (A (n + 1) x v) ≤ B * (1 + p x) * ∏ i, p (v i)

def circlePositiveJetLift (hS : IsCircleModel T γ S)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (ℕ → ℝ → ℝ))
    (hmember : ∀ n x, x ∈ U → ∀ v, CircleMember T γ (A n x v))
    (hbound : CirclePositiveJetNormBounds (T := T) (γ := γ) (U := U) A) :
    ∀ n : ℕ, E → E [×n]→L[ℝ] S.Space
  | 0, x => by
      classical
      exact if hx : x ∈ U then
        ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E)
          (circleRealize hS (A 0 x Fin.elim0) (hmember 0 x hx Fin.elim0))
        else 0
  | n + 1, x => by
      classical
      exact if hx : x ∈ U then
        liftCircleContinuousMultilinear hS (A (n + 1) x) (hmember (n + 1) x hx) (by
          intro s
          obtain ⟨p, B, hp, hB, hb⟩ := hbound n s
          exact ⟨p, B * (1 + p x), hp, hb x hx⟩)
        else 0

theorem circlePositiveJetLift_decode (hS : IsCircleModel T γ S)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (ℕ → ℝ → ℝ))
    (hmember : ∀ n x, x ∈ U → ∀ v, CircleMember T γ (A n x v))
    (hbound : CirclePositiveJetNormBounds (T := T) (γ := γ) (U := U) A)
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    S.decode (circlePositiveJetLift hS A hmember hbound n x v) = A n x v := by
  classical
  cases n with
  | zero =>
      have hv : v = Fin.elim0 := Subsingleton.elim _ _
      rw [hv]
      simp only [circlePositiveJetLift, dif_pos hx,
        ContinuousMultilinearMap.constOfIsEmpty_apply, circleRealize_decode]
  | succ n =>
      simp only [circlePositiveJetLift, dif_pos hx]
      exact liftCircleContinuousMultilinear_decode hS (A (n + 1) x)
        (hmember (n + 1) x hx) _ v

theorem circlePositiveJetLift_coordinate_bound (hS : IsCircleModel T γ S)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (ℕ → ℝ → ℝ))
    (hmember : ∀ n x, x ∈ U → ∀ v, CircleMember T γ (A n x v))
    (hbound : CirclePositiveJetNormBounds (T := T) (γ := γ) (U := U) A) :
    ∀ n s, ∃ p : Seminorm ℝ E, ∃ B : ℝ, Continuous p ∧ 0 ≤ B ∧
      ∀ x ∈ U, ∀ v : Fin (n + 1) → E,
        ‖(circlePositiveJetLift hS A hmember hbound (n + 1) x v).val s‖ ≤
          B * (1 + p x) * ∏ i, p (v i) := by
  intro n s
  obtain ⟨p, B, hp, hB, hb⟩ := hbound n s
  refine ⟨p, B, hp, hB, ?_⟩
  intro x hx v
  rw [hS.2.2.2.2.2.2.2, circlePositiveJetLift_decode hS A hmember hbound (n + 1) x hx v]
  exact hb x hx v

theorem exists_circle_smoothDirections_of_positive_scalar_jets
    (hS : IsCircleModel T γ S)
    (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m))
    (hU : IsOpen U) (hc : Convex ℝ U) (f : E → S.Space)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (ℕ → ℝ → ℝ))
    (hmember : ∀ n x, x ∈ U → ∀ v, CircleMember T γ (A n x v))
    (hbound : CirclePositiveJetNormBounds (T := T) (γ := γ) (U := U) A)
    (hzero : ∀ x ∈ U, A 0 x Fin.elim0 = S.decode (f x))
    (hscalar : ∀ n (x w : E) (v : Fin n → E) (t : ℝ), x + t • w ∈ U → ∀ m b θ,
      HasDerivAt (fun u => iteratedDeriv b (A n (x + u • w) v m) θ)
        (iteratedDeriv b (A (n + 1) (x + t • w) (Fin.cons w v) m) θ) t)
    (henergy : CircleJetSecondEnvelopes (T := T) (γ := γ) (U := U) A) :
    ∃ J : SmoothDirections U f, ∀ n x, x ∈ U → ∀ v : Fin n → E,
      S.decode (J.D n x v) = A n x v := by
  let L := circlePositiveJetLift hS A hmember hbound
  have hzeroL : ∀ x ∈ U, L 0 x Fin.elim0 = f x := by
    intro x hx
    apply hS.2.2.2.2.2.1
    exact (circlePositiveJetLift_decode hS A hmember hbound 0 x hx Fin.elim0).trans
      (hzero x hx)
  have hline : ∀ n x, x ∈ U → ∀ (v : Fin n → E) (w : E),
      HasProjectiveLineDerivAt (fun y => L n y v) (L (n + 1) x (Fin.cons w v)) x w :=
    circleJetFamily_hasProjectiveLineDerivAt hS hM hH hU A L
      (circlePositiveJetLift_decode hS A hmember hbound) hscalar henergy
  let J := smoothDirectionsOfPositiveProjectiveJetBounds L hU hc hzeroL hline
    (circlePositiveJetLift_coordinate_bound hS A hmember hbound)
  refine ⟨J, ?_⟩
  intro n x hx v
  exact circlePositiveJetLift_decode hS A hmember hbound n x hx v

end ContinuousFlexibility.Statements
