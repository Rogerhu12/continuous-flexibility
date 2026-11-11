import ContinuousFlexibility.Analysis.CircleTaylorDifferentiation
import ContinuousFlexibility.Analysis.ProjectiveJetContinuity

/-!
# Circle-valued directional towers from actual weighted scalar jets

The field jets are realized in the supplied circle model. A summable
second-variation envelope proves the genuine projective line derivative.
The seminorm estimates then give joint continuity in the base point and
all directions. No circle-valued differentiability is assumed in this
assembly step.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ENNReal BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {T : MaterialData} {γ : ℝ} {S : CircleModelData} {U : Set E}

def CircleJetNormBounds
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (ℕ → ℝ → ℝ)) : Prop :=
  ∀ n s, ∃ p : Seminorm ℝ E, ∃ B : ℝ, Continuous p ∧ 0 ≤ B ∧
    ∀ x ∈ U, ∀ v : Fin n → E,
      circleNorm T γ s (A n x v) ≤ B * (1 + p x) * ∏ i, p (v i)

def circleJetLift (hS : IsCircleModel T γ S)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (ℕ → ℝ → ℝ))
    (hmember : ∀ n x, x ∈ U → ∀ v, CircleMember T γ (A n x v))
    (hbound : CircleJetNormBounds (T := T) (γ := γ) (U := U) A)
    (n : ℕ) (x : E) : E [×n]→L[ℝ] S.Space := by
  classical
  exact if hx : x ∈ U then
    liftCircleContinuousMultilinear hS (A n x) (hmember n x hx) (by
      intro s
      obtain ⟨p, B, hp, hB, hb⟩ := hbound n s
      exact ⟨p, B * (1 + p x), hp, hb x hx⟩)
    else 0

theorem circleJetLift_decode (hS : IsCircleModel T γ S)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (ℕ → ℝ → ℝ))
    (hmember : ∀ n x, x ∈ U → ∀ v, CircleMember T γ (A n x v))
    (hbound : CircleJetNormBounds (T := T) (γ := γ) (U := U) A)
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    S.decode (circleJetLift hS A hmember hbound n x v) = A n x v := by
  classical
  simp only [circleJetLift, dif_pos hx]
  exact liftCircleContinuousMultilinear_decode hS (A n x) (hmember n x hx) _ v

theorem circleJetLift_coordinate_bound (hS : IsCircleModel T γ S)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (ℕ → ℝ → ℝ))
    (hmember : ∀ n x, x ∈ U → ∀ v, CircleMember T γ (A n x v))
    (hbound : CircleJetNormBounds (T := T) (γ := γ) (U := U) A) :
    ∀ n s, ∃ p : Seminorm ℝ E, ∃ B : ℝ, Continuous p ∧ 0 ≤ B ∧
      ∀ x ∈ U, ∀ v : Fin n → E,
        ‖(circleJetLift hS A hmember hbound n x v).val s‖ ≤
          B * (1 + p x) * ∏ i, p (v i) := by
  intro n s
  obtain ⟨p, B, hp, hB, hb⟩ := hbound n s
  refine ⟨p, B, hp, hB, ?_⟩
  intro x hx v
  rw [hS.2.2.2.2.2.2.2, circleJetLift_decode hS A hmember hbound n x hx v]
  exact hb x hx v

/-- A local second-variation envelope controls all components at once.
The radius is fixed before the output order; its energy envelope may
depend on that order, just as the projective topology requires. -/
def CircleJetSecondEnvelopes
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (ℕ → ℝ → ℝ)) : Prop :=
  ∀ n x, x ∈ U → ∀ (v : Fin n → E) (w : E),
    ∃ δ : ℝ, 0 < δ ∧ (∀ t : ℝ, |t| < δ → x + t • w ∈ U) ∧
      ∀ s, ∃ energy : ℕ → ℝ≥0∞, ∃ B : ℝ,
        (∑' m, energy m) < ⊤ ∧ 0 ≤ B ∧
        ∀ t : ℝ, |t| < δ → ∀ m b k, b + k ≤ s → ∀ θ,
          (T.M (T.sample m) ^ k * T.H (T.sample m) ^ (-γ)) *
              |iteratedDeriv b (A (n + 2) (x + t • w)
                (Fin.cons w (Fin.cons w v)) m) θ| ≤ B * Real.sqrt (energy m).toReal

theorem circleJetLift_hasProjectiveLineDerivAt
    (hS : IsCircleModel T γ S)
    (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m))
    (hU : IsOpen U)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (ℕ → ℝ → ℝ))
    (hmember : ∀ n x, x ∈ U → ∀ v, CircleMember T γ (A n x v))
    (hbound : CircleJetNormBounds (T := T) (γ := γ) (U := U) A)
    (hscalar : ∀ n (x w : E) (v : Fin n → E) (t : ℝ), x + t • w ∈ U → ∀ m b θ,
      HasDerivAt (fun u => iteratedDeriv b (A n (x + u • w) v m) θ)
        (iteratedDeriv b (A (n + 1) (x + t • w) (Fin.cons w v) m) θ) t)
    (henergy : CircleJetSecondEnvelopes (T := T) (γ := γ) (U := U) A)
    (n : ℕ) (x : E) (hx : x ∈ U) (v : Fin n → E) (w : E) :
    HasProjectiveLineDerivAt
      (fun y => circleJetLift hS A hmember hbound n y v)
      (circleJetLift hS A hmember hbound (n + 1) x (Fin.cons w v)) x w := by
  let L := circleJetLift hS A hmember hbound
  obtain ⟨δ, hδ, hmem, hb⟩ := henergy n x hx v w
  let J₁ : ℝ → ℕ → ℕ → ℝ → ℝ := fun t m b θ =>
    iteratedDeriv b (A (n + 1) (x + t • w) (Fin.cons w v) m) θ
  let J₂ : ℝ → ℕ → ℕ → ℝ → ℝ := fun t m b θ =>
    iteratedDeriv b (A (n + 2) (x + t • w) (Fin.cons w (Fin.cons w v)) m) θ
  have hlineCont : Continuous (fun t : ℝ => x + t • w) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hfirst (t : ℝ) (ht : |t| < δ) (m b : ℕ) (θ : ℝ) :
      HasDerivAt (fun u => iteratedDeriv b (S.decode (L n (x + u • w) v) m) θ)
        (J₁ t m b θ) t := by
    apply (hscalar n x w v t (hmem t ht) m b θ).congr_of_eventuallyEq
    have hu : ∀ᶠ u in 𝓝 t, x + u • w ∈ U :=
      hlineCont.continuousAt.eventually (hU.mem_nhds (hmem t ht))
    filter_upwards [hu] with u hux
    rw [show S.decode (L n (x + u • w) v) = A n (x + u • w) v from
      circleJetLift_decode hS A hmember hbound n _ hux v]
  have hsecond (t : ℝ) (ht : |t| < δ) (m b : ℕ) (θ : ℝ) :
      HasDerivAt (fun u => J₁ u m b θ) (J₂ t m b θ) t :=
    hscalar (n + 1) x w (Fin.cons w v) t (hmem t ht) m b θ
  have hvalue (m b : ℕ) (θ : ℝ) :
      J₁ 0 m b θ = iteratedDeriv b (S.decode (L (n + 1) x (Fin.cons w v)) m) θ := by
    rw [show S.decode (L (n + 1) x (Fin.cons w v)) = A (n + 1) x (Fin.cons w v) from
      circleJetLift_decode hS A hmember hbound (n + 1) x hx (Fin.cons w v)]
    simp only [J₁, zero_smul, add_zero]
  exact circle_hasProjectiveCurveDerivAt_of_weighted_second_jets hS hM hH
    (fun t : ℝ => L n (x + t • w) v) (L (n + 1) x (Fin.cons w v))
    J₁ J₂ hδ hfirst hsecond hvalue hb

/-- Complete circle-valued smoothness, including joint continuity and
actual projective difference quotients, from the scalar jet data. -/
theorem exists_circle_smoothDirections_of_scalar_jets
    (hS : IsCircleModel T γ S)
    (hM : ∀ m, 0 ≤ T.M (T.sample m)) (hH : ∀ m, 0 ≤ T.H (T.sample m))
    (hU : IsOpen U) (hc : Convex ℝ U) (f : E → S.Space)
    (A : ∀ n : ℕ, E → MultilinearMap ℝ (fun _ : Fin n => E) (ℕ → ℝ → ℝ))
    (hmember : ∀ n x, x ∈ U → ∀ v, CircleMember T γ (A n x v))
    (hbound : CircleJetNormBounds (T := T) (γ := γ) (U := U) A)
    (hzero : ∀ x ∈ U, A 0 x Fin.elim0 = S.decode (f x))
    (hscalar : ∀ n (x w : E) (v : Fin n → E) (t : ℝ), x + t • w ∈ U → ∀ m b θ,
      HasDerivAt (fun u => iteratedDeriv b (A n (x + u • w) v m) θ)
        (iteratedDeriv b (A (n + 1) (x + t • w) (Fin.cons w v) m) θ) t)
    (henergy : CircleJetSecondEnvelopes (T := T) (γ := γ) (U := U) A) :
    ∃ J : SmoothDirections U f, ∀ n x, x ∈ U → ∀ v : Fin n → E,
      S.decode (J.D n x v) = A n x v := by
  let L := circleJetLift hS A hmember hbound
  have hzeroL : ∀ x ∈ U, L 0 x Fin.elim0 = f x := by
    intro x hx
    apply hS.2.2.2.2.2.1
    exact (circleJetLift_decode hS A hmember hbound 0 x hx Fin.elim0).trans (hzero x hx)
  have hline : ∀ n x, x ∈ U → ∀ (v : Fin n → E) (w : E),
      HasProjectiveLineDerivAt (fun y => L n y v) (L (n + 1) x (Fin.cons w v)) x w :=
    circleJetLift_hasProjectiveLineDerivAt hS hM hH hU A hmember hbound hscalar henergy
  let J := smoothDirectionsOfProjectiveJetBounds L hU hc hzeroL hline
    (circleJetLift_coordinate_bound hS A hmember hbound)
  refine ⟨J, ?_⟩
  intro n x hx v
  exact circleJetLift_decode hS A hmember hbound n x hx v

end ContinuousFlexibility.Statements
