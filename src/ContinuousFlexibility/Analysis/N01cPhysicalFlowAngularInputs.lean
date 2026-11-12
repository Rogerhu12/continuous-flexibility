import ContinuousFlexibility.Analysis.N01cGraphInputInterpolation
import ContinuousFlexibility.Analysis.N01cPhysicalGraphNormalization

/-!
# Fixed interpolation and finite angular flow inputs

The low base is chosen before all parameter and spatial orders.
Zero-parameter angular factors use one fixed offset. Positive parameter
factors keep their prefix loss in the spatial exponent.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- The already proved spatial-power estimate, with its four indices named. -/
def SpatialPowerInterpolation (p : ℕ → Seminorm ℝ X)
    (base loss offset : ℕ) : Prop :=
  ∀ s : ℕ, ∃ C : ℝ, 1 ≤ C ∧
    ∀ n : ℕ, n ≤ s → ∀ x : X, p base x ≤ 1 →
    ∀ R : ℝ, 1 ≤ R → p (s + loss) x ≤ R →
      p (n + offset) x ≤ C * R ^ ((n : ℝ) / ((s : ℝ) + 1))

theorem SpatialPowerInterpolation.mono_base
    {p : ℕ → Seminorm ℝ X} {base base' loss offset : ℕ}
    (h : SpatialPowerInterpolation p base loss offset)
    (hp : Monotone p) (hb : base ≤ base') :
    SpatialPowerInterpolation p base' loss offset := by
  intro s
  obtain ⟨C, hC, hc⟩ := h s
  exact ⟨C, hC, fun n hn x hx R hR hh =>
    hc n hn x ((hp hb x).trans hx) R hR hh⟩

/-- Enlarge constants only over the finite angular input prefix. The
angular exponent and the parameter loss are left unchanged. -/
theorem exists_finite_angularFlowJet_constants
    {ι : Type*} (p : ℕ → Seminorm ℝ X) (center : X) (base o₀ K offset N : ℕ)
    (U : Set X) (I : ι → Set ℝ) (Θ : ι → X → PolarPoint → ℝ)
    (H E : ι → ℝ) (hH : ∀ m, 0 ≤ H m) (hE : ∀ m, 1 ≤ E m)
    (hzero : ∀ β : ℕ, 1 ≤ β → ∃ C : ℝ, 0 < C ∧
      ∀ m r, r ∈ I m → ∀ θ x, x ∈ U →
        |iteratedDeriv β (fun η => Θ m x (r, η)) θ| ≤
          C * (1 + p (β - 1 + o₀) (x - center)))
    (hpositive : ∀ β : ℕ, ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
      ∀ m r, r ∈ I m → ∀ θ : ℝ,
      ∀ J : SmoothDirections U
        (fun x => iteratedDeriv β (fun η => Θ m x (r, η)) θ),
      ∀ j : ℕ, j ≤ K → 0 < j → ∀ x ∈ U, ∀ v : Fin j → X,
        |J.D j x v| ≤ C * H m * E m ^ A *
          oneHighVariationWeight p base (β + offset) (x - center) v) :
    ∃ Cz Cp Ap : ℝ, 1 ≤ Cz ∧ 1 ≤ Cp ∧ 0 ≤ Ap ∧
      (∀ β : ℕ, 1 ≤ β → β ≤ N → ∀ m r, r ∈ I m → ∀ θ x, x ∈ U →
        |iteratedDeriv β (fun η => Θ m x (r, η)) θ| ≤
          Cz * (1 + p (β - 1 + o₀) (x - center))) ∧
      (∀ β : ℕ, β ≤ N → ∀ m r, r ∈ I m → ∀ θ : ℝ,
        ∀ J : SmoothDirections U
          (fun x => iteratedDeriv β (fun η => Θ m x (r, η)) θ),
        ∀ j : ℕ, j ≤ K → 0 < j → ∀ x ∈ U, ∀ v : Fin j → X,
          |J.D j x v| ≤ Cp * H m * E m ^ Ap *
            oneHighVariationWeight p base (β + offset) (x - center) v) := by
  classical
  let Pz : Fin (N + 1) → ℝ → ℝ → Prop := fun β C _ =>
    1 ≤ β.val → ∀ m r, r ∈ I m → ∀ θ x, x ∈ U →
      |iteratedDeriv β.val (fun η => Θ m x (r, η)) θ| ≤
        C * (1 + p (β.val - 1 + o₀) (x - center))
  have hzmono : ∀ β C A C' A', 1 ≤ C → 0 ≤ A → C ≤ C' → A ≤ A' →
      Pz β C A → Pz β C' A' := by
    intro β C A C' A' _ _ hCC _ hb hβ m r hr θ x hx
    exact (hb hβ m r hr θ x hx).trans
      (mul_le_mul_of_nonneg_right hCC (by positivity))
  have hzbound : ∀ β, ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧ Pz β C A := by
    intro β
    by_cases hβ : 1 ≤ β.val
    · obtain ⟨C, hC, hb⟩ := hzero β.val hβ
      refine ⟨1 + C, 0, by linarith, le_rfl, ?_⟩
      intro _ m r hr θ x hx
      exact (hb m r hr θ x hx).trans
        (mul_le_mul_of_nonneg_right (by linarith : C ≤ 1 + C) (by positivity))
    · exact ⟨1, 0, le_rfl, le_rfl, fun hh => (hβ hh).elim⟩
  obtain ⟨Cz, _, hCz, _, hz⟩ := exists_finite_graph_materialConstants Pz hzmono hzbound
  let Pp : Fin (N + 1) → ℝ → ℝ → Prop := fun β C A =>
    ∀ m r, r ∈ I m → ∀ θ : ℝ,
    ∀ J : SmoothDirections U
      (fun x => iteratedDeriv β.val (fun η => Θ m x (r, η)) θ),
    ∀ j : ℕ, j ≤ K → 0 < j → ∀ x ∈ U, ∀ v : Fin j → X,
      |J.D j x v| ≤ C * H m * E m ^ A *
        oneHighVariationWeight p base (β.val + offset) (x - center) v
  have hpmono : ∀ β C A C' A', 1 ≤ C → 0 ≤ A → C ≤ C' → A ≤ A' →
      Pp β C A → Pp β C' A' := by
    intro β C A C' A' hC _ hCC hAA hb m r hr θ J j hj hjpos x hx v
    have hfac : C * H m * E m ^ A ≤ C' * H m * E m ^ A' :=
      mul_le_mul (mul_le_mul_of_nonneg_right hCC (hH m))
        (Real.rpow_le_rpow_of_exponent_le (hE m) hAA)
        (Real.rpow_nonneg (zero_le_one.trans (hE m)) _)
        (mul_nonneg ((zero_le_one.trans hC).trans hCC) (hH m))
    exact (hb m r hr θ J j hj hjpos x hx v).trans
      (mul_le_mul_of_nonneg_right hfac
        (oneHighVariationWeight_nonneg p base (β.val + offset) (x - center) v))
  have hpbound : ∀ β, ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧ Pp β C A :=
    fun β => hpositive β.val
  obtain ⟨Cp, Ap, hCp, hAp, hp⟩ := exists_finite_graph_materialConstants Pp hpmono hpbound
  refine ⟨Cz, Cp, Ap, hCz, hCp, hAp, ?_, ?_⟩
  · intro β hβ hβN
    exact hz ⟨β, Nat.lt_succ_of_le hβN⟩ hβ
  · intro β hβN
    exact hp ⟨β, Nat.lt_succ_of_le hβN⟩

end ContinuousFlexibility.Analysis
