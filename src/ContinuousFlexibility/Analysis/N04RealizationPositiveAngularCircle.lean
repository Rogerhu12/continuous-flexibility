module

public import ContinuousFlexibility.Analysis.N04RealizationPositiveCircleInverse
public import ContinuousFlexibility.Analysis.PositiveAngularTaylorInterpolation

/-!
# The finite angular interpolation in the original circle model

Only the finitely many supplied endpoint displacements are realized.
The radial coefficients are the actual fixed Taylor and cutoff factors.
The resulting circle tower decodes to the literal interpolation, with
the original state domain and collar width.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}
  {U : Set E}

private theorem finiteCircleSumDirections
    {I : Type*} (hU : IsOpen U) (f : I → E → S.Space) :
    ∀ s : Finset I, (∀ i ∈ s, Nonempty (SmoothDirections U (f i))) →
      Nonempty (SmoothDirections U (fun x => ∑ i ∈ s, f i x)) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro _
      exact ⟨(smoothDirectionsLinearOn (0 : E →L[ℝ] S.Space) hU).congrOn
        (fun x _ => by simp only [ContinuousLinearMap.zero_apply, Finset.sum_empty])⟩
  | @insert i s hi ih =>
      intro hJ
      obtain ⟨Ji⟩ := hJ i (Finset.mem_insert_self i s)
      obtain ⟨Js⟩ := ih (fun j hj => hJ j (Finset.mem_insert_of_mem hj))
      exact ⟨(smoothDirectionsAdd Ji Js).congrOn
        (fun x _ => (Finset.sum_insert hi).symm)⟩

private theorem finiteAngularDisplacement
    (n : ℕ) (c r θ : ℝ) (A : ℕ → ℝ → ℝ) :
    (∑ j : Fin (n + 1), (r - c) ^ (j : ℕ) / ((j : ℕ).factorial : ℝ) *
      (A j θ - if (j : ℕ) = 0 then θ else 0)) =
        boundaryTaylorPolynomial n c A (r, θ) - θ := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    (r - c) ^ j / (j.factorial : ℝ) * (A j θ - if j = 0 then θ else 0))]
  calc
    _ = ∑ j ∈ Finset.range (n + 1),
        (A j θ / (j.factorial : ℝ) * (r - c) ^ j -
          if j = 0 then θ else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j = 0
      · subst j
        simp only [Nat.factorial_zero, Nat.cast_one, div_one, pow_zero,
          one_mul, if_pos rfl, mul_one]
      · simp only [if_neg hj, sub_zero]
        ring
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      simp [boundaryTaylorPolynomial]

/-- The same fixed finite interpolation has a circle-valued displacement
tower, obtained from its supplied endpoint towers. -/
theorem n04Realization_positiveAngularTaylor_circleDirections
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) (hi : HasInterpolation S.grading)
    (hU : IsOpen U) (n m : ℕ) (l r δ : ℝ)
    (A : E → Bool → ℕ → ℝ → ℝ)
    (F : Bool → Fin (n + 1) → E → S.Space)
    (J : ∀ side j, SmoothDirections U (F side j))
    (hF : ∀ side j x, x ∈ U →
      S.decode (F side j x) = circleSingleComponentField m
        (fun θ => A x side j θ - if (j : ℕ) = 0 then θ else 0)) :
    ∃ G : E × ℝ → S.Space,
      ∃ K : SmoothDirections (U ×ˢ univ) G,
        ∀ x ∈ U ×ˢ univ,
          S.decode (G x) = circleSingleComponentField m
            (fun θ => positiveAngularTaylorInterpolation n l r δ
              (A x.1) (x.2, θ) - θ) := by
  classical
  let c : Bool → ℝ := fun side => if side then r else l
  let w : Bool → Fin (n + 1) → ℝ → ℝ := fun side j t =>
    positiveEndpointCutoff (c side) δ t *
      ((t - c side) ^ (j : ℕ) / ((j : ℕ).factorial : ℝ))
  let term : Bool → Fin (n + 1) → E × ℝ → S.Space := fun side j x =>
    circleProductBilinear hS hT hD hγ
      (circleSingletonLinear hS m (w side j x.2)) (F side j x.1)
  have hdomain : IsOpen (U ×ˢ (univ : Set ℝ)) := hU.prod isOpen_univ
  have hterm (side : Bool) (j : Fin (n + 1)) :
      Nonempty (SmoothDirections (U ×ˢ univ) (term side j)) := by
    have hw : ContDiff ℝ ∞ (w side j) :=
      (contDiff_positiveEndpointCutoff (c side) δ).mul
        (((contDiff_id.sub contDiff_const).pow (j : ℕ)).div_const _)
    let Jw : SmoothDirections (U ×ˢ univ) (fun x : E × ℝ => w side j x.2) :=
      (smoothDirectionsOfContDiffOn isOpen_univ hw.contDiffOn).compLinear
        (ContinuousLinearMap.snd ℝ E ℝ) hdomain (fun _ _ => mem_univ _)
          |>.congrOn (fun _ _ => by simp only [ContinuousLinearMap.coe_snd'])
    let JF : SmoothDirections (U ×ˢ univ) (fun x : E × ℝ => F side j x.1) :=
      (J side j).compLinear (ContinuousLinearMap.fst ℝ E ℝ) hdomain
        (fun _ hx => hx.1)
          |>.congrOn (fun _ _ => by simp only [ContinuousLinearMap.coe_fst'])
    exact ⟨circleProductDirections hS hT hD hγ hi
      (circleSingletonDirections hS m Jw) JF⟩
  let sideField : Bool → E × ℝ → S.Space := fun side x => ∑ j, term side j x
  have hside (side : Bool) :
      Nonempty (SmoothDirections (U ×ˢ univ) (sideField side)) :=
    finiteCircleSumDirections hdomain (term side) Finset.univ
      (fun j _ => hterm side j)
  let G : E × ℝ → S.Space := fun x => sideField false x + sideField true x
  let K : SmoothDirections (U ×ˢ univ) G :=
    smoothDirectionsAdd (hside false).some (hside true).some
  refine ⟨G, K, ?_⟩
  intro x hx
  have hvalue (side : Bool) (j : Fin (n + 1)) (i : ℕ) (θ : ℝ) :
      S.decode (term side j x) i θ =
        if i = m then w side j x.2 *
          (A x.1 side j θ - if (j : ℕ) = 0 then θ else 0) else 0 := by
    dsimp only [term]
    rw [circleProductBilinear_decode, circleSingletonLinear_decode, hF side j x.1 hx.1]
    by_cases him : i = m
    · subst i
      simp only [circleSingletonField, circleSingleComponentField, ite_true]
    · simp only [circleSingletonField, circleSingleComponentField,
        if_neg him, zero_mul]
  have hsideValue (side : Bool) (i : ℕ) (θ : ℝ) :
      S.decode (sideField side x) i θ =
        if i = m then positiveEndpointCutoff (c side) δ x.2 *
          (boundaryTaylorPolynomial n (c side) (A x.1 side) (x.2, θ) - θ)
        else 0 := by
    dsimp only [sideField]
    rw [map_sum]
    simp only [Finset.sum_apply]
    simp_rw [hvalue]
    by_cases him : i = m
    · simp only [if_pos him]
      calc
        _ = positiveEndpointCutoff (c side) δ x.2 *
            ∑ j : Fin (n + 1),
              (x.2 - c side) ^ (j : ℕ) / ((j : ℕ).factorial : ℝ) *
                (A x.1 side j θ - if (j : ℕ) = 0 then θ else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          dsimp only [w]
          ring
        _ = _ := by rw [finiteAngularDisplacement]
    · simp only [if_neg him, Finset.sum_const_zero]
  funext i θ
  change S.decode (sideField false x + sideField true x) i θ = _
  rw [map_add]
  simp only [Pi.add_apply, hsideValue, circleSingleComponentField]
  by_cases him : i = m
  · simp only [if_pos him]
    change positiveEndpointCutoff l δ x.2 *
      (boundaryTaylorPolynomial n l (A x.1 false) (x.2, θ) - θ) +
      positiveEndpointCutoff r δ x.2 *
      (boundaryTaylorPolynomial n r (A x.1 true) (x.2, θ) - θ) = _
    simp only [positiveAngularTaylorInterpolation, positiveAngularTaylorPatch]
    ring
  · simp only [if_neg him, add_zero]

end ContinuousFlexibility.Analysis
