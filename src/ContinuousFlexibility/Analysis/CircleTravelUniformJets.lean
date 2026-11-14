module

public import ContinuousFlexibility.Analysis.CircleTranslationUniformBounds
public import ContinuousFlexibility.Analysis.CirclePositiveInverseUniformBounds
public import ContinuousFlexibility.Analysis.TameUniformFamilyJets

/-!
# Uniform chart jets with arbitrary componentwise travel

Forward composition moves travel into an isometric input translation.
Inverse composition moves it into an isometric output translation. All
constants in the genuine jet estimates are therefore chosen before any
member of the travel family. A fixed half-lower-bound open domain retains
the actual positive inverse and contains every lift with the stated lower
derivative bound.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

private theorem travel_constant_family_of_global_oneHigh
    {I E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    {U : Set E} {f : E → F} (J : SmoothDirections U f)
    (hb : ∀ n, ∃ base loss : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, p base x ≤ R → ∀ v : Fin n → E,
        q s (J.D n x v) ≤ C * tameJetSize p n s loss base x v) :
    UniformFamilyJetBounds p q (fun _ : I => J) := by
  intro n
  refine uniformFamilyLowGrowthOn_of_oneHigh (p := p) (q := q) (U := U)
    (fun (_ : I) (x : E) (v : Fin n → E) => J.D n x v) ?_
  obtain ⟨base, loss, hbound⟩ := hb n
  refine ⟨base, loss, fun R hR s => ?_⟩
  obtain ⟨C, hC, hc⟩ := hbound R hR s
  exact ⟨C, hC, fun _ x _ hx v => hc x hx v⟩

private theorem travel_restricted_constant_family_of_oneHigh
    {I E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    {U V : Set E} {f : E → F} (J : SmoothDirections U f)
    (hV : IsOpen V) (hVU : V ⊆ U) (A : E → Prop) (hVA : ∀ x ∈ V, A x)
    (hb : ∀ n, ∃ base loss : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, A x → p base x ≤ R → ∀ v : Fin n → E,
        q s (J.D n x v) ≤ C * tameJetSize p n s loss base x v) :
    UniformFamilyJetBounds p q
      (fun _ : I => smoothDirectionsRestrict J hV hVU) := by
  intro n
  refine uniformFamilyLowGrowthOn_of_oneHigh (p := p) (q := q) (U := V)
    (fun (_ : I) (x : E) (v : Fin n → E) => J.D n x v) ?_
  obtain ⟨base, loss, hbound⟩ := hb n
  refine ⟨base, loss, fun R hR s => ?_⟩
  obtain ⟨C, hC, hc⟩ := hbound R hR s
  exact ⟨C, hC, fun _ x hx hlow v => hc x (hVA x hx) hlow v⟩

variable {I : Type*} {D : ReferenceData} {T : MaterialData} {γ : ℝ} {S : CircleModelData}

def circleUniformInverseDomain (S : CircleModelData) (a : ℝ) : Set S.Space :=
  interior {e | ∀ m θ, a / 2 ≤ 1 + deriv (S.decode e m) θ}

theorem circleUniformInverseDomain_isOpen (S : CircleModelData) (a : ℝ) :
    IsOpen (circleUniformInverseDomain S a) := isOpen_interior

theorem circleUniformInverseDomain_subset_positive {a : ℝ} (ha : 0 < a) :
    circleUniformInverseDomain S a ⊆ circlePositiveLiftDomain S := by
  intro e he m θ
  exact (half_pos ha).trans_le (interior_subset he m θ)

theorem mem_circleUniformInverseDomain
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ) {a : ℝ} (ha : 0 < a)
    (e : S.Space) (hlower : ∀ m θ, a ≤ 1 + deriv (S.decode e m) θ) :
    e ∈ circleUniformInverseDomain S a := by
  have h := circleAffineLift_mem_interior_half_lower hS hT hD hγ (fun _ => 0) a ha e
    (fun m θ => by simpa only [circleAffineLift_deriv hS] using hlower m θ)
  simpa only [circleUniformInverseDomain, circleAffineLift_deriv hS] using h

theorem circleComposition_uniformFamilyJetBounds
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hi : HasInterpolation S.grading) (travel : I → ℕ → ℝ)
    (J : ∀ i, SmoothDirections univ (fun x : S.Space × S.Space =>
      circleShiftedChartComposeLinear hS hT hD hγ (travel i) x.1 x.2)) :
    UniformFamilyJetBounds (pairGrading S.grading S.grading) S.grading J := by
  letI : ∀ n, CompleteSpace (S.level n) :=
    fun n => (hS.2.1 n).isComplete.completeSpace_coe
  let p : ℕ → Seminorm ℝ (S.Space × S.Space) := pairGrading S.grading S.grading
  have hm := gradedSeminorm_monotone (fun n => S.level n) S.bond
  have hp : Monotone p := tamePairGrading_monotone hm hm
  let hz := exists_circleChartComposition_uniform_oneHigh hS hT hD hγ hi (fun _ => 0)
  let J₀ : SmoothDirections univ (fun x : S.Space × S.Space =>
      circleShiftedChartComposeContinuousLinear hS hT hD hγ (fun _ => 0) x.1 x.2) :=
    hz.choose
  have hJ₀ : UniformFamilyJetBounds p S.grading (fun _ : I => J₀) :=
    travel_constant_family_of_global_oneHigh p S.grading J₀ hz.choose_spec.2
  let L : I → (S.Space × S.Space) →L[ℝ] S.Space × S.Space := fun i =>
    (ContinuousLinearMap.fst ℝ S.Space S.Space).prod
      ((circleTranslationContinuousLinear hS hT hD hγ (travel i)).comp
        (ContinuousLinearMap.snd ℝ S.Space S.Space))
  have hL (s : ℕ) (i : I) (x : S.Space × S.Space) : p s (L i x) ≤ p s x := by
    change S.grading s x.1 +
      S.grading s (circleTranslationContinuousLinear hS hT hD hγ (travel i) x.2) ≤
        S.grading s x.1 + S.grading s x.2
    exact add_le_add le_rfl (circleTranslationContinuousLinear_grading_le hS hT hD hγ _ s x.2)
  have hlin := uniformFamilyJetBounds_linear (p := p) (q := p) isOpen_univ hp L 0
    (fun s => ⟨1, zero_le_one, fun i x => by
      simpa only [Nat.add_zero, one_mul] using hL s i x⟩)
  have heq (i : I) (x : S.Space × S.Space) (_hx : x ∈ (univ : Set (S.Space × S.Space))) :
      circleShiftedChartComposeContinuousLinear hS hT hD hγ (fun _ => 0)
        (L i x).1 (L i x).2 =
      circleShiftedChartComposeLinear hS hT hD hγ (travel i) x.1 x.2 :=
    (circleShiftedChartComposeContinuousLinear_apply
      (D := D) (T := T) (γ := γ) (S := S) hS hT hD hγ (fun _ => 0) x.1
      (circleTranslationContinuousLinear hS hT hD hγ (travel i) x.2)).trans
      (circleShiftedChartComposeLinear_eq_zero_travel
        hS hT hD hγ (travel i) x.1 x.2).symm
  exact hlin.comp_of_eq hp isOpen_univ isOpen_univ hJ₀
    (fun _ _ _ => mem_univ _) J heq

theorem circlePositiveInverse_uniformFamilyJetBounds
    (hS : IsCircleModel T γ S) (hT : IsMaterialData D T)
    (hD : IsAccumulatingProfile D) (hγ : 0 < γ)
    (hi : HasInterpolation S.grading) (travel : I → ℕ → ℝ)
    (JP : ∀ i, SmoothDirections (circlePositiveLiftDomain S ×ˢ univ)
      (fun x : S.Space × S.Space =>
        circlePositiveInverseComposeLinear hS hT hD hγ (travel i) x.1 x.2))
    (a : ℝ) (ha : 0 < a) :
    UniformFamilyJetBounds (pairGrading S.grading S.grading) S.grading
      (fun i => smoothDirectionsRestrict (JP i)
        ((circleUniformInverseDomain_isOpen S a).prod isOpen_univ)
        (fun _ hx => ⟨circleUniformInverseDomain_subset_positive ha hx.1, hx.2⟩)) := by
  let p : ℕ → Seminorm ℝ (S.Space × S.Space) := pairGrading S.grading S.grading
  have hm := gradedSeminorm_monotone (fun n => S.level n) S.bond
  have hp : Monotone p := tamePairGrading_monotone hm hm
  let W : Set S.Space := circleUniformInverseDomain S a
  have hW : IsOpen W := circleUniformInverseDomain_isOpen S a
  have hsub : W ⊆ circlePositiveLiftDomain S := circleUniformInverseDomain_subset_positive ha
  let hzero := smoothTameOn_circlePositiveInverseComposeLinear hS hT hD hγ hi (fun _ => 0)
  let J₀ : SmoothDirections (circlePositiveLiftDomain S ×ˢ univ)
      (fun x : S.Space × S.Space =>
        circlePositiveInverseComposeLinear hS hT hD hγ (fun _ => 0) x.1 x.2) :=
    hzero.choose
  let K₀ : SmoothDirections (W ×ˢ univ)
      (fun x : S.Space × S.Space =>
        circlePositiveInverseComposeLinear hS hT hD hγ (fun _ => 0) x.1 x.2) :=
    smoothDirectionsRestrict J₀ (hW.prod isOpen_univ)
      (fun _ hx => ⟨hsub hx.1, hx.2⟩)
  have hlower (x : S.Space × S.Space) (hx : x ∈ W ×ˢ univ) (m : ℕ) (θ : ℝ) :
      a / 2 ≤ deriv (circleAffineLift (fun _ => 0) (S.decode x.1) 1 m) θ :=
    (interior_subset hx.1 m θ).trans_eq
      (circleAffineLift_deriv hS (fun _ => 0) x.1 m θ).symm
  have hK₀ : UniformFamilyJetBounds p S.grading (fun _ : I => K₀) :=
    travel_restricted_constant_family_of_oneHigh p S.grading J₀
      (hW.prod isOpen_univ) (fun _ hx => ⟨hsub hx.1, hx.2⟩)
      (fun x => ∀ m θ,
        a / 2 ≤ deriv (circleAffineLift (fun _ => 0) (S.decode x.1) 1 m) θ)
      hlower (circlePositiveInverseComposeLinear_uniform_oneHigh
        hS hT hD hγ hi (fun _ => 0) J₀ (a / 2) (half_pos ha))
  let L : I → S.Space →L[ℝ] S.Space := fun i =>
    circleTranslationContinuousLinear hS hT hD hγ (fun m => -travel i m)
  have hpost := hK₀.postContinuousLinear hp L 0
    (fun s => ⟨1, zero_le_one, fun i y => by
      simpa only [Nat.add_zero, one_mul] using
        circleTranslationContinuousLinear_grading_le hS hT hD hγ (fun m => -travel i m) s y⟩)
  apply hpost.congr
    (fun i => smoothDirectionsRestrict (JP i) (hW.prod isOpen_univ)
      (fun _ hx => ⟨hsub hx.1, hx.2⟩))
  intro i x hx
  exact (circlePositiveInverseComposeLinear_eq_zero_travel hS hT hD hγ (travel i)
    x.1 x.2 (hsub hx.1)).symm

end ContinuousFlexibility.Statements
