import ContinuousFlexibility.Analysis.N01cCosineAngularJets
import ContinuousFlexibility.Analysis.N01cMixedPowerNormalization
import ContinuousFlexibility.Analysis.N01cParameterCalculus
import ContinuousFlexibility.Analysis.N01cWeightAbsorption

/-!
# Actual mixed parameter bounds for the cosine speed

On the positive half-period every genuine angular state tower is the
physical speed-difference tower times the cosine velocity. Positive
state order removes the fixed reference constant. At each endpoint the
actual angular family is identically zero. The same physical speed loss
therefore controls all these jets on the closed half-period.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

section ScalarTransport

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

theorem n01c_smoothDirections_D_const_mul
    {U : Set X} {f g : X → ℝ} (J : SmoothDirections U f) (K : SmoothDirections U g)
    (a : ℝ) (he : ∀ x ∈ U, f x = a * g x)
    (k : ℕ) {x : X} (hx : x ∈ U) (v : Fin k → X) :
    J.D k x v = a * K.D k x v := by
  let A := a • ContinuousLinearMap.id ℝ ℝ
  let H : SmoothDirections U f :=
    (smoothDirections_postcompCLM K A).congr (fun x hx => by
      simpa only [A, Function.comp_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul] using (he x hx).symm)
  have h := congrArg (fun L : X [×k]→L[ℝ] ℝ => L v)
    (HasProjectiveJetsOn.unique J.open_domain J.hasProjectiveJetsOn
      H.hasProjectiveJetsOn k x hx)
  exact h.trans (by
    change (smoothDirections_postcompCLM K A).D k x v = _
    rw [smoothDirections_postcompCLM_D_apply]
    simp only [A, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul])

theorem n01c_smoothDirections_D_affine
    {U : Set X} {f g : X → ℝ} (J : SmoothDirections U f) (K : SmoothDirections U g)
    (a c : ℝ) (he : ∀ x ∈ U, f x = a * g x + c)
    {k : ℕ} (hk : 0 < k) {x : X} (hx : x ∈ U) (v : Fin k → X) :
    J.D k x v = a * K.D k x v := by
  let C := smoothDirections_constant J.open_domain (-c)
  let H : SmoothDirections U (fun y => f y - c) :=
    (smoothDirectionsAdd J C).congr (fun _ _ => (sub_eq_add_neg _ _).symm)
  have hH : H.D k x v = a * K.D k x v :=
    n01c_smoothDirections_D_const_mul H K a
      (fun y hy => by rw [he y hy]; ring) k hx v
  exact (smoothDirections_D_sub_constant J H hk hx v).symm.trans hH

/-- Quantifier transport keeps the parameter loss before the spatial
order and keeps all large concrete state types outside this selection. -/
theorem n01c_transport_order_constants
    (Q R : ℕ → ℕ → ℕ → ℝ → Prop)
    (hQ : ∀ k : ℕ, ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ Q k d s B)
    (hstep : ∀ k d s B, 0 < B → Q k d s B →
      ∃ C : ℝ, 0 < C ∧ R k d s C) :
    ∀ k : ℕ, ∃ d : ℕ, ∀ s : ℕ, ∃ C : ℝ, 0 < C ∧ R k d s C := by
  intro k
  obtain ⟨d, hd⟩ := hQ k
  refine ⟨d, fun s => ?_⟩
  obtain ⟨B, hB, hb⟩ := hd s
  exact hstep k d s B hB hb

end ScalarTransport

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

section ExactJets

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  (hA : N01PartA D T S C) (hε : 0 < ε) (hB : N01PartB D S C base ε)

/-- Exact identification for every genuine angular state tower, including
zero state order when the angular order is positive. -/
theorem componentCosineAngularStateJet_D_eq
    (m b k : ℕ) (hkb : 0 < k + b) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) Real.pi)
    (θ : ℝ)
    (J : SmoothDirections (stateNeighborhood S C base ε)
      (fun z => iteratedDeriv b (fun η => componentCosineSpeed D S C m (z, (t, η))) θ))
    (K : SmoothDirections (stateNeighborhood S C base ε)
      (characteristicSpeedFamily D S C 0 b
        (rootCosinePath (C.left m) (C.right m) t, θ)))
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (v : Fin k → (AnnularState S × ℝ)) :
    J.D k z v = ((C.right m - C.left m) / 2 * Real.sin t) * K.D k z v := by
  by_cases hb : b = 0
  · subst b
    have hk : 0 < k := by omega
    apply n01c_smoothDirections_D_affine J K _
      (((C.right m - C.left m) / 2 * Real.sin t) *
        minusCharacteristicSpeed (originalCoefficients D S C (C.referenceState, 0))
          (rootCosinePath (C.left m) (C.right m) t, θ)) ?_ hk hz v
    intro y hy
    simp only [iteratedDeriv_zero, characteristicSpeedFamily, mixedDerivative]
    rw [componentCosineSpeed_eq_transformed hS hT hA hB hy m ht]
    ring
  · exact n01c_smoothDirections_D_const_mul J K _
      (fun y hy => iteratedDeriv_componentCosineSpeed_positive
        hS hT hA hε hB hy m b (Nat.pos_of_ne_zero hb) ht θ) k hz v

/-- At a sine zero every actual angular state jet is exactly zero. -/
theorem componentCosineAngularStateJet_D_zero
    (m b k : ℕ) {t : ℝ} (ht : Real.sin t = 0) (θ : ℝ)
    (J : SmoothDirections (stateNeighborhood S C base ε)
      (fun z => iteratedDeriv b (fun η => componentCosineSpeed D S C m (z, (t, η))) θ))
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (v : Fin k → (AnnularState S × ℝ)) :
    J.D k z v = 0 := by
  let J0 : SmoothDirections (stateNeighborhood S C base ε) (fun _ => (0 : ℝ)) :=
    J.congr (fun y _ => iteratedDeriv_componentCosineSpeed_zero_of_sin_zero y m b ht θ)
  by_cases hk : k = 0
  · subst k
    exact smoothDirections_D_zero_apply J0 hz v
  · exact smoothDirections_D_constant J0 (Nat.pos_of_ne_zero hk) hz v

end ExactJets

end ContinuousFlexibility.Statements

namespace ContinuousFlexibility.Blueprint

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

/-- The genuine cosine mixed jets inherit the physical speed estimate on
the whole closed positive half-period, with no loss of the material
height factor and no extra spatial-order-dependent state loss. -/
theorem n01_componentCosineAngularStateJets_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε) (hB : N01PartB D S C base ε)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hSpeed : CharacteristicSpeedTameBounds D T S C base loss ε) :
    ∀ k : ℕ, ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ m b t θ, b ≤ s → t ∈ Icc (0 : ℝ) Real.pi → 0 < k + b →
      ∀ J : SmoothDirections (stateNeighborhood S C base ε)
        (fun z => iteratedDeriv b (fun η => componentCosineSpeed D S C m (z, (t, η))) θ),
      ∀ z ∈ stateNeighborhood S C base ε, ∀ v : Fin k → (AnnularState S × ℝ),
        |J.D k z v| ≤ B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B *
          oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
            base (s + loss + d) (z - (C.referenceState, 0)) v := by
  letI : IsTopologicalAddGroup (AnnularState S × ℝ) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S × ℝ) := inferInstance
  apply n01c_transport_order_constants _ _ hSpeed.2
  intro k d s B hBpos hbound
  obtain ⟨C₀, hC₀, hweight⟩ :=
    exists_sameConstant_materialWeight_bound (((D.b - D.a) / 2) * B) B (3 / 4 : ℝ)
  refine ⟨C₀, hC₀, ?_⟩
  intro m b t θ hb ht hkb J z hz v
  have hsample := materialSample_mem_radialCore hT hA.1.1.choose_spec.2.1 (C.cell m)
  have hH : 0 ≤ T.H (T.sample (C.cell m)) :=
    (hT.2.1 _ hsample).2.1.le
  have hE0 : 1 ≤ T.E0 (T.sample (C.cell m)) := hE _ hsample
  have hW := oneHighVariationWeight_nonneg
    (pairGrading (stateGrading S) realGrading) base (s + loss + d)
    (z - (C.referenceState, 0)) v
  have htarget : 0 ≤ C₀ * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
      T.E0 (T.sample (C.cell m)) ^ C₀ *
      oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
        base (s + loss + d) (z - (C.referenceState, 0)) v := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hC₀.le (Real.rpow_nonneg hH _))
        (Real.rpow_nonneg (zero_le_one.trans hE0) _)) hW
  by_cases ht0 : t = 0
  · subst t
    rw [componentCosineAngularStateJet_D_zero m b k Real.sin_zero θ J hz v, abs_zero]
    exact htarget
  by_cases htπ : t = Real.pi
  · subst t
    rw [componentCosineAngularStateJet_D_zero m b k Real.sin_pi θ J hz v, abs_zero]
    exact htarget
  have hti : t ∈ Ioo (0 : ℝ) Real.pi :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 htπ⟩
  have hr := rootCosinePath_mem_Ioo (hA.2.2.1.1 m).2.1 hti
  have hdata := hbound m 0 b (rootCosinePath (C.left m) (C.right m) t, θ)
    (by simpa only [zero_add] using hb) hr
  let K := Classical.choose hdata
  have hK := Classical.choose_spec hdata
  have hvalue := componentCosineAngularStateJet_D_eq
    hS hT hA hε hB m b k hkb hti θ J K hz v
  have hraw :
      |K.D k z v| ≤ B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ B *
        oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
          base (s + loss + d) (z - (C.referenceState, 0)) v := by
    simpa only [pow_zero, one_mul] using hK z hz v
  have hlen : 0 ≤ (C.right m - C.left m) / 2 :=
    div_nonneg (sub_nonneg.mpr (hA.2.2.1.1 m).2.1.le) (by norm_num)
  have hwidth : (C.right m - C.left m) / 2 ≤ (D.b - D.a) / 2 := by
    linarith [(hA.2.2.1.1 m).1, (hA.2.2.1.1 m).2.2]
  have hcos : |(C.right m - C.left m) / 2 * Real.sin t| ≤ (D.b - D.a) / 2 := by
    rw [abs_mul, abs_of_nonneg hlen]
    exact (mul_le_of_le_one_right hlen
      (abs_le.mpr ⟨Real.neg_one_le_sin t, Real.sin_le_one t⟩)).trans hwidth
  have hwidth0 : 0 ≤ (D.b - D.a) / 2 := hlen.trans hwidth
  calc
    |J.D k z v| = |(C.right m - C.left m) / 2 * Real.sin t| * |K.D k z v| := by
      rw [hvalue, abs_mul]
    _ ≤ ((D.b - D.a) / 2) *
        (B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
          T.E0 (T.sample (C.cell m)) ^ B *
          oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
            base (s + loss + d) (z - (C.referenceState, 0)) v) :=
      mul_le_mul hcos hraw (abs_nonneg _) hwidth0
    _ = (((D.b - D.a) / 2) * B) * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ B *
        oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
          base (s + loss + d) (z - (C.referenceState, 0)) v := by ring
    _ ≤ _ := hweight _ _ _ hH hE0 hW

end ContinuousFlexibility.Blueprint
