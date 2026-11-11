import ContinuousFlexibility.Analysis.N01cRadialPowerInputs
import ContinuousFlexibility.Analysis.N01cInverseProfileBounds
import ContinuousFlexibility.Analysis.N01cProfileBaseBounds
import ContinuousFlexibility.Analysis.N01cCoefficientMixedParameterJets
import ContinuousFlexibility.Analysis.N01cStateInterpolation

/-!
# The actual radial inputs of the normalized coefficients

The three inputs are the state profile, its first radial derivative, and
its reciprocal. Their quantitative bounds use the original material
estimates, actual localization, and the actual parameter towers.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter Function
open ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped Topology ContDiff BigOperators

set_option backward.isDefEq.respectTransparency true

def coefficientRadialInput (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) : Fin 3 → AnnularState S → ℝ → ℝ :=
  Fin.cases (stateProfile D S C)
    (Fin.cases (fun x => deriv (stateProfile D S C x))
      (fun _ x r => (stateProfile D S C x r)⁻¹))

def coefficientRadialInputJets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hD : RadialProfileGeometry D)
    (hχ : ContDiff ℝ ∞ D.chi) (n : ℕ) (r : ℝ) (hr : r ∈ Ioo D.a D.b) :
    ∀ i : Fin 3, SmoothDirections univ
      (fun x : AnnularState S => iteratedDeriv n (coefficientRadialInput D S C i x) r) :=
  Fin.cases
    (stateProfileRadialJetSmoothDirections hS hT hA.1.1 hD hA.2.2.1 hχ n r hr)
    (Fin.cases
      ((stateProfileRadialJetSmoothDirections hS hT hA.1.1 hD hA.2.2.1 hχ (n + 1) r hr).congr
        (fun _ _ => by
          rw [iteratedDeriv_succ']
          simp only [coefficientRadialInput, Fin.cases_succ, Fin.cases_zero]))
      (fun _ => stateInverseProfileRadialJetSmoothDirections
        hS hT hA.1.1 hD hA.2.2.1 hχ n r hr))

/-- The actual partition of unity covers every interior radial point. -/
theorem radialPartition_exists_cell {D : ReferenceData} (hP : RadialPartition D)
    {r : ℝ} (hr : r ∈ Ioo D.a D.b) : ∃ m, r ∈ D.cells m := by
  by_contra hnone
  have hz (m : ℕ) : D.localizer m r = 0 := by
    by_contra hm
    exact hnone ⟨m, hP.2.2.1 m hm⟩
  have hh := (hP.2.2.2.2.1 r hr).2
  simp only [hz, tsum_zero] at hh
  norm_num at hh

def coefficientRadialInput_regular
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε) (i : Fin 3) :
    MixedJetRegularity (stateNeighborhood S C base ε) (annularOpen D)
      (fun z q => coefficientRadialInput D S C i z.1 q.1) := by
  letI : IsTopologicalAddGroup (AnnularState S × ℝ) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S × ℝ) := inferInstance
  have hD : RadialProfileGeometry D := hA.1.1.choose_spec.1
  have hχ : ContDiff ℝ ∞ D.chi := hA.1.2.2.2.1.1
  let L : (AnnularState S × ℝ) →L[ℝ] AnnularState S :=
    ContinuousLinearMap.fst ℝ (AnnularState S) ℝ
  apply radialMixedRegularity (isOpen_stateNeighborhood S C base ε)
    (fun z r => coefficientRadialInput D S C i z.1 r)
    (Jr := fun n r hr => smoothDirections_precompCLM
      (coefficientRadialInputJets hS hT hA hD hχ n r hr i) L)
  intro z hz
  fin_cases i
  · exact (contDiff_stateProfile_of_partA hS hT hA z.1).contDiffOn
  · exact ((contDiff_infty_iff_deriv.mp
      (contDiff_stateProfile_of_partA hS hT hA z.1)).2).contDiffOn
  · intro r hr
    have hw := (n01PartB_denominators_pos hD hS hA.2.1 hB hz
      (p := (r, 0)) ⟨hr, mem_univ _⟩).1
    exact ((contDiff_stateProfile_of_partA hS hT hA z.1).contDiffAt.inv hw.ne').contDiffWithinAt

/-- The projection estimate is proved before specializing the state module. -/
private theorem coefficientRadialInput_fst_grading_le
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (base : ℕ) (v : E × ℝ) :
    p 0 v.1 ≤ pairGrading p realGrading base v := by
  rw [tamePairGrading_apply]
  exact (hp (Nat.zero_le base) v.1).trans
    (le_add_of_nonneg_right (apply_nonneg _ _))

/-- Rearrange only real scalar weights, before inserting a concrete state jet. -/
private theorem coefficientRadialInput_norm_weight_order
    {u B H W P : ℝ} (h : |u| ≤ (B * H * W) * P) :
    ‖u‖ ≤ B * W * H * P := by
  rw [Real.norm_eq_abs]
  exact h.trans_eq (by ring)

/-- Covering and scalar normalization are transported as one quantified bound. -/
private theorem coefficientRadialInput_positive_transport
    {X V : Type*} {I : Set ℝ} {U : Set X}
    (cells : ℕ → Set ℝ) (H E : ℝ → ℝ) (P : V → ℝ)
    (hcover : ∀ r ∈ I, ∃ m, r ∈ cells m)
    (F G : ∀ r, r ∈ I → X → V → ℝ)
    (hFG : ∀ r hr x v, F r hr x v = G r hr x v)
    (hraw : ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ m r (hr : r ∈ I), r ∈ cells m → ∀ x ∈ U, ∀ v,
        |F r hr x v| ≤ (B * H r * E r ^ A) * P v) :
    ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧
      ∀ r (hr : r ∈ I), ∀ x ∈ U, ∀ v,
        ‖G r hr x v‖ ≤ B * E r ^ A * H r * P v := by
  obtain ⟨B, A, hB, hA, hb⟩ := hraw
  refine ⟨B, A, hB, hA.le, fun r hr x hx v => ?_⟩
  obtain ⟨m, hm⟩ := hcover r hr
  have hh := coefficientRadialInput_norm_weight_order (hb m r hr hm x hx v)
  rw [hFG] at hh
  exact hh

/-- Selection among three scalar jet families is independent of their state type. -/
private theorem coefficientRadialInput_three_positive_transport
    {X V : Type*} {I : Set ℝ} {U : Set X}
    (cells : ℕ → Set ℝ) (H E : ℝ → ℝ) (P : V → ℝ)
    (hcover : ∀ r ∈ I, ∃ m, r ∈ cells m)
    (F₀ F₁ F₂ : ∀ r, r ∈ I → X → V → ℝ)
    (G : Fin 3 → ∀ r, r ∈ I → X → V → ℝ)
    (hG : ∀ i r hr x v, G i r hr x v =
      Fin.cases (F₀ r hr x v) (Fin.cases (F₁ r hr x v) (fun _ => F₂ r hr x v)) i)
    (h₀ : ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ m r (hr : r ∈ I), r ∈ cells m → ∀ x ∈ U, ∀ v,
        |F₀ r hr x v| ≤ (B * H r * E r ^ A) * P v)
    (h₁ : ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ m r (hr : r ∈ I), r ∈ cells m → ∀ x ∈ U, ∀ v,
        |F₁ r hr x v| ≤ (B * H r * E r ^ A) * P v)
    (h₂ : ∃ B A : ℝ, 0 < B ∧ 0 < A ∧
      ∀ m r (hr : r ∈ I), r ∈ cells m → ∀ x ∈ U, ∀ v,
        |F₂ r hr x v| ≤ (B * H r * E r ^ A) * P v)
    (i : Fin 3) :
    ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧
      ∀ r (hr : r ∈ I), ∀ x ∈ U, ∀ v,
        ‖G i r hr x v‖ ≤ B * E r ^ A * H r * P v := by
  revert i
  refine Fin.cases ?_ (Fin.cases ?_ (fun j => ?_))
  · exact coefficientRadialInput_positive_transport cells H E P hcover F₀ (G 0)
      (fun r hr x v => by
        simpa only [Fin.cases_zero] using (hG 0 r hr x v).symm) h₀
  · exact coefficientRadialInput_positive_transport cells H E P hcover F₁ (G (0 : Fin 2).succ)
      (fun r hr x v => by
        simpa only [Fin.cases_succ, Fin.cases_zero] using
          (hG (0 : Fin 2).succ r hr x v).symm) h₁
  · exact coefficientRadialInput_positive_transport cells H E P hcover F₂ (G j.succ.succ)
      (fun r hr x v => by
        simpa only [Fin.cases_succ] using (hG j.succ.succ r hr x v).symm) h₂

private theorem coefficientRadialInput_zero_material_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hD : RadialProfileGeometry D)
    (hχ : ContDiff ℝ ∞ D.chi) (hε : 0 < ε)
    (hB : N01PartB D S C base ε)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m))
    (hχloc : tsupport D.chi ⊆ Ioo D.a D.b)
    (i : Fin 3) (n : ℕ) :
    ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧
      ∀ r ∈ Ioo D.a D.b, ∀ z ∈ stateNeighborhood S C base ε,
        ‖iteratedDeriv n (coefficientRadialInput D S C i z.1) r‖ ≤ B * T.E0 r ^ A := by
  letI : TopologicalSpace (AnnularState S) := inferInstance
  letI : AddCommGroup (AnnularState S) := inferInstance
  letI : Module ℝ (AnnularState S) := inferInstance
  letI : IsTopologicalAddGroup (AnnularState S) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S) := inferInstance
  letI : TopologicalSpace (AnnularState S × ℝ) := inferInstance
  letI : AddCommGroup (AnnularState S × ℝ) := inferInstance
  letI : Module ℝ (AnnularState S × ℝ) := inferInstance
  letI : IsTopologicalAddGroup (AnnularState S × ℝ) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S × ℝ) := inferInstance
  have hP : RadialPartition D := hA.1.1.choose_spec.2.1
  revert i
  refine Fin.cases ?_ (Fin.cases ?_ (fun _ => ?_))
  · obtain ⟨B, A, hB0, hA0, hb⟩ :=
      iteratedDeriv_stateProfile_material_bound hS hT hA hD hχ hε hB hE hloc hχloc n
    refine ⟨B, A, hB0, hA0.le, fun r hr z hz => ?_⟩
    obtain ⟨m, hm⟩ := radialPartition_exists_cell hP hr
    simpa only [Real.norm_eq_abs, coefficientRadialInput, Fin.cases_zero]
      using hb m r hr hm z hz
  · obtain ⟨B, A, hB0, hA0, hb⟩ :=
      iteratedDeriv_stateProfile_material_bound hS hT hA hD hχ hε hB hE hloc hχloc (n + 1)
    refine ⟨B, A, hB0, hA0.le, fun r hr z hz => ?_⟩
    obtain ⟨m, hm⟩ := radialPartition_exists_cell hP hr
    simpa only [Real.norm_eq_abs, coefficientRadialInput, Fin.cases_succ, Fin.cases_zero,
      iteratedDeriv_succ'] using hb m r hr hm z hz
  · obtain ⟨B, A, hB0, hA0, hb⟩ :=
      iteratedDeriv_stateInverseProfile_material_bound hS hT hA hD hχ hε hB hE hloc hχloc n
    refine ⟨B, A, hB0, hA0.le, fun r hr z hz => ?_⟩
    obtain ⟨m, hm⟩ := radialPartition_exists_cell hP hr
    simpa only [Real.norm_eq_abs, coefficientRadialInput, Fin.cases_succ]
      using hb m r hr hm z hz

private theorem coefficientRadialInput_positive_material_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hD : RadialProfileGeometry D)
    (hχ : ContDiff ℝ ∞ D.chi) (hε : 0 < ε)
    (hB : N01PartB D S C base ε)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m))
    (hχloc : tsupport D.chi ⊆ Ioo D.a D.b)
    (i : Fin 3) (n k : ℕ) (hk : 0 < k) :
    ∃ B A : ℝ, 0 < B ∧ 0 ≤ A ∧
      ∀ r (hr : r ∈ Ioo D.a D.b), ∀ z ∈ stateNeighborhood S C base ε,
      ∀ v : Fin k → AnnularState S,
        ‖(coefficientRadialInputJets hS hT hA hD hχ n r hr i).D k z.1 v‖ ≤
          B * T.E0 r ^ A * T.H r ^ (3 / 4 : ℝ) * ∏ j, stateGrading S 0 (v j) := by
  have hP : RadialPartition D := hA.1.1.choose_spec.2.1
  let F₀ : ∀ r, r ∈ Ioo D.a D.b → (AnnularState S × ℝ) → (Fin k → AnnularState S) → ℝ :=
    fun r hr z v =>
      (stateProfileRadialJetSmoothDirections hS hT hA.1.1 hD hA.2.2.1 hχ n r hr).D k z.1 v
  let F₁ : ∀ r, r ∈ Ioo D.a D.b → (AnnularState S × ℝ) → (Fin k → AnnularState S) → ℝ :=
    fun r hr z v =>
      (stateProfileRadialJetSmoothDirections hS hT hA.1.1 hD hA.2.2.1 hχ (n + 1) r hr).D k z.1 v
  let F₂ : ∀ r, r ∈ Ioo D.a D.b → (AnnularState S × ℝ) → (Fin k → AnnularState S) → ℝ :=
    fun r hr z v =>
      (stateInverseProfileRadialJetSmoothDirections hS hT hA.1.1 hD hA.2.2.1 hχ n r hr).D k z.1 v
  let G : Fin 3 → ∀ r, r ∈ Ioo D.a D.b →
      (AnnularState S × ℝ) → (Fin k → AnnularState S) → ℝ :=
    fun j r hr z v => (coefficientRadialInputJets hS hT hA hD hχ n r hr j).D k z.1 v
  have hG : ∀ j r hr z v, G j r hr z v =
      Fin.cases (F₀ r hr z v) (Fin.cases (F₁ r hr z v) (fun _ => F₂ r hr z v)) j := by
    intro j
    refine Fin.cases ?_ (Fin.cases ?_ (fun _ => ?_)) j
    · intro r hr z v
      simp only [G, F₀, coefficientRadialInputJets, Fin.cases_zero]
    · intro r hr z v
      simp only [G, F₁, coefficientRadialInputJets, Fin.cases_succ, Fin.cases_zero,
        SmoothDirections.congr]
    · intro r hr z v
      simp only [G, F₂, coefficientRadialInputJets, Fin.cases_succ]
  exact coefficientRadialInput_three_positive_transport
    (X := AnnularState S × ℝ) (V := Fin k → AnnularState S)
    (I := Ioo D.a D.b) (U := stateNeighborhood S C base ε)
    D.cells (fun r => T.H r ^ (3 / 4 : ℝ)) T.E0
    (fun v => ∏ j, stateGrading S 0 (v j))
    (fun r hr => radialPartition_exists_cell hP hr) F₀ F₁ F₂ G hG
    (stateProfileRadialJetSmoothDirections_material_bound
      hS hT hA hD hχ hε hB hE hloc hχloc n k hk)
    (stateProfileRadialJetSmoothDirections_material_bound
      hS hT hA hD hχ hε hB hE hloc hχloc (n + 1) k hk)
    (stateInverseProfileRadialJetSmoothDirections_material_bound
      hS hT hA hD hχ hε hB hE hloc hχloc n k hk) i

/-- The actual profile, profile derivative and inverse profile have the
same mixed power control, at any fixed interpolation indices. -/
theorem coefficientRadialInput_powerBounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε)
    (hB : N01PartB D S C base ε)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r)
    (hloc : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (C.cell m))
    (hχloc : tsupport D.chi ⊆ Ioo D.a D.b) (i : Fin 3) :
    MixedPowerBounds (pairGrading (stateGrading S) realGrading) (C.referenceState, 0)
      base loss (stateNeighborhood S C base ε) (annularOpen D)
      (fun q => T.H q.1 ^ (3 / 4 : ℝ)) (fun q => T.E0 q.1)
      (fun z q => coefficientRadialInput D S C i z.1 q.1) := by
  letI : TopologicalSpace (AnnularState S) := inferInstance
  letI : AddCommGroup (AnnularState S) := inferInstance
  letI : Module ℝ (AnnularState S) := inferInstance
  letI : IsTopologicalAddGroup (AnnularState S) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S) := inferInstance
  letI : TopologicalSpace (AnnularState S × ℝ) := inferInstance
  letI : AddCommGroup (AnnularState S × ℝ) := inferInstance
  letI : Module ℝ (AnnularState S × ℝ) := inferInstance
  letI : IsTopologicalAddGroup (AnnularState S × ℝ) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S × ℝ) := inferInstance
  have hD : RadialProfileGeometry D := hA.1.1.choose_spec.1
  have hχ : ContDiff ℝ ∞ D.chi := hA.1.2.2.2.1.1
  let L : (AnnularState S × ℝ) →L[ℝ] AnnularState S :=
    ContinuousLinearMap.fst ℝ (AnnularState S) ℝ
  have hL : ∀ v : AnnularState S × ℝ,
      stateGrading S 0 (L v) ≤ pairGrading (stateGrading S) realGrading base v := by
    intro v
    simpa only [L, ContinuousLinearMap.coe_fst'] using
      coefficientRadialInput_fst_grading_le (stateGrading S) (stateGrading_monotone S) base v
  apply projectedRadialJets_powerBounds
    (X := AnnularState S × ℝ) (Y := AnnularState S)
    (U := stateNeighborhood S C base ε) (I := Ioo D.a D.b)
    (H := fun r => T.H r ^ (3 / 4 : ℝ)) (E := T.E0)
    (pairGrading (stateGrading S) realGrading) (stateGrading S 0)
    (C.referenceState, 0) base loss
    (fun r hr => Real.rpow_nonneg (hT.2.1 r hr).2.1.le _) hE L hL
    (coefficientRadialInput D S C i)
    (fun n r hr => coefficientRadialInputJets hS hT hA hD hχ n r hr i)
  · intro n
    simpa only [L, ContinuousLinearMap.coe_fst'] using
      coefficientRadialInput_zero_material_bound hS hT hA hD hχ hε hB hE hloc hχloc i n
  · intro n k hk
    simpa only [L, ContinuousLinearMap.coe_fst'] using
      coefficientRadialInput_positive_material_bound hS hT hA hD hχ hε hB hE hloc hχloc i n k hk

end ContinuousFlexibility.Statements
