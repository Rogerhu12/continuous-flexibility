module

public import ContinuousFlexibility.Analysis.N07aActualForwardDifferentialBound
public import ContinuousFlexibility.Analysis.N07aInverseChartBounds
public import ContinuousFlexibility.Analysis.N07aInverseJetBudget
public import ContinuousFlexibility.Analysis.N06Neighborhood
public import ContinuousFlexibility.Analysis.N07aParameterNeighborhood

/-!
# All forward-chart jets on the actual moving domains

The inverse chart is estimated on its fixed canonical domain. Its genuine
inverse relations and the uniform first forward bound supply the finite
inverse-jet formula. A single final interpolation gives one loss for all
positive spatial derivative orders.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency true

private theorem n07a_forwardJets_with_orders {Condition : ℕ → ℕ → Prop} {P : Prop}
    (h : ∃ low loss, Condition low loss)
    (hP : ∀ low loss, Condition low loss → P) : P := by
  obtain ⟨low, loss, hbound⟩ := h
  exact hP low loss hbound

private theorem n07a_forwardJets_with_neighborhood
    {base : ℕ} {ε : ℝ} {Condition : ℕ → ℝ → Prop} {P : Prop}
    (h : ∃ b, base ≤ b ∧ ∃ η, 0 < η ∧ η ≤ ε ∧ Condition b η)
    (hP : ∀ b, base ≤ b → ∀ η, 0 < η → η ≤ ε → Condition b η → P) : P := by
  obtain ⟨b, hb, η, hη, hηε, hbound⟩ := h
  exact hP b hb η hη hηε hbound

private theorem n07a_forwardJets_restrict_predicate
    {Z : Type*} {U V : Set Z} {A B : (ℕ → ℝ) → Prop}
    {Bound : ℕ → ℕ → (ℕ → ℝ) → Z → Prop} (hVU : V ⊆ U)
    (h : ∃ loss, ∀ n : ℕ, 0 < n → ∃ e : ℕ → ℝ,
      A e ∧ B e ∧ ∀ z ∈ U, Bound loss n e z) :
    ∃ loss, ∀ n : ℕ, 0 < n → ∃ e : ℕ → ℝ,
      A e ∧ B e ∧ ∀ z ∈ V, Bound loss n e z := by
  obtain ⟨loss, hbound⟩ := h
  refine ⟨loss, fun n hn => ?_⟩
  obtain ⟨e, heA, heB, heb⟩ := hbound n hn
  exact ⟨e, heA, heB, fun z hz => heb z (hVU hz)⟩

private theorem n07a_forwardJets_remove_low_predicate
    {Z : Type*} {U V : Set Z} {A B : (ℕ → ℝ) → Prop}
    {Bound : ℕ → (ℕ → ℝ) → Z → Prop} {P : Z → Prop}
    (hVU : V ⊆ U) (hP : ∀ z ∈ V, P z)
    (h : ∀ n : ℕ, 0 < n → ∃ e : ℕ → ℝ,
      A e ∧ B e ∧ ∀ z ∈ U, P z → Bound n e z) :
    ∀ n : ℕ, 0 < n → ∃ e : ℕ → ℝ,
      A e ∧ B e ∧ ∀ z ∈ V, Bound n e z := by
  intro n hn
  obtain ⟨e, heA, heB, heb⟩ := h n hn
  exact ⟨e, heA, heB, fun z hz => heb z (hVU hz) (hP z hz)⟩

private theorem n07a_forwardJets_chart_prefix {A B C D E F R : Prop}
    (h : A ∧ B ∧ C ∧ D ∧ E ∧ F ∧ R) : A ∧ B ∧ C ∧ D ∧ E ∧ F :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

private theorem n07a_forwardJets_point_bound (f : PolarPoint → PolarPoint) (n : ℕ)
    {x y : PolarPoint} {B : ℝ} (hxy : x = y)
    (h : ‖iteratedFDeriv ℝ n f x‖ ≤ B) : ‖iteratedFDeriv ℝ n f y‖ ≤ B :=
  hxy ▸ h

private theorem n07a_forwardJets_from_inverse
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S}
    {Z : Type*} [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (p : ℕ → Seminorm ℝ Z) (hp : Monotone p) (hIp : HasSmoothing p)
    (U : Set Z) (Ω Q : Z → ℕ → Set PolarPoint)
    (F G : Z → ℕ → PolarPoint → PolarPoint)
    (hΩ : ∀ z ∈ U, ∀ m, IsOpen (Ω z m))
    (hQ : ∀ z ∈ U, ∀ m, IsOpen (Q z m))
    (hcharts : ∀ z ∈ U, ∀ m,
      MapsTo (F z m) (Ω z m) (Q z m) ∧
      MapsTo (G z m) (Q z m) (Ω z m) ∧
      (∀ x ∈ Ω z m, G z m (F z m x) = x) ∧
      (∀ y ∈ Q z m, F z m (G z m y) = y) ∧
      ContDiffOn ℝ ∞ (F z m) (Ω z m) ∧ ContDiffOn ℝ ∞ (G z m) (Q z m))
    (hInverse : ∀ z ∈ U, ∀ m y, y ∈ Q z m →
      (fderiv ℝ (G z m) y).comp (fderiv ℝ (F z m) (G z m y)) =
        ContinuousLinearMap.id ℝ PolarPoint)
    (hFirst : ∃ b : ℕ → ℝ, N07aSampleSubpower T K b ∧ (∀ m, 0 ≤ b m) ∧
      ∀ z ∈ U, ∀ m x, x ∈ Ω z m → ‖fderiv ℝ (F z m) x‖ ≤ b m)
    (hInv : ∃ d, ∀ n : ℕ, 0 < n → ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ z ∈ U, ∀ m y, y ∈ Q z m →
          ‖iteratedFDeriv ℝ n (G z m) y‖ ≤ e m * (1 + p ((n - 1) + d) z)) :
    ∃ low loss : ℕ, ∀ n : ℕ, 0 < n → ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ z ∈ U, p low z ≤ 1 → ∀ m x, x ∈ Ω z m →
          ‖iteratedFDeriv ℝ n (F z m) x‖ ≤ e m * (1 + p ((n - 1) + loss) z) := by
  have hF (z : Z) (hz : z ∈ U) (m : ℕ) (y : PolarPoint) (hy : y ∈ Q z m) :
      ContDiffAt ℝ ∞ (F z m) (G z m y) :=
    (hcharts z hz m).2.2.2.2.1.contDiffAt
      ((hΩ z hz m).mem_nhds ((hcharts z hz m).2.1 hy))
  have hG (z : Z) (hz : z ∈ U) (m : ℕ) (y : PolarPoint) (hy : y ∈ Q z m) :
      ContDiffAt ℝ ∞ (G z m) y :=
    (hcharts z hz m).2.2.2.2.2.contDiffAt ((hQ z hz m).mem_nhds hy)
  have hFG (z : Z) (hz : z ∈ U) (m : ℕ) (y : PolarPoint) (hy : y ∈ Q z m) :
      (F z m ∘ G z m) =ᶠ[𝓝 y] id := by
    filter_upwards [(hQ z hz m).mem_nhds hy] with q hq
    exact (hcharts z hz m).2.2.2.1 q hq
  have hInverse' (z : Z) (hz : z ∈ U) (m : ℕ)
      (y : PolarPoint) (hy : y ∈ Q z m) (v : PolarPoint) :
      fderiv ℝ (G z m) y (fderiv ℝ (F z m) (G z m y) v) = v :=
    congrArg (fun A : PolarPoint →L[ℝ] PolarPoint => A v) (hInverse z hz m y hy)
  obtain ⟨b, hb, hb0, hbb⟩ := hFirst
  have hfirst (z : Z) (hz : z ∈ U) (m : ℕ) (y : PolarPoint) (hy : y ∈ Q z m) :
      ‖fderiv ℝ (F z m) (G z m y)‖ ≤ b m :=
    hbb z hz m _ ((hcharts z hz m).2.1 hy)
  obtain ⟨d, hInv⟩ := hInv
  obtain ⟨low, loss, hbound⟩ := n07a_inverseJet_fixedLoss hD hT p hp hIp
    U Q F G d hF hG hFG hInverse' hb hb0 hfirst hInv
  refine ⟨low, loss, fun n hn => ?_⟩
  obtain ⟨e, he, he0, heb⟩ := hbound n hn
  refine ⟨e, he, he0, fun z hz hlow m x hx => ?_⟩
  exact n07a_forwardJets_point_bound (F z m) n ((hcharts z hz m).2.2.1 x hx)
    (heb z hz hlow m (F z m x) ((hcharts z hz m).1 hx))

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base : ℕ} {ε : ℝ}

def N07aActualForwardJetBounds (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (K : CanonicalData S) (base : ℕ) (ε : ℝ) : Prop :=
  ∃ loss : ℕ, ∀ n : ℕ, 0 < n → ∃ e : ℕ → ℝ,
    N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m x,
        x ∈ physicalPieceOpen S K (liftSectorParameter S C z) m →
          ‖iteratedFDeriv ℝ n (K.chart (liftSectorParameter S C z) m) x‖ ≤
            e m * (1 + CanonicalGeometry.parameterGrading S ((n - 1) + loss) z)

theorem N07aActualForwardJetBounds.restrict
    (h : N07aActualForwardJetBounds T S C K base ε)
    {base' : ℕ} {ε' : ℝ} (hb : base ≤ base') (he : ε' ≤ ε) :
    N07aActualForwardJetBounds T S C K base' ε' := by
  exact n07a_forwardJets_restrict_predicate (n07a_sectorNeighborhood_mono hb he) h

theorem n07a_actualForward_positive_jets
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (hrefState : referenceStateConditions D S C)
    (hgeom : CanonicalGeometry D S C K base ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hFirst : N07aActualForwardFirstBound T S C K base ε) :
    ∃ low loss : ℕ, ∀ n : ℕ, 0 < n → ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ z ∈ sectorNeighborhood S base ε ε,
          CanonicalGeometry.parameterGrading S low z ≤ 1 → ∀ m x,
          x ∈ physicalPieceOpen S K (liftSectorParameter S C z) m →
            ‖iteratedFDeriv ℝ n (K.chart (liftSectorParameter S C z) m) x‖ ≤
              e m * (1 + CanonicalGeometry.parameterGrading S ((n - 1) + loss) z) := by
  exact n07a_forwardJets_from_inverse hD hT (CanonicalGeometry.parameterGrading S)
    (n07aParameterGrading_monotone S)
    (hasSmoothing_pairGrading (solve_sector_hasSmoothing hS) hasSmoothing_realGrading)
    (sectorNeighborhood S base ε ε)
    (fun z m => physicalPieceOpen S K (liftSectorParameter S C z) m)
    (fun _ => canonicalOpen S K)
    (fun z m => K.chart (liftSectorParameter S C z) m)
    (fun z m => K.inverseChart (liftSectorParameter S C z) m)
    (fun z hz m => (hgeom.domains (liftSectorParameter S C z)
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (hrefState.liftSectorParameter_sector z) m).1)
    (fun _ _ _ => isOpen_Ioo.prod isOpen_univ)
    (fun z hz m => n07a_forwardJets_chart_prefix
      (hgeom.charts (liftSectorParameter S C z)
        (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
        (hrefState.liftSectorParameter_sector z) m))
    (fun z hz m y hy => (n07a_actualChart_fderiv_inverse hgeom
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (hrefState.liftSectorParameter_sector z) m hy).2)
    hFirst (n07a_inverseChart_positive_jets hD hT href hcur
      (fun m => (hgeom.referenceBounds m).2.1) (fun m => (hgeom.referenceBounds m).1))

/-- Both the uniform first bound and all positive-order forward bounds
follow on one stronger neighborhood from the original geometry jets. -/
theorem n07a_actualForwardJets_neighborhood
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hε : 0 < ε)
    (hrefState : referenceStateConditions D S C)
    (hgeom : CanonicalGeometry D S C K base ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧
      N07aActualForwardFirstBound T S C K base' η ∧
        N07aActualForwardJetBounds T S C K base' η := by
  refine n07a_forwardJets_with_neighborhood
    (n07a_actualForwardFirstBound_neighborhood hD hT hε hrefState hgeom href hcur) ?_
  intro base₁ hb₁ η₁ hη₁ hη₁ε hFirst
  have hgeom₁ := n06_CanonicalGeometry_mono hgeom hb₁ hη₁ε
  have hcur₁ := n07a_currentJets_restrict hD hT hcur hb₁ hη₁ε
  refine n07a_forwardJets_with_orders
    (n07a_actualForward_positive_jets hD hT hS hrefState hgeom₁ href hcur₁ hFirst) ?_
  intro low loss hbound
  refine n07a_forwardJets_with_neighborhood
    (n07a_lowParameter_neighborhood (S := S) (base := base₁) hη₁ low) ?_
  intro base₂ hb₂ η hη hηη₁ hnew
  refine ⟨base₂, hb₁.trans hb₂, η, hη, hηη₁.trans hη₁ε,
    hFirst.restrict hb₂ hηη₁, loss, ?_⟩
  exact n07a_forwardJets_remove_low_predicate hnew.1 hnew.2 hbound

end ContinuousFlexibility.Analysis
