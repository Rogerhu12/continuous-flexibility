import ContinuousFlexibility.Analysis.N07aActualForwardDifferentialBound
import ContinuousFlexibility.Analysis.N07aInverseChartBounds
import ContinuousFlexibility.Analysis.N07aInverseJetBudget
import ContinuousFlexibility.Analysis.N06Neighborhood

/-!
# All forward-chart jets on the actual moving domains

The inverse chart is estimated on its fixed canonical domain. Its genuine
inverse relations and the uniform first forward bound supply the finite
inverse-jet formula. A single final interpolation gives one loss for all
positive spatial derivative orders.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency true

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
  obtain ⟨loss, hbound⟩ := h
  refine ⟨loss, fun n hn => ?_⟩
  obtain ⟨e, hes, he0, heb⟩ := hbound n hn
  exact ⟨e, hes, he0, fun z hz => heb z (n07a_sectorNeighborhood_mono hb he hz)⟩

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
  let p := CanonicalGeometry.parameterGrading S
  let U := sectorNeighborhood S base ε ε
  let F := fun z m => K.chart (liftSectorParameter S C z) m
  let G := fun z m => K.inverseChart (liftSectorParameter S C z) m
  have hc (z : CanonicalGeometry.Parameter S) (hz : z ∈ U) (m : ℕ) :=
    hgeom.charts (liftSectorParameter S C z)
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (hrefState.liftSectorParameter_sector z) m
  have hΩ (z : CanonicalGeometry.Parameter S) (hz : z ∈ U) (m : ℕ) :
      IsOpen (physicalPieceOpen S K (liftSectorParameter S C z) m) :=
    (hgeom.domains (liftSectorParameter S C z)
      (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
      (hrefState.liftSectorParameter_sector z) m).1
  have hQ (m : ℕ) : IsOpen (canonicalOpen S K m) := isOpen_Ioo.prod isOpen_univ
  have hF (z : CanonicalGeometry.Parameter S) (hz : z ∈ U) (m : ℕ)
      (y : PolarPoint) (hy : y ∈ canonicalOpen S K m) :
      ContDiffAt ℝ ∞ (F z m) (G z m y) :=
    (hc z hz m).2.2.2.2.1.contDiffAt ((hΩ z hz m).mem_nhds ((hc z hz m).2.1 hy))
  have hG (z : CanonicalGeometry.Parameter S) (hz : z ∈ U) (m : ℕ)
      (y : PolarPoint) (hy : y ∈ canonicalOpen S K m) : ContDiffAt ℝ ∞ (G z m) y :=
    (hc z hz m).2.2.2.2.2.1.contDiffAt ((hQ m).mem_nhds hy)
  have hFG (z : CanonicalGeometry.Parameter S) (hz : z ∈ U) (m : ℕ)
      (y : PolarPoint) (hy : y ∈ canonicalOpen S K m) : (F z m ∘ G z m) =ᶠ[𝓝 y] id := by
    filter_upwards [(hQ m).mem_nhds hy] with q hq
    exact (hc z hz m).2.2.2.1 q hq
  have hInverse (z : CanonicalGeometry.Parameter S) (hz : z ∈ U) (m : ℕ)
      (y : PolarPoint) (hy : y ∈ canonicalOpen S K m) (v : PolarPoint) :
      fderiv ℝ (G z m) y (fderiv ℝ (F z m) (G z m y) v) = v :=
    congrArg (fun A : PolarPoint →L[ℝ] PolarPoint => A v)
      (n07a_actualChart_fderiv_inverse hgeom
        (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
        (hrefState.liftSectorParameter_sector z) m hy).2
  obtain ⟨b, hb, hb0, hbb⟩ := hFirst
  have hfirst (z : CanonicalGeometry.Parameter S) (hz : z ∈ U) (m : ℕ)
      (y : PolarPoint) (hy : y ∈ canonicalOpen S K m) :
      ‖fderiv ℝ (F z m) (G z m y)‖ ≤ b m := hbb z hz m _ ((hc z hz m).2.1 hy)
  obtain ⟨d, hInv⟩ := n07a_inverseChart_positive_jets hD hT href hcur
    (fun m => (hgeom.referenceBounds m).2.1) (fun m => (hgeom.referenceBounds m).1)
  obtain ⟨low, loss, hbound⟩ := n07a_inverseJet_fixedLoss hD hT p
    (n07aParameterGrading_monotone S)
    (hasSmoothing_pairGrading (solve_sector_hasSmoothing hS) hasSmoothing_realGrading)
    U (fun _ => canonicalOpen S K) F G d hF hG hFG hInverse hb hb0 hfirst hInv
  refine ⟨low, loss, fun n hn => ?_⟩
  obtain ⟨e, he, he0, heb⟩ := hbound n hn
  refine ⟨e, he, he0, fun z hz hlow m x hx => ?_⟩
  have h := heb z hz hlow m (F z m x) ((hc z hz m).1 hx)
  have hinverse : G z m (F z m x) = x := (hc z hz m).2.2.1 x hx
  simpa only [hinverse] using h

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
  obtain ⟨base₁, hb₁, η₁, hη₁, hη₁ε, hFirst⟩ :=
    n07a_actualForwardFirstBound_neighborhood hD hT hε hrefState hgeom href hcur
  have hgeom₁ := n06_CanonicalGeometry_mono hgeom hb₁ hη₁ε
  have hcur₁ := n07a_currentJets_restrict hD hT hcur hb₁ hη₁ε
  obtain ⟨low, loss, hbound⟩ := n07a_actualForward_positive_jets
    hD hT hS hrefState hgeom₁ href hcur₁ hFirst
  let η := min η₁ (1 / 2 : ℝ)
  have hη : 0 < η := lt_min hη₁ (by norm_num)
  have hηη₁ : η ≤ η₁ := min_le_left _ _
  have hηhalf : η ≤ 1 / 2 := min_le_right _ _
  refine ⟨max base₁ low, hb₁.trans (le_max_left _ _), η, hη,
    hηη₁.trans hη₁ε, hFirst.restrict (le_max_left _ _) hηη₁, loss, ?_⟩
  intro n hn
  obtain ⟨e, he, he0, heb⟩ := hbound n hn
  refine ⟨e, he, he0, fun z hz m x hx => ?_⟩
  have hlow : CanonicalGeometry.parameterGrading S low z ≤ 1 := by
    have hlt := n07a_parameterGrading_lt_twice_radius (le_max_right base₁ low) hz
    linarith only [hlt, hηhalf]
  exact heb z (n07a_sectorNeighborhood_mono (le_max_left _ _) hηη₁ hz) hlow m x hx

end ContinuousFlexibility.Analysis
