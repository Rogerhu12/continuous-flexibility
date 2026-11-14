module

public import ContinuousFlexibility.Analysis.N06RelativeCanonicalBoundaryPatch

/-!
# The actual derivative of the relative patch at each boundary

The boundary value as a function of angle determines the tangential
derivative. Together with the matched first radial jet it determines the
whole ordinary derivative, hence its true Jacobian. On a piece whose
actual domain is its reference rectangle, the relative construction
retains the original N04 nonzero Jacobian at both endpoints.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ContDiff

/-- Equality of the actual boundary trace and the two scalar radial
derivatives determines the full derivative of a planar chart. -/
theorem n06_fderiv_eq_of_axis_trace_and_radial_jets
    {F G : PolarPoint → PolarPoint} {c θ : ℝ}
    (hF : DifferentiableAt ℝ F (c, θ)) (hG : DifferentiableAt ℝ G (c, θ))
    (htrace : ∀ η, F (c, η) = G (c, η))
    (h₁ : deriv (fun x => (F (x, θ)).1) c = deriv (fun x => (G (x, θ)).1) c)
    (h₂ : deriv (fun x => (F (x, θ)).2) c = deriv (fun x => (G (x, θ)).2) c) :
    fderiv ℝ F (c, θ) = fderiv ℝ G (c, θ) := by
  have hradF : HasDerivAt (fun x => F (x, θ)) (fderiv ℝ F (c, θ) (1, 0)) c :=
    hF.hasFDerivAt.comp_hasDerivAt c
      ((hasDerivAt_id c).prodMk (hasDerivAt_const c θ))
  have hradG : HasDerivAt (fun x => G (x, θ)) (fderiv ℝ G (c, θ) (1, 0)) c :=
    hG.hasFDerivAt.comp_hasDerivAt c
      ((hasDerivAt_id c).prodMk (hasDerivAt_const c θ))
  have hradF₁ : HasDerivAt (fun x => (F (x, θ)).1)
      (fderiv ℝ F (c, θ) (1, 0)).1 c :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt c hradF
  have hradG₁ : HasDerivAt (fun x => (G (x, θ)).1)
      (fderiv ℝ G (c, θ) (1, 0)).1 c :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt c hradG
  have hradF₂ : HasDerivAt (fun x => (F (x, θ)).2)
      (fderiv ℝ F (c, θ) (1, 0)).2 c :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt c hradF
  have hradG₂ : HasDerivAt (fun x => (G (x, θ)).2)
      (fderiv ℝ G (c, θ) (1, 0)).2 c :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt c hradG
  have hr : fderiv ℝ F (c, θ) (1, 0) = fderiv ℝ G (c, θ) (1, 0) :=
    Prod.ext (hradF₁.deriv.symm.trans (h₁.trans hradG₁.deriv))
      (hradF₂.deriv.symm.trans (h₂.trans hradG₂.deriv))
  have hangF : HasDerivAt (fun η => F (c, η)) (fderiv ℝ F (c, θ) (0, 1)) θ :=
    hF.hasFDerivAt.comp_hasDerivAt θ
      ((hasDerivAt_const θ c).prodMk (hasDerivAt_id θ))
  have hangG : HasDerivAt (fun η => G (c, η)) (fderiv ℝ G (c, θ) (0, 1)) θ :=
    hG.hasFDerivAt.comp_hasDerivAt θ
      ((hasDerivAt_const θ c).prodMk (hasDerivAt_id θ))
  have he := congrArg (fun f : ℝ → PolarPoint => deriv f θ) (funext htrace)
  have ht : fderiv ℝ F (c, θ) (0, 1) = fderiv ℝ G (c, θ) (0, 1) :=
    hangF.deriv.symm.trans (he.trans hangG.deriv)
  apply ContinuousLinearMap.ext
  intro v
  have hv : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hv, map_add, map_add, map_smul, map_smul, map_smul, map_smul, hr, ht]

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff

variable {D : ReferenceData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S}
  {base : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- The constructed chart has exactly the original current derivative at
every endpoint, including the tangential column. -/
theorem n06_relativeCanonicalChart_boundary_fderiv
    (hA : N04PartA D S C K base ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {δ : ℝ} (hδ : 0 < δ) (m : ℕ)
    (hΩ : physicalPieceOpen S K z m = referencePhysicalPieceOpen S K m)
    (hgap : 2 * δ ≤ K.physicalRight m - K.physicalLeft m)
    (side : Bool) (θ : ℝ) :
    fderiv ℝ (n06RelativeCanonicalChart C K δ z m)
        (if side then K.physicalRight m else K.physicalLeft m, θ) =
      fderiv ℝ (K.chart z m)
        (if side then K.physicalRight m else K.physicalLeft m, θ) := by
  have hle := (hA.referenceBounds m).1.le
  have hp : (if side then K.physicalRight m else K.physicalLeft m) ∈
      Icc (K.physicalLeft m) (K.physicalRight m) := by
    cases side
    · exact ⟨le_rfl, hle⟩
    · exact ⟨hle, le_rfl⟩
  have hnew := (n06_relativeCanonicalPatch_closed hA href hsref hz hs δ m hΩ
    (p := (if side then K.physicalRight m else K.physicalLeft m, θ)) hp).1
  have hold := (n06_actualCanonical_rectangle_data hA hz hs m hΩ
    (p := (if side then K.physicalRight m else K.physicalLeft m, θ)) hp).1
  have htrace (η : ℝ) :
      n06RelativeCanonicalChart C K δ z m
          (if side then K.physicalRight m else K.physicalLeft m, η) =
        K.chart z m (if side then K.physicalRight m else K.physicalLeft m, η) := by
    have hj := n06_relativeCanonicalChart_boundary_jets hA href hsref hz hs hδ m hΩ hgap
      side (j := 0) (by norm_num) η
    apply Prod.ext
    · simpa only [radialBoundaryJet, iteratedDeriv_zero] using hj.1
    · simpa only [radialBoundaryJet, iteratedDeriv_zero] using hj.2
  have hj := n06_relativeCanonicalChart_boundary_jets hA href hsref hz hs hδ m hΩ hgap
    side (j := 1) (by norm_num) θ
  apply n06_fderiv_eq_of_axis_trace_and_radial_jets
    (hnew.differentiableAt (by simp)) (hold.differentiableAt (by simp)) htrace
  · simpa only [radialBoundaryJet, iteratedDeriv_one] using hj.1
  · simpa only [radialBoundaryJet, iteratedDeriv_one] using hj.2

/-- Endpoint Jacobian nondegeneracy is retained from the true N04 chart. -/
theorem n06_relativeCanonicalChart_boundary_jacobian
    (hA : N04PartA D S C K base ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {δ : ℝ} (hδ : 0 < δ) (m : ℕ)
    (hΩ : physicalPieceOpen S K z m = referencePhysicalPieceOpen S K m)
    (hgap : 2 * δ ≤ K.physicalRight m - K.physicalLeft m)
    (side : Bool) (θ : ℝ) :
    planeJacobian (n06RelativeCanonicalChart C K δ z m)
        (if side then K.physicalRight m else K.physicalLeft m, θ) =
      planeJacobian (K.chart z m)
        (if side then K.physicalRight m else K.physicalLeft m, θ) ∧
    planeJacobian (n06RelativeCanonicalChart C K δ z m)
        (if side then K.physicalRight m else K.physicalLeft m, θ) ≠ 0 := by
  have he : planeJacobian (n06RelativeCanonicalChart C K δ z m)
        (if side then K.physicalRight m else K.physicalLeft m, θ) =
      planeJacobian (K.chart z m)
        (if side then K.physicalRight m else K.physicalLeft m, θ) := by
    simp only [planeJacobian,
      n06_relativeCanonicalChart_boundary_fderiv hA href hsref hz hs hδ m hΩ hgap side θ]
  refine ⟨he, ?_⟩
  rw [he]
  have hle := (hA.referenceBounds m).1.le
  have hp : (if side then K.physicalRight m else K.physicalLeft m) ∈
      Icc (K.physicalLeft m) (K.physicalRight m) := by
    cases side
    · exact ⟨le_rfl, hle⟩
    · exact ⟨hle, le_rfl⟩
  exact (n06_actualCanonical_rectangle_data hA hz hs m hΩ
    (p := (if side then K.physicalRight m else K.physicalLeft m, θ)) hp).2.2.1

end ContinuousFlexibility.Statements
