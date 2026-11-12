import ContinuousFlexibility.Analysis.N06RelativeBoundaryJacobian
import ContinuousFlexibility.Analysis.N06RootTransmissionJets

/-!
# The relative patch preserves genuine boundary first jets

The logarithmic-height construction retains the value and first radial
derivative of its actual positive target height. Exponentiation therefore
retains the height itself and its genuine first derivative. Together with
the already proved full chart derivative identity, this transfers an
actual root first-jet record to the explicitly constructed relative patch.

Only endpoint data of the actual forward functions are used. No inverse
boundary value or reconstructed-field transmission is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ContDiff

private theorem n06_positive_height_firstJets_of_log_jets
    {f g : PolarPoint → ℝ} {r θ : ℝ}
    (hf : DifferentiableAt ℝ f (r, θ)) (hg : DifferentiableAt ℝ g (r, θ))
    (hfpos : 0 < f (r, θ)) (hgpos : 0 < g (r, θ))
    (hvalue : Real.log (f (r, θ)) = Real.log (g (r, θ)))
    (hderiv : deriv (fun x => Real.log (f (x, θ))) r =
      deriv (fun x => Real.log (g (x, θ))) r) :
    f (r, θ) = g (r, θ) ∧ radialPartial f (r, θ) = radialPartial g (r, θ) := by
  have hv : f (r, θ) = g (r, θ) := by
    calc
      f (r, θ) = Real.exp (Real.log (f (r, θ))) := (Real.exp_log hfpos).symm
      _ = Real.exp (Real.log (g (r, θ))) := congrArg Real.exp hvalue
      _ = g (r, θ) := Real.exp_log hgpos
  have hfr : HasDerivAt (fun x => f (x, θ)) (radialPartial f (r, θ)) r :=
    hf.hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_id r).prodMk (hasDerivAt_const r θ))
  have hgr : HasDerivAt (fun x => g (x, θ)) (radialPartial g (r, θ)) r :=
    hg.hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_id r).prodMk (hasDerivAt_const r θ))
  have he : radialPartial f (r, θ) / f (r, θ) = radialPartial g (r, θ) / g (r, θ) :=
    (hfr.log hfpos.ne').deriv.symm.trans (hderiv.trans (hgr.log hgpos.ne').deriv)
  rw [hv] at he
  exact ⟨hv, (div_left_inj' hgpos.ne').mp he⟩

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S}
  {base : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- The explicit positive-height patch has the original current height
and radial first derivative at both actual physical endpoints. -/
theorem n06_relativeCanonicalHeight_boundary_firstJets
    (hA : N04PartA D S C K base ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {δ : ℝ} (hδ : 0 < δ) (m : ℕ)
    (hgap : 2 * δ ≤ K.physicalRight m - K.physicalLeft m)
    (side : Bool) (θ : ℝ) :
    n06RelativeCanonicalHeight C K δ z m
        (if side then K.physicalRight m else K.physicalLeft m, θ) =
      K.height z m (if side then K.physicalRight m else K.physicalLeft m, θ) ∧
    radialPartial (n06RelativeCanonicalHeight C K δ z m)
        (if side then K.physicalRight m else K.physicalLeft m, θ) =
      radialPartial (K.height z m)
        (if side then K.physicalRight m else K.physicalLeft m, θ) := by
  have hp : (if side then K.physicalRight m else K.physicalLeft m) ∈
      Icc (K.physicalLeft m) (K.physicalRight m) := by
    cases side
    · exact ⟨le_rfl, (hA.2.2.2.1 m).1.le⟩
    · exact ⟨(hA.2.2.2.1 m).1.le, le_rfl⟩
  have hnew := n06_relativeCanonicalPatch_closed hA href hsref hz hs δ m
    (p := (if side then K.physicalRight m else K.physicalLeft m, θ)) hp
  have hold := hA.2.2.2.2.2.2.2.2.1 z hz hs m
    (if side then K.physicalRight m else K.physicalLeft m, θ) hp
  have hlog₀ := n06_relativeCanonicalHeight_log_boundary_jets hA href hsref hz hs
    hδ m hgap side (j := 0) (by norm_num) θ
  have hlog₁ := n06_relativeCanonicalHeight_log_boundary_jets hA href hsref hz hs
    hδ m hgap side (j := 1) (by norm_num) θ
  apply n06_positive_height_firstJets_of_log_jets
    (hnew.2.1.differentiableAt (by simp)) (hold.2.1.differentiableAt (by simp))
    hnew.2.2 hold.2.2.2
  · simpa only [radialBoundaryJet, iteratedDeriv_zero] using hlog₀
  · simpa only [radialBoundaryJet, iteratedDeriv_one] using hlog₁

/-- The constructed relative chart and height preserve every field of
an actual current root first-jet record. Its shared boundary functions
and its physical radial orientation remain the original ones. -/
theorem n06_relativeCanonicalPatch_firstJets
    (hA : N04PartA D S C K base ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {δ : ℝ} (hδ : 0 < δ) (m : ℕ)
    (hgap : 2 * δ ≤ K.physicalRight m - K.physicalLeft m)
    (side : Bool) {y σ : ℝ} {β H ρ κ Hr : ℝ → ℝ}
    (J : N06RootFirstJets (K.chart z m) (K.height z m)
      (if side then K.physicalRight m else K.physicalLeft m) y σ β H ρ κ Hr) :
    N06RootFirstJets (n06RelativeCanonicalChart C K δ z m)
      (n06RelativeCanonicalHeight C K δ z m)
      (if side then K.physicalRight m else K.physicalLeft m) y σ β H ρ κ Hr := by
  have hp : (if side then K.physicalRight m else K.physicalLeft m) ∈
      Icc (K.physicalLeft m) (K.physicalRight m) := by
    cases side
    · exact ⟨le_rfl, (hA.2.2.2.1 m).1.le⟩
    · exact ⟨(hA.2.2.2.1 m).1.le, le_rfl⟩
  have hnew (θ : ℝ) := n06_relativeCanonicalPatch_closed hA href hsref hz hs δ m
    (p := (if side then K.physicalRight m else K.physicalLeft m, θ)) hp
  refine ⟨fun θ => (hnew θ).1.differentiableAt (by simp),
    fun θ => (hnew θ).2.1.differentiableAt (by simp), ?_, ?_, ?_, ?_⟩
  · intro θ
    have hj := n06_relativeCanonicalChart_boundary_jets hA href hsref hz hs
      hδ m hgap side (j := 0) (by norm_num) θ
    have he : n06RelativeCanonicalChart C K δ z m
        (if side then K.physicalRight m else K.physicalLeft m, θ) =
      K.chart z m (if side then K.physicalRight m else K.physicalLeft m, θ) := by
      apply Prod.ext
      · simpa only [radialBoundaryJet, iteratedDeriv_zero] using hj.1
      · simpa only [radialBoundaryJet, iteratedDeriv_zero] using hj.2
    exact he.trans (J.chart_value θ)
  · intro θ
    exact (n06_relativeCanonicalHeight_boundary_firstJets hA href hsref hz hs
      hδ m hgap side θ).1.trans (J.height_value θ)
  · intro θ
    rw [n06_relativeCanonicalChart_boundary_fderiv hA href hsref hz hs hδ m hgap side θ]
    exact J.chart_radial θ
  · intro θ
    exact (n06_relativeCanonicalHeight_boundary_firstJets hA href hsref hz hs
      hδ m hgap side θ).2.trans (J.height_radial θ)

end ContinuousFlexibility.Statements
