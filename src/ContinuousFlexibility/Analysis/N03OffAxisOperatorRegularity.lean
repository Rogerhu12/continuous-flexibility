module

public import ContinuousFlexibility.Analysis.EvenPeriodicTestGerms
public import ContinuousFlexibility.Analysis.N01CoefficientValueJets
public import ContinuousFlexibility.Analysis.CoordinatePotentialRegularity

/-!
# Actual N03 operator regularity away from the reflection axes

The height-space error is genuinely smooth in the physical variables.
Every smooth physical test has a true even periodic height-test germ at
a non-axis point. Locality of the actual divergence therefore makes its
stored corrected-operator output smooth there. No differentiability of
the stored mixed or angular coefficient is assumed in this argument.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- Actual divergence preserves equality of germs, even for arbitrary
coefficient functions. This is an equality of output germs, not just
an equality of values at the center. -/
theorem divergenceOperator_eventuallyEq_of_germ
    (A : SymmetricCoefficients) {u v : PolarPoint → ℝ} {p : PolarPoint}
    (huv : u =ᶠ[𝓝 p] v) :
    divergenceOperator A u =ᶠ[𝓝 p] divergenceOperator A v := by
  have hd : fderiv ℝ u =ᶠ[𝓝 p] fderiv ℝ v := huv.fderiv
  have hr : radialPartial u =ᶠ[𝓝 p] radialPartial v :=
    hd.mono fun q hq => congrArg (fun D : PolarPoint →L[ℝ] ℝ => D (1, 0)) hq
  have ht : angularPartial u =ᶠ[𝓝 p] angularPartial v :=
    hd.mono fun q hq => congrArg (fun D : PolarPoint →L[ℝ] ℝ => D (0, 1)) hq
  have hfr :
      (fun q => A.a q * radialPartial u q + A.b q * angularPartial u q) =ᶠ[𝓝 p]
        (fun q => A.a q * radialPartial v q + A.b q * angularPartial v q) := by
    filter_upwards [hr, ht] with q hqr hqt
    rw [hqr, hqt]
  have hft :
      (fun q => A.b q * radialPartial u q + A.c q * angularPartial u q) =ᶠ[𝓝 p]
        (fun q => A.b q * radialPartial v q + A.c q * angularPartial v q) := by
    filter_upwards [hr, ht] with q hqr hqt
    rw [hqr, hqt]
  filter_upwards [hfr.fderiv (𝕜 := ℝ), hft.fderiv (𝕜 := ℝ)] with q hqr hqt
  exact congrArg₂ (fun a b : ℝ => a + b)
    (congrArg (fun D : PolarPoint →L[ℝ] ℝ => D (1, 0)) hqr)
    (congrArg (fun D : PolarPoint →L[ℝ] ℝ => D (0, 1)) hqt)

/-- The N03 identity on genuine HeightPair tests implies actual infinite
smoothness of every globally smooth test's corrected divergence at every
non-axis physical point. The assertion concerns operator output only. -/
theorem n03_contDiffAt_divergenceOperator_of_nonaxis
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN01 : N01Properties D T S C base loss ε)
    (hN03 : N03Properties D T S C R L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D)
    (hsin : Real.sin (2 * p.2) ≠ 0)
    {u : PolarPoint → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiffAt ℝ ∞ (divergenceOperator (L.coefficients z) u) p := by
  obtain ⟨η, _, hη⟩ := exists_heightPair_germ_of_nonaxis hT hS hp hsin hu
  let e : PolarPoint → ℝ :=
    (S.height (3 / 4 : ℝ)).decode ((L.error z (R.residual z) η).val)
  have hAnn : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have he : ContDiffOn ℝ ∞ e (annularOpen D) :=
    ((hS.1 (3 / 4 : ℝ)).2.2.2.1 ((L.error z (R.residual z) η).val)).1
  have hoa : ContDiffOn ℝ ∞ (originalCoefficients D S C z).a (annularOpen D) :=
    contDiffOn_originalCoefficientComponent_of_n01 hS hT hN01 hz hs 0
  have hob : ContDiffOn ℝ ∞ (originalCoefficients D S C z).b (annularOpen D) :=
    contDiffOn_originalCoefficientComponent_of_n01 hS hT hN01 hz hs 1
  have hoc : ContDiffOn ℝ ∞ (originalCoefficients D S C z).c (annularOpen D) :=
    contDiffOn_originalCoefficientComponent_of_n01 hS hT hN01 hz hs 2
  have hO : ContDiffAt ℝ ∞ (divergenceOperator (originalCoefficients D S C z) u) p :=
    contDiffAt_divergenceOperator
      ((hoa p hp).contDiffAt (hAnn.mem_nhds hp))
      ((hob p hp).contDiffAt (hAnn.mem_nhds hp))
      ((hoc p hp).contDiffAt (hAnn.mem_nhds hp)) hu.contDiffAt
  have hL := divergenceOperator_eventuallyEq_of_germ (L.coefficients z) hη
  have hOriginal := divergenceOperator_eventuallyEq_of_germ
    (originalCoefficients D S C z) hη
  have hsame : divergenceOperator (L.coefficients z) u =ᶠ[𝓝 p]
      (fun q => divergenceOperator (originalCoefficients D S C z) u q - e q) := by
    filter_upwards [hAnn.mem_nhds hp, hL, hOriginal] with q hq hLq hOq
    have herror : divergenceOperator (originalCoefficients D S C z) (heightPairField S η) q -
        divergenceOperator (L.coefficients z) (heightPairField S η) q = e q :=
      hN03.2.2.2.2.2.1 z hz hs η q hq
    rw [hLq, hOq] at herror
    linarith only [herror]
  exact (hO.sub ((he p hp).contDiffAt (hAnn.mem_nhds hp))).congr_of_eventuallyEq hsame

end ContinuousFlexibility.Analysis
