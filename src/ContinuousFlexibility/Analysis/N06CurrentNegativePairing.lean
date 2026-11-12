import ContinuousFlexibility.Analysis.N06CurrentNegativeGreen

/-!
# Actual negative operator pairings and the original graph approximation

N04 identifies the actual current source transform of `L_z phi` with the
negative principal expression plus the actual potential. The potential
terms cancel in Green's identity. Applying this identity to the one modal
family extracted from the original N05 graph gives finite actual-operator
pairings and their L2 bulk limit. No equation, trace matching, or regularity
of the bare physical coefficient fields is supplied as an extra input.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}
  {φ : PolarPoint → ℝ}

/-- The actual negative potential cancels in the canonical Green
pairing. Its actual L2 multiplier property comes from N04, with no
radiality or periodicity assumption on the potential. -/
theorem n06_negative_current_pairing_rewrite
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hm : K.positive m = false) (hφ : ContDiff ℝ ∞ φ)
    {U Q : PolarPoint → ℝ}
    (hU : MemLp U 2 (canonicalMeasure S K m))
    (hQ : MemLp Q 2 (canonicalMeasure S K m)) :
    (∫ p, (Q p + K.potential z m p * U p) * canonicalHeight S K z m φ p
      ∂canonicalMeasure S K m) -
      (∫ p, U p * canonicalSource S K z m (divergenceOperator (L.coefficients z) φ) p
        ∂canonicalMeasure S K m) =
      (∫ p, Q p * canonicalHeight S K z m φ p ∂canonicalMeasure S K m) -
      ∫ p, U p * n06NegativePrincipalTest (canonicalHeight S K z m φ) p
        ∂canonicalMeasure S K m := by
  have hW := n06_current_canonicalHeight_memLp h04 hz hs m hφ.continuous.continuousOn
  have hPW := n06_currentHeight_negativePrincipal_memLp h04 hz hs hφ (m := m)
  have hLφ := n06_negative_current_operatorTest_memLp h04 hz hs m hm hφ
  have hVU := n06_negativePotential_mul_memLp h04 hz hs m hm hU
  have hF : MemLp (fun p => Q p + K.potential z m p * U p)
      2 (canonicalMeasure S K m) := hQ.add hVU
  have hI : Integrable (fun p => (Q p + K.potential z m p * U p) *
      canonicalHeight S K z m φ p) (canonicalMeasure S K m) := hF.integrable_mul hW
  have hJ : Integrable (fun p => U p *
      canonicalSource S K z m (divergenceOperator (L.coefficients z) φ) p)
      (canonicalMeasure S K m) := hU.integrable_mul hLφ
  have hI₀ : Integrable (fun p => Q p * canonicalHeight S K z m φ p)
      (canonicalMeasure S K m) := hQ.integrable_mul hW
  have hJ₀ : Integrable (fun p => U p *
      n06NegativePrincipalTest (canonicalHeight S K z m φ) p)
      (canonicalMeasure S K m) := hU.integrable_mul hPW
  rw [← integral_sub hI hJ, ← integral_sub hI₀ hJ₀]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
  rw [n06_negative_current_operatorTest_eq h04 hz hs m hm hφ ⟨hp.1, mem_univ _⟩]
  unfold n06NegativePrincipalTest
  ring

end ContinuousFlexibility.Statements

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}
  {φ : PolarPoint → ℝ}

/-- The actual negative operator Green identity for the same finite
modal representatives supplied by the original graph. The boundary is
the genuine derivative of the finite value field. -/
theorem N06NegativeGraphApproximation.current_green
    {U G : CanonicalL2 S K m} (P : N06NegativeGraphApproximation U G)
    (Q : N06CurrentHeightTestTraces S K z m φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hm : K.positive m = false) (hφ : ContDiff ℝ ∞ φ)
    (hφp : Function.Periodic φ (0, Real.pi)) (N : ℕ) :
    (∫ p, (n06NegativeFinitePrincipal P.modes N p +
        K.potential z m p * n06NegativeFiniteValue P.modes N p) *
      canonicalHeight S K z m φ p ∂canonicalMeasure S K m) -
      (∫ p, n06NegativeFiniteValue P.modes N p *
        canonicalSource S K z m (divergenceOperator (L.coefficients z) φ) p
          ∂canonicalMeasure S K m) =
      ∫ θ in (0 : ℝ)..Real.pi,
        (Q.value (K.right m, θ) *
            radialPartial (n06NegativeFiniteValue P.modes N) (K.right m, θ) -
          n06NegativeFiniteValue P.modes N (K.right m, θ) * Q.radial (K.right m, θ)) -
        (Q.value (K.left m, θ) *
            radialPartial (n06NegativeFiniteValue P.modes N) (K.left m, θ) -
          n06NegativeFiniteValue P.modes N (K.left m, θ) * Q.radial (K.left m, θ)) := by
  rw [n06_negative_current_pairing_rewrite h04 hz hs hm hφ
    (P.value_memLp N) (P.principal_memLp N)]
  let Dm : ReferenceData := { D with a := K.left m, b := K.right m }
  have hrow := n06_finiteMixedField_physical_weakH2 (D := Dm) P.left_lt_right.le
    (Finset.range (N + 1)) P.modes (fun i _ => P.contDiff i) (fun i _ => P.deriv_ac i)
    (fun i _ => P.mode_memLp i) (fun i _ => P.deriv_memLp i)
    (fun i _ => P.second_memLp i)
  have hderiv : radialPartial (n06NegativeFiniteValue P.modes N) =
      n06FiniteMixedField (Finset.range (N + 1)) P.modes 1 0 := by
    simpa only [n06NegativeFiniteValue, n06FiniteMixedField, iteratedDeriv_zero]
      using hrow.radial_value
  rw [hderiv]
  exact Q.finite_negative_green h04 hz hs hφ hφp (Finset.range (N + 1)) P.modes
    (fun i _ => P.contDiff i) (fun i _ => P.deriv_ac i)
    (fun i _ => P.mode_memLp i) (fun i _ => P.second_memLp i)

/-- The same actual-operator bulk expressions converge in the original
L2 spaces. Finite interface terms may therefore be cancelled before this
limit; no all-mode endpoint trace convergence is needed. -/
theorem N06NegativeGraphApproximation.current_bulk_tendsto
    {U G : CanonicalL2 S K m} (P : N06NegativeGraphApproximation U G)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hm : K.positive m = false) (hφ : ContDiff ℝ ∞ φ) :
    Tendsto (fun N =>
      (∫ p, (n06NegativeFinitePrincipal P.modes N p +
          K.potential z m p * n06NegativeFiniteValue P.modes N p) *
        canonicalHeight S K z m φ p ∂canonicalMeasure S K m) -
      (∫ p, n06NegativeFiniteValue P.modes N p *
        canonicalSource S K z m (divergenceOperator (L.coefficients z) φ) p
          ∂canonicalMeasure S K m)) atTop
      (𝓝 ((∫ p, (G p + K.potential z m p * U p) * canonicalHeight S K z m φ p
        ∂canonicalMeasure S K m) -
      ∫ p, U p * canonicalSource S K z m (divergenceOperator (L.coefficients z) φ) p
        ∂canonicalMeasure S K m)) := by
  have hW := n06_current_canonicalHeight_memLp h04 hz hs m hφ.continuous.continuousOn
  have hPW := n06_currentHeight_negativePrincipal_memLp h04 hz hs hφ (m := m)
  have hlim := P.bulk_pairings_tendsto hW hPW
  rw [n06_negative_current_pairing_rewrite h04 hz hs hm hφ (Lp.memLp U) (Lp.memLp G)]
  exact hlim.congr' (Eventually.of_forall (fun N =>
    (n06_negative_current_pairing_rewrite h04 hz hs hm hφ
      (P.value_memLp N) (P.principal_memLp N)).symm))

end ContinuousFlexibility.Analysis
