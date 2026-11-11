import ContinuousFlexibility.Analysis.CoupledLogProfilePointwise
import ContinuousFlexibility.Analysis.CoupledScalarHeightDerivative
import ContinuousFlexibility.Analysis.SpacesParameterJets

/-!
# Actual coefficient jets control every logarithmic state direction

At zero external parameter the radial coefficient is the physical profile.
The genuine first coefficient jet from N01 therefore controls all spatial
jets of the reference profile times the actual logarithmic perturbation.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem coupled_stateKappa_reference
    (href : referenceStateConditions D S C) (m : ℕ) :
    stateKappa S C.referenceState m = 0 := by
  simp only [stateKappa, href.2.2.2.1, map_zero, Pi.zero_apply,
    angularMean, intervalIntegral.integral_zero, mul_zero]

theorem coupled_stateProfile_reference
    (href : referenceStateConditions D S C) :
    stateProfile D S C C.referenceState = D.w := by
  funext r
  simp only [stateProfile, href.2.2.1, coupled_stateKappa_reference href,
    zero_mul, tsum_zero, zero_add, Real.exp_zero, mul_one]

theorem coupled_stateHeight_zero_parameter (x : AnnularState S) :
    stateHeight D S C (x, 0) =
      Radial.radialHeightField (stateRadialHeight D S C x) := by
  funext p
  simp only [stateHeight, Radial.radialHeightField, zero_mul, add_zero]

/-- Only the actual radial coefficient is needed for the profile extraction. -/
theorem coupled_coefficientA_zeroParameter (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε)
    (x : AnnularState S) (p : PolarPoint) :
    (originalCoefficients D S C (x, 0)).a p = stateProfile D S C x p.1 := by
  have hw := contDiff_stateProfile_of_n01 hS hT hN x
  have hhw := stateRadialHeight_hasDerivAt_of_contDiff hw
  change polarLinearA (stateProfile D S C x) (stateHeight D S C (x, 0)) p = _
  rw [coupled_stateHeight_zero_parameter]
  simp only [polarLinearA, linearRadial, polarScale,
    Radial.polarDiscriminant_radialHeightField hhw,
    Radial.heightRadial_radialHeightField hhw,
    Radial.heightAngular_radialHeightField hhw,
    angularPartial_const, heightQ, mul_zero, add_zero,
    heightDiscriminant_radial, inverseDThreeHalves_one, mul_one, Radial.radialHeightField]

theorem coupled_contDiff_stateControlSum (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε)
    (x : AnnularState S) : ContDiff ℝ ∞ (stateControlSum C x) := by
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  obtain ⟨hleft, hright⟩ := stateControlSum_flatJets_of_eventually_small hC x
    (stateKappa_controlJet_eventually_small hS hT hN x)
  obtain ⟨B, hB⟩ := hN.1.1
  have h := contDiff_extendZeroOutside hB.1.2.1
    (contDiffOn_stateControlSum hC x) hleft hright
  have he : extendZeroOutside D.a D.b (stateControlSum C x) = stateControlSum C x := by
    funext r
    by_cases hr : r ∈ Ioo D.a D.b
    · exact extendZeroOutside_of_mem hr
    · exact (extendZeroOutside_of_notMem hr).trans (stateControlSum_zero_off_core hC x hr).symm
  rwa [he] at h

theorem coupled_contDiff_stateLogProfile (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε)
    (x : AnnularState S) : ContDiff ℝ ∞ (coupled_stateLogProfile D S C x) :=
  (contDiff_const.mul hN.1.2.2.2.1.1).add (coupled_contDiff_stateControlSum hT hS hN x)

theorem coupled_coefficientFamily_zeroParameter (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε)
    (x : AnnularState S) (a b : ℕ) (p : PolarPoint) :
    coefficientFamily D S C 0 a b p (x, 0) =
      mixedDerivative a b (fun q => stateProfile D S C x q.1 - D.w q.1) p := by
  simp only [coefficientFamily, ↓reduceIte]
  apply congrArg (fun f : PolarPoint → ℝ => mixedDerivative a b f p)
  funext q
  rw [coupled_coefficientA_zeroParameter hT hS hN,
    coupled_coefficientA_zeroParameter hT hS hN, coupled_stateProfile_reference hN.2.2.1]

private theorem coupled_exp_line_mixedDerivative_hasDerivAt
    {w L w₀ : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (hL : ContDiff ℝ ∞ L)
    (hw₀ : ContDiff ℝ ∞ w₀) (a b : ℕ) (p : PolarPoint) :
    HasDerivAt
      (fun t : ℝ => mixedDerivative a b
        (fun q => w q.1 * Real.exp (t * L q.1) - w₀ q.1) p)
      (mixedDerivative a b (fun q => w q.1 * L q.1) p) 0 := by
  let F : ℝ × PolarPoint → ℝ := fun z =>
    w z.2.1 * Real.exp (z.1 * L z.2.1) - w₀ z.2.1
  have hF : ContDiff ℝ ∞ F :=
    ((hw.comp contDiff_snd.fst).mul
      (contDiff_fst.mul (hL.comp contDiff_snd.fst)).exp).sub
        (hw₀.comp contDiff_snd.fst)
  have hd := spaces_hasDerivAt_parameter_mixedDerivative hF a b 0 p
  have hparameter : (fun q : PolarPoint => deriv (fun t : ℝ => F (t, q)) 0) =
      fun q => w q.1 * L q.1 := by
    funext q
    have h := ((((hasDerivAt_id (0 : ℝ)).mul_const (L q.1)).exp).const_mul
      (w q.1)).sub_const (w₀ q.1)
    simpa only [F, id_eq, zero_mul, Real.exp_zero, one_mul] using h.deriv
  rw [hparameter] at hd
  exact hd

/-- Parameter differentiation commutes with every actual spatial coefficient
jet because the exponential line is jointly smooth in the parameter and point. -/
theorem coupled_coefficientA_jet_state_hasDerivAt (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε)
    (x v : AnnularState S) (a b : ℕ) (p : PolarPoint) :
    HasDerivAt
      (fun t : ℝ => coefficientFamily D S C 0 a b p
        (x + coupledScalarAction (E := AnnularState S) t v, 0))
      (mixedDerivative a b
        (fun q => stateProfile D S C x q.1 * coupled_stateLogProfile D S C v q.1) p) 0 := by
  have hw := contDiff_stateProfile_of_n01 hS hT hN x
  have hL := coupled_contDiff_stateLogProfile hT hS hN v
  have hw₀ : ContDiff ℝ ∞ D.w := hN.1.1.choose_spec.1.2.2.1.1
  apply (coupled_exp_line_mixedDerivative_hasDerivAt hw hL hw₀ a b p).congr_of_eventuallyEq
  exact Eventually.of_forall fun t => by
    rw [coupled_coefficientFamily_zeroParameter hT hS hN]
    apply congrArg (fun f : PolarPoint → ℝ => mixedDerivative a b f p)
    funext q
    exact congrArg (fun y : ℝ => y - D.w q.1)
      (coupled_stateProfile_affine hS hN.2.2.2.1 x v t q.1)

private theorem coupled_oneHigh_first_product_zero
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (base high : ℕ) (v : E) :
    oneHighVariationWeight (pairGrading p realGrading) base high
      (0 : E × ℝ) (Fin.cons (v, 0) Fin.elim0) = p base v + p high v := by
  simp [oneHighVariationWeight, pairGrading, realGrading]

/-- Every spatial order is extracted from the genuine first parameter jet of
N01, retaining its same fixed loss and its actual evaluation cell. -/
theorem coupled_logProfile_reference_jet_bound (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m r, r ∈ D.cells m → ∀ v : AnnularState S,
      |iteratedDeriv s (fun t => D.w t * coupled_stateLogProfile D S C v t) r| ≤
        B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B *
          (stateGrading S base v + stateGrading S (s + loss) v) := by
  let hcoeff := hN.2.2.2.2.2.2.2.2.2.2.2.1 1 s
  let B : ℝ := hcoeff.choose
  have hB : 0 < B := hcoeff.choose_spec.1
  let hBj := hcoeff.choose_spec.2
  refine ⟨B, hB, ?_⟩
  intro m r hr v
  let hjets := hBj m 0 s 0 (r, 0) (by omega) hr
  let J := hjets.choose
  have hJ := hjets.choose_spec
  have hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε := by
    constructor
    · simpa only [sub_self, map_zero] using hN.2.1
    · simpa only [abs_zero] using hN.2.1
  have hline := J.hasProjectiveJetsOn.hasLineDerivAt J.open_domain hz (v, 0)
  have hd : HasDerivAt
      (fun t : ℝ => coefficientFamily D S C 0 s 0 (r, 0)
        ((C.referenceState, 0) + (coupledScalarAction (E := AnnularState S × ℝ) t (v, 0))))
      (J.D 1 (C.referenceState, 0) (Fin.cons (v, 0) Fin.elim0)) 0 :=
    hasDerivAt_iff_tendsto_slope_zero.mpr hline
  have hd' : HasDerivAt
      (fun t : ℝ => coefficientFamily D S C 0 s 0 (r, 0) (C.referenceState + (coupledScalarAction (E := AnnularState S) t v), 0))
      (J.D 1 (C.referenceState, 0) (Fin.cons (v, 0) Fin.elim0)) 0 := by
    simpa only [coupledScalarAction_prod_mk, Prod.mk_add_mk,
      coupledScalarAction_zero, add_zero] using hd
  have ha := coupled_coefficientA_jet_state_hasDerivAt hT hS hN C.referenceState v s 0 (r, 0)
  have hvalue : J.D 1 (C.referenceState, 0) (Fin.cons (v, 0) Fin.elim0) =
      iteratedDeriv s (fun t => D.w t * coupled_stateLogProfile D S C v t) r := by
    simpa only [coupled_stateProfile_reference hN.2.2.1, mixedDerivative, iteratedDeriv_zero]
      using hd'.unique ha
  have hbound := hJ (C.referenceState, 0) hz (Fin.cons (v, 0) Fin.elim0)
  simpa only [hvalue, sub_self, coupled_oneHigh_first_product_zero] using hbound

end ContinuousFlexibility.Statements
