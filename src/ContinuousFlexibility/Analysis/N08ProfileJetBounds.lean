import ContinuousFlexibility.Analysis.N08ProfileCoefficient
import ContinuousFlexibility.Analysis.SpacesParameterJets

/-!
# All actual spatial jets of logarithmic profile directions

The globally smooth logarithmic control sum gives joint smoothness of each
real parameter line. The established mixed-derivative commutation theorem
then identifies N01's first coefficient jet with every spatial derivative of
the reference profile times that control direction.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem n08_contDiff_stateControlSum (hT : IsMaterialData D T)
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

theorem n08_contDiff_stateLogProfile (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε)
    (x : AnnularState S) : ContDiff ℝ ∞ (n08_stateLogProfile D S C x) :=
  (contDiff_const.mul hN.1.2.2.2.1.1).add (n08_contDiff_stateControlSum hT hS hN x)

theorem n08_coefficientFamily_zeroParameter (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε)
    (x : AnnularState S) (a b : ℕ) (p : PolarPoint) :
    coefficientFamily D S C 0 a b p (x, 0) =
      mixedDerivative a b (fun q => stateProfile D S C x q.1 - D.w q.1) p := by
  simp only [coefficientFamily, ↓reduceIte]
  apply congrArg (fun f : PolarPoint → ℝ => mixedDerivative a b f p)
  funext q
  rw [n08_coefficientA_zeroParameter hT hS hN,
    n08_coefficientA_zeroParameter hT hS hN, n08_stateProfile_reference hN.2.2.1]

/-- Parameter differentiation commutes with every actual spatial coefficient
jet because the exponential line is jointly smooth in the parameter and point. -/
theorem n08_coefficientA_jet_state_hasDerivAt (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε)
    (x v : AnnularState S) (a b : ℕ) (p : PolarPoint) :
    HasDerivAt
      (fun t : ℝ => coefficientFamily D S C 0 a b p (x + n08StateSMul S t v, 0))
      (mixedDerivative a b
        (fun q => stateProfile D S C x q.1 * n08_stateLogProfile D S C v q.1) p) 0 := by
  let F : ℝ × PolarPoint → ℝ := fun z =>
    stateProfile D S C x z.2.1 * Real.exp (z.1 * n08_stateLogProfile D S C v z.2.1) -
      D.w z.2.1
  have hw := contDiff_stateProfile_of_n01 hS hT hN x
  have hL := n08_contDiff_stateLogProfile hT hS hN v
  obtain ⟨B, hB⟩ := hN.1.1
  have hF : ContDiff ℝ ∞ F :=
    ((hw.comp contDiff_snd.fst).mul
      (contDiff_fst.mul (hL.comp contDiff_snd.fst)).exp).sub
        (hB.1.2.2.1.1.comp contDiff_snd.fst)
  have hd := spaces_hasDerivAt_parameter_mixedDerivative hF a b 0 p
  have hparameter : (fun q : PolarPoint => deriv (fun t : ℝ => F (t, q)) 0) =
      fun q => stateProfile D S C x q.1 * n08_stateLogProfile D S C v q.1 := by
    funext q
    have h := (n08_stateProfile_hasDerivAt hS hN.2.2.2.1 x v q.1).sub_const (D.w q.1)
    simpa only [F, n08_stateProfile_affine hS hN.2.2.2.1] using h.deriv
  rw [hparameter] at hd
  convert hd using 1
  funext t
  rw [n08_coefficientFamily_zeroParameter hT hS hN]
  apply congrArg (fun f : PolarPoint → ℝ => mixedDerivative a b f p)
  funext q
  exact congrArg (fun y : ℝ => y - D.w q.1)
    (n08_stateProfile_affine hS hN.2.2.2.1 x v t q.1)

private theorem n08_oneHigh_first_product_zero
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (base high : ℕ) (v : E) :
    oneHighVariationWeight (pairGrading p realGrading) base high
      (0 : E × ℝ) (Fin.cons (v, 0) Fin.elim0) = p base v + p high v := by
  simp [oneHighVariationWeight, pairGrading, realGrading]

/-- Every spatial order is extracted from the genuine first parameter jet of
N01, retaining its same fixed loss and its actual evaluation cell. -/
theorem n08_logProfile_reference_jet_bound (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hN : N01Properties D T S C base loss ε) (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m r, r ∈ D.cells m → ∀ v : AnnularState S,
      |iteratedDeriv s (fun t => D.w t * n08_stateLogProfile D S C v t) r| ≤
        B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B *
          (stateGrading S base v + stateGrading S (s + loss) v) := by
  have hcoeff := hN.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨B, hB, hBj⟩ := hcoeff 1 s
  refine ⟨B, hB, ?_⟩
  intro m r hr v
  obtain ⟨J, hJ⟩ := hBj m 0 s 0 (r, 0) (by omega) hr
  have hz : (C.referenceState, 0) ∈ stateNeighborhood S C base ε := by
    constructor
    · simpa only [sub_self, map_zero] using hN.2.1
    · simpa only [abs_zero] using hN.2.1
  have hline := J.hasProjectiveJetsOn.hasLineDerivAt J.open_domain hz (v, 0)
  have hd : HasDerivAt
      (fun t : ℝ => coefficientFamily D S C 0 s 0 (r, 0)
        ((C.referenceState, 0) + n08StateParameterSMul S t (v, 0)))
      (J.D 1 (C.referenceState, 0) (Fin.cons (v, 0) Fin.elim0)) 0 :=
    hasDerivAt_iff_tendsto_slope_zero.mpr hline
  have hd' : HasDerivAt
      (fun t : ℝ => coefficientFamily D S C 0 s 0 (r, 0) (C.referenceState + n08StateSMul S t v, 0))
      (J.D 1 (C.referenceState, 0) (Fin.cons (v, 0) Fin.elim0)) 0 := by
    simpa only [n08StateParameterSMul, n08StateSMul, n08RealSMul,
      Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero] using hd
  have ha := n08_coefficientA_jet_state_hasDerivAt hT hS hN C.referenceState v s 0 (r, 0)
  have hvalue : J.D 1 (C.referenceState, 0) (Fin.cons (v, 0) Fin.elim0) =
      iteratedDeriv s (fun t => D.w t * n08_stateLogProfile D S C v t) r := by
    simpa only [n08_stateProfile_reference hN.2.2.1, mixedDerivative, iteratedDeriv_zero]
      using hd'.unique ha
  have hbound := hJ (C.referenceState, 0) hz (Fin.cons (v, 0) Fin.elim0)
  simpa only [hvalue, sub_self, n08_oneHigh_first_product_zero] using hbound

end ContinuousFlexibility.Statements
