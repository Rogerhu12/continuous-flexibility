import ContinuousFlexibility.Analysis.N01cHeightProductBounds

/-!
# All spatial jets of the actual polar-height parameter inputs

Every ordinary mixed spatial jet of the five polar height inputs is a
genuine continuous-linear functional of the state. The normalized angular
input uses the finite reciprocal-radius Leibniz expansion. Its two further
partials shift the actual mixed-derivative indices on the open nonzero
radius region.

Multiplication by q gives the genuine quadratic parameter tower at every
spatial order. Tower uniqueness and the previously proved weighted
polar-jet estimate retain one high factor, H^(3/4), and a spatial loss of
four, independently of the parameter order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- Identify any genuine tower for q times a linear input with its
explicit quadratic tower, without unfolding a composition construction. -/
theorem qLinear_D_eq (L : E →L[ℝ] ℝ) {U : Set (E × ℝ)} {f : E × ℝ → ℝ}
    (J : SmoothDirections U f) (hformula : ∀ z ∈ U, f z = z.2 * L z.1)
    (n : ℕ) (z : E × ℝ) (hz : z ∈ U) (v : Fin n → (E × ℝ)) :
    J.D n z v = (smoothDirections_qLinear L).D n z v := by
  let Q : E × ℝ →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ E ℝ
  let A : E × ℝ →L[ℝ] ℝ := L.comp (ContinuousLinearMap.fst ℝ E ℝ)
  have hproduct : ∀ y ∈ U, f y = Q y * A y := by
    intro y hy
    simpa only [Q, A, ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst'] using hformula y hy
  exact scalarLinearProduct_D_eq Q A J hproduct n z hz v

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

private theorem finite_scalarCLM_sum_apply
    {E I : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] [Fintype I]
    (c : I → ℝ) (L : I → E →L[ℝ] ℝ) (x : E) :
    (∑ i, c i • L i) x = ∑ i, c i * L i x := by
  simp only [sum_apply, smul_apply, smul_eq_mul]

private theorem contDiff_angularPartial_for_polarJets
    {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (angularPartial f) := by
  have hzero : mixedDerivative 0 0 f = f := by
    funext q
    simp only [mixedDerivative, iteratedDeriv_zero]
  have he : angularPartial f = mixedDerivative 0 1 f :=
    (congrArg angularPartial hzero.symm).trans (angularPartial_mixedDerivative hf 0 0)
  rw [he]
  exact contDiff_mixedDerivative hf 0 1

/-- The exact finite linear combination for an arbitrary ordinary mixed
jet of the normalized angular height input. -/
def stateUHeightAngularMixedJetCLM
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (a b : ℕ) (p : PolarPoint) (hp : p ∈ annularOpen D) :
    AnnularState S →L[ℝ] ℝ :=
  ∑ i : Fin (a + 1),
    ((a.choose i.val : ℝ) * iteratedDeriv i.val (fun r : ℝ => r⁻¹) p.1) •
      stateUJetCLM hT hS (a - i.val) (b + 1) p hp

set_option backward.isDefEq.respectTransparency true in
theorem stateUHeightAngularMixedJetCLM_apply
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (a b : ℕ) (p : PolarPoint) (hp : p ∈ annularOpen D) (hr : p.1 ≠ 0)
    (x : AnnularState S) :
    stateUHeightAngularMixedJetCLM hT hS a b p hp x =
      mixedDerivative a b (heightAngular (stateU S x)) p := by
  let c : Fin (a + 1) → ℝ := fun i =>
    (a.choose i.val : ℝ) * iteratedDeriv i.val (fun r : ℝ => r⁻¹) p.1
  let L : Fin (a + 1) → AnnularState S →L[ℝ] ℝ := fun i =>
    stateUJetCLM hT hS (a - i.val) (b + 1) p hp
  have hf : ContDiff ℝ ∞ (stateU S x) :=
    physical_height_with_cutoff_contDiff hT hS
      (by norm_num : (0 : ℝ) < 3 / 4) x.1.1 x.1.2
  have hθ := contDiff_angularPartial_for_polarJets hf
  have hinv : ContDiffAt ℝ ∞ (fun r : ℝ => r⁻¹) p.1 :=
    contDiffAt_id.inv hr
  have hfield : heightAngular (stateU S x) =
      (fun q => q.1⁻¹ * angularPartial (stateU S x) q) := by
    funext q
    exact (div_eq_mul_inv _ _).trans (mul_comm _ _)
  have hformula :
      mixedDerivative a b (heightAngular (stateU S x)) p =
        ∑ i : Fin (a + 1), c i * mixedDerivative (a - i.val) (b + 1) (stateU S x) p := by
    calc
      _ = mixedDerivative a b
          (fun q => q.1⁻¹ * angularPartial (stateU S x) q) p :=
        congrArg (fun f : PolarPoint → ℝ => mixedDerivative a b f p) hfield
      _ = ∑ i : Fin (a + 1), c i *
          mixedDerivative (a - i.val) b (angularPartial (stateU S x)) p :=
        mixedDerivative_radial_mul hθ a b p hinv
      _ = _ := Finset.sum_congr rfl fun i _ =>
        congrArg (fun t : ℝ => c i * t)
          (mixedDerivative_angularPartial isOpen_univ hf.contDiffOn
            (a - i.val) b (mem_univ p))
  calc
    _ = ∑ i : Fin (a + 1), c i * L i x := finite_scalarCLM_sum_apply c L x
    _ = ∑ i : Fin (a + 1), c i *
        mixedDerivative (a - i.val) (b + 1) (stateU S x) p :=
      Finset.sum_congr rfl fun i _ =>
        congrArg (fun t : ℝ => c i * t)
          (stateUJetCLM_apply (D := D) (T := T) (S := S) hT hS
            (a - i.val) (b + 1) p hp x)
    _ = mixedDerivative a b (heightAngular (stateU S x)) p := hformula.symm

/-- All five higher spatial input functionals, in the original polar order. -/
def stateUPolarMixedJetCLM
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (a b : ℕ) (p : PolarPoint) (hp : p ∈ annularOpen D) :
    Fin 5 → AnnularState S →L[ℝ] ℝ :=
  Fin.cases (stateUJetCLM hT hS (a + 1) b p hp)
    (Fin.cases (stateUHeightAngularMixedJetCLM hT hS a b p hp)
      (Fin.cases (stateUJetCLM hT hS (a + 1 + 1) b p hp)
        (Fin.cases (stateUHeightAngularMixedJetCLM hT hS (a + 1) b p hp)
          (Fin.cases (stateUHeightAngularMixedJetCLM hT hS a (b + 1) p hp)
            (fun i => Fin.elim0 i)))))

set_option backward.isDefEq.respectTransparency true in
/-- The functionals evaluate the actual mixed spatial jets, including
the derivatives of the reciprocal radius in both normalized inputs. -/
theorem stateUPolarMixedJetCLM_apply
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (a b : ℕ) (p : PolarPoint) (hp : p ∈ annularOpen D) (hr : p.1 ≠ 0)
    (i : Fin 5) (x : AnnularState S) :
    stateUPolarMixedJetCLM hT hS a b p hp i x =
      mixedDerivative a b (stateUPolarInput S i x) p := by
  have hf : ContDiff ℝ ∞ (stateU S x) :=
    physical_height_with_cutoff_contDiff hT hS
      (by norm_num : (0 : ℝ) < 3 / 4) x.1.1 x.1.2
  have hk : ContDiff ℝ ∞ (heightRadial (stateU S x)) := by
    have he : heightRadial (stateU S x) = mixedDerivative 1 0 (stateU S x) :=
      funext (heightRadial_eq_firstMixedJet hf)
    rw [he]
    exact contDiff_mixedDerivative hf 1 0
  let V : Set PolarPoint := {q | q.1 ≠ 0}
  have hV : IsOpen V := isOpen_ne.preimage continuous_fst
  have hpV : p ∈ V := hr
  have hangular : ContDiffOn ℝ ∞ (heightAngular (stateU S x)) V :=
    (contDiff_angularPartial_for_polarJets hf).contDiffOn.div contDiffOn_fst
      (fun q hq => hq)
  have hradial :
      mixedDerivative a b (heightRadial (stateU S x)) p =
        mixedDerivative (a + 1) b (stateU S x) p :=
    mixedDerivative_radialPartial isOpen_univ hf.contDiffOn a b (mem_univ p)
  have hradialRadial :
      mixedDerivative a b (radialPartial (heightRadial (stateU S x))) p =
        mixedDerivative (a + 1 + 1) b (stateU S x) p :=
    (mixedDerivative_radialPartial isOpen_univ hk.contDiffOn a b (mem_univ p)).trans
      (mixedDerivative_radialPartial isOpen_univ hf.contDiffOn (a + 1) b (mem_univ p))
  have hradialAngular :
      mixedDerivative a b (radialPartial (heightAngular (stateU S x))) p =
        mixedDerivative (a + 1) b (heightAngular (stateU S x)) p :=
    mixedDerivative_radialPartial hV hangular a b hpV
  have hangularAngular :
      mixedDerivative a b (angularPartial (heightAngular (stateU S x))) p =
        mixedDerivative a (b + 1) (heightAngular (stateU S x)) p :=
    mixedDerivative_angularPartial hV hangular a b hpV
  refine Fin.cases
    ((stateUJetCLM_apply hT hS (a + 1) b p hp x).trans hradial.symm) ?_ i
  refine Fin.cases (stateUHeightAngularMixedJetCLM_apply hT hS a b p hp hr x) ?_
  refine Fin.cases
    ((stateUJetCLM_apply hT hS (a + 1 + 1) b p hp x).trans hradialRadial.symm) ?_
  refine Fin.cases
    ((stateUHeightAngularMixedJetCLM_apply hT hS (a + 1) b p hp hr x).trans
      hradialAngular.symm) ?_
  refine Fin.cases
    ((stateUHeightAngularMixedJetCLM_apply hT hS a (b + 1) p hp hr x).trans
      hangularAngular.symm) ?_
  exact fun j => Fin.elim0 j

set_option backward.isDefEq.respectTransparency true in
/-- The actual state-parameter tower of every higher polar input. -/
def stateUPolarMixedJetSmoothDirections
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (a b : ℕ) (p : PolarPoint) (hp : p ∈ annularOpen D) (hr : p.1 ≠ 0) (i : Fin 5) :
    SmoothDirections univ (fun x : AnnularState S =>
      mixedDerivative a b (stateUPolarInput S i x) p) :=
  (smoothDirectionsLinear (stateUPolarMixedJetCLM hT hS a b p hp i)).congr
    (fun x _ => stateUPolarMixedJetCLM_apply hT hS a b p hp hr i x)

set_option backward.isDefEq.respectTransparency true in
/-- The actual joint-parameter tower after multiplication by q. -/
def qStateUPolarMixedJetSmoothDirections
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (a b : ℕ) (p : PolarPoint) (hp : p ∈ annularOpen D) (hr : p.1 ≠ 0) (i : Fin 5) :
    SmoothDirections univ (fun z : AnnularState S × ℝ =>
      z.2 * mixedDerivative a b (stateUPolarInput S i z.1) p) :=
  (smoothDirections_qLinear (E := AnnularState S) (stateUPolarMixedJetCLM hT hS a b p hp i)).congr
    (fun z _ => congrArg (fun t : ℝ => z.2 * t)
      (stateUPolarMixedJetCLM_apply hT hS a b p hp hr i z.1))

set_option backward.isDefEq.respectTransparency true in
/-- Any genuine tower of the same spatial input has exactly the
quadratic tower just constructed, at every parameter order. -/
theorem qStateUPolarMixedJet_D_eq
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (a b : ℕ) (p : PolarPoint) (hp : p ∈ annularOpen D) (hr : p.1 ≠ 0) (i : Fin 5)
    {U : Set (AnnularState S × ℝ)}
    (J : SmoothDirections U (fun z => z.2 * mixedDerivative a b (stateUPolarInput S i z.1) p))
    (k : ℕ) (z : AnnularState S × ℝ) (hz : z ∈ U) (v : Fin k → (AnnularState S × ℝ)) :
    J.D k z v = (qStateUPolarMixedJetSmoothDirections hT hS a b p hp hr i).D k z v := by
  letI : IsTopologicalAddGroup (AnnularState S) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S) := inferInstance
  let L : AnnularState S →L[ℝ] ℝ := stateUPolarMixedJetCLM hT hS a b p hp i
  have hformula (y : AnnularState S × ℝ) (_hy : y ∈ U) :
      y.2 * mixedDerivative a b (stateUPolarInput S i y.1) p = y.2 * L y.1 :=
    congrArg (fun t : ℝ => y.2 * t)
      (stateUPolarMixedJetCLM_apply hT hS a b p hp hr i y.1).symm
  exact qLinear_D_eq (E := AnnularState S) L J hformula k z hz v

set_option backward.isDefEq.respectTransparency true in
/-- All physical mixed spatial jets of all five q-dependent polar inputs
share a one-high weighted bound with fixed loss four for every parameter
order. The actual H exponent and E0 power are retained. -/
theorem stateU_qPolarMixedJets_oneHigh_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hD : 0 < D.a) (s : ℕ) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ i : Fin 5, ∀ a b : ℕ, a + b ≤ s →
      ∀ p ∈ annularOpen D, ∀ U : Set (AnnularState S × ℝ),
      ∀ J : SmoothDirections U
        (fun z => z.2 * mixedDerivative a b (stateUPolarInput S i z.1) p),
      ∀ k base : ℕ, ∀ x0 : AnnularState S, ∀ z ∈ U, |z.2| ≤ 1 →
      ∀ v : Fin k → (AnnularState S × ℝ),
        |J.D k z v| ≤ C * T.E0 p.1 ^ A * T.H p.1 ^ (3 / 4 : ℝ) *
          (1 + stateGrading S (s + 4) x0) *
          oneHighVariationWeight (pairGrading (stateGrading S) realGrading)
            base (s + 4) (z - (x0, 0)) v := by
  letI : IsTopologicalAddGroup (AnnularState S) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S) := inferInstance
  obtain ⟨C, A, hC, hA, hraw⟩ := stateU_polarMixedJets_le_E0_stateGrading hT hS hD s
  refine ⟨C, A, hC, hA, fun i a b hab p hp U J k base x0 z hz hq v => ?_⟩
  have hr : p.1 ≠ 0 := (hD.trans hp.1.1).ne'
  let L : AnnularState S →L[ℝ] ℝ := stateUPolarMixedJetCLM hT hS a b p hp i
  have hW : 0 ≤ C * T.E0 p.1 ^ A * T.H p.1 ^ (3 / 4 : ℝ) :=
    mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (hT.2.1 _ hp.1).2.2.1.le _))
      (Real.rpow_nonneg (hT.2.1 _ hp.1).2.1.le _)
  have hinput (x : AnnularState S) :
      |mixedDerivative a b (stateUPolarInput S i x) p| ≤
        C * T.E0 p.1 ^ A * T.H p.1 ^ (3 / 4 : ℝ) * stateGrading S (s + 4) x := by
    have hfive := hraw x a b hab p hp
    refine Fin.cases hfive.1 ?_ i
    refine Fin.cases hfive.2.1 ?_
    refine Fin.cases hfive.2.2.1 ?_
    refine Fin.cases hfive.2.2.2.1 ?_
    refine Fin.cases hfive.2.2.2.2 ?_
    exact fun j => Fin.elim0 j
  have hL (x : AnnularState S) :
      |L x| ≤ (C * T.E0 p.1 ^ A * T.H p.1 ^ (3 / 4 : ℝ)) *
        stateGrading S (s + 4) x := by
    calc
      _ = |mixedDerivative a b (stateUPolarInput S i x) p| :=
        congrArg abs (stateUPolarMixedJetCLM_apply hT hS a b p hp hr i x)
      _ ≤ _ := hinput x
  have hformula (y : AnnularState S × ℝ) (_hy : y ∈ U) :
      y.2 * mixedDerivative a b (stateUPolarInput S i y.1) p = y.2 * L y.1 :=
    congrArg (fun t : ℝ => y.2 * t)
      (stateUPolarMixedJetCLM_apply hT hS a b p hp hr i y.1).symm
  exact qLinear_oneHigh_bound (E := AnnularState S) (stateGrading S) L
    base (s + 4) hW hL J hformula k x0 z hz hq v

end ContinuousFlexibility.Statements
