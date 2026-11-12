import ContinuousFlexibility.Analysis.N01cSpatialParameterComposition
import ContinuousFlexibility.Analysis.N01cCoefficientParameters
import ContinuousFlexibility.Analysis.N01cPolarMixedParameterJets
import ContinuousFlexibility.Analysis.N01cProfileMixedDerivatives
import ContinuousFlexibility.Analysis.N01cSpatialCoefficients

/-!
# All spatial jets of the actual coefficient family

The finite input contains the radius, the actual controlled profile and
its derivative, and the five actual q-dependent polar height fields.
Every spatial input jet has its already constructed genuine parameter
tower. Spatial Faà di Bruno composition therefore constructs, on the
same full N01b neighbourhood, the true parameter tower for every mixed
spatial derivative of every original coefficient.

The last construction subtracts the fixed actual reference field and
returns precisely the coefficientFamily appearing in the task statement.
The explicit spatial partition identity is retained for the subsequent
raw weighted estimates.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Function ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The eight actual primitive fields, including the varying radius. -/
def coefficientPrimitiveVector (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (z : AnnularState S × ℝ) (p : PolarPoint) :
    Fin 8 → ℝ :=
  Fin.cons p.1
    (Fin.cons (stateProfile D S C z.1 p.1)
      (Fin.cons (deriv (stateProfile D S C z.1) p.1)
        (fun i : Fin 5 => z.2 * stateUPolarInput S i z.1 p)))

/-- Explicit evaluations avoid numerical-index reduction inside nested
finite tuples. The last five slots are reached by three successor maps. -/
theorem coefficientPrimitiveVector_evaluations (D : ReferenceData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (z : AnnularState S × ℝ) (p : PolarPoint) :
    coefficientPrimitiveVector D S C z p 0 = p.1 ∧
    coefficientPrimitiveVector D S C z p 1 = stateProfile D S C z.1 p.1 ∧
    coefficientPrimitiveVector D S C z p 2 = deriv (stateProfile D S C z.1) p.1 ∧
    coefficientPrimitiveVector D S C z p 3 = z.2 * heightRadial (stateU S z.1) p ∧
    coefficientPrimitiveVector D S C z p 4 = z.2 * heightAngular (stateU S z.1) p ∧
    coefficientPrimitiveVector D S C z p 5 =
      z.2 * radialPartial (heightRadial (stateU S z.1)) p ∧
    coefficientPrimitiveVector D S C z p 6 =
      z.2 * radialPartial (heightAngular (stateU S z.1)) p ∧
    coefficientPrimitiveVector D S C z p 7 =
      z.2 * angularPartial (heightAngular (stateU S z.1)) p := by
  have htail (j : Fin 5) :
      coefficientPrimitiveVector D S C z p j.succ.succ.succ =
        z.2 * stateUPolarInput S j z.1 p := by
    simp only [coefficientPrimitiveVector, Fin.cons_succ]
  have hi3 : (0 : Fin 5).succ.succ.succ = (3 : Fin 8) := by decide
  have hi4 : (0 : Fin 4).succ.succ.succ.succ = (4 : Fin 8) := by decide
  have hi5 : (0 : Fin 3).succ.succ.succ.succ.succ = (5 : Fin 8) := by decide
  have hi6 : (0 : Fin 2).succ.succ.succ.succ.succ.succ = (6 : Fin 8) := by decide
  have hi7 : (0 : Fin 1).succ.succ.succ.succ.succ.succ.succ = (7 : Fin 8) := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [coefficientPrimitiveVector, Fin.cons_zero]
  · simp only [coefficientPrimitiveVector, Fin.cons_one, Fin.cons_zero]
  · have htwo :
        coefficientPrimitiveVector D S C z p (0 : Fin 6).succ.succ =
          deriv (stateProfile D S C z.1) p.1 := by
      simp only [coefficientPrimitiveVector, Fin.cons_succ, Fin.cons_zero]
    exact htwo
  · have h := htail (0 : Fin 5)
    rw [hi3] at h
    simpa only [stateUPolarInput, Fin.cases_succ, Fin.cases_zero] using h
  · have h := htail (0 : Fin 4).succ
    rw [hi4] at h
    simpa only [stateUPolarInput, Fin.cases_succ, Fin.cases_zero] using h
  · have h := htail (0 : Fin 3).succ.succ
    rw [hi5] at h
    simpa only [stateUPolarInput, Fin.cases_succ, Fin.cases_zero] using h
  · have h := htail (0 : Fin 2).succ.succ.succ
    rw [hi6] at h
    simpa only [stateUPolarInput, Fin.cases_succ, Fin.cases_zero] using h
  · have h := htail (0 : Fin 1).succ.succ.succ.succ
    rw [hi7] at h
    simpa only [stateUPolarInput, Fin.cases_succ, Fin.cases_zero] using h

/-- The discriminant expressed in the eight actual primitive inputs. -/
def coefficientPrimitiveDiscriminant (y : Fin 8 → ℝ) : ℝ :=
  heightDiscriminant (radialEnergy (y 1)) (y 1 + y 3) (y 4)

/-- The second denominator expressed in the same actual inputs. -/
def coefficientPrimitiveQ (y : Fin 8 → ℝ) : ℝ :=
  heightQ (radialEnergy (y 1)) (y 1 + y 3) (y 7)

/-- The scalar kernel of each of the three original coefficients. -/
def coefficientPrimitiveKernel (i : Fin 3) (y : Fin 8 → ℝ) : ℝ :=
  let E := radialEnergy (y 1)
  let Er := 2 * y 1 * y 2
  let k := y 1 + y 3
  let kr := y 2 + y 5
  let t := inverseDThreeHalves (coefficientPrimitiveDiscriminant y)
  if i = 0 then linearRadial E k (y 7) t else
  if i = 1 then linearMixed E (y 6) t else
    correctedAngular (y 0) E Er k (y 4) kr (y 6) (y 7) t

def coefficientPrimitiveDomain : Set (Fin 8 → ℝ) :=
  {y | y 0 ≠ 0 ∧ 0 < coefficientPrimitiveDiscriminant y ∧ coefficientPrimitiveQ y ≠ 0}

/-- One field of the original, unchanged coefficient triple. -/
def coefficientOriginalField (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (i : Fin 3) (z : AnnularState S × ℝ) :
    PolarPoint → ℝ :=
  if i = 0 then (originalCoefficients D S C z).a else
  if i = 1 then (originalCoefficients D S C z).b else (originalCoefficients D S C z).c

theorem isOpen_coefficientPrimitiveDomain : IsOpen coefficientPrimitiveDomain := by
  have hE : Continuous (fun y : Fin 8 → ℝ => radialEnergy (y 1)) :=
    continuous_const.add ((continuous_apply 1).pow 2)
  have hk : Continuous (fun y : Fin 8 → ℝ => y 1 + y 3) :=
    (continuous_apply 1).add (continuous_apply 3)
  have hD : Continuous coefficientPrimitiveDiscriminant :=
    (hE.mul (continuous_const.sub ((continuous_apply 4).pow 2))).sub (hk.pow 2)
  have hQ : Continuous coefficientPrimitiveQ := hk.add (hE.mul (continuous_apply 7))
  exact (isOpen_ne.preimage (continuous_apply 0)).inter
    ((isOpen_lt continuous_const hD).inter (isOpen_ne.preimage hQ))

/-- Smoothness of the outer kernels includes the spatially varying radius. -/
theorem contDiffOn_coefficientPrimitiveKernel (i : Fin 3) :
    ContDiffOn ℝ ∞ (coefficientPrimitiveKernel i) coefficientPrimitiveDomain := by
  intro y hy
  have hj (j : Fin 8) : ContDiffAt ℝ ∞ (fun v : Fin 8 → ℝ => v j) y :=
    contDiffAt_apply ℝ ℝ j y
  have hE : ContDiffAt ℝ ∞ (fun v : Fin 8 → ℝ => radialEnergy (v 1)) y :=
    contDiffAt_const.add ((hj 1).pow 2)
  have hEr : ContDiffAt ℝ ∞ (fun v : Fin 8 → ℝ => 2 * v 1 * v 2) y :=
    (contDiffAt_const.mul (hj 1)).mul (hj 2)
  have hk : ContDiffAt ℝ ∞ (fun v : Fin 8 → ℝ => v 1 + v 3) y :=
    (hj 1).add (hj 3)
  have hkr : ContDiffAt ℝ ∞ (fun v : Fin 8 → ℝ => v 2 + v 5) y :=
    (hj 2).add (hj 5)
  have hd : ContDiffAt ℝ ∞ coefficientPrimitiveDiscriminant y :=
    (hE.mul (contDiffAt_const.sub ((hj 4).pow 2))).sub (hk.pow 2)
  have hq : ContDiffAt ℝ ∞ coefficientPrimitiveQ y := hk.add (hE.mul (hj 7))
  have ht : ContDiffAt ℝ ∞ (fun v : Fin 8 → ℝ =>
      inverseDThreeHalves (coefficientPrimitiveDiscriminant v)) y :=
    contDiffAt_const.div (hd.mul (hd.sqrt hy.2.1.ne'))
      (mul_ne_zero hy.2.1.ne' (Real.sqrt_pos.mpr hy.2.1).ne')
  have hnum : ContDiffAt ℝ ∞ (fun v : Fin 8 → ℝ =>
      darbouxNumerator (v 0) (radialEnergy (v 1)) (2 * v 1 * v 2)
        (v 1 + v 3) (v 4) (v 2 + v 5) (v 6) (v 7)) y :=
    ((hq.mul hkr).sub ((hE.mul (hj 0)).mul ((hj 6).pow 2))).sub
      ((hEr.div_const 2).mul ((contDiffAt_const.sub ((hj 4).pow 2)).add (hk.mul (hj 7))))
  have hA : ContDiffAt ℝ ∞ (fun v : Fin 8 → ℝ =>
      linearRadial (radialEnergy (v 1)) (v 1 + v 3) (v 7)
        (inverseDThreeHalves (coefficientPrimitiveDiscriminant v))) y := hq.mul ht
  have hB : ContDiffAt ℝ ∞ (fun v : Fin 8 → ℝ =>
      linearMixed (radialEnergy (v 1)) (v 6)
        (inverseDThreeHalves (coefficientPrimitiveDiscriminant v))) y :=
    (hE.neg.mul (hj 6)).mul ht
  have hC : ContDiffAt ℝ ∞ (fun v : Fin 8 → ℝ =>
      correctedAngular (v 0) (radialEnergy (v 1)) (2 * v 1 * v 2)
        (v 1 + v 3) (v 4) (v 2 + v 5) (v 6) (v 7)
        (inverseDThreeHalves (coefficientPrimitiveDiscriminant v))) y :=
    ((((hE.mul hkr).sub ((hEr.mul hk).div_const 2)).mul ht).div (hj 0) hy.1).sub
      ((hE.mul ((hnum.mul ht).div (hj 0) hy.1)).div hq hy.2.2)
  unfold coefficientPrimitiveKernel
  by_cases hi : i = 0
  · simpa only [if_pos hi] using hA.contDiffWithinAt
  · by_cases hi' : i = 1
    · simpa only [if_neg hi, if_pos hi'] using hB.contDiffWithinAt
    · simpa only [if_neg hi, if_neg hi'] using hC.contDiffWithinAt

/-- The actual state polar fields are spatially smooth in the open annulus. -/
theorem contDiffOn_stateUPolarInput
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) (hD : 0 < D.a)
    (x : AnnularState S) (i : Fin 5) :
    ContDiffOn ℝ ∞ (stateUPolarInput S i x) (annularOpen D) := by
  intro p hp
  have hr : p.1 ≠ 0 := (hD.trans hp.1.1).ne'
  have hf : ContDiffAt ℝ ∞ (stateU S x) p := (contDiff_stateU hT hS x).contDiffAt
  have hk : ContDiffAt ℝ ∞ (heightRadial (stateU S x)) p :=
    contDiffAt_heightRadial hf (by simp)
  have hθ : ContDiffAt ℝ ∞ (heightAngular (stateU S x)) p :=
    contDiffAt_heightAngular hf (by simp) hr
  have hkr : ContDiffAt ℝ ∞ (radialPartial (heightRadial (stateU S x))) p :=
    contDiffAt_radialPartial hk (by simp)
  have hpr : ContDiffAt ℝ ∞ (radialPartial (heightAngular (stateU S x))) p :=
    contDiffAt_radialPartial hθ (by simp)
  have hpθ : ContDiffAt ℝ ∞ (angularPartial (heightAngular (stateU S x))) p :=
    contDiffAt_angularPartial hθ (by simp)
  refine Fin.cases hk.contDiffWithinAt ?_ i
  refine Fin.cases hθ.contDiffWithinAt ?_
  refine Fin.cases hkr.contDiffWithinAt ?_
  refine Fin.cases hpr.contDiffWithinAt ?_
  refine Fin.cases hpθ.contDiffWithinAt ?_
  exact fun j => Fin.elim0 j

theorem contDiffOn_coefficientPrimitiveVector
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (z : AnnularState S × ℝ) :
    ContDiffOn ℝ ∞ (coefficientPrimitiveVector D S C z) (annularOpen D) := by
  obtain ⟨K, hK⟩ := hA.1.1
  have hw := contDiff_stateProfile_of_partA hS hT hA z.1
  have hwr : ContDiff ℝ ∞ (deriv (stateProfile D S C z.1)) :=
    (contDiff_infty_iff_deriv.mp hw).2
  apply contDiffOn_pi.mpr
  refine Fin.cases contDiff_fst.contDiffOn ?_
  refine Fin.cases (hw.comp contDiff_fst).contDiffOn ?_
  refine Fin.cases (hwr.comp contDiff_fst).contDiffOn ?_
  intro i
  exact contDiffOn_const.mul (contDiffOn_stateUPolarInput hT hS hK.1.1 z.1 i)

set_option backward.isDefEq.respectTransparency true in
/-- Every component of the primitive vector has genuine parameter towers
at every ordinary mixed spatial order. -/
def n01_coefficientPrimitiveMixedSmoothDirections
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (p : PolarPoint) (hp : p ∈ annularOpen D)
    (a b : ℕ) :
    ∀ j : Fin 8, SmoothDirections univ (fun z : AnnularState S × ℝ =>
      mixedDerivative a b (fun q => coefficientPrimitiveVector D S C z q j) p) := by
  letI : IsTopologicalAddGroup (AnnularState S × ℝ) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S × ℝ) := inferInstance
  have hD : RadialProfileGeometry D := by
    obtain ⟨K, hK⟩ := hA.1.1
    exact hK.1
  have hχ : ContDiff ℝ ∞ D.chi := hA.1.2.2.2.1.1
  have hr : p.1 ≠ 0 := (hD.1.trans hp.1.1).ne'
  let L : (AnnularState S × ℝ) →L[ℝ] AnnularState S :=
    ContinuousLinearMap.fst ℝ (AnnularState S) ℝ
  let Jr : SmoothDirections univ (fun _ : AnnularState S × ℝ =>
      mixedDerivative a b (fun q : PolarPoint => q.1) p) :=
    smoothDirections_constant isOpen_univ _
  have Jw : SmoothDirections univ (fun z : AnnularState S × ℝ =>
      mixedDerivative a b (fun q : PolarPoint => stateProfile D S C z.1 q.1) p) := by
    by_cases hb : b = 0
    · let J := smoothDirections_precompCLM
        (stateProfileRadialJetSmoothDirections hS hT hA.1.1 hD hA.2.2.1 hχ a p.1 hp.1) L
      refine J.congr (fun z _ => ?_)
      simp only [mixedDerivative_radialFunction, hb, ite_true,
        Function.comp_apply, L, ContinuousLinearMap.coe_fst']
    · let J : SmoothDirections univ (fun _ : AnnularState S × ℝ => (0 : ℝ)) :=
        smoothDirections_constant isOpen_univ 0
      exact J.congr (fun _ _ => by
        simp only [mixedDerivative_radialFunction, if_neg hb])
  have Jwr : SmoothDirections univ (fun z : AnnularState S × ℝ =>
      mixedDerivative a b (fun q : PolarPoint => deriv (stateProfile D S C z.1) q.1) p) := by
    by_cases hb : b = 0
    · let J := smoothDirections_precompCLM
        (stateProfileRadialJetSmoothDirections hS hT hA.1.1 hD hA.2.2.1 hχ
          (a + 1) p.1 hp.1) L
      refine J.congr (fun z _ => ?_)
      simp only [mixedDerivative_radialFunction, hb, ite_true, iteratedDeriv_succ',
        Function.comp_apply, L, ContinuousLinearMap.coe_fst']
    · let J : SmoothDirections univ (fun _ : AnnularState S × ℝ => (0 : ℝ)) :=
        smoothDirections_constant isOpen_univ 0
      exact J.congr (fun _ _ => by
        simp only [mixedDerivative_radialFunction, if_neg hb])
  have Jheight : ∀ i : Fin 5, SmoothDirections univ (fun z : AnnularState S × ℝ =>
      mixedDerivative a b (fun q => z.2 * stateUPolarInput S i z.1 q) p) :=
    fun i => (qStateUPolarMixedJetSmoothDirections hT hS a b p hp hr i).congr
      (fun z _ => (mixedDerivative_const_mul z.2 (stateUPolarInput S i z.1) a b p).symm)
  exact Fin.cases Jr (Fin.cases Jw (Fin.cases Jwr Jheight))

theorem coefficientPrimitiveDiscriminant_eq
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (z : AnnularState S × ℝ) (p : PolarPoint) :
    coefficientPrimitiveDiscriminant (coefficientPrimitiveVector D S C z p) =
      polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p := by
  obtain ⟨_, h1, _, h3, h4, _, _, _⟩ :=
    coefficientPrimitiveVector_evaluations D S C z p
  simp only [coefficientPrimitiveDiscriminant, h1, h3, h4,
    polarDiscriminant, profileEnergy,
    heightRadial_stateHeight hS hT hA z p, heightAngular_stateHeight hS hT hA z p]

theorem coefficientPrimitiveQ_eq
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (z : AnnularState S × ℝ)
    {p : PolarPoint} (hr : p.1 ≠ 0) :
    coefficientPrimitiveQ (coefficientPrimitiveVector D S C z p) =
      heightQ (profileEnergy (stateProfile D S C z.1) p)
        (heightRadial (stateHeight D S C z) p)
        (angularPartial (heightAngular (stateHeight D S C z)) p) := by
  obtain ⟨_, h1, _, h3, _, _, _, h7⟩ :=
    coefficientPrimitiveVector_evaluations D S C z p
  simp only [coefficientPrimitiveQ, h1, h3, h7,
    profileEnergy, heightRadial_stateHeight hS hT hA z p,
    angularPartial_heightAngular_stateHeight hS hT hA z hr]

/-- Substitution of the real height and profile identities gives exactly
the original coefficient, for every nonzero physical radius. -/
theorem coefficientPrimitiveKernel_eq_original
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (i : Fin 3) (z : AnnularState S × ℝ)
    {p : PolarPoint} (hr : p.1 ≠ 0) :
    coefficientPrimitiveKernel i (coefficientPrimitiveVector D S C z p) =
      coefficientOriginalField D S C i z p := by
  have hEr := radialPartial_profileEnergy (x := p)
    ((contDiff_stateProfile_of_partA hS hT hA z.1).differentiable (by simp) p.1)
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ :=
    coefficientPrimitiveVector_evaluations D S C z p
  unfold coefficientPrimitiveKernel coefficientOriginalField
  split_ifs <;>
    simp only [h0, h1, h2, h3, h4, h5, h6, h7,
      originalCoefficients, polarLinearA, polarLinearB,
      polarCorrectedC, polarScale, coefficientPrimitiveDiscriminant,
      polarDiscriminant, hEr, profileEnergy,
      heightRadial_stateHeight hS hT hA z p,
      heightAngular_stateHeight hS hT hA z p,
      radialPartial_heightRadial_stateHeight hS hT hA z p,
      radialPartial_heightAngular_stateHeight hS hT hA z hr,
      angularPartial_heightAngular_stateHeight hS hT hA z hr]

theorem coefficientPrimitiveVector_mapsTo
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε) :
    MapsTo (coefficientPrimitiveVector D S C z) (annularOpen D)
      coefficientPrimitiveDomain := by
  obtain ⟨K, hK⟩ := hA.1.1
  intro p hp
  have hr : p.1 ≠ 0 := (hK.1.1.trans hp.1.1).ne'
  have hden := n01PartB_denominators_pos hK.1 hS hA.2.1 hB hz hp
  refine ⟨?_, ?_, ?_⟩
  · simpa only [coefficientPrimitiveVector, Fin.cons_zero] using hr
  · rw [coefficientPrimitiveDiscriminant_eq hS hT hA]
    exact hden.2.2
  · rw [coefficientPrimitiveQ_eq hS hT hA z hr]
    exact hden.2.1.ne'

theorem contDiffOn_coefficientOriginalField
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    (i : Fin 3) {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε) :
    ContDiffOn ℝ ∞ (coefficientOriginalField D S C i z) (annularOpen D) := by
  have h := n01_originalCoefficients_contDiffOn hS hT hA hB hz
  by_cases hi : i = 0
  · simpa only [coefficientOriginalField, if_pos hi] using h.1
  · by_cases hi' : i = 1
    · simpa only [coefficientOriginalField, if_neg hi, if_pos hi'] using h.2.1
    · simpa only [coefficientOriginalField, if_neg hi, if_neg hi'] using h.2.2

/-- The actual spatial derivative equals its finite ordered-partition
expression in genuine primitive spatial jets. -/
theorem coefficientOriginalField_mixedDerivative_eq_partitions
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    (i : Fin 3) (a b : ℕ) {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    mixedDerivative a b (coefficientOriginalField D S C i z) p =
      ∑ c : OrderedFinpartition (a + b),
        iteratedFDeriv ℝ c.length (coefficientPrimitiveKernel i)
          (coefficientPrimitiveVector D S C z p)
          (fun j => iteratedFDeriv ℝ (c.partSize j)
            (coefficientPrimitiveVector D S C z) p
            (fun l => cylinderBasisVector (cylinderMixedWord a b (c.emb j l)))) := by
  obtain ⟨K, hK⟩ := hA.1.1
  have hΩ : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hu := contDiffOn_coefficientPrimitiveVector hS hT hA z
  have hg := contDiffOn_coefficientPrimitiveKernel i
  have hm := coefficientPrimitiveVector_mapsTo hS hT hA hB hz
  have he : EqOn (coefficientPrimitiveKernel i ∘ coefficientPrimitiveVector D S C z)
      (coefficientOriginalField D S C i z) (annularOpen D) :=
    fun q hq => coefficientPrimitiveKernel_eq_original hS hT hA i z
      (hK.1.1.trans hq.1.1).ne'
  rw [← mixedDerivative_eq_of_eqOn hΩ (hg.comp hu hm)
    (contDiffOn_coefficientOriginalField hS hT hA hB i hz) he a b hp]
  exact mixedDerivative_comp_ordered hΩ isOpen_coefficientPrimitiveDomain hu hg hm a b hp

set_option backward.isDefEq.respectTransparency true in
/-- Every actual original coefficient has a genuine parameter tower after
arbitrary mixed spatial differentiation, on the original full neighbourhood. -/
def n01_originalCoefficientMixedSmoothDirections
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    (i : Fin 3) (a b : ℕ) (p : PolarPoint) (hp : p ∈ annularOpen D) :
    SmoothDirections (stateNeighborhood S C base ε)
      (fun z => mixedDerivative a b (coefficientOriginalField D S C i z) p) := by
  letI : IsTopologicalAddGroup (AnnularState S × ℝ) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S × ℝ) := inferInstance
  have hD : RadialProfileGeometry D := by
    obtain ⟨K, hK⟩ := hA.1.1
    exact hK.1
  let U := stateNeighborhood S C base ε
  have hU : IsOpen U := isOpen_stateNeighborhood S C base ε
  have hΩ : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  let u : (AnnularState S × ℝ) → PolarPoint → Fin 8 → ℝ := coefficientPrimitiveVector D S C
  let g : (Fin 8 → ℝ) → ℝ := coefficientPrimitiveKernel i
  have hu : ∀ z ∈ U, ContDiffOn ℝ ∞ (u z) (annularOpen D) :=
    fun z _ => contDiffOn_coefficientPrimitiveVector hS hT hA z
  have hg : ContDiffOn ℝ ∞ g coefficientPrimitiveDomain :=
    contDiffOn_coefficientPrimitiveKernel i
  have hm : ∀ z ∈ U, MapsTo (u z) (annularOpen D) coefficientPrimitiveDomain :=
    fun _ hz => coefficientPrimitiveVector_mapsTo hS hT hA hB hz
  let J : ∀ c d : ℕ, ∀ j : Fin 8,
      SmoothDirections U (fun z => mixedDerivative c d (fun q => u z q j) p) :=
    fun c d j => (n01_coefficientPrimitiveMixedSmoothDirections hS hT hA p hp c d j).restrict
      hU (subset_univ _)
  let K : SmoothDirections U (fun z => mixedDerivative a b (g ∘ u z) p) :=
    smoothDirections_mixedDerivative_comp (X := AnnularState S × ℝ)
      hU hΩ isOpen_coefficientPrimitiveDomain hu hg hm p hp J a b
  refine K.congr (fun z hz => ?_)
  exact mixedDerivative_eq_of_eqOn hΩ (hg.comp (hu z hz) (hm z hz))
    (contDiffOn_coefficientOriginalField hS hT hA hB i hz)
    (fun q hq => coefficientPrimitiveKernel_eq_original hS hT hA i z
      (hD.1.trans hq.1.1).ne') a b hp

set_option backward.isDefEq.respectTransparency true in
/-- The tower required in CoefficientFamilyTameBounds exists for every
spatial index and interior point, with the same N01b base and radius.
Only the primitive geometry and positive radius hypotheses are used. -/
def n01_coefficientFamilySmoothDirections
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε) (hε : 0 < ε)
    (i : Fin 3) (a b : ℕ) (p : PolarPoint) (hp : p ∈ annularOpen D) :
    SmoothDirections (stateNeighborhood S C base ε) (coefficientFamily D S C i a b p) := by
  letI : IsTopologicalAddGroup (AnnularState S × ℝ) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S × ℝ) := inferInstance
  have href : (C.referenceState, (0 : ℝ)) ∈ stateNeighborhood S C base ε :=
    reference_mem_stateNeighborhood S C base hε
  have hΩ : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  let f : (AnnularState S × ℝ) → PolarPoint → ℝ := coefficientOriginalField D S C i
  have hf : ∀ z ∈ stateNeighborhood S C base ε,
      ContDiffOn ℝ ∞ (f z) (annularOpen D) :=
    fun _ hz => contDiffOn_coefficientOriginalField hS hT hA hB i hz
  let J := n01_originalCoefficientMixedSmoothDirections hS hT hA hB i a b p hp
  let K := smoothDirections_mixedDifference (X := AnnularState S × ℝ)
    hΩ hf (C.referenceState, 0) href a b p hp J
  exact K.congr (fun _ _ => rfl)

end ContinuousFlexibility.Statements
