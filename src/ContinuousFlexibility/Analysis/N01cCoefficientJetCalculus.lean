import ContinuousFlexibility.Analysis.TameJetComposition
import ContinuousFlexibility.Analysis.TameElementaryCalculus
import ContinuousFlexibility.Statements.Nonlinear
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Genuine parameter jets of the scalar coefficient formulas

The intermediate space in the coefficient calculation is a finite tuple of
real scalar jets.  A smooth map on that normed space can be composed with an
actual `SmoothDirections` tower on the original, possibly nonnormable, state
space.  The tower is the existing ordered-partition tower; its derivative
recurrence follows from the ordinary Fréchet chain rule and the proved
variable-multilinear curve rule.

We apply this calculus to the existing `linearRadial`, `linearMixed`, and
`correctedAngular` formulas, with their actual `inverseDThreeHalves` scale.
The only denominator hypotheses are positivity of the height discriminant
and nonvanishing of `heightQ`.  The final constructor specializes directly to
`originalCoefficients`.  These are parameter-smoothness results at a fixed
spatial point, not spatially differentiated or quantitative tame estimates.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function
open ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

section NormedOuterCalculus

variable {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Evaluation of a genuine Fréchet jet along a differentiable curve has
the next Fréchet jet as its derivative, with the curve velocity first. -/
private theorem hasProjectiveCurveDerivAt_iteratedFDeriv
    {g : Y → Z} {c : ℝ → Y} {dc : Y} {t : ℝ}
    (hc : HasDerivAt c dc t) (hg : ContDiffAt ℝ ∞ g (c t))
    (n : ℕ) (v : Fin n → Y) :
    HasProjectiveCurveDerivAt (fun s => iteratedFDeriv ℝ n g (c s) v)
      (iteratedFDeriv ℝ (n + 1) g (c t) (Fin.cons dc v)) t := by
  have hj : DifferentiableAt ℝ (iteratedFDeriv ℝ n g) (c t) :=
    hg.differentiableAt_iteratedFDeriv
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)
  have hd := (hj.continuousMultilinear_apply_const v).hasFDerivAt.comp_hasDerivAt t hc
  rw [fderiv_continuousMultilinear_apply_const_apply hj] at hd
  have hnext : iteratedFDeriv ℝ (n + 1) g (c t) (Fin.cons dc v) =
      fderiv ℝ (iteratedFDeriv ℝ n g) (c t) dc v := by
    simp only [iteratedFDeriv_succ_apply_left, Fin.cons_zero, Fin.tail_cons]
  rw [← hnext] at hd
  exact hd.tendsto_slope_zero

/-- A smooth map on an open normed domain has its actual Fréchet derivatives
as a verified projective directional tower. -/
theorem hasProjectiveJetsOn_of_contDiffOn {V : Set Y} {g : Y → Z}
    (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V) :
    HasProjectiveJetsOn g (fun n => iteratedFDeriv ℝ n g) V := by
  refine ⟨?_, ?_, ?_⟩
  · intro x _
    exact iteratedFDeriv_zero_apply _
  · intro n
    have hj : ContinuousOn (iteratedFDeriv ℝ n g) V := by
      intro x hx
      exact ((hg.contDiffAt (hV.mem_nhds hx)).continuousAt_iteratedFDeriv
        (by simp)).continuousWithinAt
    exact (hj.comp continuous_fst.continuousOn (fun _ hp => hp.1)).eval
      continuous_snd.continuousOn
  · intro n x hx w v
    have hc : HasDerivAt (fun t : ℝ => x + t • w) w 0 := by
      simpa only [id_eq, one_smul] using
        ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x
    have hgx : ContDiffAt ℝ ∞ g (x + (0 : ℝ) • w) := by
      simpa only [zero_smul, add_zero] using hg.contDiffAt (hV.mem_nhds hx)
    simpa only [HasProjectiveLineDerivAt, zero_smul, add_zero] using
      hasProjectiveCurveDerivAt_iteratedFDeriv hc hgx n v

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

private theorem compositionTerm_hasLineDerivAt_normed
    {U : Set X} {V : Set Y} {u : X → Y} {g : Y → Z}
    {J : ProjectiveJetFamily X Y}
    (hU : IsOpen U) (hV : IsOpen V) (hu : HasProjectiveJetsOn u J U)
    (hg : ContDiffOn ℝ ∞ g V) (hmap : MapsTo u U V)
    {n : ℕ} (c : OrderedFinpartition n) {x : X} (hx : x ∈ U)
    (w : X) (v : Fin n → X) :
    HasProjectiveLineDerivAt
      (fun y => projectiveCompositionTerm u J (fun j => iteratedFDeriv ℝ j g) c y v)
      (projectiveCompositionTerm u J (fun j => iteratedFDeriv ℝ j g)
          (c.extend none) x (Fin.cons w v) +
        ∑ i : Fin c.length,
          projectiveCompositionTerm u J (fun j => iteratedFDeriv ℝ j g)
            (c.extend (some i)) x (Fin.cons w v)) x w := by
  have hcurve : HasDerivAt (fun t : ℝ => u (x + t • w))
      (projectiveFirstJetValue J x w) 0 :=
    hasDerivAt_iff_tendsto_slope_zero.mpr (hu.hasLineDerivAt hU hx w)
  have houter : ContDiffAt ℝ ∞ g (u (x + (0 : ℝ) • w)) := by
    simpa only [zero_smul, add_zero] using hg.contDiffAt (hV.mem_nhds (hmap hx))
  have hcoeff : ContinuousAt
      (fun t : ℝ => iteratedFDeriv ℝ c.length g (u (x + t • w))) 0 :=
    ContinuousAt.comp (f := fun t : ℝ => u (x + t • w)) (x := (0 : ℝ))
      (houter.continuousAt_iteratedFDeriv (by simp)) hcurve.continuousAt
  have hB (vs : Fin c.length → Y) :
      ContinuousAt (fun p : ℝ × (Fin c.length → Y) =>
        iteratedFDeriv ℝ c.length g (u (x + p.1 • w)) p.2) (0, vs) :=
    (ContinuousAt.comp
      (f := fun p : ℝ × (Fin c.length → Y) => p.1) (x := ((0 : ℝ), vs))
      hcoeff continuousAt_fst).eval continuousAt_snd
  have hslots (i : Fin c.length) :
      HasProjectiveCurveDerivAt
        (fun t : ℝ => J (c.partSize i) (x + t • w) (v ∘ c.emb i))
        (J (c.partSize i + 1) x (Fin.cons w (v ∘ c.emb i))) 0 :=
    hu.2.2 (c.partSize i) x hx w (v ∘ c.emb i)
  have hB₀ : HasProjectiveCurveDerivAt
      (fun t : ℝ => iteratedFDeriv ℝ c.length g (u (x + t • w))
        (fun i => J (c.partSize i) (x + (0 : ℝ) • w) (v ∘ c.emb i)))
      (iteratedFDeriv ℝ (c.length + 1) g (u x)
        (Fin.cons (projectiveFirstJetValue J x w)
          (fun i => J (c.partSize i) x (v ∘ c.emb i)))) 0 := by
    simpa only [zero_smul, add_zero] using
      hasProjectiveCurveDerivAt_iteratedFDeriv hcurve houter c.length
        (fun i => J (c.partSize i) x (v ∘ c.emb i))
  have hd := hasProjectiveCurveDerivAt_variableMultilinear
    (fun t : ℝ => iteratedFDeriv ℝ c.length g (u (x + t • w)))
    (fun t i => J (c.partSize i) (x + t • w) (v ∘ c.emb i))
    (fun i => J (c.partSize i + 1) x (Fin.cons w (v ∘ c.emb i)))
    (iteratedFDeriv ℝ (c.length + 1) g (u x)
      (Fin.cons (projectiveFirstJetValue J x w)
        (fun i => J (c.partSize i) x (v ∘ c.emb i))))
    0 hB hslots hB₀
  simp only [projectiveCompositionTerm_extend_none, projectiveCompositionTerm_extend_some]
  simpa only [HasProjectiveLineDerivAt, projectiveCompositionTerm_apply,
    zero_smul, add_zero] using hd

/-- Composition with a smooth normed outer function uses the existing
ordered-partition jets on the original topological source. -/
theorem hasProjectiveJetsOn_contDiff_comp
    {U : Set X} {V : Set Y} {u : X → Y} {g : Y → Z}
    {J : ProjectiveJetFamily X Y}
    (hU : IsOpen U) (hV : IsOpen V) (hu : HasProjectiveJetsOn u J U)
    (hg : ContDiffOn ℝ ∞ g V) (hmap : MapsTo u U V) :
    HasProjectiveJetsOn (g ∘ u)
      (projectiveCompositionJets u J (fun n => iteratedFDeriv ℝ n g)) U := by
  classical
  have houter := hasProjectiveJetsOn_of_contDiffOn hV hg
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [projectiveCompositionJets_apply, Fintype.sum_unique]
    change iteratedFDeriv ℝ 0 g (u x)
      (fun i : Fin 0 => J 1 x (fun _ => Fin.elim0 i)) = g (u x)
    exact iteratedFDeriv_zero_apply _
  · intro n
    simp only [projectiveCompositionJets_apply]
    exact continuousOn_finsetSum Finset.univ
      (fun c _ => hu.continuousOn_compositionTerm houter hmap c)
  · intro n x hx w v
    rw [projectiveCompositionJets_succ]
    have hd := HasProjectiveCurveDerivAt.finset_sum Finset.univ
      (fun c _ => compositionTerm_hasLineDerivAt_normed hU hV hu hg hmap c hx w v)
    simpa only [HasProjectiveLineDerivAt, projectiveCompositionJets_apply] using hd

/-- The resulting verified tower, without normability assumptions on its
parameter space or any additional derivative hypotheses. -/
def smoothDirections_contDiff_comp
    {U : Set X} {V : Set Y} {u : X → Y} {g : Y → Z}
    (J : SmoothDirections U u) (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V)
    (hmap : MapsTo u U V) : SmoothDirections U (g ∘ u) :=
  smoothDirectionsOfJets J.open_domain
    (projectiveCompositionJets u J.D (fun n => iteratedFDeriv ℝ n g))
    (hasProjectiveJetsOn_contDiff_comp J.open_domain hV J.hasProjectiveJetsOn hg hmap)

/-- The constructed tower has the explicit ordered-partition derivative
formula, so later estimates can use its actual multilinear evaluations. -/
theorem smoothDirections_contDiff_comp_D_apply
    {U : Set X} {V : Set Y} {u : X → Y} {g : Y → Z}
    (J : SmoothDirections U u) (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V)
    (hmap : MapsTo u U V) (n : ℕ) (x : X) (v : Fin n → X) :
    (smoothDirections_contDiff_comp J hV hg hmap).D n x v =
      ∑ c : OrderedFinpartition n,
        iteratedFDeriv ℝ c.length g (u x)
          (fun i => J.D (c.partSize i) x (v ∘ c.emb i)) := by
  change projectiveCompositionJets u J.D (fun j => iteratedFDeriv ℝ j g) n x v = _
  simp only [projectiveCompositionJets_apply, projectiveCompositionTerm_apply]

end NormedOuterCalculus

section FiniteInputs

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]

/-- A finite tuple of the given scalar towers, retaining every actual jet. -/
def smoothDirections_scalarTuple {m : ℕ} {U : Set X} {f : Fin m → X → ℝ}
    (hU : IsOpen U) (J : ∀ i, SmoothDirections U (f i)) :
    SmoothDirections U (fun x i => f i x) where
  open_domain := hU
  D := fun n x => ContinuousMultilinearMap.pi (fun i => (J i).D n x)
  zero := by
    intro x hx
    funext i
    rw [ContinuousMultilinearMap.pi_apply, (J i).zero x hx]
  continuous := by
    intro n
    apply continuousOn_pi.mpr
    intro i
    simpa only [ContinuousMultilinearMap.pi_apply] using (J i).continuous n
  derivative := by
    intro n x hx v w
    unfold HasProjectiveLineDerivAt HasProjectiveCurveDerivAt
    apply tendsto_pi_nhds.mpr
    intro i
    simpa only [HasProjectiveLineDerivAt, HasProjectiveCurveDerivAt,
      Pi.smul_apply, Pi.sub_apply, ContinuousMultilinearMap.pi_apply] using
      (J i).derivative n x hx v w

theorem smoothDirections_scalarTuple_D_apply {m : ℕ} {U : Set X}
    {f : Fin m → X → ℝ} (hU : IsOpen U) (J : ∀ i, SmoothDirections U (f i))
    (n : ℕ) (x : X) (v : Fin n → X) (i : Fin m) :
    (smoothDirections_scalarTuple hU J).D n x v i = (J i).D n x v := by
  change ContinuousMultilinearMap.pi (fun j => (J j).D n x) v i = _
  exact ContinuousMultilinearMap.pi_apply _ _ _

end FiniteInputs

section ScalarCoefficientCalculus

/-- These are the seven existing scalar inputs, in the order
`E, Er, k, p, kr, pr, pθ`; no independent geometric data are introduced. -/
private theorem contDiffAt_scalarCoefficientFormulas (r : ℝ) (y : Fin 7 → ℝ)
    (hD : 0 < heightDiscriminant (y 0) (y 2) (y 3))
    (hQ : heightQ (y 0) (y 2) (y 6) ≠ 0) :
    ContDiffAt ℝ ∞ (fun v : Fin 7 → ℝ =>
      linearRadial (v 0) (v 2) (v 6)
        (inverseDThreeHalves (heightDiscriminant (v 0) (v 2) (v 3)))) y ∧
    ContDiffAt ℝ ∞ (fun v : Fin 7 → ℝ =>
      linearMixed (v 0) (v 5)
        (inverseDThreeHalves (heightDiscriminant (v 0) (v 2) (v 3)))) y ∧
    ContDiffAt ℝ ∞ (fun v : Fin 7 → ℝ =>
      correctedAngular r (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)
        (inverseDThreeHalves (heightDiscriminant (v 0) (v 2) (v 3)))) y := by
  have hj (i : Fin 7) : ContDiffAt ℝ ∞ (fun v : Fin 7 → ℝ => v i) y :=
    contDiffAt_apply ℝ ℝ i y
  have hd : ContDiffAt ℝ ∞ (fun v : Fin 7 → ℝ =>
      heightDiscriminant (v 0) (v 2) (v 3)) y :=
    ((hj 0).mul (contDiffAt_const.sub ((hj 3).pow 2))).sub ((hj 2).pow 2)
  have hq : ContDiffAt ℝ ∞ (fun v : Fin 7 → ℝ => heightQ (v 0) (v 2) (v 6)) y :=
    (hj 2).add ((hj 0).mul (hj 6))
  have ht : ContDiffAt ℝ ∞ (fun v : Fin 7 → ℝ =>
      inverseDThreeHalves (heightDiscriminant (v 0) (v 2) (v 3))) y :=
    contDiffAt_const.div (hd.mul (hd.sqrt hD.ne'))
      (mul_ne_zero hD.ne' (Real.sqrt_pos.mpr hD).ne')
  have hnum : ContDiffAt ℝ ∞ (fun v : Fin 7 → ℝ =>
      darbouxNumerator r (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) y :=
    ((hq.mul (hj 4)).sub (((hj 0).mul contDiffAt_const).mul ((hj 5).pow 2))).sub
      (((hj 1).div_const 2).mul
        ((contDiffAt_const.sub ((hj 3).pow 2)).add ((hj 2).mul (hj 6))))
  refine ⟨hq.mul ht, ((hj 0).neg.mul (hj 5)).mul ht, ?_⟩
  exact (((((hj 0).mul (hj 4)).sub (((hj 1).mul (hj 2)).div_const 2)).mul ht).div_const r).sub
    (((hj 0).mul ((hnum.mul ht).div_const r)).div hq hQ)

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- Genuine parameter towers for all three actual algebraic coefficient
formulas, assembled from seven given scalar towers on their common domain. -/
def smoothDirections_scalarCoefficients {U : Set X}
    (r : ℝ) (f : Fin 7 → X → ℝ) (J : ∀ i, SmoothDirections U (f i))
    (hD : ∀ x ∈ U, 0 < heightDiscriminant (f 0 x) (f 2 x) (f 3 x))
    (hQ : ∀ x ∈ U, heightQ (f 0 x) (f 2 x) (f 6 x) ≠ 0) :
    SmoothDirections U (fun x => linearRadial (f 0 x) (f 2 x) (f 6 x)
      (inverseDThreeHalves (heightDiscriminant (f 0 x) (f 2 x) (f 3 x)))) ×
    SmoothDirections U (fun x => linearMixed (f 0 x) (f 5 x)
      (inverseDThreeHalves (heightDiscriminant (f 0 x) (f 2 x) (f 3 x)))) ×
    SmoothDirections U (fun x =>
      correctedAngular r (f 0 x) (f 1 x) (f 2 x) (f 3 x) (f 4 x) (f 5 x) (f 6 x)
        (inverseDThreeHalves (heightDiscriminant (f 0 x) (f 2 x) (f 3 x)))) := by
  let V : Set (Fin 7 → ℝ) := {y |
    0 < heightDiscriminant (y 0) (y 2) (y 3) ∧ heightQ (y 0) (y 2) (y 6) ≠ 0}
  have hdisc : Continuous (fun y : Fin 7 → ℝ => heightDiscriminant (y 0) (y 2) (y 3)) :=
    ((continuous_apply 0).mul (continuous_const.sub ((continuous_apply 3).pow 2))).sub
      ((continuous_apply 2).pow 2)
  have hq : Continuous (fun y : Fin 7 → ℝ => heightQ (y 0) (y 2) (y 6)) :=
    (continuous_apply 2).add ((continuous_apply 0).mul (continuous_apply 6))
  have hV : IsOpen V := (isOpen_lt continuous_const hdisc).inter (isOpen_ne.preimage hq)
  let K := smoothDirections_scalarTuple (J 0).open_domain J
  have hmap : MapsTo (fun x i => f i x) U V := fun x hx => ⟨hD x hx, hQ x hx⟩
  have ha : ContDiffOn ℝ ∞ (fun y : Fin 7 → ℝ =>
      linearRadial (y 0) (y 2) (y 6)
        (inverseDThreeHalves (heightDiscriminant (y 0) (y 2) (y 3)))) V :=
    fun y hy => (contDiffAt_scalarCoefficientFormulas r y hy.1 hy.2).1.contDiffWithinAt
  have hb : ContDiffOn ℝ ∞ (fun y : Fin 7 → ℝ =>
      linearMixed (y 0) (y 5)
        (inverseDThreeHalves (heightDiscriminant (y 0) (y 2) (y 3)))) V :=
    fun y hy => (contDiffAt_scalarCoefficientFormulas r y hy.1 hy.2).2.1.contDiffWithinAt
  have hc : ContDiffOn ℝ ∞ (fun y : Fin 7 → ℝ =>
      correctedAngular r (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6)
        (inverseDThreeHalves (heightDiscriminant (y 0) (y 2) (y 3)))) V :=
    fun y hy => (contDiffAt_scalarCoefficientFormulas r y hy.1 hy.2).2.2.contDiffWithinAt
  exact ⟨smoothDirections_contDiff_comp K hV ha hmap,
    smoothDirections_contDiff_comp K hV hb hmap,
    smoothDirections_contDiff_comp K hV hc hmap⟩

/-- The scalar calculus applies to the existing coefficient fields of actual
profile and height families. Each input is the spatial derivative appearing
in their definitions, not a freely chosen replacement coefficient. -/
def smoothDirections_polarCoefficients {U : Set X}
    (w : X → ℝ → ℝ) (z : X → PolarPoint → ℝ) (p : PolarPoint)
    (JE : SmoothDirections U (fun x => profileEnergy (w x) p))
    (JEr : SmoothDirections U (fun x => radialPartial (profileEnergy (w x)) p))
    (Jk : SmoothDirections U (fun x => heightRadial (z x) p))
    (Jp : SmoothDirections U (fun x => heightAngular (z x) p))
    (Jkr : SmoothDirections U (fun x => radialPartial (heightRadial (z x)) p))
    (Jpr : SmoothDirections U (fun x => radialPartial (heightAngular (z x)) p))
    (Jpθ : SmoothDirections U (fun x => angularPartial (heightAngular (z x)) p))
    (hD : ∀ x ∈ U, 0 < polarDiscriminant (w x) (z x) p)
    (hQ : ∀ x ∈ U, heightQ (profileEnergy (w x) p) (heightRadial (z x) p)
      (angularPartial (heightAngular (z x)) p) ≠ 0) :
    SmoothDirections U (fun x => polarLinearA (w x) (z x) p) ×
    SmoothDirections U (fun x => polarLinearB (w x) (z x) p) ×
    SmoothDirections U (fun x => polarCorrectedC (w x) (z x) p) := by
  let f : Fin 7 → X → ℝ :=
    ![fun x => profileEnergy (w x) p,
      fun x => radialPartial (profileEnergy (w x)) p,
      fun x => heightRadial (z x) p,
      fun x => heightAngular (z x) p,
      fun x => radialPartial (heightRadial (z x)) p,
      fun x => radialPartial (heightAngular (z x)) p,
      fun x => angularPartial (heightAngular (z x)) p]
  have J : ∀ i, SmoothDirections U (f i) := by
    refine Fin.cases JE ?_
    refine Fin.cases JEr ?_
    refine Fin.cases Jk ?_
    refine Fin.cases Jp ?_
    refine Fin.cases Jkr ?_
    refine Fin.cases Jpr ?_
    refine Fin.cases Jpθ ?_
    exact Fin.elim0
  exact smoothDirections_scalarCoefficients p.1 f J hD hQ

end ScalarCoefficientCalculus

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency true in
/-- Direct specialization to the actual N01 coefficient families, at one
fixed spatial point and on the supplied common parameter domain. -/
def originalCoefficientsSmoothDirections
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (U : Set (AnnularState S × ℝ)) (p : PolarPoint)
    (JE : SmoothDirections U
      (fun z => profileEnergy (stateProfile D S C z.1) p))
    (JEr : SmoothDirections U
      (fun z => radialPartial (profileEnergy (stateProfile D S C z.1)) p))
    (Jk : SmoothDirections U (fun z => heightRadial (stateHeight D S C z) p))
    (Jp : SmoothDirections U (fun z => heightAngular (stateHeight D S C z) p))
    (Jkr : SmoothDirections U
      (fun z => radialPartial (heightRadial (stateHeight D S C z)) p))
    (Jpr : SmoothDirections U
      (fun z => radialPartial (heightAngular (stateHeight D S C z)) p))
    (Jpθ : SmoothDirections U
      (fun z => angularPartial (heightAngular (stateHeight D S C z)) p))
    (hD : ∀ z ∈ U, 0 < polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p)
    (hQ : ∀ z ∈ U, heightQ (profileEnergy (stateProfile D S C z.1) p)
      (heightRadial (stateHeight D S C z) p)
      (angularPartial (heightAngular (stateHeight D S C z)) p) ≠ 0) :
    SmoothDirections U (fun z => (originalCoefficients D S C z).a p) ×
    SmoothDirections U (fun z => (originalCoefficients D S C z).b p) ×
    SmoothDirections U (fun z => (originalCoefficients D S C z).c p) := by
  letI : IsTopologicalAddGroup (AnnularState S × ℝ) := inferInstance
  letI : ContinuousSMul ℝ (AnnularState S × ℝ) := inferInstance
  let w : (AnnularState S × ℝ) → ℝ → ℝ :=
    fun z : AnnularState S × ℝ => stateProfile D S C z.1
  let h : (AnnularState S × ℝ) → PolarPoint → ℝ := stateHeight D S C
  let J : SmoothDirections U (fun z => polarLinearA (w z) (h z) p) ×
      SmoothDirections U (fun z => polarLinearB (w z) (h z) p) ×
      SmoothDirections U (fun z => polarCorrectedC (w z) (h z) p) :=
    smoothDirections_polarCoefficients (X := AnnularState S × ℝ) (U := U)
      w h p JE JEr Jk Jp Jkr Jpr Jpθ hD hQ
  refine ⟨J.1.congr ?_, J.2.1.congr ?_, J.2.2.congr ?_⟩
  all_goals
    intro z _
    rfl

end ContinuousFlexibility.Statements
