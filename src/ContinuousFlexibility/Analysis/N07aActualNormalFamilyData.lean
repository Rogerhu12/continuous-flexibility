module

public import ContinuousFlexibility.Analysis.N07aActualCanonicalSolutionData
public import ContinuousFlexibility.Analysis.N07aActualInverseVolume
public import ContinuousFlexibility.Analysis.N07aRelativeVolumeFirstJets
public import ContinuousFlexibility.Analysis.N07aReferenceOperatorIdentity

/-!
# One actual Banach family for the normal bootstrap

The base source is fixed once, extended by zero outside its legitimate
neighborhood. Every higher source class and every weak jet concerns that
same input to the prescribed relative and reference inverses.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff

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
  {V : VolumeModelData S K} {b : ℕ} {B : CanonicalDomainData S K V b}
  {P : RelativeInverseData S K V b B} {base loss : ℕ} {ε : ℝ}

local instance n07aNormalFamilyDataLevelGroup (t : ℝ) (s : ℕ) :
    NormedAddCommGroup (V.level (3 / 4 : ℝ) t s) := Submodule.normedAddCommGroup _
local instance n07aNormalFamilyDataLevelSpace (t : ℝ) (s : ℕ) :
    NormedSpace ℝ (V.level (3 / 4 : ℝ) t s) := Submodule.normedSpace _
local instance n07aNormalFamilyDataGraphGroup : NormedAddCommGroup B.Space :=
  Submodule.normedAddCommGroup _
local instance n07aNormalFamilyDataGraphSpace : NormedSpace ℝ B.Space := Submodule.normedSpace _

theorem n07a_currentCanonicalSourceValue_eq_withoutColumns
    (U : CanonicalGeometry.Parameter S → S.Source → CanonicalUnknown S K)
    (z : CanonicalGeometry.Parameter S) (f : S.Source) (m : ℕ) :
    n07aCurrentCanonicalSourceValue D S C L K (liftSectorParameter S C z)
      (U z f) ((S.height (3 / 4 : ℝ)).decode f.val) m =
    n07aCanonicalSourceWithoutColumns D S C L K (fun z f => n07aUnknownScalar (U z f))
      z f m := by
  unfold n07aCanonicalSourceWithoutColumns
  funext y
  simp only [n07aUnknownScalar]
  exact congrFun (n07aCurrentCanonicalSourceValue_eq_sum (D := D) (C := C) (L := L)
    (liftSectorParameter S C z) (U z f) ((S.height (3 / 4 : ℝ)).decode f.val) m) y

private theorem n07a_normalFamily_sourceGrading (n : ℕ) (f : S.Source) :
    S.sourceGrading n f = (S.height (3 / 4 : ℝ)).grading n f.val := by
  simp only [PhysicalSpacesData.sourceGrading, Seminorm.comp_apply, Submodule.subtype_apply]

structure N07aActualNormalFamilyData
    (D : ReferenceData) (T : MaterialData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (V : VolumeModelData S K) (b : ℕ) (B : CanonicalDomainData S K V b)
    (P : RelativeInverseData S K V b B) (base : ℕ) (ε : ℝ) where
  neighborhoodBase : ℕ
  base_le : base ≤ neighborhoodBase
  neighborhoodRadius : ℝ
  radius_pos : 0 < neighborhoodRadius
  radius_le : neighborhoodRadius ≤ ε
  F₀ : CanonicalGeometry.Parameter S → S.Source → V.level (3 / 4 : ℝ) 0 b
  w : CanonicalGeometry.Parameter S → S.Source → ℕ → PolarPoint → ℝ
  interval : ∀ m, K.left m < K.right m
  low : ℕ
  firstLoss : ℕ
  C₀ : ℝ
  Cα : ℝ
  C₀_pos : 0 < C₀
  Cα_nonneg : 0 ≤ Cα
  baseNorm : ∀ z f, ‖F₀ z f‖ ≤ C₀ * S.sourceGrading low f
  scalars : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ f i,
    |n07aUnknownScalar (n07aActualCanonicalUnknown C B P F₀ z f) i| ≤
      Cα * S.sourceGrading low f
  sourceAE : ∀ z ∈ sectorNeighborhood S neighborhoodBase neighborhoodRadius neighborhoodRadius,
    ∀ f m, (n07aActualCanonicalSource F₀ z f m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] canonicalSource S K (liftSectorParameter S C z) m
        ((S.height (3 / 4 : ℝ)).decode f.val)
  relation : ∀ z ∈ sectorNeighborhood S neighborhoodBase neighborhoodRadius neighborhoodRadius,
    ∀ f, PerturbedCanonicalRelation D S C K L (liftSectorParameter S C z)
      (n07aActualCanonicalUnknown C B P F₀ z f) (n07aActualCanonicalSource F₀ z f)
  even : ∀ z ∈ sectorNeighborhood S neighborhoodBase neighborhoodRadius neighborhoodRadius,
    ∀ f m, n07aAngularReflection m ((n07aActualCanonicalUnknown C B P F₀ z f).1 m) =
      (n07aActualCanonicalUnknown C B P F₀ z f).1 m
  regular : ∀ z ∈ sectorNeighborhood S neighborhoodBase neighborhoodRadius neighborhoodRadius,
    ∀ f m k, N07aCanonicalNormalRegular S K m
      ((n07aActualCanonicalUnknown C B P F₀ z f).1 m) k
  decode : ∀ z (hz : z ∈ sectorNeighborhood S neighborhoodBase neighborhoodRadius neighborhoodRadius)
    f m, w z f m = n07aCanonicalSmoothDecode (interval m)
      ⟨(n07aActualCanonicalUnknown C B P F₀ z f).1 m, regular z hz f m⟩
  equation : ∀ z ∈ sectorNeighborhood S neighborhoodBase neighborhoodRadius neighborhoodRadius,
    ∀ f m, EqOn (mixedDerivative 2 0 (w z f m))
      (n07aNormalRhs
        (fun i => n07aNormalCoefficientFamily
          (fun k z m => n07aPrincipalField K (liftSectorParameter S C z) m k)
          (fun m => if K.positive m then -1 else 1) i z m)
        (w z f m)
        (n07aCanonicalSourceWithoutColumns D S C L K
          (fun z f => n07aUnknownScalar (n07aActualCanonicalUnknown C B P F₀ z f)) z f m))
      (canonicalOpen S K m)
  firstWeak : ∀ a : ℕ, a ≤ 1 → ∀ n c : ℕ, ∃ A : ℝ, 0 < A ∧
    ∀ z ∈ sectorNeighborhood S neighborhoodBase neighborhoodRadius neighborhoodRadius,
      ∀ f m, ∃ J : CanonicalL2 S K m,
        N07aWeakCanonicalMixedDerivative S K m
          ((n07aActualCanonicalUnknown C B P F₀ z f).1 m) J a n ∧
        ‖J‖ ≤ A *
          (T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) * (T.M (T.sample (K.cell m)) ^ c)⁻¹) *
          (S.sourceGrading (c + (a + n) + firstLoss) f +
            (1 + CanonicalGeometry.parameterGrading S (c + (a + n) + firstLoss) z) *
              S.sourceGrading low f)

theorem n07a_exists_actualNormalFamilyData
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hprincipal : CanonicalGeometry.ReferencePrincipal T S C K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (h05 : N05Properties D T S C K V b B)
    (h06 : N06Properties D S C K L V b B P base ε)
    (hAngular : N07aAngularProperties S C K V b B P base ε) :
    Nonempty (N07aActualNormalFamilyData D T S C L K V b B P base ε) := by
  classical
  have hv := n07a_actualSource_relativeInverse_volume hD hT hS h01.2.1 h01.2.2.1
    h04 href hcur h05.2.1 hAngular
  let b₀ : ℕ := hv.choose
  let e₀ : ℝ := hv.choose_spec.2.choose
  have hv₀ := hv.choose_spec.2.choose_spec
  let low : ℕ := hv₀.2.2.choose
  let d : ℕ := hv₀.2.2.choose_spec.choose
  let C₀ : ℝ := hv₀.2.2.choose_spec.choose_spec.choose
  have hC := hv₀.2.2.choose_spec.choose_spec.choose_spec
  let FH : CanonicalGeometry.Parameter S → (S.height (3 / 4 : ℝ)).Space →
      V.level (3 / 4 : ℝ) 0 b := hC.2.choose
  have hFH := hC.2.choose_spec
  let Ω₀ := sectorNeighborhood S b₀ e₀ e₀
  let F₀ : CanonicalGeometry.Parameter S → S.Source → V.level (3 / 4 : ℝ) 0 b :=
    fun z f => if hz : z ∈ Ω₀ then FH z f.val else 0
  have hF₀ (z : CanonicalGeometry.Parameter S) (hz : z ∈ Ω₀) (f : S.Source) :
      F₀ z f = FH z f.val := by simp only [F₀, dif_pos hz]
  have hnorm (z : CanonicalGeometry.Parameter S) (f : S.Source) :
      ‖F₀ z f‖ ≤ C₀ * S.sourceGrading low f := by
    by_cases hz : z ∈ Ω₀
    · exact (congrArg (fun u : V.level (3 / 4 : ℝ) 0 b => ‖u‖) (hF₀ z hz f)).le.trans
        (hFH.1 z hz f.val).2
    · have he : F₀ z f = 0 := by simp only [F₀, dif_neg hz]
      rw [he, norm_zero]
      exact mul_nonneg hC.1.le (apply_nonneg _ _)
  have hsource (z : CanonicalGeometry.Parameter S) (hz : z ∈ Ω₀)
      (f : S.Source) (m : ℕ) :
      (n07aActualCanonicalSource F₀ z f m : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K m] canonicalSource S K (liftSectorParameter S C z) m
          ((S.height (3 / 4 : ℝ)).decode f.val) := by
    simpa only [n07aActualCanonicalSource, hF₀ z hz f] using (hFH.1 z hz f.val).1 m
  have hlift : ∀ t s : ℕ, ∃ A : ℝ, 0 < A ∧ ∀ z ∈ Ω₀, ∀ f : S.Source,
      ∃ Q : V.level (3 / 4 : ℝ) (t : ℝ) (b + s),
        V.forget (3 / 4 : ℝ) (t : ℝ) (b + s) Q =
          V.forget (3 / 4 : ℝ) 0 b (P.inverse (liftSectorParameter S C z) (F₀ z f)) ∧
        ‖Q‖ ≤ A * (S.sourceGrading (t + s + d) f +
          (1 + CanonicalGeometry.parameterGrading S (t + s + d) z) * S.sourceGrading low f) := by
    intro t s
    let bound := hFH.2 t s
    refine ⟨bound.choose, bound.choose_spec.1, fun z hz f => ?_⟩
    let datum := bound.choose_spec.2 z hz f.val
    let Q : V.level (3 / 4 : ℝ) (t : ℝ) (b + s) := datum.choose
    have he : V.forget (3 / 4 : ℝ) 0 b
        (P.inverse (liftSectorParameter S C z) (F₀ z f)) =
        V.forget (3 / 4 : ℝ) 0 b (P.inverse (liftSectorParameter S C z) (FH z f.val)) :=
      congrArg (fun v : V.level (3 / 4 : ℝ) 0 b =>
        V.forget (3 / 4 : ℝ) 0 b (P.inverse (liftSectorParameter S C z) v)) (hF₀ z hz f)
    refine ⟨Q, datum.choose_spec.1.trans he.symm, ?_⟩
    have hcost :
        (S.height (3 / 4 : ℝ)).grading (t + s + d) f.val +
            (1 + CanonicalGeometry.parameterGrading S (t + s + d) z) *
              (S.height (3 / 4 : ℝ)).grading low f.val =
          S.sourceGrading (t + s + d) f +
            (1 + CanonicalGeometry.parameterGrading S (t + s + d) z) * S.sourceGrading low f :=
      congrArg₂ (fun a r : ℝ => a +
        (1 + CanonicalGeometry.parameterGrading S (t + s + d) z) * r)
        (n07a_normalFamily_sourceGrading (t + s + d) f).symm
        (n07a_normalFamily_sourceGrading low f).symm
    exact datum.choose_spec.2.trans_eq (congrArg (fun r : ℝ => bound.choose * r) hcost)
  have hf := n07a_relativeVolume_firstJets hD hT h05 S.sourceGrading
    (n07aSourceGrading_monotone S) Ω₀ low d F₀ hlift
  let firstLoss : ℕ := hf.choose
  have hfirst := hf.choose_spec
  have hq := n07a_currentCanonical_qualitative_neighborhood hD hT hS h01.2.1
    h01.2.2.1 h04 href hprincipal hcur
  let bq : ℕ := hq.choose
  let eq : ℝ := hq.choose_spec.2.choose
  have hqb := hq.choose_spec.2.choose_spec
  let base' : ℕ := max b₀ bq
  let ε' : ℝ := min e₀ eq
  let Ω := sectorNeighborhood S base' ε' ε'
  have hbase : base ≤ base' := hv.choose_spec.1.trans (le_max_left b₀ bq)
  have he : ε' ≤ ε := (min_le_left e₀ eq).trans hv₀.2.1
  have hΩ₀ : Ω ⊆ Ω₀ :=
    n07a_sectorNeighborhood_mono (S := S) (le_max_left b₀ bq) (min_le_left e₀ eq)
  have hΩq : Ω ⊆ sectorNeighborhood S bq eq eq :=
    n07a_sectorNeighborhood_mono (S := S) (le_max_right b₀ bq) (min_le_right e₀ eq)
  have hΩ : Ω ⊆ sectorNeighborhood S base ε ε :=
    n07a_sectorNeighborhood_mono (S := S) hbase he
  let U := n07aActualCanonicalUnknown C B P F₀
  let F := n07aActualCanonicalSource F₀
  have hrel (z : CanonicalGeometry.Parameter S) (hz : z ∈ Ω) (f : S.Source) :
      PerturbedCanonicalRelation D S C K L (liftSectorParameter S C z) (U z f) (F z f) :=
    n07aBaseInverse_perturbed h05 h06
      (liftSectorParameter_mem_stateNeighborhood (S := S) (C := C) (hΩ hz) le_rfl)
      (h01.2.2.1.liftSectorParameter_sector z) (F₀ z f)
  have hregular₁ (z : CanonicalGeometry.Parameter S) (hz : z ∈ Ω)
      (f : S.Source) (m : ℕ) : N07aCanonicalNormalRegular S K m ((U z f).1 m) 1 := by
    intro a ha n
    let bound := hfirst a ha n 0
    let jet := bound.choose_spec.2 z (hΩ₀ hz) f m
    exact ⟨jet.choose, jet.choose_spec.1⟩
  have hex (z : CanonicalGeometry.Parameter S) (hz : z ∈ Ω) (f : S.Source) (m : ℕ) :=
    hqb.2.2 z (hΩq hz) (U z f) (F z f) f (hrel z hz f)
      (hsource z (hΩ₀ hz) f) (hregular₁ z hz f) m
  let hregular : ∀ z ∈ Ω, ∀ f m k, N07aCanonicalNormalRegular S K m ((U z f).1 m) k :=
    fun z hz f m => (hex z hz f m).choose
  let w : CanonicalGeometry.Parameter S → S.Source → ℕ → PolarPoint → ℝ :=
    fun z f m => if hz : z ∈ Ω then n07aCanonicalSmoothDecode (h04.1.referenceBounds m).2.1
      ⟨(U z f).1 m, hregular z hz f m⟩ else 0
  have hw (z : CanonicalGeometry.Parameter S) (hz : z ∈ Ω) (f : S.Source) (m : ℕ) :
      w z f m = n07aCanonicalSmoothDecode (h04.1.referenceBounds m).2.1
        ⟨(U z f).1 m, hregular z hz f m⟩ := by simp only [w, dif_pos hz]
  let Cα : ℝ := (2 * ‖B.inverse‖) * C₀
  have hCα : 0 ≤ Cα := mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) hC.1.le
  refine ⟨{
    neighborhoodBase := base'
    base_le := hbase
    neighborhoodRadius := ε'
    radius_pos := lt_min hv₀.1 hqb.1
    radius_le := he
    F₀ := F₀
    w := w
    interval := fun m => (h04.1.referenceBounds m).2.1
    low := low
    firstLoss := firstLoss
    C₀ := C₀
    Cα := Cα
    C₀_pos := hC.1
    Cα_nonneg := hCα
    baseNorm := hnorm
    scalars := ?_
    sourceAE := fun z hz => hsource z (hΩ₀ hz)
    relation := hrel
    even := ?_
    regular := hregular
    decode := hw
    equation := ?_
    firstWeak := ?_
  }⟩
  · intro z hz f i
    exact ((n07aBaseInverse_scalar_bound h06
      (liftSectorParameter_mem_stateNeighborhood (S := S) (C := C) hz le_rfl)
      (h01.2.2.1.liftSectorParameter_sector z) (F₀ z f) i).trans
      (mul_le_mul_of_nonneg_left (hnorm z f)
        (mul_nonneg (by norm_num) (norm_nonneg _)))).trans_eq (by dsimp only [Cα]; ring)
  · intro z _ f m
    let u := n07aBaseInverse B P (liftSectorParameter S C z) (F₀ z f)
    have hg := (h05.2.2.2.2.2.2.1 u.val).mp u.property
    let W : V.level (3 / 4 : ℝ) (-B.lossMaterial) 0 := hg.1.choose
    have hW := hg.1.choose_spec
    have heven := n07a_volume_forget_reflection h05.2.1 W m
    have hm : V.forget (3 / 4 : ℝ) (-B.lossMaterial) 0 W m = u.val.1.1 m :=
      congrFun hW m
    exact (congrArg (n07aAngularReflection m) hm).symm.trans (heven.trans hm)
  · intro z hz f m y hy
    let decoded : PolarPoint → ℝ := n07aCanonicalSmoothDecode (h04.1.referenceBounds m).2.1
      ⟨(U z f).1 m, hregular z hz f m⟩
    let A : Fin 6 → PolarPoint → ℝ := fun i => n07aNormalCoefficientFamily
      (fun k z m => n07aPrincipalField K (liftSectorParameter S C z) m k)
      (fun m => if K.positive m then -1 else 1) i z m
    have hleft : mixedDerivative 2 0 (w z f m) y = mixedDerivative 2 0 decoded y :=
      congrArg (fun v : PolarPoint → ℝ => mixedDerivative 2 0 v y) (hw z hz f m)
    have heq : mixedDerivative 2 0 decoded y =
        n07aNormalRhs A decoded
          (n07aCurrentCanonicalSourceValue D S C L K (liftSectorParameter S C z)
            (U z f) ((S.height (3 / 4 : ℝ)).decode f.val) m) y :=
      (hex z hz f m).choose_spec hy
    have hright := congrArg₂ (fun v g : PolarPoint → ℝ => n07aNormalRhs A v g y)
      (hw z hz f m).symm
      (n07a_currentCanonicalSourceValue_eq_withoutColumns (D := D) (C := C) (L := L) U z f m)
    exact hleft.trans (heq.trans hright)
  · intro a ha n c
    let bound := hfirst a ha n c
    exact ⟨bound.choose, bound.choose_spec.1,
      fun z hz f m => bound.choose_spec.2 z (hΩ₀ hz) f m⟩

end ContinuousFlexibility.Analysis
