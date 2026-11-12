import ContinuousFlexibility.Analysis.N07aCanonicalSourceVolume
import ContinuousFlexibility.Statements.N07aRegularity

/-!
# The same relative inverse applied to the actual physical source

The base source is chosen once. All higher source realizations have the
same image under forget, so the angular theorem applies to exactly that
base input. A fixed low-order ball bounds its base norm uniformly.
-/

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

local instance n07aActualInverseVolumeLevelGroup (t : ℝ) (s : ℕ) :
    NormedAddCommGroup (V.level (3 / 4 : ℝ) t s) := Submodule.normedAddCommGroup _

local instance n07aActualInverseVolumeLevelSpace (t : ℝ) (s : ℕ) :
    NormedSpace ℝ (V.level (3 / 4 : ℝ) t s) := Submodule.normedSpace _

theorem n07a_actualSource_relativeInverse_volume
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hε : 0 < ε)
    (hrefState : referenceStateConditions D S C)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hV : IsVolumeModel T S K V)
    (hAngular : N07aAngularProperties S C K V b B P base ε) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      ∃ low outLoss : ℕ, ∃ C₀ : ℝ, 0 < C₀ ∧
      ∃ F₀ : CanonicalGeometry.Parameter S → (S.height (3 / 4 : ℝ)).Space →
          V.level (3 / 4 : ℝ) 0 b,
        (∀ z ∈ sectorNeighborhood S base' ε' ε', ∀ u,
          (∀ m, (V.forget (3 / 4 : ℝ) 0 b (F₀ z u) m : PolarPoint → ℝ)
            =ᵐ[canonicalMeasure S K m]
              canonicalSource S K (liftSectorParameter S C z) m
                ((S.height (3 / 4 : ℝ)).decode u)) ∧
          ‖F₀ z u‖ ≤ C₀ * (S.height (3 / 4 : ℝ)).grading low u) ∧
        ∀ t s : ℕ, ∃ Cts : ℝ, 0 < Cts ∧
          ∀ z ∈ sectorNeighborhood S base' ε' ε', ∀ u,
            ∃ Q : V.level (3 / 4 : ℝ) (t : ℝ) (b + s),
              V.forget (3 / 4 : ℝ) (t : ℝ) (b + s) Q =
                V.forget (3 / 4 : ℝ) 0 b
                  (P.inverse (liftSectorParameter S C z) (F₀ z u)) ∧
              ‖Q‖ ≤ Cts * ((S.height (3 / 4 : ℝ)).grading (t + s + outLoss) u +
                (1 + CanonicalGeometry.parameterGrading S (t + s + outLoss) z) *
                  (S.height (3 / 4 : ℝ)).grading low u) := by
  classical
  let p := CanonicalGeometry.parameterGrading S
  let q := (S.height (3 / 4 : ℝ)).grading
  have hp : Monotone p := n07aParameterGrading_monotone S
  have hq : Monotone q := gradedSeminorm_monotone _ _
  let sourceData := n07a_canonicalSource_height_volume (γ := (3 / 4 : ℝ)) hD hT hS
    (by norm_num) (by norm_num) hε hrefState h04 href hcur hV
  let base₁ : ℕ := sourceData.choose
  have hbase₁ : base ≤ base₁ := sourceData.choose_spec.1
  let ε₁ : ℝ := sourceData.choose_spec.2.choose
  have sourceRadius := sourceData.choose_spec.2.choose_spec
  have hε₁ : 0 < ε₁ := sourceRadius.1
  have hε₁le : ε₁ ≤ ε := sourceRadius.2.1
  let low₁ : ℕ := sourceRadius.2.2.choose
  let d₁ : ℕ := sourceRadius.2.2.choose_spec.choose
  have hsource := sourceRadius.2.2.choose_spec.choose_spec
  let d₂ : ℕ := hAngular.choose
  have hangular := hAngular.choose_spec
  let low := max low₁ (b + d₁)
  let outLoss := b + max d₁ d₂
  let smaller := n07a_lowParameter_neighborhood (S := S) (base := base₁) hε₁ low
  let base' : ℕ := smaller.choose
  have hbase' : base₁ ≤ base' := smaller.choose_spec.1
  let ε' : ℝ := smaller.choose_spec.2.choose
  have smallerRadius := smaller.choose_spec.2.choose_spec
  have hε' : 0 < ε' := smallerRadius.1
  have hε'le : ε' ≤ ε₁ := smallerRadius.2.1
  have hU := smallerRadius.2.2.1
  have hlow := smallerRadius.2.2.2
  let U := sectorNeighborhood S base' ε' ε'
  have hU₀ : U ⊆ sectorNeighborhood S base ε ε :=
    fun _ hz => n07a_sectorNeighborhood_mono (S := S) hbase₁ hε₁le (hU hz)
  let sourceAt : ℝ → Prop := fun t => ∃ A₀ : ℝ, 0 < A₀ ∧
      ∀ z ∈ sectorNeighborhood S base₁ ε₁ ε₁,
        ∀ u : (S.height (3 / 4 : ℝ)).Space,
          ∃ F : V.level (3 / 4 : ℝ) t b,
            (∀ m, (V.forget (3 / 4 : ℝ) t b F m : PolarPoint → ℝ)
              =ᵐ[canonicalMeasure S K m]
                canonicalSource S K (liftSectorParameter S C z) m
                  ((S.height (3 / 4 : ℝ)).decode u)) ∧
            ‖F‖ ≤ A₀ * (q (b + d₁) u + (1 + p (b + d₁) z) * q low₁ u)
  have sourceAtZero : sourceAt ((0 : ℕ) : ℝ) := by
    simpa only [sourceAt, zero_add] using hsource 0 b
  have sourceBase : sourceAt 0 :=
    Eq.mp (congrArg sourceAt (by norm_num : ((0 : ℕ) : ℝ) = 0)) sourceAtZero
  let A₀ : ℝ := sourceBase.choose
  have hA₀ : 0 < A₀ := sourceBase.choose_spec.1
  have hsource₀ := sourceBase.choose_spec.2
  let F₀ : CanonicalGeometry.Parameter S → (S.height (3 / 4 : ℝ)).Space →
      V.level (3 / 4 : ℝ) 0 b :=
    fun z u => if hz : z ∈ U then (hsource₀ z (hU hz) u).choose else 0
  have hbaseSource (z : CanonicalGeometry.Parameter S) (hz : z ∈ U)
      (u : (S.height (3 / 4 : ℝ)).Space) :
      (∀ m, (V.forget (3 / 4 : ℝ) 0 b (F₀ z u) m : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K m]
          canonicalSource S K (liftSectorParameter S C z) m
            ((S.height (3 / 4 : ℝ)).decode u)) ∧
      ‖F₀ z u‖ ≤ (3 * A₀) * q low u := by
    have he : F₀ z u = (hsource₀ z (hU hz) u).choose := by
      simp only [F₀, dif_pos hz]
    have hdata := (hsource₀ z (hU hz) u).choose_spec
    refine ⟨?_, ?_⟩
    · intro m
      have hefun := congrArg (fun G : V.level (3 / 4 : ℝ) 0 b =>
        (V.forget (3 / 4 : ℝ) 0 b G m : PolarPoint → ℝ)) he
      have hae : (V.forget (3 / 4 : ℝ) 0 b (F₀ z u) m : PolarPoint → ℝ)
          =ᵐ[canonicalMeasure S K m]
            (V.forget (3 / 4 : ℝ) 0 b (hsource₀ z (hU hz) u).choose m : PolarPoint → ℝ) :=
        Filter.Eventually.of_forall (fun p => congrFun hefun p)
      exact hae.trans (hdata.1 m)
    have hplow : p (b + d₁) z ≤ 1 := (hp (le_max_right _ _) z).trans (hlow z hz)
    have hqlow : q (b + d₁) u ≤ q low u := hq (le_max_right _ _) u
    have hq₁ : q low₁ u ≤ q low u := hq (le_max_left _ _) u
    have hfactor : q (b + d₁) u + (1 + p (b + d₁) z) * q low₁ u ≤ 3 * q low u := by
      have hfirst := mul_le_mul_of_nonneg_right (add_le_add (le_refl (1 : ℝ)) hplow)
        (apply_nonneg (q low₁) u)
      nlinarith only [hfirst, hqlow, hq₁]
    have hdataBound : ‖(hsource₀ z (hU hz) u).choose‖ ≤
        A₀ * (q (b + d₁) u + (1 + p (b + d₁) z) * q low₁ u) := hdata.2
    exact (congrArg (fun G : V.level (3 / 4 : ℝ) 0 b => ‖G‖) he).le.trans
      ((hdataBound.trans (mul_le_mul_of_nonneg_left hfactor hA₀.le)).trans_eq (by ring))
  refine ⟨base', hbase₁.trans hbase', ε', hε', hε'le.trans hε₁le,
    low, outLoss, 3 * A₀, by positivity, F₀, hbaseSource, fun t s => ?_⟩
  let sourceHigh := hsource t (b + s)
  let A : ℝ := sourceHigh.choose
  have hA : 0 < A := sourceHigh.choose_spec.1
  have hsourceHigh := sourceHigh.choose_spec.2
  let angularHigh := hangular t s
  let C₁ : ℝ := angularHigh.choose
  have hC₁ : 0 < C₁ := angularHigh.choose_spec.1
  have hQ := angularHigh.choose_spec.2
  refine ⟨C₁ * (A + 3 * A₀), by positivity, fun z hz u => ?_⟩
  let sourcePoint := hsourceHigh z (hU hz) u
  let Fts : V.level (3 / 4 : ℝ) (t : ℝ) (b + s) := sourcePoint.choose
  have hFts := sourcePoint.choose_spec.1
  have hFtsBound := sourcePoint.choose_spec.2
  have hsame : V.forget (3 / 4 : ℝ) (t : ℝ) (b + s) Fts =
      V.forget (3 / 4 : ℝ) 0 b (F₀ z u) := by
    funext m
    apply Lp.ext
    exact (hFts m).trans ((hbaseSource z hz u).1 m).symm
  let inversePoint := hQ z (hU₀ hz) (F₀ z u) Fts hsame
  let Q : V.level (3 / 4 : ℝ) (t : ℝ) (b + s) := inversePoint.choose
  have hQsame := inversePoint.choose_spec.1
  have hQbound := inversePoint.choose_spec.2
  refine ⟨Q, hQsame, hQbound.trans ?_⟩
  let X := q (t + s + outLoss) u + (1 + p (t + s + outLoss) z) * q low u
  have hX : 0 ≤ X := add_nonneg (apply_nonneg _ _)
    (mul_nonneg (add_nonneg zero_le_one (apply_nonneg _ _)) (apply_nonneg _ _))
  have h₁ : t + (b + s) + d₁ ≤ t + s + outLoss := by
    dsimp only [outLoss]
    have hh := le_max_left d₁ d₂
    omega
  have h₂ : b + t + s + d₂ ≤ t + s + outLoss := by
    dsimp only [outLoss]
    have hh := le_max_right d₁ d₂
    omega
  have hF : ‖Fts‖ ≤ A * X := hFtsBound.trans
    (mul_le_mul_of_nonneg_left
      (add_le_add (hq h₁ u)
        (mul_le_mul (add_le_add le_rfl (hp h₁ z))
          (hq (le_max_left _ _) u) (apply_nonneg _ _)
          (add_nonneg zero_le_one (apply_nonneg _ _)))) hA.le)
  have hbase : (1 + p (b + t + s + d₂) z) * ‖F₀ z u‖ ≤ (3 * A₀) * X := by
    calc
      _ ≤ (1 + p (t + s + outLoss) z) * ((3 * A₀) * q low u) :=
        mul_le_mul (add_le_add le_rfl (hp h₂ z)) (hbaseSource z hz u).2
          (norm_nonneg _) (add_nonneg zero_le_one (apply_nonneg _ _))
      _ ≤ (3 * A₀) * X := by
        dsimp only [X]
        nlinarith only [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hA₀.le)
          (apply_nonneg (q (t + s + outLoss)) u)]
  exact (mul_le_mul_of_nonneg_left (add_le_add hF hbase) hC₁.le).trans_eq (by ring)

end ContinuousFlexibility.Analysis
