module

public import ContinuousFlexibility.Analysis.N07aActualNormalFamilyData
public import ContinuousFlexibility.Analysis.N07aCurrentNormalBounds
public import ContinuousFlexibility.Analysis.N07aNormalExpansionTame
public import ContinuousFlexibility.Analysis.N07aLinearJetsFromL2
public import ContinuousFlexibility.Analysis.SolveResidualSpaces

/-!
# Fixed-loss jets of the same actual canonical solution

Only finitely many fixed low-order balls are intersected. The original
first-normal weak jets and the original source with its three scalar
columns feed the exact normal recurrence. Open-strip Sobolev estimates
then give the pointwise mixed jets used in physical reconstruction.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff BigOperators ENNReal

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

private theorem n07a_normalTerminal_mono
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (hp : Monotone p) (hq : Monotone q)
    {low₀ low d₀ d k : ℕ} (hlow : low₀ ≤ low) (hd : d₀ ≤ d)
    {e w : ℝ} (he : 0 ≤ e) (hw : 0 ≤ w) (z : E) (f : F) {N : ℝ≥0∞}
    (hN : N ≤ ENNReal.ofReal (e * w *
      (q (k + d₀) f + (1 + p (k + d₀) z) * q low₀ f))) :
    N ≤ ENNReal.ofReal (e * w *
      (q (k + d) f + (1 + p (k + d) z) * q low f)) := by
  apply hN.trans (ENNReal.ofReal_le_ofReal ?_)
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg he hw)
  exact add_le_add (hq (Nat.add_le_add_left hd k) f)
    (mul_le_mul (add_le_add le_rfl (hp (Nat.add_le_add_left hd k) z))
      (hq hlow f) (apply_nonneg _ _) (add_nonneg zero_le_one (apply_nonneg _ _)))

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {b : ℕ} {B : CanonicalDomainData S K V b}
  {P : RelativeInverseData S K V b B} {base loss : ℕ} {ε : ℝ}

local instance n07aCanonicalSolutionBoundsLevelGroup :
    NormedAddCommGroup (V.level (3 / 4 : ℝ) 0 b) := Submodule.normedAddCommGroup _
local instance n07aCanonicalSolutionBoundsLevelSpace :
    NormedSpace ℝ (V.level (3 / 4 : ℝ) 0 b) := Submodule.normedSpace _

theorem n07a_exists_actualCanonicalSolutionData
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hprincipal : CanonicalGeometry.ReferencePrincipal T S C K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (hRatio : N07aActualMaterialRatios T S C K base ε)
    (h05 : N05Properties D T S C K V b B)
    (h06 : N06Properties D S C K L V b B P base ε)
    (hAngular : N07aAngularProperties S C K V b B P base ε) :
    ∃ base' : ℕ, base ≤ base' ∧ ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      Nonempty (N07aActualCanonicalSolutionData D T S C L K V b B P base' ε') := by
  classical
  let data : N07aActualNormalFamilyData D T S C L K V b B P base ε :=
    Classical.choice (n07a_exists_actualNormalFamilyData hD hT hS h01 h04 href
      hprincipal hcur h05 h06 hAngular)
  let p := CanonicalGeometry.parameterGrading S
  let q := S.sourceGrading
  let weight : ℕ → ℕ → ℝ := fun c m =>
    T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) * (T.M (T.sample (K.cell m)) ^ c)⁻¹
  have hp : Monotone p := n07aParameterGrading_monotone S
  have hq : Monotone q := n07aSourceGrading_monotone S
  have hIp : HasSmoothing p :=
    hasSmoothing_pairGrading (solve_sector_hasSmoothing hS) hasSmoothing_realGrading
  have hIq : HasSmoothing q := solve_source_hasSmoothing hS
  have hw (c m : ℕ) : 0 ≤ weight c m := by
    have hs := hT.2.1 _ (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m))
    exact mul_nonneg (Real.rpow_nonneg hs.2.1.le _)
      (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans hs.2.2.2) c))
  let α := fun z f => n07aUnknownScalar (n07aActualCanonicalUnknown C B P data.F₀ z f)
  let source := n07aCanonicalSourceWithoutColumns D S C L K α
  let A := n07aNormalCoefficientFamily
    (fun k z m => n07aPrincipalField K (liftSectorParameter S C z) m k)
    (fun m => if K.positive m then -1 else 1)
  have hs := n07a_actualSource_withoutColumns_terminal hD hS hT h01 h04 href hcur hRatio
    α data.low data.Cα data.Cα_nonneg data.scalars
  let lowS : ℕ := hs.choose
  let dS : ℕ := hs.choose_spec.choose
  have hsbound := hs.choose_spec.choose_spec
  have ha := n07a_currentNormalCoefficients_sampleJetBounds hD hT hS href hcur data.interval
  let lowA : ℕ := ha.choose
  let dA : ℕ := ha.choose_spec.choose
  have habound := ha.choose_spec.choose_spec
  have hn₁ := n07a_lowParameter_neighborhood (S := S) (base := data.neighborhoodBase)
    data.radius_pos (max lowA lowS)
  let b₁ : ℕ := hn₁.choose
  let e₁ : ℝ := hn₁.choose_spec.2.choose
  have hn₁b := hn₁.choose_spec.2.choose_spec
  let Ω₁ := sectorNeighborhood S b₁ e₁ e₁
  have hΩdata : Ω₁ ⊆ sectorNeighborhood S data.neighborhoodBase
      data.neighborhoodRadius data.neighborhoodRadius := hn₁b.2.2.1
  have hΩold : Ω₁ ⊆ sectorNeighborhood S base ε ε := fun z hz =>
    n07a_sectorNeighborhood_mono (S := S) data.base_le data.radius_le (hΩdata hz)
  have hlowA (z : CanonicalGeometry.Parameter S) (hz : z ∈ Ω₁) : p lowA z ≤ 1 :=
    (hp (le_max_left lowA lowS) z).trans (hn₁b.2.2.2 z hz)
  have hlowS (z : CanonicalGeometry.Parameter S) (hz : z ∈ Ω₁) : p lowS z ≤ 1 :=
    (hp (le_max_right lowA lowS) z).trans (hn₁b.2.2.2 z hz)
  have hA (i : Fin 6) : N07aSampleJetBounds T K p Ω₁ (canonicalOpen S K) dA (A i) :=
    (habound i).restrict (fun z hz => ⟨hΩold hz, hlowA z hz⟩)
  have hAs (i : Fin 6) (z : CanonicalGeometry.Parameter S) (hz : z ∈ Ω₁) (m : ℕ) :
      ContDiffOn ℝ ∞ (A i z m) (canonicalOpen S K m) := by
    let χ := n07aCurrentOpenCoefficient href hcur z (hΩold hz) m (data.interval m)
    have h := n07aOpenNormalCoefficients_smooth (χ 0) (χ 1) (χ 2) (χ 3)
      ((χ 4).constMul (if K.positive m then -1 else 1)) i
    rw [n07a_currentNormalCoefficients_eq href hcur z (hΩold hz) m (data.interval m) i] at h
    exact h
  have hws (z : CanonicalGeometry.Parameter S) (hz : z ∈ Ω₁) (f : S.Source) (m : ℕ) :
      ContDiffOn ℝ ∞ (data.w z f m) (canonicalOpen S K m) := by
    rw [data.decode z (hΩdata hz) f m]
    exact (n07aCanonicalSmoothRepresentative_properties (data.interval m)
      ⟨_, data.regular z (hΩdata hz) f m⟩).1
  have hwp (z : CanonicalGeometry.Parameter S) (hz : z ∈ Ω₁) (f : S.Source) (m : ℕ) :
      Function.Periodic (data.w z f m) (0, Real.pi) := by
    rw [data.decode z (hΩdata hz) f m]
    exact (n07aCanonicalSmoothRepresentative_properties (data.interval m)
      ⟨_, data.regular z (hΩdata hz) f m⟩).2.1
  have hfs (z : CanonicalGeometry.Parameter S) (hz : z ∈ Ω₁) (f : S.Source) (m : ℕ) :
      ContDiffOn ℝ ∞ (source z f m) (canonicalOpen S K m) := by
    have hsource := n07a_canonicalSource_contDiffOn h01.2.2.1 h04 hcur z (hΩold hz)
      ((hS.1 (3 / 4 : ℝ)).2.2.2.1 f.val).1 m
    have hcolumns : ContDiffOn ℝ ∞
        (fun y => ∑ i : Fin 3, α z f i *
          n07aScalarColumn D S C L K (liftSectorParameter S C z) m i y)
        (canonicalOpen S K m) :=
      ContDiffOn.sum (fun i _ => contDiffOn_const.mul
        (n07aCurrentScalarOpenCoefficient href hcur z (hΩold hz) m (data.interval m) i).smooth)
    exact hsource.sub hcolumns
  have heq (z : CanonicalGeometry.Parameter S) (hz : z ∈ Ω₁) (f : S.Source) (m : ℕ) :
      EqOn (mixedDerivative 2 0 (data.w z f m))
        (n07aNormalRhs (fun i => A i z m) (data.w z f m) (source z f m))
        (canonicalOpen S K m) := data.equation z (hΩdata hz) f m
  let low : ℕ := max data.low lowS
  let df : ℕ := max data.firstLoss dS
  have hterminal : ∀ sourceFlag : Bool, ∀ a n : ℕ, (sourceFlag = false → a ≤ 1) →
      ∀ c : ℕ, ∃ e : ℕ → ℝ, N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ z ∈ Ω₁, ∀ f m,
          eLpNorm (mixedDerivative a n (if sourceFlag then source z f m else data.w z f m))
            2 (canonicalMeasure S K m) ≤ ENNReal.ofReal
              (e m * weight c m * (q (c + (a + n) + df) f +
                (1 + p (c + (a + n) + df) z) * q low f)) := by
    intro sourceFlag a n ha c
    cases sourceFlag with
    | false =>
      let bound := data.firstWeak a (ha rfl) n c
      let C₁ : ℝ := bound.choose
      have hC₁ : 0 < C₁ := bound.choose_spec.1
      refine ⟨fun _ => C₁, N07aSampleSubpower.const hD hT C₁,
        fun _ => hC₁.le, fun z hz f m => ?_⟩
      let jet := bound.choose_spec.2 z (hΩdata hz) f m
      let J : CanonicalL2 S K m := jet.choose
      have hJ := jet.choose_spec
      let u : n07aCanonicalSmoothSpace S K m :=
        ⟨(n07aActualCanonicalUnknown C B P data.F₀ z f).1 m,
          data.regular z (hΩdata hz) f m⟩
      have he : eLpNorm (mixedDerivative a n (data.w z f m)) 2 (canonicalMeasure S K m) =
          ENNReal.ofReal ‖J‖ := by
        calc
          _ = eLpNorm (mixedDerivative a n (n07aCanonicalSmoothDecode (data.interval m) u))
              2 (canonicalMeasure S K m) :=
            congrArg (fun v : PolarPoint → ℝ => eLpNorm (mixedDerivative a n v)
              2 (canonicalMeasure S K m)) (data.decode z (hΩdata hz) f m)
          _ = eLpNorm (J : PolarPoint → ℝ) 2 (canonicalMeasure S K m) :=
            eLpNorm_congr_ae (n07aCanonicalSmoothDecode_mixed_ae (data.interval m) a n u J hJ.1)
          _ = ENNReal.ofReal ‖J‖ := by rw [← Lp.enorm_def, ← ofReal_norm]
      exact n07a_normalTerminal_mono p q hp hq (le_max_left data.low lowS)
        (le_max_left data.firstLoss dS) hC₁.le (hw c m) z f
        (he.le.trans (ENNReal.ofReal_le_ofReal hJ.2))
    | true =>
      let bound := hsbound a n c
      refine ⟨bound.choose, bound.choose_spec.1, bound.choose_spec.2.1, fun z hz f m => ?_⟩
      exact n07a_normalTerminal_mono p q hp hq (le_max_right data.low lowS)
        (le_max_right data.firstLoss dS) (bound.choose_spec.2.1 m) (hw c m) z f
        (bound.choose_spec.2.2 z (hΩold hz) (hlowS z hz) f m)
  have hn := n07a_normalExpansion_fixedLoss hD hT p q hp hq hIp hIq Ω₁ weight hw
    A data.w source dA low df hA hAs hws hfs heq hterminal
  let low₂ : ℕ := hn.choose
  let d₂ : ℕ := hn.choose_spec.choose
  have hnb := hn.choose_spec.choose_spec
  have hn₂ := n07a_lowParameter_neighborhood (S := S) (base := b₁) hn₁b.1 low₂
  let b₂ : ℕ := hn₂.choose
  let e₂ : ℝ := hn₂.choose_spec.2.choose
  have hn₂b := hn₂.choose_spec.2.choose_spec
  let Ω₂ := sectorNeighborhood S b₂ e₂ e₂
  have hΩ₂ : Ω₂ ⊆ Ω₁ := hn₂b.2.2.1
  have hL2 : ∀ a n c : ℕ, ∃ e : ℕ → ℝ, N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
      ∀ z ∈ Ω₂, ∀ f m,
        eLpNorm (mixedDerivative a n (data.w z f m)) 2 (canonicalMeasure S K m) ≤
          ENNReal.ofReal (e m * weight c m * (q (c + (a + n) + d₂) f +
            (1 + p (c + (a + n) + d₂) z) * q low₂ f)) := by
    intro a n c
    let bound := hnb a n c
    exact ⟨bound.choose, bound.choose_spec.1, bound.choose_spec.2.1,
      fun z hz f m => bound.choose_spec.2.2 z (hΩ₂ hz) (hn₂b.2.2.2 z hz) f m⟩
  have hj := n07a_sampleLinearJetBounds_of_mixed_L2 hD hT href data.interval p q hp hq
    Ω₂ weight hw low₂ d₂ data.w
    (fun z hz => hws z (hΩ₂ hz))
    (fun z hz f m y _ => hwp z (hΩ₂ hz) f m y) hL2
  let finalLow : ℕ := max data.low low₂
  have hj' := hj.low_mono hq hw (le_max_right data.low low₂)
  have hbase : base ≤ b₂ := data.base_le.trans (hn₁.choose_spec.1.trans hn₂.choose_spec.1)
  have he : e₂ ≤ ε := hn₂b.2.1.trans (hn₁b.2.1.trans data.radius_le)
  have hΩfinal : Ω₂ ⊆ sectorNeighborhood S data.neighborhoodBase
      data.neighborhoodRadius data.neighborhoodRadius := fun _ hz => hΩdata (hΩ₂ hz)
  refine ⟨b₂, hbase, e₂, hn₂b.1, he, ⟨{
    F₀ := data.F₀
    w := data.w
    interval := data.interval
    low := finalLow
    loss := d₂ + 2
    C₀ := data.C₀
    Cα := data.Cα
    C₀_pos := data.C₀_pos
    Cα_nonneg := data.Cα_nonneg
    baseNorm := ?_
    scalars := ?_
    sourceAE := fun z hz => data.sourceAE z (hΩfinal hz)
    relation := fun z hz => data.relation z (hΩfinal hz)
    even := fun z hz => data.even z (hΩfinal hz)
    regular := fun z hz => data.regular z (hΩfinal hz)
    decode := fun z hz => data.decode z (hΩfinal hz)
    equation := fun z hz => data.equation z (hΩfinal hz)
    jets := hj'
  }⟩⟩
  · intro z _ f
    exact (data.baseNorm z f).trans (mul_le_mul_of_nonneg_left
      (hq (le_max_left data.low low₂) f) data.C₀_pos.le)
  · intro z hz f i
    exact (data.scalars z (hΩold (hΩ₂ hz)) f i).trans
      (mul_le_mul_of_nonneg_left (hq (le_max_left data.low low₂) f) data.Cα_nonneg)

end ContinuousFlexibility.Analysis
