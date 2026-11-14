module

public import ContinuousFlexibility.Analysis.N07aFiniteScalarColumnJets
public import ContinuousFlexibility.Analysis.N07aSourceLinearTerminal
public import ContinuousFlexibility.Analysis.N07aScalarColumnVolumes
public import ContinuousFlexibility.Analysis.N07aCanonicalSourceRegularity
public import ContinuousFlexibility.Analysis.N07aModeBudgetMaterial
public import ContinuousFlexibility.Analysis.N07aReferenceScalarMaps
public import ContinuousFlexibility.Analysis.N07aBaseInverse

/-!
# The original canonical source after subtracting its three actual columns

The column coefficients need only the low-source bound supplied by the
same base inverse. Fixed physical support gives every material decay
order for these actual columns. Subtraction from the original canonical
source yields exactly the mixed L² terminal used by normal expansion.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff BigOperators ENNReal

set_option backward.isDefEq.respectTransparency true

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul n07aNonlinearSectorParameterSub

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S} {L : ReturnCorrectionData S}
  {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}

local instance n07aScalarSourceGroup : AddCommGroup S.Source := Submodule.addCommGroup _
local instance n07aScalarSourceModule : Module ℝ S.Source := Submodule.module _
local instance n07aScalarSourceSMul : SMul ℝ S.Source :=
  (inferInstance : Module ℝ S.Source).toSMul

def n07aCanonicalSourceWithoutColumns
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (K : CanonicalData S)
    (α : Parameter S → S.Source → Fin 3 → ℝ)
    (z : Parameter S) (f : S.Source) (m : ℕ) : PolarPoint → ℝ := fun y =>
  canonicalSource S K (liftSectorParameter S C z) m
    ((S.height (3 / 4 : ℝ)).decode f.val) y -
      ∑ i : Fin 3, α z f i * n07aScalarColumn D S C L K (liftSectorParameter S C z) m i y

theorem n07a_actualSource_withoutColumns_terminal
    (hD : IsAccumulatingProfile D) (hS : IsPhysicalSpaces D T S)
    (hT : IsMaterialData D T) (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (hRatio : N07aActualMaterialRatios T S C K base ε)
    (α : Parameter S → S.Source → Fin 3 → ℝ) (lowα : ℕ) (Aα : ℝ) (hAα : 0 ≤ Aα)
    (hα : ∀ z ∈ sectorNeighborhood S base ε ε, ∀ f i,
      |α z f i| ≤ Aα * S.sourceGrading lowα f) :
    ∃ low d : ℕ, ∀ a b c : ℕ, ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
      ∀ z ∈ sectorNeighborhood S base ε ε, parameterGrading S low z ≤ 1 → ∀ f m,
        eLpNorm (mixedDerivative a b (n07aCanonicalSourceWithoutColumns D S C L K α z f m))
          2 (canonicalMeasure S K m) ≤
            ENNReal.ofReal (e m * (T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
              (T.M (T.sample (K.cell m)) ^ c)⁻¹) *
                (S.sourceGrading (c + (a + b) + d) f +
                  (1 + parameterGrading S (c + (a + b) + d) z) * S.sourceGrading low f)) := by
  let p := parameterGrading S
  let q := S.sourceGrading
  let U₀ := sectorNeighborhood S base ε ε
  let w : ℕ → ℕ → ℝ := fun c m => T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
    (T.M (T.sample (K.cell m)) ^ c)⁻¹
  have hw (c m : ℕ) : 0 < w c m := by
    have hm := hT.2.1 _ (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m))
    exact mul_pos (Real.rpow_pos_of_pos hm.2.1 _) (inv_pos.mpr
      (pow_pos (zero_lt_one.trans_le hm.2.2.2) _))
  have hp : Monotone p := n07aParameterGrading_monotone S
  have hq : Monotone q := fun _ _ h f => gradedSeminorm_monotone _ _ h f.val
  have hI (m : ℕ) : K.left m < K.right m := (h04.1.referenceBounds m).2.1
  let φ : Fin 3 → Parameter S → ℕ → PolarPoint → ℝ :=
    fun i z m => n07aScalarColumn D S C L K (liftSectorParameter S C z) m i
  have hcoeff := n07a_canonicalAtomFields_sampleJetBounds hD hT href hcur hI
  let dc : ℕ := hcoeff.choose
  have hφ (i : Fin 3) : N07aSampleJetBounds T K p U₀ (canonicalOpen S K) dc (φ i) := by
    have heq : φ i = n07aCanonicalAtomField D T S C L K (n07aScalarColumnAtom i) :=
      funext fun z => funext fun m => n07aScalarColumn_eq_atomField z m (hI m) i
    rw [heq]
    exact hcoeff.choose_spec (n07aScalarColumnAtom i)
  have hφs (i : Fin 3) (z : Parameter S) (hz : z ∈ U₀) (m : ℕ) :
      ContDiffOn ℝ ∞ (φ i z m) (canonicalOpen S K m) :=
    (n07aCurrentScalarOpenCoefficient href hcur z hz m (hI m) i).smooth
  let support := n07a_canonicalScalarColumns_finite_support hD hS hT h01 h04 href hRatio
  let I : Finset ℕ := support.choose
  have hsupport := support.choose_spec
  have hzero (i : Fin 3) (z : Parameter S) (hz : z ∈ U₀) (m : ℕ) (hm : m ∉ I) :
      EqOn (φ i z m) (fun _ => (0 : ℝ)) (canonicalOpen S K m) :=
    hsupport _ (liftSectorParameter_mem_stateNeighborhood (S := S) (C := C) hz le_rfl)
      (h01.2.2.1.liftSectorParameter_sector z) m hm i
  have hcols := n07a_finiteScalarColumns_sampleLinearJets hD hT hp w hw φ hφ hφs
    I hzero α Aα hAα hα
  have hsource := n07a_canonicalSource_height_sampleJets hD hT hS
    (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) ≤ 1)
    h01.2.2.1 h04 href hcur hRatio
  let ls : ℕ := hsource.choose
  let ds : ℕ := hsource.choose_spec.choose
  let low : ℕ := max ls lowα
  let d : ℕ := max ds dc
  let U : Set (Parameter S) := {z | z ∈ U₀ ∧ p low z ≤ 1}
  let source : Parameter S → S.Source → ℕ → PolarPoint → ℝ := fun z f m =>
    canonicalSource S K (liftSectorParameter S C z) m ((S.height (3 / 4 : ℝ)).decode f.val)
  let columns : Parameter S → S.Source → ℕ → PolarPoint → ℝ :=
    fun z f m y => ∑ i : Fin 3, α z f i * φ i z m y
  have hsrc : N07aSampleLinearJetBounds T K p q U (canonicalOpen S K) w ls ds source := by
    intro a b c
    have h := hsource.choose_spec.choose_spec a b c
    refine ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1, fun z hz f m y hy => ?_⟩
    exact h.choose_spec.2.2 z
      ⟨hz.1, (hp (le_max_left ls lowα) z).trans hz.2⟩ f.val m y hy
  have hs := (hsrc.low_mono hq (fun c m => (hw c m).le) (le_max_left ls lowα)).loss_mono
    hp hq (fun c m => (hw c m).le) (le_max_left ds dc)
  have hc := ((hcols.restrict (fun z (hz : z ∈ U) => hz.1)).low_mono hq
    (fun c m => (hw c m).le) (le_max_right ls lowα)).loss_mono
      hp hq (fun c m => (hw c m).le) (le_max_right ds dc)
  have hss (z : Parameter S) (hz : z ∈ U) (f : S.Source) (m : ℕ) :
      ContDiffOn ℝ ∞ (source z f m) (canonicalOpen S K m) :=
    n07a_canonicalSource_contDiffOn h01.2.2.1 h04 hcur z hz.1
      ((hS.1 (3 / 4 : ℝ)).2.2.2.1 f.val).1 m
  have hcs (z : Parameter S) (hz : z ∈ U) (f : S.Source) (m : ℕ) :
      ContDiffOn ℝ ∞ (columns z f m) (canonicalOpen S K m) :=
    ContDiffOn.sum (fun i _ => contDiffOn_const.mul (hφs i z hz.1 m))
  have ht := hs.sub hc hss hcs
  have hperiodic (z : Parameter S) (hz : z ∈ U) (f : S.Source) (m : ℕ)
      (y : PolarPoint) (hy : y ∈ canonicalOpen S K m) :
      (source z f m (y + (0, Real.pi)) - columns z f m (y + (0, Real.pi))) =
        source z f m y - columns z f m y := by
    have hs : source z f m (y + (0, Real.pi)) = source z f m y :=
      n07a_canonicalSource_periodic_on h01.2.2.1 h04 hcur z hz.1
        ((hS.1 (3 / 4 : ℝ)).2.2.2.1 f.val).2.2.1 m y hy
    have hc : columns z f m (y + (0, Real.pi)) = columns z f m y :=
      Finset.sum_congr rfl (fun i _ => congrArg (fun t : ℝ => α z f i * t)
        ((n07aCurrentScalarOpenCoefficient href hcur z hz.1 m (hI m) i).periodic y hy))
    exact congrArg₂ (fun r s : ℝ => r - s) hs hc
  have hterminal := n07a_sampleLinearJet_mixed_eLpNorm hD hT hI
    (n07a_canonicalModeNormalization_subpower hD hT href) (fun c m => (hw c m).le)
    ht (fun z hz f m => (hss z hz f m).sub (hcs z hz f m)) hperiodic
  refine ⟨low, d, fun a b c => ?_⟩
  let bound := hterminal a b c
  let e : ℕ → ℝ := bound.choose
  have he : N07aSampleSubpower T K e := bound.choose_spec.1
  have he0 : ∀ m, 0 ≤ e m := bound.choose_spec.2.1
  exact ⟨e, he, he0, fun z hz hlow f m => bound.choose_spec.2.2 z ⟨hz, hlow⟩ f m⟩

section BaseScalars

variable {V : VolumeModelData S K} {b : ℕ} {B : CanonicalDomainData S K V b}
  {P : RelativeInverseData S K V b B}

local instance n07aScalarSourceLevelGroup : NormedAddCommGroup (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedAddCommGroup _
local instance n07aScalarSourceLevelSpace : NormedSpace ℝ (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedSpace _
local instance n07aScalarSourceUnknownGroup : NormedAddCommGroup (CanonicalUnknown S K) :=
  inferInstance
local instance n07aScalarSourceGraphGroup : NormedAddCommGroup B.Space := Submodule.normedAddCommGroup _
local instance n07aScalarSourceGraphSpace : NormedSpace ℝ B.Space := Submodule.normedSpace _

theorem n07aBaseInverse_scalar_bound
    (h06 : N06Properties D S C K L V b B P base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (F : V.level (3 / 4 : ℝ) 0 b) (i : Fin 3) :
    |n07aUnknownScalar (n07aBaseInverse B P z F).val.1 i| ≤
      (2 * ‖B.inverse‖) * ‖F‖ :=
  (n07aUnknownScalar_abs_le_norm _ i).trans
    ((norm_fst_le (n07aBaseInverse B P z F).val).trans (n07aBaseInverse_bound h06 hz hs F))

end BaseScalars

end ContinuousFlexibility.Analysis
