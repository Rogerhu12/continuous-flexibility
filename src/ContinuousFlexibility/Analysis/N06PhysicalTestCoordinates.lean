import ContinuousFlexibility.Analysis.N05CanonicalTests
import ContinuousFlexibility.Analysis.N06ScalarColumns
import ContinuousFlexibility.Analysis.N06FinitePieceTests

/-!
# Continuous test coordinates of the original graph and source

The original forget map is only declared linear into a dependent function
space. Its value on each fixed cylinder is nevertheless a continuous
linear map: the volume-model identity identifies it with the actual
weighted zeroth jet. The graph height and all three scalar coordinates
are continuous projections of the original graph. These maps make every
finite collection of actual L2 test pairings a closed condition on the
same graph and source spaces.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

variable {S : PhysicalSpacesData} {K : CanonicalData S}
  {V : VolumeModelData S K} {b : ℕ}

/-- The actual material-weighted zeroth coordinate on one cylinder. -/
def n06VolumeCoordinate (T : MaterialData) (V : VolumeModelData S K)
    (γ t : ℝ) (s m : ℕ) : V.level γ t s →L[ℝ] CanonicalL2 S K m :=
  (T.M (T.sample (K.cell m)) ^ (-t) * T.H (T.sample (K.cell m)) ^ γ) •
    ((n05CanonicalJetCoordinate S K s m 0).comp (V.level γ t s).subtypeL)

theorem n06VolumeCoordinate_apply {T : MaterialData}
    (hV : IsVolumeModel T S K V) (γ t : ℝ) (s m : ℕ) (F : V.level γ t s) :
    n06VolumeCoordinate T V γ t s m F = V.forget γ t s F m := by
  simp only [n06VolumeCoordinate, smul_apply,
    ContinuousLinearMap.comp_apply, n05CanonicalJetCoordinate_apply,
    Submodule.subtypeL_apply, hV.2.2.2 γ t s F m]

/-- A cylinder height is projected from the original graph, without
using a chosen inverse or changing its domain. -/
def n06GraphHeightCoordinate (B : CanonicalDomainData S K V b) (m : ℕ) :
    B.Space →L[ℝ] CanonicalL2 S K m :=
  (lp.evalCLM ℝ (fun n => CanonicalL2 S K n) 2 m).comp
    ((ContinuousLinearMap.fst ℝ (CanonicalL2Sequence S K) (ℝ × ℝ × ℝ)).comp
      ((ContinuousLinearMap.fst ℝ (CanonicalUnknown S K)
        (V.level (3 / 4 : ℝ) 0 b)).comp B.graph.subtypeL))

theorem n06GraphHeightCoordinate_apply (B : CanonicalDomainData S K V b)
    (m : ℕ) (u : B.Space) : n06GraphHeightCoordinate B m u = u.val.1.1 m := by
  simp only [n06GraphHeightCoordinate, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', Submodule.subtypeL_apply]
  exact LinearMap.mkContinuous_apply ..

def n06GraphScalars (B : CanonicalDomainData S K V b) :
    B.Space →L[ℝ] (ℝ × ℝ × ℝ) :=
  (ContinuousLinearMap.snd ℝ (CanonicalL2Sequence S K) (ℝ × ℝ × ℝ)).comp
    ((ContinuousLinearMap.fst ℝ (CanonicalUnknown S K)
      (V.level (3 / 4 : ℝ) 0 b)).comp B.graph.subtypeL)

theorem n06GraphScalars_apply (B : CanonicalDomainData S K V b) (u : B.Space) :
    n06GraphScalars B u = u.val.1.2 := by
  simp only [n06GraphScalars, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Submodule.subtypeL_apply]

/-- An actual finite test residual on the fixed graph-source product. -/
def n06GraphSourceTestResidual (T : MaterialData)
    (B : CanonicalDomainData S K V b) (I : Finset ℕ)
    (heightTest sourceTest : ℕ → PolarPoint → ℝ)
    (hh : ∀ m, MemLp (heightTest m) 2 (canonicalMeasure S K m))
    (hf : ∀ m, MemLp (sourceTest m) 2 (canonicalMeasure S K m))
    (s k c : ℝ) : (B.Space × V.level (3 / 4 : ℝ) 0 b) →L[ℝ] ℝ :=
  n06FinitePieceResidual (E := B.Space × V.level (3 / 4 : ℝ) 0 b) (canonicalMeasure S K) I
    (fun m => (n06GraphHeightCoordinate B m).comp
      (ContinuousLinearMap.fst ℝ B.Space (V.level (3 / 4 : ℝ) 0 b)))
    (fun m => (n06VolumeCoordinate T V (3 / 4 : ℝ) 0 b m).comp
      (ContinuousLinearMap.snd ℝ B.Space (V.level (3 / 4 : ℝ) 0 b)))
    (fun m => (hh m).toLp (heightTest m)) (fun m => (hf m).toLp (sourceTest m))
    ((n06ScalarSynthesis s k c).comp
      ((n06GraphScalars B).comp
        (ContinuousLinearMap.fst ℝ B.Space (V.level (3 / 4 : ℝ) 0 b))))

theorem n06GraphSourceTestResidual_apply {T : MaterialData}
    (hV : IsVolumeModel T S K V) (B : CanonicalDomainData S K V b) (I : Finset ℕ)
    (heightTest sourceTest : ℕ → PolarPoint → ℝ)
    (hh : ∀ m, MemLp (heightTest m) 2 (canonicalMeasure S K m))
    (hf : ∀ m, MemLp (sourceTest m) 2 (canonicalMeasure S K m))
    (s k c : ℝ) (p : B.Space × V.level (3 / 4 : ℝ) 0 b) :
    n06GraphSourceTestResidual T B I heightTest sourceTest hh hf s k c p =
      (∑ m ∈ I, ((∫ q, p.1.val.1.1 m q * heightTest m q ∂canonicalMeasure S K m) -
        ∫ q, V.forget (3 / 4 : ℝ) 0 b p.2 m q * sourceTest m q
          ∂canonicalMeasure S K m)) +
      (p.1.val.1.2.1 * s + p.1.val.1.2.2.1 * k + p.1.val.1.2.2.2 * c) := by
  simp only [n06GraphSourceTestResidual, n06FinitePieceResidual_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', n06GraphHeightCoordinate_apply,
    n06VolumeCoordinate_apply hV, n06GraphScalars_apply,
    n06ScalarSynthesis_apply, smul_eq_mul]
  apply congrArg (fun a : ℝ => a +
    (p.1.val.1.2.1 * s + p.1.val.1.2.2.1 * k + p.1.val.1.2.2.2 * c))
  apply Finset.sum_congr rfl
  intro m _
  apply congrArg₂ (fun a b : ℝ => a - b)
  · apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (hh m)] with q hq
    rw [hq]
  · apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (hf m)] with q hq
    rw [hq]

/-- The physical coordinates themselves give a closed residual equation;
continuity of the full dependent forget map is not an extra assumption. -/
theorem n06GraphSourceTest_isClosed {T : MaterialData}
    (hV : IsVolumeModel T S K V) (B : CanonicalDomainData S K V b) (I : Finset ℕ)
    (heightTest sourceTest : ℕ → PolarPoint → ℝ)
    (hh : ∀ m, MemLp (heightTest m) 2 (canonicalMeasure S K m))
    (hf : ∀ m, MemLp (sourceTest m) 2 (canonicalMeasure S K m)) (s k c : ℝ) :
    IsClosed {p : B.Space × V.level (3 / 4 : ℝ) 0 b |
      (∑ m ∈ I, ((∫ q, p.1.val.1.1 m q * heightTest m q ∂canonicalMeasure S K m) -
        ∫ q, V.forget (3 / 4 : ℝ) 0 b p.2 m q * sourceTest m q
          ∂canonicalMeasure S K m)) +
      (p.1.val.1.2.1 * s + p.1.val.1.2.2.1 * k + p.1.val.1.2.2.2 * c) = 0} := by
  simpa only [n06GraphSourceTestResidual_apply hV] using
    isClosed_eq (n06GraphSourceTestResidual T B I heightTest sourceTest hh hf s k c).continuous
      continuous_const

end ContinuousFlexibility.Statements
