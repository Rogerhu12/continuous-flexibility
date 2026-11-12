import ContinuousFlexibility.Analysis.N01cParameterCalculus
import ContinuousFlexibility.Analysis.N01cStateParameterJets
import ContinuousFlexibility.Analysis.N01cStateHeightJets
import ContinuousFlexibility.Analysis.N01cHeightGeometry
import ContinuousFlexibility.Analysis.N01cFullNeighborhood

/-!
# Actual parameter towers for all three original coefficients

The seven scalar inputs are constructed from the actual controlled
profile, its actual radial derivative, and the five continuous-linear
polar jets of `stateU`.  The fundamental theorem of calculus identifies
the jets of the exact integral defining `stateHeight`.

N01a supplies these input towers on the entire joint parameter space.
N01b supplies the positive denominators on the same full neighbourhood
through the geometry-preserving sector projection.  Finite-dimensional
composition therefore gives genuine parameter towers of the three
original coefficient formulas at every interior point.  No coefficient
regularity or quantitative tame estimate is assumed here.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The exact seven scalar inputs of the coefficient formula have actual
parameter towers. Their spatial arguments are fixed, while every original
state coordinate and the real perturbation parameter remain variable. -/
def n01_coefficientInputSmoothDirections
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (p : PolarPoint) (hp : p ∈ annularOpen D) :
    SmoothDirections univ (fun z : AnnularState S × ℝ =>
      profileEnergy (stateProfile D S C z.1) p) ×
    SmoothDirections univ (fun z : AnnularState S × ℝ =>
      radialPartial (profileEnergy (stateProfile D S C z.1)) p) ×
    SmoothDirections univ (fun z : AnnularState S × ℝ =>
      heightRadial (stateHeight D S C z) p) ×
    SmoothDirections univ (fun z : AnnularState S × ℝ =>
      heightAngular (stateHeight D S C z) p) ×
    SmoothDirections univ (fun z : AnnularState S × ℝ =>
      radialPartial (heightRadial (stateHeight D S C z)) p) ×
    SmoothDirections univ (fun z : AnnularState S × ℝ =>
      radialPartial (heightAngular (stateHeight D S C z)) p) ×
    SmoothDirections univ (fun z : AnnularState S × ℝ =>
      angularPartial (heightAngular (stateHeight D S C z)) p) := by
  have hD : RadialProfileGeometry D := by
    obtain ⟨K, hK⟩ := hA.1.1
    exact hK.1
  have hχ : ContDiff ℝ ∞ D.chi := hA.1.2.2.2.1.1
  have hr : p.1 ≠ 0 := (hD.1.trans hp.1.1).ne'
  let L : (AnnularState S × ℝ) →L[ℝ] AnnularState S :=
    ContinuousLinearMap.fst ℝ (AnnularState S) ℝ
  let Jw : SmoothDirections univ (fun z : AnnularState S × ℝ =>
      stateProfile D S C z.1 p.1) :=
    smoothDirections_precompCLM
      (stateProfileSmoothDirections hS hT hA.1.1 hA.2.2.1 p.1 hp.1) L
  let Jwr : SmoothDirections univ (fun z : AnnularState S × ℝ =>
      deriv (stateProfile D S C z.1) p.1) :=
    smoothDirections_precompCLM
      (stateProfileDerivSmoothDirections hS hT hA.1.1 hD hA.2.2.1 hχ p.1 hp.1) L
  let Jq : SmoothDirections univ (fun z : AnnularState S × ℝ => z.2) :=
    smoothDirectionsLinear (ContinuousLinearMap.snd ℝ (AnnularState S) ℝ)
  have henergy : ContDiff ℝ ∞ (fun y : ℝ => 1 + y ^ 2) :=
    contDiff_const.add (contDiff_id.pow 2)
  let JE₀ := smoothDirections_contDiff_comp Jw isOpen_univ henergy.contDiffOn
    (fun _ _ => mem_univ _)
  let JE : SmoothDirections univ (fun z : AnnularState S × ℝ =>
      profileEnergy (stateProfile D S C z.1) p) :=
    JE₀.congr (fun _ _ => rfl)
  let JEr₀ := smoothDirections_realMul (smoothDirections_realConstMul 2 Jw) Jwr
  let JEr : SmoothDirections univ (fun z : AnnularState S × ℝ =>
      radialPartial (profileEnergy (stateProfile D S C z.1)) p) :=
    JEr₀.congr (fun z _ =>
      (radialPartial_profileEnergy (x := p)
        ((contDiff_stateProfile_of_partA hS hT hA z.1).differentiable (by simp) p.1)).symm)
  let Jk₀ := smoothDirectionsAdd Jw
    (smoothDirections_realMul Jq (stateUHeightRadialSmoothDirections hT hS p hp))
  let Jk : SmoothDirections univ (fun z : AnnularState S × ℝ =>
      heightRadial (stateHeight D S C z) p) :=
    Jk₀.congr (fun z _ => (heightRadial_stateHeight hS hT hA z p).symm)
  let Jp₀ := smoothDirections_realMul Jq
    (stateUHeightAngularSmoothDirections hT hS p hp)
  let Jp : SmoothDirections univ (fun z : AnnularState S × ℝ =>
      heightAngular (stateHeight D S C z) p) :=
    Jp₀.congr (fun z _ => (heightAngular_stateHeight hS hT hA z p).symm)
  let Jkr₀ := smoothDirectionsAdd Jwr
    (smoothDirections_realMul Jq (stateURadialHeightRadialSmoothDirections hT hS p hp))
  let Jkr : SmoothDirections univ (fun z : AnnularState S × ℝ =>
      radialPartial (heightRadial (stateHeight D S C z)) p) :=
    Jkr₀.congr (fun z _ => (radialPartial_heightRadial_stateHeight hS hT hA z p).symm)
  let Jpr₀ := smoothDirections_realMul Jq
    (stateURadialHeightAngularSmoothDirections hT hS p hp hr)
  let Jpr : SmoothDirections univ (fun z : AnnularState S × ℝ =>
      radialPartial (heightAngular (stateHeight D S C z)) p) :=
    Jpr₀.congr (fun z _ => (radialPartial_heightAngular_stateHeight hS hT hA z hr).symm)
  let Jpθ₀ := smoothDirections_realMul Jq
    (stateUAngularHeightAngularSmoothDirections hT hS p hp hr)
  let Jpθ : SmoothDirections univ (fun z : AnnularState S × ℝ =>
      angularPartial (heightAngular (stateHeight D S C z)) p) :=
    Jpθ₀.congr (fun z _ => (angularPartial_heightAngular_stateHeight hS hT hA z hr).symm)
  exact ⟨JE, JEr, Jk, Jp, Jkr, Jpr, Jpθ⟩

/-- N01a and N01b imply parameter smoothness of all three actual original
coefficients on N01b's full neighbourhood, with its unchanged base and
radius. There are no assumed input towers or denominator hypotheses. -/
def n01_originalCoefficientsSmoothDirections
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    (p : PolarPoint) (hp : p ∈ annularOpen D) :
    SmoothDirections (stateNeighborhood S C base ε)
      (fun z => (originalCoefficients D S C z).a p) ×
    SmoothDirections (stateNeighborhood S C base ε)
      (fun z => (originalCoefficients D S C z).b p) ×
    SmoothDirections (stateNeighborhood S C base ε)
      (fun z => (originalCoefficients D S C z).c p) := by
  have hD : RadialProfileGeometry D := by
    obtain ⟨K, hK⟩ := hA.1.1
    exact hK.1
  let J := n01_coefficientInputSmoothDirections hS hT hA p hp
  have hU := isOpen_stateNeighborhood S C base ε
  refine originalCoefficientsSmoothDirections D S C (stateNeighborhood S C base ε) p
    (J.1.restrict hU (subset_univ _))
    (J.2.1.restrict hU (subset_univ _))
    (J.2.2.1.restrict hU (subset_univ _))
    (J.2.2.2.1.restrict hU (subset_univ _))
    (J.2.2.2.2.1.restrict hU (subset_univ _))
    (J.2.2.2.2.2.1.restrict hU (subset_univ _))
    (J.2.2.2.2.2.2.restrict hU (subset_univ _)) ?_ ?_
  · intro z hz
    exact (n01PartB_denominators_pos hD hS hA.2.1 hB hz hp).2.2
  · intro z hz
    exact (n01PartB_denominators_pos hD hS hA.2.1 hB hz hp).2.1.ne'

end ContinuousFlexibility.Statements
