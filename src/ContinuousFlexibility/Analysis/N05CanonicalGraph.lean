module

public import ContinuousFlexibility.Analysis.N05CanonicalTests

/-!
# The canonical weak angular jet graph is closed

The evenness equation and all weak angular derivative equations are kept
literally. They are intersections of kernels of continuous linear maps on
the actual outer lp and inner finite L² products.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

def n05CanonicalReflectionResidual (S : PhysicalSpacesData) (K : CanonicalData S)
    (s m : ℕ) : CanonicalVolumeJets S K s →L[ℝ] CanonicalL2 S K m :=
  ((n05CanonicalReflection S K m).toContinuousLinearMap -
    ContinuousLinearMap.id ℝ (CanonicalL2 S K m)).comp
      (n05CanonicalJetCoordinate S K s m 0)

theorem n05CanonicalReflectionResidual_apply (S : PhysicalSpacesData) (K : CanonicalData S)
    (s m : ℕ) (v : CanonicalVolumeJets S K s) :
    n05CanonicalReflectionResidual S K s m v =
      n05CanonicalReflection S K m (v m 0) - v m 0 := by
  simp only [n05CanonicalReflectionResidual, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    LinearIsometry.coe_toContinuousLinearMap, n05CanonicalJetCoordinate_apply]

def n05CanonicalWeakTest (S : PhysicalSpacesData) (K : CanonicalData S)
    (s m : ℕ) (j : Fin (s + 1)) (φ : PolarPoint → ℝ) (hφ : CanonicalTest S K m φ) :
    CanonicalVolumeJets S K s →L[ℝ] ℝ :=
  (n05CanonicalTestPairing S K m φ (n05CanonicalTest_memLp hφ)).comp
      (n05CanonicalJetCoordinate S K s m j) -
    (-1 : ℝ) ^ j.val •
      (n05CanonicalTestPairing S K m (mixedDerivative 0 j.val φ)
        (n05CanonicalTest_angular_memLp hφ j.val)).comp
          (n05CanonicalJetCoordinate S K s m 0)

theorem n05CanonicalWeakTest_apply (S : PhysicalSpacesData) (K : CanonicalData S)
    (s m : ℕ) (j : Fin (s + 1)) (φ : PolarPoint → ℝ) (hφ : CanonicalTest S K m φ)
    (v : CanonicalVolumeJets S K s) :
    n05CanonicalWeakTest S K s m j φ hφ v =
      (∫ p, v m j p * φ p ∂canonicalMeasure S K m) -
        (-1 : ℝ) ^ j.val *
          (∫ p, v m 0 p * mixedDerivative 0 j.val φ p ∂canonicalMeasure S K m) := by
  simp only [n05CanonicalWeakTest, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    n05CanonicalJetCoordinate_apply, n05CanonicalTestPairing_apply]

def n05CanonicalClosedSubmodule (S : PhysicalSpacesData) (K : CanonicalData S)
    (s : ℕ) : Submodule ℝ (CanonicalVolumeJets S K s) :=
  (⨅ m : ℕ, (n05CanonicalReflectionResidual S K s m).ker) ⊓
    (⨅ m : ℕ, ⨅ j : Fin (s + 1),
      ⨅ φ : {φ : PolarPoint → ℝ // CanonicalTest S K m φ},
        (n05CanonicalWeakTest S K s m j φ.val φ.prop).ker)

theorem n05CanonicalClosedSubmodule_carrier (S : PhysicalSpacesData) (K : CanonicalData S)
    (s : ℕ) :
    (n05CanonicalClosedSubmodule S K s : Set (CanonicalVolumeJets S K s)) =
      canonicalVolumeGraph S K s := by
  apply Set.ext
  intro v
  change (v ∈ n05CanonicalClosedSubmodule S K s) ↔
    ((∀ m : ℕ, (fun p : PolarPoint => v m 0 (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] (v m 0 : PolarPoint → ℝ)) ∧
      ∀ (m : ℕ) (j : Fin (s + 1)),
        WeakCanonicalAngularDerivative S K m (v m 0) (v m j) j.val)
  simp only [n05CanonicalClosedSubmodule, Submodule.mem_inf, Submodule.mem_iInf,
    LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    n05CanonicalReflectionResidual_apply, n05CanonicalWeakTest_apply, sub_eq_zero]
  constructor
  · rintro ⟨href, hweak⟩
    refine ⟨fun m => (n05CanonicalReflection_fixed_iff S K m (v m 0)).mp (href m), ?_⟩
    intro m j φ hφ
    exact hweak m j ⟨φ, hφ⟩
  · rintro ⟨href, hweak⟩
    exact ⟨fun m => (n05CanonicalReflection_fixed_iff S K m (v m 0)).mpr (href m),
      fun m j φ => hweak m j φ.val φ.prop⟩

theorem n05CanonicalClosedSubmodule_isClosed (S : PhysicalSpacesData)
    (K : CanonicalData S) (s : ℕ) :
    IsClosed (n05CanonicalClosedSubmodule S K s : Set (CanonicalVolumeJets S K s)) := by
  simp only [n05CanonicalClosedSubmodule, Submodule.coe_inf, Submodule.coe_iInf]
  apply IsClosed.inter
  · exact isClosed_iInter fun m => (n05CanonicalReflectionResidual S K s m).isClosed_ker
  · exact isClosed_iInter fun m => isClosed_iInter fun j => isClosed_iInter fun φ =>
      (n05CanonicalWeakTest S K s m j φ.val φ.prop).isClosed_ker

instance n05CanonicalClosedSubmodule_completeSpace (S : PhysicalSpacesData)
    (K : CanonicalData S) (s : ℕ) : CompleteSpace (n05CanonicalClosedSubmodule S K s) :=
  (n05CanonicalClosedSubmodule_isClosed S K s).isComplete.completeSpace_coe

theorem n05CanonicalVolumeGraph_isClosed (S : PhysicalSpacesData)
    (K : CanonicalData S) (s : ℕ) : IsClosed (canonicalVolumeGraph S K s) := by
  rw [← n05CanonicalClosedSubmodule_carrier S K s]
  exact n05CanonicalClosedSubmodule_isClosed S K s

end ContinuousFlexibility.Statements
