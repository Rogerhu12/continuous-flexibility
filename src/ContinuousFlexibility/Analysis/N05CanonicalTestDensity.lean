module

public import ContinuousFlexibility.Analysis.N05CanonicalUniqueness
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Density of actual smooth periodic canonical tests in L²

The prescribed canonical tests form a linear space. Their orthogonal
complement is trivial by the distributional separation theorem, so their
actual L² classes are dense in each canonical rectangle.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace

theorem n05CanonicalTest_zero (S : PhysicalSpacesData) (K : CanonicalData S) (m : ℕ) :
    CanonicalTest S K m (0 : PolarPoint → ℝ) := by
  refine ⟨contDiff_const, ?_, ∅, isCompact_empty, empty_subset _, ?_⟩
  · intro p
    rfl
  · intro r hr θ
    rfl

theorem n05CanonicalTest_add {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {φ ψ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) (hψ : CanonicalTest S K m ψ) :
    CanonicalTest S K m (φ + ψ) := by
  obtain ⟨Jφ, hJφ, hJφI, hzφ⟩ := hφ.2.2
  obtain ⟨Jψ, hJψ, hJψI, hzψ⟩ := hψ.2.2
  refine ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1, Jφ ∪ Jψ,
    hJφ.union hJψ, union_subset hJφI hJψI, ?_⟩
  intro r hr θ
  have hrφ : r ∉ Jφ := fun h => hr (Or.inl h)
  have hrψ : r ∉ Jψ := fun h => hr (Or.inr h)
  simp only [Pi.add_apply, hzφ r hrφ θ, hzψ r hrψ θ, add_zero]

theorem n05CanonicalTest_smul {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) (c : ℝ) :
    CanonicalTest S K m (c • φ) := by
  obtain ⟨J, hJ, hJI, hz⟩ := hφ.2.2
  refine ⟨contDiff_const.smul hφ.1, ?_, J, hJ, hJI, ?_⟩
  · intro p
    change c • φ (p + (0, Real.pi)) = c • φ p
    rw [hφ.2.1 p]
  · intro r hr θ
    simp only [Pi.smul_apply, hz r hr θ, smul_zero]

def n05CanonicalTestL2 {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) : CanonicalL2 S K m :=
  (n05CanonicalTest_memLp hφ).toLp φ

theorem n05CanonicalTestL2_ae {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) :
    (n05CanonicalTestL2 hφ : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] φ :=
  MemLp.coeFn_toLp (n05CanonicalTest_memLp hφ)

theorem n05CanonicalTestL2_add {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {φ ψ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) (hψ : CanonicalTest S K m ψ) :
    n05CanonicalTestL2 (n05CanonicalTest_add hφ hψ) =
      n05CanonicalTestL2 hφ + n05CanonicalTestL2 hψ :=
  MemLp.toLp_add (n05CanonicalTest_memLp hφ) (n05CanonicalTest_memLp hψ)

theorem n05CanonicalTestL2_smul {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) (c : ℝ) :
    n05CanonicalTestL2 (n05CanonicalTest_smul hφ c) = c • n05CanonicalTestL2 hφ :=
  MemLp.toLp_const_smul c (n05CanonicalTest_memLp hφ)

def n05CanonicalTestSubmodule (S : PhysicalSpacesData) (K : CanonicalData S) (m : ℕ) :
    Submodule ℝ (CanonicalL2 S K m) where
  carrier := {u | ∃ (φ : PolarPoint → ℝ) (hφ : CanonicalTest S K m φ),
    n05CanonicalTestL2 hφ = u}
  zero_mem' := ⟨0, n05CanonicalTest_zero S K m, MemLp.toLp_zero _⟩
  add_mem' := by
    rintro u v ⟨φ, hφ, rfl⟩ ⟨ψ, hψ, rfl⟩
    exact ⟨φ + ψ, n05CanonicalTest_add hφ hψ, n05CanonicalTestL2_add hφ hψ⟩
  smul_mem' := by
    rintro c u ⟨φ, hφ, rfl⟩
    exact ⟨c • φ, n05CanonicalTest_smul hφ c, n05CanonicalTestL2_smul hφ c⟩

theorem n05CanonicalTestSubmodule_dense (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) :
    Dense (n05CanonicalTestSubmodule S K m : Set (CanonicalL2 S K m)) := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  rw [Submodule.topologicalClosure_eq_top_iff]
  apply (Submodule.eq_bot_iff _).mpr
  intro u hu
  apply n05CanonicalL2_eq_zero_of_test S K m u
  intro φ hφ
  have hi : inner ℝ (n05CanonicalTestL2 hφ) u = 0 :=
    ((n05CanonicalTestSubmodule S K m).mem_orthogonal u).mp hu _
      ⟨φ, hφ, rfl⟩
  exact (n05CanonicalTestPairing_apply S K m φ (n05CanonicalTest_memLp hφ) u).symm.trans hi

end ContinuousFlexibility.Statements

