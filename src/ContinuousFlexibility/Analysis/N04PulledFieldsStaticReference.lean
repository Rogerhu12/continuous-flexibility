module

public import ContinuousFlexibility.Analysis.N04RealizationLeadCurrentData

/-!
# State-independent families satisfy the current difference interface

The quantitative part of `CurrentJetDataOn` estimates differences from
the reference.  A state-independent family therefore satisfies it with
zero difference towers, regardless of the sizes of its reference jets.
Only the spatial smoothness and periodicity already requested by the
qualitative part of the interface are used below.

This is a statement about the interface itself, not a counterexample to
the full realization obligation.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

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

/-- No uniform bound on the raw reference derivatives is needed by the
current difference interface for a state-independent family. The
constant towers are retained on the pieces satisfying `P`. -/
theorem n04PulledFields_staticReference_currentJetDataOn
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {P : ℕ → Prop} {base : ℕ} {ε : ℝ} (f₀ : ℕ → PolarPoint → ℝ)
    (hregular : ∀ m, P m → ContDiffOn ℝ ∞ (f₀ m) unitStrip)
    (hperiodic : ∀ m, P m → ∀ q ∈ unitStrip,
      f₀ m (q + (0, Real.pi)) = f₀ m q)
    (hE : ∀ m, 0 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m))) :
    CurrentJetDataOn S T cell P base ε (fun _ m => f₀ m) f₀ := by
  letI : IsTopologicalAddGroup (Parameter S) :=
    (n07aParameterGrading_withSeminorms S).isTopologicalAddGroup
  letI : ContinuousSMul ℝ (Parameter S) :=
    (n07aParameterGrading_withSeminorms S).continuousSMul
  have hopen : IsOpen (sectorNeighborhood S base ε ε) :=
    isOpen_sectorNeighborhood S base ε ε
  have hzero (m i j : ℕ) (q : unitStrip) :
      mixedDerivative i j (fun y => f₀ m y - f₀ m y) q.val = 0 := by
    simp only [sub_self, mixedDerivative_fun_zero]
  let J (m i j : ℕ) (q : unitStrip) :
      SmoothDirections (sectorNeighborhood S base ε ε)
        (fun _ => mixedDerivative i j (fun y => f₀ m y - f₀ m y) q.val) :=
    (smoothDirections_constant hopen (0 : ℝ)).congrOn
      (fun _ _ => (hzero m i j q).symm)
  have hcost (m : ℕ) :
      0 ≤ 1 * T.E0 (T.sample (cell m)) ^ (1 : ℝ) *
        T.H (T.sample (cell m)) ^ (3 / 4 : ℝ) :=
    mul_nonneg (mul_nonneg zero_le_one (Real.rpow_nonneg (hE m) _))
      (Real.rpow_nonneg (hH m) _)
  refine ⟨fun _ _ m hm => ⟨hregular m hm, hperiodic m hm⟩,
    (fun m _ => J m), ⟨0, fun _ => ⟨1, one_pos, ?_⟩⟩,
    fun k => ⟨0, fun _ => ⟨1, one_pos, ?_⟩⟩⟩
  · intro z _ m _ q i j _
    rw [hzero m i j q, abs_zero]
    exact mul_nonneg (hcost m) (apply_nonneg _ _)
  · intro z hz v m _ q i j _
    have hJzero : (J m i j q).D k z v = 0 := by
      by_cases hk : k = 0
      · subst k
        exact smoothDirections_D_zero_apply (smoothDirections_constant hopen (0 : ℝ)) hz v
      · exact smoothDirections_D_constant (smoothDirections_constant hopen (0 : ℝ))
          (Nat.pos_of_ne_zero hk) hz v
    rw [hJzero, abs_zero]
    exact mul_nonneg (hcost m) (oneHighVariationWeight_nonneg _ _ _ _ _)

end ContinuousFlexibility.Analysis
