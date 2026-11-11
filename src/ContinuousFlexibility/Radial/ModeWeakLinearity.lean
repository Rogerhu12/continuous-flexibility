import ContinuousFlexibility.Radial.ModeTestIntegrability

/-!
# Linear and closed modal weak graphs

The frozen weak equation is expressed using genuine Hilbert test vectors.
This proves linearity and closure in the existing Lp product topology;
neither property relies on arithmetic with undefined Bochner integrals.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open ContinuousFlexibility.Statements

def matchingSmoothVector (D : ReferenceData) (hD : IsAccumulatingProfile D)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) : RadialModeL2 D :=
  (matching_memLp_of_continuousOn hD hψ.continuous.measurable
    hψ.continuous.continuousOn 2).toLp ψ

def matchingJacobiVector (D : ReferenceData) (hD : IsAccumulatingProfile D)
    (j : ℕ) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) : RadialModeL2 D :=
  (matchingJacobiTest_memLp hD hψ j).toLp (matchingJacobiTest D j ψ)

theorem modeLocalEquation_iff_inner {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (j : ℕ) (J : Set ℝ) (U F : RadialModePair D) :
    ModeLocalEquation D j J U F ↔
      ∀ (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ), HasCompactSupport ψ →
        Function.support ψ ⊆ J →
        ⟪U.1, matchingJacobiVector D hD j ψ hψ⟫_ℝ -
            U.2 * (∫ r in D.a..D.b, referenceColumn D r * ψ r) =
          -⟪F.1, matchingSmoothVector D hD ψ hψ⟫_ℝ := by
  constructor
  · intro h ψ hψ hc hs
    have hh := h ψ hψ hc hs
    change (∫ r in D.a..D.b, U.1 r * radialJacobi ((j : ℝ) ^ 2) D.w ψ r) -
      U.2 * (∫ r in D.a..D.b, referenceColumn D r * ψ r) =
      -(∫ r in D.a..D.b, matchingDensity D r * F.1 r * ψ r) at hh
    rw [matchingJacobi_integral_eq_inner hD U.1 hψ j,
      matchingSource_integral_eq_inner hD F.1
        (matching_memLp_of_continuousOn hD hψ.continuous.measurable
          hψ.continuous.continuousOn 2)] at hh
    exact hh
  · intro h ψ hψ hc hs
    have hh := h ψ hψ hc hs
    dsimp only [matchingJacobiVector, matchingSmoothVector] at hh
    rw [← matchingJacobi_integral_eq_inner hD U.1 hψ j,
      ← matchingSource_integral_eq_inner hD F.1
        (matching_memLp_of_continuousOn hD hψ.continuous.measurable
          hψ.continuous.continuousOn 2)] at hh
    exact hh

theorem modeLocalEquation_zero {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (j : ℕ) (J : Set ℝ) : ModeLocalEquation D j J 0 0 := by
  apply (modeLocalEquation_iff_inner hD j J 0 0).mpr
  intro ψ hψ hc hs
  simp only [Prod.fst_zero, Prod.snd_zero, inner_zero_left, zero_mul, sub_zero, neg_zero]

theorem modeLocalEquation_add {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {j : ℕ} {J : Set ℝ} {U F V H : RadialModePair D}
    (hU : ModeLocalEquation D j J U F) (hV : ModeLocalEquation D j J V H) :
    ModeLocalEquation D j J (U + V) (F + H) := by
  apply (modeLocalEquation_iff_inner hD j J _ _).mpr
  intro ψ hψ hc hs
  have hu := (modeLocalEquation_iff_inner hD j J U F).mp hU ψ hψ hc hs
  have hv := (modeLocalEquation_iff_inner hD j J V H).mp hV ψ hψ hc hs
  simp only [Prod.fst_add, Prod.snd_add, inner_add_left, add_mul]
  linarith

theorem modeLocalEquation_smul {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {j : ℕ} {J : Set ℝ} {U F : RadialModePair D}
    (hU : ModeLocalEquation D j J U F) (c : ℝ) :
    ModeLocalEquation D j J (c • U) (c • F) := by
  apply (modeLocalEquation_iff_inner hD j J _ _).mpr
  intro ψ hψ hc hs
  have hu := (modeLocalEquation_iff_inner hD j J U F).mp hU ψ hψ hc hs
  simp only [Prod.fst_smul, Prod.snd_smul, real_inner_smul_left, smul_eq_mul]
  have huc := congrArg (fun z : ℝ => c * z) hu
  nlinarith only [huc]

theorem modeLocalEquation_neg {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {j : ℕ} {J : Set ℝ} {U F : RadialModePair D}
    (hU : ModeLocalEquation D j J U F) :
    ModeLocalEquation D j J (-U) (-F) := by
  simpa only [neg_one_smul] using modeLocalEquation_smul hD hU (-1)

theorem modeLocalEquation_sub {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {j : ℕ} {J : Set ℝ} {U F V H : RadialModePair D}
    (hU : ModeLocalEquation D j J U F) (hV : ModeLocalEquation D j J V H) :
    ModeLocalEquation D j J (U - V) (F - H) := by
  simpa only [sub_eq_add_neg] using
    modeLocalEquation_add hD hU (modeLocalEquation_neg hD hV)

theorem modeLocalEquation_finset_sum {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {ι : Type*} {j : ℕ} {J : Set ℝ} (s : Finset ι) (U F : ι → RadialModePair D)
    (h : ∀ i ∈ s, ModeLocalEquation D j J (U i) (F i)) :
    ModeLocalEquation D j J (∑ i ∈ s, U i) (∑ i ∈ s, F i) := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
      intro h
      simpa only [Finset.sum_empty] using modeLocalEquation_zero hD j J
  | @insert i s hi ih =>
      intro h
      simp only [Finset.sum_insert hi]
      exact modeLocalEquation_add hD (h i (Finset.mem_insert_self i s))
        (ih (fun k hk => h k (Finset.mem_insert_of_mem hk)))

/-- Restricting the family of test functions needs no analytic hypothesis. -/
theorem modeLocalEquation_mono {D : ReferenceData} {j : ℕ} {J K : Set ℝ}
    {U F : RadialModePair D} (h : ModeLocalEquation D j J U F) (hKJ : K ⊆ J) :
    ModeLocalEquation D j K U F := by
  intro ψ hψ hc hs
  exact h ψ hψ hc (hs.trans hKJ)

/-- Closedness is in the existing product norm on Lp × ℝ. -/
theorem isClosed_modeLocalEquation {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (j : ℕ) (J : Set ℝ) :
    IsClosed {p : RadialModePair D × RadialModePair D |
      ModeLocalEquation D j J p.1 p.2} := by
  simp only [modeLocalEquation_iff_inner hD, setOf_forall]
  refine isClosed_iInter fun ψ => isClosed_iInter fun hψ =>
    isClosed_iInter fun hc => isClosed_iInter fun hs => ?_
  exact isClosed_eq
    ((continuous_fst.fst.inner continuous_const).sub
      (continuous_fst.snd.mul_const
        (∫ r in D.a..D.b, referenceColumn D r * ψ r)))
    ((continuous_snd.fst.inner continuous_const).neg)

/-- The maximal local weak graph as a closed linear relation. -/
def modeLocalGraph (D : ReferenceData) (hD : IsAccumulatingProfile D)
    (j : ℕ) (J : Set ℝ) :
    Submodule ℝ (RadialModePair D × RadialModePair D) where
  carrier := {p | ModeLocalEquation D j J p.1 p.2}
  zero_mem' := modeLocalEquation_zero hD j J
  add_mem' := fun hU hV => modeLocalEquation_add hD hU hV
  smul_mem' := fun c _ hU => modeLocalEquation_smul hD hU c

theorem mem_modeLocalGraph {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {j : ℕ} {J : Set ℝ} {p : RadialModePair D × RadialModePair D} :
    p ∈ modeLocalGraph D hD j J ↔ ModeLocalEquation D j J p.1 p.2 := Iff.rfl

theorem modeLocalGraph_isClosed {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (j : ℕ) (J : Set ℝ) :
    IsClosed (modeLocalGraph D hD j J : Set (RadialModePair D × RadialModePair D)) :=
  isClosed_modeLocalEquation hD j J

end ContinuousFlexibility.Radial
