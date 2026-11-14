module

public import ContinuousFlexibility.Analysis.N01cOpticalCellComparison
public import ContinuousFlexibility.Statements.RadialTargets
public import ContinuousFlexibility.Radial.ReferenceReturnComponents

/-!
# From actual optical model components to the primitive certificate

At each negative point, the construction identifies its actual component,
a cell of the model index containing that point, and a lower bound on the
whole component. The overlap comparison then allows every containing cell
as the designated nonlinear cell.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Real
open ContinuousFlexibility.Radial

/-- An actual component and its optical estimate at a specified model
cell scale. This contains no nonlinear estimate or flow assertion. -/
def N01cOpticalModelAt (D : ReferenceData) (c α r : ℝ) : Prop :=
  ∃ l h : ℝ, ∃ n : ℕ,
    NegativeRadialComponent D l h ∧ r ∈ Ioo l h ∧
    (∃ m : ℕ, D.cellIndex m = n ∧ r ∈ D.cells m) ∧
    ∀ t ∈ Ioo l h,
      c * radialE n ^ (-α) * min (t - l) (h - t) ≤
        -deriv D.w t / (t * D.w t)

/-- Decreasing the positive scalar lower constant preserves the actual
model, component and cell label. -/
theorem N01cOpticalModelAt.mono_constant
    {D : ReferenceData} {c c' α r : ℝ} (h : N01cOpticalModelAt D c α r)
    (hcc : c' ≤ c) : N01cOpticalModelAt D c' α r := by
  obtain ⟨l, u, n, hcomp, hr, hcell, hlower⟩ := h
  refine ⟨l, u, n, hcomp, hr, hcell, fun t ht => ?_⟩
  have hδ : 0 ≤ min (t - l) (u - t) :=
    le_min (sub_nonneg.mpr ht.1.le) (sub_nonneg.mpr ht.2.le)
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcc (rpow_nonneg (exp_pos _).le _)) hδ).trans
      (hlower t ht)

/-- The pointwise construction cover proves the uniform primitive
geometry on the same reference, with any chosen containing cell. -/
theorem n01c_radialPrimitiveGeometry_of_opticalPointCover
    {D : ReferenceData} (hD : IsAccumulatingProfile D)
    (hχ : tsupport D.chi ⊆ radialCore D)
    {c α : ℝ} (hc : 0 < c) (hα : 0 ≤ α)
    (hcover : ∀ r ∈ radialCore D, deriv D.w r < 0 → N01cOpticalModelAt D c α r) :
    N01RadialPrimitiveGeometry D := by
  obtain ⟨B, hB, hb⟩ := exists_n01c_overlappingCell_negativePower hD hc hα
  refine ⟨hχ, B, hB, fun l h m hcomponent hhost r hr => ?_⟩
  let p : ℝ := (l + h) / 2
  have hp : p ∈ Ioo l h := by
    constructor <;> dsimp only [p] <;> linarith only [hcomponent.2.1]
  have hpCore : p ∈ radialCore D :=
    ⟨hcomponent.1.trans hp.1, hp.2.trans hcomponent.2.2.1⟩
  obtain ⟨l', h', n, hmodel, hpmodel, ⟨j, hj, hpj⟩, hlower⟩ :=
    hcover p hpCore (hcomponent.2.2.2.2.2 p hp)
  obtain ⟨hl, hh⟩ := negativeRadialComponent_unique_of_mem hcomponent hmodel hp hpmodel
  subst l'
  subst h'
  have hweight := hb j m p hpj (hhost hp)
  rw [hj] at hweight
  have hδ : 0 ≤ min (r - l) (h - r) :=
    le_min (sub_nonneg.mpr hr.1.le) (sub_nonneg.mpr hr.2.le)
  exact (mul_le_mul_of_nonneg_right hweight hδ).trans (hlower r hr)

end ContinuousFlexibility.Statements
