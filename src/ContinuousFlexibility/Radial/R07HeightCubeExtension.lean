import ContinuousFlexibility.Radial.HeightSelectionPrinciple
import ContinuousFlexibility.Radial.R07HeightUpdate

/-!
# Total extensions of functions on the admissible height cube

Analytic parameter theorems naturally use the subtype of admissible heights.
The countable selection theorem uses total functions of the raw sequence.
The following extension preserves all values, continuity on the cube, and
coordinate-update invariance, while allowing any fixed value off the cube.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Function

def r07HeightExtension {Y : Type*} (default : Y) (f : Statements.HeightRatios → Y)
    (σ : ℕ → ℝ) : Y := by
  classical
  exact if hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2 then f ⟨σ, hσ⟩ else default

theorem r07HeightExtension_admissible {Y : Type*} (default : Y)
    (f : Statements.HeightRatios → Y) (σ : ℕ → ℝ) (hσ : ∀ n, 1 ≤ σ n ∧ σ n ≤ 2) :
    r07HeightExtension default f σ = f ⟨σ, hσ⟩ := by
  simp only [r07HeightExtension, dif_pos hσ]

def r07HeightUpdate (σ : Statements.HeightRatios) (n : ℕ) (t : Icc (1 : ℝ) 2) :
    Statements.HeightRatios :=
  ⟨update σ.val n t.val, morseHeight_update_admissible σ.property n t.property⟩

theorem continuousOn_r07HeightExtension {Y : Type*} [TopologicalSpace Y] (default : Y)
    {f : Statements.HeightRatios → Y} (hf : Continuous f) :
    ContinuousOn (r07HeightExtension default f) heightCube := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  let lift : heightCube → Statements.HeightRatios := fun σ => ⟨σ.val, mem_heightCube.mp σ.property⟩
  have hlift : Continuous lift := continuous_subtype_val.subtype_mk _
  have he : (fun σ : heightCube => r07HeightExtension default f σ.val) = fun σ => f (lift σ) := by
    funext σ
    exact r07HeightExtension_admissible default f σ.val (mem_heightCube.mp σ.property)
  rw [he]
  exact hf.comp hlift

theorem r07HeightExtension_update {Y : Type*} (default : Y)
    {f : Statements.HeightRatios → Y} (n : ℕ)
    (hf : ∀ σ t, f (r07HeightUpdate σ n t) = f σ)
    {σ : ℕ → ℝ} (hσ : σ ∈ heightCube) {t : ℝ} (ht : t ∈ Icc (1 : ℝ) 2) :
    r07HeightExtension default f (update σ n t) = r07HeightExtension default f σ := by
  have hσ' := mem_heightCube.mp hσ
  rw [r07HeightExtension_admissible default f _ (morseHeight_update_admissible hσ' n ht),
    r07HeightExtension_admissible default f σ hσ']
  exact hf ⟨σ, hσ'⟩ ⟨t, ht⟩

end ContinuousFlexibility.Radial
