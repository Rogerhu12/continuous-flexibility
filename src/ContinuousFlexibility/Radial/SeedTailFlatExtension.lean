import ContinuousFlexibility.Statements.Radial
import ContinuousFlexibility.Radial.CentralStatementBridges

/-!
# Flat extension of a specified natural second-mode solution

The physical flatness conclusion supplies one nonzero natural solution.
Uniqueness of the natural line transfers its smooth endpoint extension
to every specified natural solution, without replacing that solution.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set
open scoped ContDiff
open ContinuousFlexibility.Statements

/-- Transfer a physical flat extension from one nonzero natural solution
to a specified solution on the same actual tail. -/
theorem tailPhysicalFlatExtension_of_naturalEquation
    {D : ReferenceData} {T : DeepTailData} {right : Bool} {j start : ℕ}
    {u : ℝ → ℝ} (hline : TailNaturalLineAndKernel T)
    (hflat : TailPhysicalFlatConclusion D T right j start)
    (hu : TailNaturalEquation T u) :
    ∃ v : ℝ → ℝ, ContDiff ℝ ∞ v ∧
      (∀ x ∈ Ioo T.entrance T.endpoint,
        v (tailPhysicalRadius right x) =
          (tailPhysicalRadius right x / (if right then D.b else D.a)) ^
            ((j : ℝ) ^ 2) * u x) ∧
      ∀ s : ℕ, radialJet s v (if right then D.b else D.a) = 0 := by
  obtain ⟨u₀, _, _, hunique, _⟩ := hline
  obtain ⟨u₁, v₁, hu₁, hne₁, hv₁, heq₁, _, hjet₁, _⟩ := hflat
  obtain ⟨c₁, hc₁⟩ := hunique u₁ hu₁
  obtain ⟨c, hc⟩ := hunique u hu
  have hc₁ne : c₁ ≠ 0 := by
    intro hz
    obtain ⟨x, hx, hn⟩ := hne₁
    apply hn
    rw [hc₁ x hx, hz, zero_mul]
  have hmul (x : ℝ) (hx : x ∈ Ioo T.entrance T.endpoint) :
      c / c₁ * u₁ x = u x := by
    rw [hc₁ x hx, hc x hx]
    field_simp [hc₁ne]
  refine ⟨fun r => c / c₁ * v₁ r, contDiff_const.mul hv₁, ?_, ?_⟩
  · intro x hx
    change c / c₁ * v₁ (tailPhysicalRadius right x) = _
    rw [heq₁ x hx]
    calc
      _ = (tailPhysicalRadius right x / (if right then D.b else D.a)) ^
          ((j : ℝ) ^ 2) * (c / c₁ * u₁ x) := by ring
      _ = _ := by rw [hmul x hx]
  · intro s
    rw [radialJet_eq_iteratedDeriv, iteratedDeriv_const_mul_field,
      ← radialJet_eq_iteratedDeriv, hjet₁ s, mul_zero]

end ContinuousFlexibility.Radial
