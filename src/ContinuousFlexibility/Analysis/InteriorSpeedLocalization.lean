import ContinuousFlexibility.Analysis.InteriorScalarFlowJets
import ContinuousFlexibility.Analysis.OneSidedOrdinaryJets

/-!
# A fixed smooth speed extension retaining every interior jet

The clamp is the identity on a larger interval than the one visited by
the flow. Thus all ordinary derivatives, including at the two visited
endpoints, agree with the original speed. No derivative of the clamp
appears in the raw-flow estimates.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def interiorLocalizedSpeed {a b ρ : ℝ} (hab : a ≤ b) (hρ : 0 < ρ)
    (f : PolarPoint → ℝ) : PolarPoint → ℝ :=
  circleFlowLocalizedSpeed (a := a - ρ) (b := b + ρ) (ε := ρ) f
    (by linarith) hρ

theorem contDiff_interiorLocalizedSpeed
    {a b ρ : ℝ} (hab : a ≤ b) (hρ : 0 < ρ) {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo (a - 2 * ρ) (b + 2 * ρ) ×ˢ (univ : Set ℝ))) :
    ContDiff ℝ ∞ (interiorLocalizedSpeed hab hρ f) := by
  apply contDiff_circleFlowLocalizedSpeed
  apply hf.mono
  intro q hq
  refine ⟨⟨?_, ?_⟩, mem_univ _⟩ <;> linarith only [hq.1.1, hq.1.2]

theorem interiorLocalizedSpeed_periodic
    {a b ρ P : ℝ} (hab : a ≤ b) (hρ : 0 < ρ) {f : PolarPoint → ℝ}
    (hperiod : ∀ r ∈ Ioo (a - 2 * ρ) (b + 2 * ρ),
      Function.Periodic (fun θ => f (r, θ)) P) :
    ∀ r : ℝ, Function.Periodic (fun θ => interiorLocalizedSpeed hab hρ f (r, θ)) P := by
  apply circleFlowLocalizedSpeed_periodic
  intro r hr
  exact hperiod r ⟨by linarith only [hr.1], by linarith only [hr.2]⟩

theorem interiorLocalizedSpeed_eqOn
    {a b ρ : ℝ} (hab : a ≤ b) (hρ : 0 < ρ) (f : PolarPoint → ℝ) :
    EqOn (interiorLocalizedSpeed hab hρ f) f
      (Ioo (a - ρ) (b + ρ) ×ˢ (univ : Set ℝ)) := by
  intro q hq
  exact circleFlowLocalizedSpeed_eq (by linarith : a - ρ ≤ b + ρ) hρ
    ⟨hq.1.1.le, hq.1.2.le⟩ q.2

theorem interiorLocalizedSpeed_eq
    {a b ρ : ℝ} (hab : a ≤ b) (hρ : 0 < ρ) (f : PolarPoint → ℝ)
    {q : PolarPoint} (hq : q.1 ∈ Icc a b) :
    interiorLocalizedSpeed hab hρ f q = f q :=
  interiorLocalizedSpeed_eqOn hab hρ f
    ⟨⟨by linarith only [hq.1, hρ], by linarith only [hq.2, hρ]⟩, mem_univ _⟩

theorem iteratedFDeriv_interiorLocalizedSpeed_eq
    {a b ρ : ℝ} (hab : a ≤ b) (hρ : 0 < ρ) (f : PolarPoint → ℝ)
    (n : ℕ) {q : PolarPoint} (hq : q.1 ∈ Icc a b) :
    iteratedFDeriv ℝ n (interiorLocalizedSpeed hab hρ f) q =
      iteratedFDeriv ℝ n f q :=
  iteratedFDeriv_eqOn_of_isOpen (isOpen_Ioo.prod isOpen_univ)
    (interiorLocalizedSpeed_eqOn hab hρ f) n
    ⟨⟨by linarith only [hq.1, hρ], by linarith only [hq.2, hρ]⟩, mem_univ _⟩

theorem interiorLocalizedSpeed_jetBounds
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} {loss : ℕ} {A : ℕ → ℝ} {z : E}
    {a b ρ : ℝ} (hab : a ≤ b) (hρ : 0 < ρ) {f : PolarPoint → ℝ}
    (hjets : InteriorSpeedJetBounds p loss A z a b f) :
    InteriorSpeedJetBounds p loss A z a b (interiorLocalizedSpeed hab hρ f) := by
  intro n r hr θ
  rw [iteratedFDeriv_interiorLocalizedSpeed_eq hab hρ f n hr]
  exact hjets n r hr θ

end ContinuousFlexibility.Analysis
