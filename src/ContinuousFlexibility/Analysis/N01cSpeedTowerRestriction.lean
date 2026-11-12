import ContinuousFlexibility.Analysis.N01cVolterraStateJets
import ContinuousFlexibility.Analysis.N01cStateSeminorms

/-!
# Restricting a genuine time-indexed speed tower

A smaller open state domain retains every original multilinear map.
The time, state and direction evaluation continuity is simply restricted
to the same smaller product domain.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

def ContinuousTimeSpeedTower.n01c_restrict
    {U V : Set E} {G : E × PolarPoint → ℝ}
    (J : ContinuousTimeSpeedTower U G) (hV : IsOpen V) (hVU : V ⊆ U) :
    ContinuousTimeSpeedTower V G where
  jet := fun t => (J.jet t).restrict (hV.prod isOpen_univ)
    (fun _ hp => ⟨hVU hp.1, hp.2⟩)
  continuous := fun n => (J.continuous n).mono
    (fun _ hp => ⟨⟨hVU hp.1.1, hp.1.2⟩, hp.2⟩)

@[simp] theorem ContinuousTimeSpeedTower.n01c_restrict_D_apply
    {U V : Set E} {G : E × PolarPoint → ℝ}
    (J : ContinuousTimeSpeedTower U G) (hV : IsOpen V) (hVU : V ⊆ U)
    (n : ℕ) (p : E × PolarPoint) (v : Fin n → E × ℝ) :
    (J.n01c_restrict hV hVU).D n p v = J.D n p v := rfl

end ContinuousFlexibility.Analysis
