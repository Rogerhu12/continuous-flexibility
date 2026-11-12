import ContinuousFlexibility.Analysis.SolveStateSpaces
import ContinuousFlexibility.Analysis.TameElementaryCalculus
import ContinuousFlexibility.Analysis.TameTransfer

/-!
# Common parameter neighborhoods for the joint residual

Increasing the defining order and decreasing either radius restricts the same
physical state neighborhood. The topology and derivative towers are unchanged.
The elementary monotonicity lemmas below are used to retain all seven preceding
nonlinear stages on the final neighborhood chosen for N08.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped Topology BigOperators

/-- The actual state seminorm defining each neighborhood is continuous. -/
theorem n08_continuous_stateGrading (S : PhysicalSpacesData) (s : ℕ) :
    Continuous (stateGrading S s) :=
  (solve_stateGrading_withSeminorms S).continuous_seminorm s

/-- The restricted state grading defines the inherited sector topology. -/
theorem n08_continuous_sectorGrading (S : PhysicalSpacesData) (s : ℕ) :
    Continuous (sectorGrading S s) :=
  (solve_sectorGrading_withSeminorms S).continuous_seminorm s

theorem n08_isOpen_stateNeighborhood (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base : ℕ) (ε : ℝ) :
    IsOpen (stateNeighborhood S C base ε) := by
  exact (isOpen_lt ((n08_continuous_stateGrading S base).comp
    (continuous_fst.sub continuous_const)) continuous_const).inter
      (isOpen_lt continuous_snd.abs continuous_const)

theorem n08_isOpen_sectorNeighborhood (S : PhysicalSpacesData)
    (base : ℕ) (ε q0 : ℝ) :
    IsOpen (sectorNeighborhood S base ε q0) := by
  exact (isOpen_lt ((n08_continuous_sectorGrading S base).comp continuous_fst)
    continuous_const).inter (isOpen_lt continuous_snd.abs continuous_const)

/-- Stronger low-order control and a smaller radius stay in the original
physical neighborhood without changing its center. -/
theorem n08_stateNeighborhood_mono {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base base' : ℕ} {ε ε' : ℝ}
    (hb : base ≤ base') (hε : ε' ≤ ε) :
    stateNeighborhood S C base' ε' ⊆ stateNeighborhood S C base ε := by
  intro z hz
  exact ⟨(solve_stateGrading_monotone S hb (z.1 - C.referenceState)).trans_lt
    (hz.1.trans_le hε), hz.2.trans_le hε⟩

/-- Both radii in the sector chart may be decreased independently. -/
theorem n08_sectorNeighborhood_mono {S : PhysicalSpacesData}
    {base base' : ℕ} {ε ε' q0 q0' : ℝ}
    (hb : base ≤ base') (hε : ε' ≤ ε) (hq : q0' ≤ q0) :
    sectorNeighborhood S base' ε' q0' ⊆ sectorNeighborhood S base ε q0 := by
  intro z hz
  exact ⟨(solve_sectorGrading_monotone S hb z.1).trans_lt (hz.1.trans_le hε),
    hz.2.trans_le hq⟩

section General

variable {E F G : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]

/-- Restrict a linear-family estimate without changing its loss or constants. -/
theorem n08_linearFamilyTame_restrict
    {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {r : ℕ → Seminorm ℝ G} {U V : Set E} {A : E → G →ₗ[ℝ] F}
    (h : LinearFamilyTame p q r U A) (hVU : V ⊆ U) :
    LinearFamilyTame p q r V A := by
  obtain ⟨loss, base, hbound⟩ := h
  refine ⟨loss, base, fun s hs => ?_⟩
  obtain ⟨K, hK, hKs⟩ := hbound s hs
  exact ⟨K, hK, fun x hx y => hKs x (hVU hx) y⟩

/-- The manuscript's one-high-factor expression is monotone in both orders. -/
theorem n08_oneHighVariationWeight_mono
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {base base' high high' : ℕ} (hb : base ≤ base') (hh : high ≤ high')
    (x : E) {k : ℕ} (v : Fin k → E) :
    oneHighVariationWeight p base high x v ≤
      oneHighVariationWeight p base' high' x v := by
  simpa only [oneHighVariationWeight, tameJetSize, Nat.zero_add] using
    tameJetSize_mono hp hh hb k 0 x v

end General

end ContinuousFlexibility.Statements
