import ContinuousFlexibility.Analysis.SolveStateSpaces
import ContinuousFlexibility.Analysis.MaterialSampleCofinite

/-!
# Restricting the common N01 neighborhood

Increasing the controlled seminorm order and decreasing the radius
preserve the same geometric data and all N01 towers.  The directional
derivatives themselves are retained; only their open domain is restricted.
This permits a later uniform geometric smallness estimate to choose its
neighborhood without replacing any of the actual returns.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

-- Use the canonical product action directly, avoiding a costly search
-- through the abstract models that make up the state space.
local instance (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul

open Set ContinuousFlexibility.Analysis
open scoped Topology BigOperators

section RestrictDirections

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  {U V : Set E} {f : E → F}

def SmoothDirections.restrict (J : SmoothDirections U f)
    (hV : IsOpen V) (hVU : V ⊆ U) : SmoothDirections V f where
  open_domain := hV
  D := J.D
  zero x hx := J.zero x (hVU hx)
  continuous n := (J.continuous n).mono (fun p hp => ⟨hVU hp.1, hp.2⟩)
  derivative n x hx v w := J.derivative n x (hVU hx) v w

end RestrictDirections

theorem oneHighVariationWeight_mono
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {b₀ b₁ h₀ h₁ k : ℕ} (hb : b₀ ≤ b₁) (hh : h₀ ≤ h₁)
    (x : E) (v : Fin k → E) :
    oneHighVariationWeight p b₀ h₀ x v ≤ oneHighVariationWeight p b₁ h₁ x v := by
  have hprod (s : Finset (Fin k)) :
      (∏ i ∈ s, p b₀ (v i)) ≤ ∏ i ∈ s, p b₁ (v i) :=
    Finset.prod_le_prod₀ (fun i hi => apply_nonneg _ _) (fun i hi => hp hb (v i))
  unfold oneHighVariationWeight
  apply add_le_add
  · exact mul_le_mul (add_le_add_right (hp hh x) 1) (hprod Finset.univ)
      (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _))
      (add_nonneg zero_le_one (apply_nonneg _ _))
  · apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul (hp hh (v i)) (hprod (Finset.univ.erase i))
      (Finset.prod_nonneg (fun _ _ => apply_nonneg _ _)) (apply_nonneg _ _)

theorem stateNeighborhood_isOpen (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (base : ℕ) (ε : ℝ) :
    IsOpen (stateNeighborhood S C base ε) := by
  have hc : Continuous (fun z : AnnularState S × ℝ =>
      stateGrading S base (z.1 - C.referenceState)) :=
    ((solve_stateGrading_withSeminorms S).continuous_seminorm base).comp
      (continuous_fst.sub continuous_const)
  exact (isOpen_lt hc continuous_const).inter
    (isOpen_lt continuous_snd.abs continuous_const)

theorem stateNeighborhood_mono (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) {base base' : ℕ} {ε ε' : ℝ}
    (hb : base ≤ base') (hε : ε' ≤ ε) :
    stateNeighborhood S C base' ε' ⊆ stateNeighborhood S C base ε := by
  intro z hz
  exact ⟨((solve_stateGrading_monotone S hb (z.1 - C.referenceState)).trans_lt hz.1).trans_le hε,
    hz.2.trans_le hε⟩

set_option backward.isDefEq.respectTransparency false in
theorem N01Properties.restrict_neighborhood
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base base' loss : ℕ} {ε ε' : ℝ}
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T)
    (hb : base ≤ base') (hε' : 0 < ε') (hε : ε' ≤ ε) :
    N01Properties D T S C base' loss ε' := by
  have hsub := stateNeighborhood_mono S C hb hε
  have hopen := stateNeighborhood_isOpen S C base' ε'
  have hD := hN.1.1
  obtain ⟨_, hbounds⟩ := hD
  have hsamples := materialSample_mem_radialCore hT hbounds.2.1
  have hH (m : ℕ) : 0 < T.H (T.sample m) := (hT.2.1 _ (hsamples m)).2.1
  have hE (m : ℕ) : 0 < T.E0 (T.sample m) := (hT.2.1 _ (hsamples m)).2.2.1
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    pairGrading_monotone (solve_stateGrading_monotone S) (fun _ _ _ _ => le_rfl)
  rcases hN with ⟨hrad, _, href, hcontrol, hcell, hcontroljets,
    hflow, hchart, hinv, hpositive, hroot, hcoeff, hflowjets⟩
  refine ⟨hrad, hε', href, hcontrol, hcell, hcontroljets,
    (fun z hz => hflow z (hsub hz)),
    (fun z hz => hchart z (hsub hz)),
    (fun z hz => hinv z (hsub hz)),
    (fun z hz => hpositive z (hsub hz)),
    (fun z hz => hroot z (hsub hz)), ?_, ?_⟩
  · intro k s
    obtain ⟨B, hB, hcoeff⟩ := hcoeff k s
    refine ⟨B, hB, ?_⟩
    intro m i a b p hab hpm
    obtain ⟨J, hJ⟩ := hcoeff m i a b p hab hpm
    refine ⟨J.restrict hopen hsub, ?_⟩
    intro z hz v
    have hC : 0 ≤ B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B :=
      mul_nonneg (mul_nonneg hB.le (Real.rpow_nonneg (hH m).le _))
        (Real.rpow_nonneg (hE m).le _)
    exact (hJ z (hsub hz) v).trans (mul_le_mul_of_nonneg_left
      (oneHighVariationWeight_mono hp hb le_rfl (z - (C.referenceState, 0)) v) hC)
  · intro k s
    obtain ⟨B, hB, hflowjets⟩ := hflowjets k s
    refine ⟨B, hB, ?_⟩
    intro m a b p hab hpm
    obtain ⟨J, hJ⟩ := hflowjets m a b p hab hpm
    refine ⟨J.restrict hopen hsub, ?_⟩
    intro z hz v
    have hC : 0 ≤ B * T.H (T.sample (C.cell m)) ^ (3 / 4 : ℝ) *
        T.E0 (T.sample (C.cell m)) ^ B :=
      mul_nonneg (mul_nonneg hB.le (Real.rpow_nonneg (hH (C.cell m)).le _))
        (Real.rpow_nonneg (hE (C.cell m)).le _)
    exact (hJ z (hsub hz) v).trans (mul_le_mul_of_nonneg_left
      (oneHighVariationWeight_mono hp hb le_rfl (z - (C.referenceState, 0)) v) hC)

end ContinuousFlexibility.Statements
