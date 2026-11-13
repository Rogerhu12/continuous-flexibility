import ContinuousFlexibility.Analysis.N04RealizationInverseJetFormula
import ContinuousFlexibility.Analysis.N01cSpatialParameterComposition

/-!
# Genuine parameter towers for a finite prefix of boundary inverse jets

The inverse maps are only required to be spatially smooth at their actual
base points. Parameter towers are constructed from the genuine first
inverse differential and finite forward jets at the same inverse point.
The local inverse formula determines every higher inverse jet without
requiring parameter regularity of a chosen root extension.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology BigOperators ContDiff

variable {X E F : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U : Set X} {f : X → E → F} {g : X → F → E}
  {x : X → F} {L : X → F →L[ℝ] E}

/-- One finite inverse step uses only genuinely differentiated lower
inverse jets. The resulting tower is identified with the actual jet. -/
def n04Realization_inverseJet_step
    (hU : IsOpen U)
    (hf : ∀ z ∈ U, ContDiffAt ℝ ∞ (f z) (g z (x z)))
    (hg : ∀ z ∈ U, ContDiffAt ℝ ∞ (g z) (x z))
    (hfg : ∀ z ∈ U, f z ∘ g z =ᶠ[𝓝 (x z)] (id : F → F))
    (hL : ∀ z ∈ U,
      (L z).comp (fderiv ℝ (f z) (g z (x z))) = ContinuousLinearMap.id ℝ E)
    (JL : SmoothDirections U L)
    {n : ℕ} (hn : 2 ≤ n)
    (JF : ∀ j, 2 ≤ j → j ≤ n →
      SmoothDirections U (fun z => iteratedFDeriv ℝ j (f z) (g z (x z))))
    (Jlower : ∀ j, 1 ≤ j → j < n → ∀ v : Fin j → F,
      SmoothDirections U (fun z => iteratedFDeriv ℝ j (g z) (x z) v))
    (v : Fin n → F) :
    SmoothDirections U (fun z => iteratedFDeriv ℝ n (g z) (x z) v) := by
  classical
  let term : OrderedFinpartition n → X → F := fun c z =>
    if 2 ≤ c.length then
      iteratedFDeriv ℝ c.length (f z) (g z (x z))
        (fun i => iteratedFDeriv ℝ (c.partSize i) (g z) (x z) (v ∘ c.emb i))
    else 0
  let JT : ∀ c, SmoothDirections U (term c) := by
    intro c
    by_cases hc : 2 ≤ c.length
    · let V : Fin c.length → X → E := fun i z =>
        iteratedFDeriv ℝ (c.partSize i) (g z) (x z) (v ∘ c.emb i)
      let JV : ∀ i, SmoothDirections U (V i) := fun i =>
        Jlower (c.partSize i) (c.partSize_pos i)
          (flowJet_partition_partSize_lt c hc i) (v ∘ c.emb i)
      let Jpair := smoothDirectionsProd (JF c.length hc c.length_le)
        (smoothDirections_vectorTuple hU JV)
      let K := smoothDirections_contDiff_comp Jpair isOpen_univ
        (contDiff_multilinearEvaluation (Y := E) (Z := F) c.length).contDiffOn
        (fun _ _ => mem_univ _)
      refine K.congr (fun z _ => ?_)
      change iteratedFDeriv ℝ c.length (f z) (g z (x z))
          (fun i => V i z) = term c z
      simp only [term, if_pos hc, V]
    · let K : SmoothDirections U (fun _ : X => (0 : F)) :=
        smoothDirections_constant hU 0
      refine K.congr (fun z _ => ?_)
      simp only [term, if_neg hc]
  let Jsum := smoothDirections_finiteSum hU JT
  let Jpair := smoothDirectionsProd JL Jsum
  have hkernel : ContDiff ℝ ∞
      (fun p : (F →L[ℝ] E) × F => -p.1 p.2) :=
    (contDiff_fst.clm_apply contDiff_snd).neg
  let K := smoothDirections_contDiff_comp Jpair isOpen_univ hkernel.contDiffOn
    (fun _ _ => mem_univ _)
  refine K.congr (fun z hz => ?_)
  change -L z (∑ c, term c z) = iteratedFDeriv ℝ n (g z) (x z) v
  exact (n04Realization_inverse_higherJet_apply (hf z hz) (hg z hz)
    (hfg z hz) (L z) (hL z hz) hn v).symm

/-- The low differential and forward prefix determine genuine parameter
towers for every positive inverse order in that prefix, on the same U. -/
theorem n04Realization_inverse_finiteJets_nonempty
    (hU : IsOpen U)
    (hf : ∀ z ∈ U, ContDiffAt ℝ ∞ (f z) (g z (x z)))
    (hg : ∀ z ∈ U, ContDiffAt ℝ ∞ (g z) (x z))
    (hfg : ∀ z ∈ U, f z ∘ g z =ᶠ[𝓝 (x z)] (id : F → F))
    (hL : ∀ z ∈ U,
      (L z).comp (fderiv ℝ (f z) (g z (x z))) = ContinuousLinearMap.id ℝ E)
    (JL : SmoothDirections U L)
    (N : ℕ)
    (JF : ∀ j, 2 ≤ j → j ≤ N →
      SmoothDirections U (fun z => iteratedFDeriv ℝ j (f z) (g z (x z)))) :
    ∀ n, 1 ≤ n → n ≤ N → ∀ v : Fin n → F,
      Nonempty (SmoothDirections U (fun z => iteratedFDeriv ℝ n (g z) (x z) v)) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn hN v
      by_cases h1 : n = 1
      · subst n
        have hkernel : ContDiff ℝ ∞ (fun A : F →L[ℝ] E => A (v 0)) :=
          contDiff_id.clm_apply contDiff_const
        let K := smoothDirections_contDiff_comp JL isOpen_univ hkernel.contDiffOn
          (fun _ _ => mem_univ _)
        refine ⟨K.congr (fun z hz => ?_)⟩
        change L z (v 0) = iteratedFDeriv ℝ 1 (g z) (x z) v
        rw [iteratedFDeriv_one_apply,
          nonlinearInverse_fderiv_eq (hf z hz) (hg z hz) (hfg z hz) (L z) (hL z hz)]
      · have hn2 : 2 ≤ n := by omega
        let Jlower : ∀ j, 1 ≤ j → j < n → ∀ w : Fin j → F,
            SmoothDirections U (fun z => iteratedFDeriv ℝ j (g z) (x z) w) :=
          fun j hj hjn w => Classical.choice
            (ih j hjn hj (Nat.le_trans hjn.le hN) w)
        exact ⟨n04Realization_inverseJet_step hU hf hg hfg hL JL hn2
          (fun j hj hjn => JF j hj (hjn.trans hN)) Jlower v⟩

/-- A selected tower for the actual finite inverse jet. The choice is
only a proof of the already fixed function, not a new inverse map. -/
def n04Realization_inverse_finiteJet_directions
    (hU : IsOpen U)
    (hf : ∀ z ∈ U, ContDiffAt ℝ ∞ (f z) (g z (x z)))
    (hg : ∀ z ∈ U, ContDiffAt ℝ ∞ (g z) (x z))
    (hfg : ∀ z ∈ U, f z ∘ g z =ᶠ[𝓝 (x z)] (id : F → F))
    (hL : ∀ z ∈ U,
      (L z).comp (fderiv ℝ (f z) (g z (x z))) = ContinuousLinearMap.id ℝ E)
    (JL : SmoothDirections U L)
    (N : ℕ)
    (JF : ∀ j, 2 ≤ j → j ≤ N →
      SmoothDirections U (fun z => iteratedFDeriv ℝ j (f z) (g z (x z))))
    (n : ℕ) (hn : 1 ≤ n) (hN : n ≤ N) (v : Fin n → F) :
    SmoothDirections U (fun z => iteratedFDeriv ℝ n (g z) (x z) v) :=
  Classical.choice
    (n04Realization_inverse_finiteJets_nonempty hU hf hg hfg hL JL N JF n hn hN v)

end ContinuousFlexibility.Analysis
