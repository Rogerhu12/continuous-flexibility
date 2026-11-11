import ContinuousFlexibility.Analysis.NormedSmoothDirections
import ContinuousFlexibility.Analysis.TameJetComposition
import ContinuousFlexibility.Analysis.TameProductDirections

/-!
# Composition into a normed target from topological parameters

The existing finite-partition formula applies to a genuine directional
tower followed by an ordinary smooth map on an open normed domain.
Every summand is differentiated along the actual parameter curve. This
allows scalar coefficient operations on the original parameter space.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

variable {E F G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {U : Set E} {V : Set F} {f : E → F} {g : F → G}
  {J : ProjectiveJetFamily E F}

theorem HasProjectiveJetsOn.compositionTerm_hasLineDerivAt_contDiff
    (hU : IsOpen U) (hJ : HasProjectiveJetsOn f J U)
    (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V) (hmap : MapsTo f U V)
    {n : ℕ} (c : OrderedFinpartition n) {x : E} (hx : x ∈ U)
    (w : E) (v : Fin n → E) :
    HasProjectiveLineDerivAt
      (fun y => projectiveCompositionTerm f J (contDiffOnJetFamily g V) c y v)
      (projectiveCompositionTerm f J (contDiffOnJetFamily g V) (c.extend none) x (Fin.cons w v) +
        ∑ i : Fin c.length, projectiveCompositionTerm f J (contDiffOnJetFamily g V)
          (c.extend (some i)) x (Fin.cons w v)) x w := by
  have hcurve : HasProjectiveCurveDerivAt (fun t : ℝ => f (x + t • w))
      (projectiveFirstJetValue J x w) 0 := hJ.hasLineDerivAt hU hx w
  have hcurve_mem : (fun t : ℝ => f (x + t • w)) 0 ∈ V := by
    simpa only [zero_smul, add_zero] using hmap hx
  have hslots (i : Fin c.length) : HasProjectiveCurveDerivAt
      (fun t : ℝ => J (c.partSize i) (x + t • w) (v ∘ c.emb i))
      (J (c.partSize i + 1) x (Fin.cons w (v ∘ c.emb i))) 0 :=
    hJ.2.2 (c.partSize i) x hx w (v ∘ c.emb i)
  have hd := hasProjectiveCurveDerivAt_contDiffOnJet_eval hV hg hcurve hcurve_mem c.length
    (fun t i => J (c.partSize i) (x + t • w) (v ∘ c.emb i))
    (fun i => J (c.partSize i + 1) x (Fin.cons w (v ∘ c.emb i))) hslots
  simp only [projectiveCompositionTerm_extend_none, projectiveCompositionTerm_extend_some]
  simpa only [HasProjectiveLineDerivAt, projectiveCompositionTerm_apply,
    zero_smul, add_zero] using hd

theorem HasProjectiveJetsOn.comp_contDiff
    (hU : IsOpen U) (hJ : HasProjectiveJetsOn f J U)
    (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V) (hmap : MapsTo f U V) :
    HasProjectiveJetsOn (g ∘ f) (projectiveCompositionJets f J (contDiffOnJetFamily g V)) U := by
  classical
  have hK := hasProjectiveJetsOn_contDiffOn hV hg
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [projectiveCompositionJets_apply, Fintype.sum_unique]
    change contDiffOnJetFamily g V 0 (f x)
      (fun i : Fin 0 => J 1 x (fun _ => Fin.elim0 i)) = g (f x)
    convert hK.1 (f x) (hmap hx) using 2
  · intro n
    simp only [projectiveCompositionJets_apply]
    exact continuousOn_finsetSum Finset.univ
      (fun c _ => hJ.continuousOn_compositionTerm hK hmap c)
  · intro n x hx w v
    rw [projectiveCompositionJets_succ]
    have hd := HasProjectiveCurveDerivAt.finset_sum Finset.univ
      (fun c _ => HasProjectiveJetsOn.compositionTerm_hasLineDerivAt_contDiff
        hU hJ hV hg hmap c hx w v)
    simpa only [HasProjectiveLineDerivAt, projectiveCompositionJets_apply] using hd

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff

variable {E F G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {U : Set E} {V : Set F} {f : E → F} {g : F → G}

/-- All orders of the actual composition on the original open domain. -/
def SmoothDirections.comp_contDiff (J : SmoothDirections U f)
    (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V) (hmap : MapsTo f U V) :
    SmoothDirections U (fun x => g (f x)) :=
  smoothDirectionsOfJets J.open_domain (projectiveCompositionJets f J.D (contDiffOnJetFamily g V))
    (HasProjectiveJetsOn.comp_contDiff J.open_domain J.hasProjectiveJetsOn hV hg hmap)

theorem SmoothDirections.comp_contDiff_apply (J : SmoothDirections U f)
    (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V) (hmap : MapsTo f U V)
    (n : ℕ) (x : E) (v : Fin n → E) :
    (J.comp_contDiff hV hg hmap).D n x v =
      ∑ c : OrderedFinpartition n,
        contDiffOnJetFamily g V c.length (f x)
          (fun i => J.D (c.partSize i) x (v ∘ c.emb i)) := by
  exact projectiveCompositionJets_apply f J.D (contDiffOnJetFamily g V) n x v

def SmoothDirections.mul {f g : E → ℝ}
    (J : SmoothDirections U f) (K : SmoothDirections U g) :
    SmoothDirections U (fun x => f x * g x) :=
  (smoothDirectionsProd J K).comp_contDiff isOpen_univ
    (contDiff_fst.mul contDiff_snd).contDiffOn (fun _ _ => mem_univ _)

end ContinuousFlexibility.Statements
