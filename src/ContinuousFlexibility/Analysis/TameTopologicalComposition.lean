module

public import ContinuousFlexibility.Analysis.TameComposition
public import ContinuousFlexibility.Analysis.ProjectiveCurveIteratedChain

/-!
# Smooth tame composition with actual topological parameter spaces

The source and intermediate spaces may be products and closed sectors.
The output is a projective limit of Banach spaces. The genuine curve
rule differentiates the finite partition expressions, while the
existing local bounds give the homogeneous tame estimates.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set Filter Function ContinuousFlexibility.Statements
open scoped Topology BigOperators

variable {X Y : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y]
  {G : ℕ → Type*} [∀ n, NormedAddCommGroup (G n)] [∀ n, NormedSpace ℝ (G n)]
  [∀ n, CompleteSpace (G n)] {g : ∀ n, G (n + 1) →L[ℝ] G n}
  {u : X → Y} {v : Y → ProjectiveLimit G g}
  {J : ProjectiveJetFamily X Y} {K : ProjectiveJetFamily Y (ProjectiveLimit G g)}
  {U : Set X} {V : Set Y}

theorem HasProjectiveJetsOn.compositionTerm_hasLineDerivAt_topological
    (hU : IsOpen U) (hV : IsOpen V)
    (hu : HasProjectiveJetsOn u J U) (hv : HasProjectiveJetsOn v K V)
    (hmap : MapsTo u U V) {n : ℕ} (c : OrderedFinpartition n)
    {x : X} (hx : x ∈ U) (w : X) (vs : Fin n → X) :
    HasProjectiveLineDerivAt (fun y => projectiveCompositionTerm u J K c y vs)
      (projectiveCompositionTerm u J K (c.extend none) x (Fin.cons w vs) +
        ∑ i : Fin c.length,
          projectiveCompositionTerm u J K (c.extend (some i)) x (Fin.cons w vs)) x w := by
  obtain ⟨W, ⟨hW, hWc⟩, hWV⟩ :=
    (LocallyConvexSpace.convex_basis (𝕜 := ℝ) (u x)).mem_iff.mp (hV.mem_nhds (hmap hx))
  have hsub : interior W ⊆ V := interior_subset.trans hWV
  have hux : u x ∈ interior W := mem_interior_iff_mem_nhds.mpr hW
  have hv' : HasProjectiveJetsOn v K (interior W) :=
    ⟨fun y hy => hv.1 y (hsub hy),
      fun n => (hv.2.1 n).mono (fun _ hy => ⟨hsub hy.1, hy.2⟩),
      fun n y hy w vs => hv.2.2 n y (hsub hy) w vs⟩
  have hcurve : HasProjectiveCurveDerivAt (fun t : ℝ => u (x + t • w))
      (projectiveFirstJetValue J x w) 0 := hu.hasLineDerivAt hU hx w
  have hcurve_mem : (fun t : ℝ => u (x + t • w)) 0 ∈ interior W := by
    simpa only [zero_smul, add_zero] using hux
  have hslots (i : Fin c.length) :
      HasProjectiveCurveDerivAt
        (fun t : ℝ => J (c.partSize i) (x + t • w) (vs ∘ c.emb i))
        (J (c.partSize i + 1) x (Fin.cons w (vs ∘ c.emb i))) 0 :=
    hu.2.2 (c.partSize i) x hx w (vs ∘ c.emb i)
  have hd := hcurve.jet_eval_topological isOpen_interior hWc.interior hv' hcurve_mem c.length
    (fun t i => J (c.partSize i) (x + t • w) (vs ∘ c.emb i))
    (fun i => J (c.partSize i + 1) x (Fin.cons w (vs ∘ c.emb i))) hslots
  simp only [projectiveCompositionTerm_extend_none, projectiveCompositionTerm_extend_some]
  simpa only [HasProjectiveLineDerivAt, projectiveCompositionTerm_apply,
    zero_smul, add_zero] using hd

theorem HasProjectiveJetsOn.comp_topological
    (hU : IsOpen U) (hV : IsOpen V)
    (hu : HasProjectiveJetsOn u J U) (hv : HasProjectiveJetsOn v K V)
    (hmap : MapsTo u U V) :
    HasProjectiveJetsOn (v ∘ u) (projectiveCompositionJets u J K) U := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [projectiveCompositionJets_apply, Fintype.sum_unique]
    change K 0 (u x) (fun i : Fin 0 => J 1 x (fun _ => Fin.elim0 i)) = v (u x)
    convert hv.1 (u x) (hmap hx) using 2
  · intro n
    simp only [projectiveCompositionJets_apply]
    exact continuousOn_finsetSum Finset.univ
      (fun c _ => hu.continuousOn_compositionTerm hv hmap c)
  · intro n x hx w vs
    rw [projectiveCompositionJets_succ]
    have h := HasProjectiveCurveDerivAt.finset_sum Finset.univ
      (fun c _ => HasProjectiveJetsOn.compositionTerm_hasLineDerivAt_topological
        hU hV hu hv hmap c hx w vs)
    simpa only [HasProjectiveLineDerivAt, projectiveCompositionJets_apply] using h

theorem smoothTameOn_comp_topological
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y}
    {r : ℕ → Seminorm ℝ (ProjectiveLimit G g)}
    (hp : Monotone p) (htp : WithSeminorms p) (htq : WithSeminorms q)
    (hU : IsOpen U) (hV : IsOpen V) (hmap : MapsTo u U V)
    (hu : SmoothTameOn p q U u) (hv : SmoothTameOn q r V v) :
    SmoothTameOn p r U (v ∘ u) := by
  obtain ⟨J, hJ⟩ := hu
  obtain ⟨K, hK⟩ := hv
  let JK := smoothDirectionsOfJets hU (projectiveCompositionJets u J.D K.D)
    (HasProjectiveJetsOn.comp_topological hU hV J.hasProjectiveJetsOn K.hasProjectiveJetsOn hmap)
  apply smoothTameOn_of_locallyTameOn_jets hp htp JK
  intro k
  exact locallyTameOn_compositionJets hp htp htq J K hJ hK hmap k

end ContinuousFlexibility.Analysis
