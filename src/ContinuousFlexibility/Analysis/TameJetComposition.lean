import ContinuousFlexibility.Analysis.ProjectiveJetCompositionTwo
import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno

/-!
# All-order composition of actual projective jets

The combinatorics is Mathlib's ordered finite partitions. The multilinear
composition and its continuity are constructed in topological modules, so
no norm is imposed on a projective limit. The actual derivative recurrence
uses the already proved variable-multilinear curve rule.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false

section FiniteSums

variable {W : Type*} [TopologicalSpace W] [AddCommGroup W] [Module ℝ W]
  [IsTopologicalAddGroup W]

theorem HasProjectiveCurveDerivAt.finset_sum {ι : Type*} (S : Finset ι)
    {f : ι → ℝ → W} {df : ι → W} {t : ℝ}
    (h : ∀ i ∈ S, HasProjectiveCurveDerivAt (f i) (df i) t) :
    HasProjectiveCurveDerivAt (fun s => ∑ i ∈ S, f i s) (∑ i ∈ S, df i) t := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using hasProjectiveCurveDerivAt_const (0 : W) t
  | @insert i S hi ih =>
      simpa only [Finset.sum_insert hi] using
        (h i (Finset.mem_insert_self i S)).add
          (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

end FiniteSums

section PartitionComposition

variable {X Y Z : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]

/-- The inputs obtained by applying one multilinear map to each block. -/
def projectivePartitionInputs {n : ℕ} (c : OrderedFinpartition n)
    (A : ∀ i, X [×c.partSize i]→L[ℝ] Y) (v : Fin n → X) : Fin c.length → Y :=
  fun i => A i (v ∘ c.emb i)

theorem projectivePartitionInputs_update {n : ℕ} (c : OrderedFinpartition n)
    (A : ∀ i, X [×c.partSize i]→L[ℝ] Y) (j : Fin n) (v : Fin n → X) (z : X) :
    projectivePartitionInputs c A (Function.update v j z) =
      Function.update (projectivePartitionInputs c A v) (c.index j)
        (A (c.index j) (Function.update (v ∘ c.emb (c.index j)) (c.invEmbedding j) z)) := by
  classical
  ext i
  by_cases hi : i = c.index j
  · subst i
    simp only [projectivePartitionInputs, Function.update_self]
    congr 1
    rw [← Function.update_comp_eq_of_injective]
    · simp only [OrderedFinpartition.emb_invEmbedding]
    · exact (c.emb_strictMono (c.index j)).injective
  · simp only [projectivePartitionInputs, Function.update_of_ne hi]
    congr 1
    apply Function.update_comp_eq_of_notMem_range
    have hd := c.disjoint (mem_univ i) (mem_univ (c.index j)) hi
    exact Set.disjoint_right.mp hd
      (mem_range.mpr ⟨c.invEmbedding j, c.emb_invEmbedding j⟩)

/-- Composition along a partition, without normability hypotheses. -/
def projectivePartitionMultilinear {n : ℕ} (c : OrderedFinpartition n)
    (B : Y [×c.length]→L[ℝ] Z) (A : ∀ i, X [×c.partSize i]→L[ℝ] Y) :
    X [×n]→L[ℝ] Z where
  toMultilinearMap := MultilinearMap.mk'
    (fun v => B (projectivePartitionInputs c A v))
    (fun v i x y => by
      simp only [projectivePartitionInputs_update, ContinuousMultilinearMap.map_update_add])
    (fun v i a x => by
      simp only [projectivePartitionInputs_update, ContinuousMultilinearMap.map_update_smul])
  cont := B.cont.comp (by
    apply continuous_pi
    intro i
    exact (A i).cont.comp (continuous_pi (fun j => continuous_apply (c.emb i j))))

@[simp] theorem projectivePartitionMultilinear_apply {n : ℕ} (c : OrderedFinpartition n)
    (B : Y [×c.length]→L[ℝ] Z) (A : ∀ i, X [×c.partSize i]→L[ℝ] Y)
    (v : Fin n → X) :
    projectivePartitionMultilinear c B A v = B (fun i => A i (v ∘ c.emb i)) := rfl

/-- One summand in the ordered-partition composition formula. -/
def projectiveCompositionTerm (f : X → Y) (J : ProjectiveJetFamily X Y)
    (K : ProjectiveJetFamily Y Z) {n : ℕ} (c : OrderedFinpartition n) (x : X) :
    X [×n]→L[ℝ] Z :=
  projectivePartitionMultilinear c (K c.length (f x)) (fun i => J (c.partSize i) x)

@[simp] theorem projectiveCompositionTerm_apply (f : X → Y) (J : ProjectiveJetFamily X Y)
    (K : ProjectiveJetFamily Y Z) {n : ℕ} (c : OrderedFinpartition n)
    (x : X) (v : Fin n → X) :
    projectiveCompositionTerm f J K c x v =
      K c.length (f x) (fun i => J (c.partSize i) x (v ∘ c.emb i)) := rfl

variable [ContinuousAdd Z]

/-- The full, all-order candidate for composition. -/
def projectiveCompositionJets (f : X → Y) (J : ProjectiveJetFamily X Y)
    (K : ProjectiveJetFamily Y Z) : ProjectiveJetFamily X Z :=
  fun n x => ∑ c : OrderedFinpartition n, projectiveCompositionTerm f J K c x

@[simp] theorem projectiveCompositionJets_apply (f : X → Y) (J : ProjectiveJetFamily X Y)
    (K : ProjectiveJetFamily Y Z) (n : ℕ) (x : X) (v : Fin n → X) :
    projectiveCompositionJets f J K n x v =
      ∑ c : OrderedFinpartition n, projectiveCompositionTerm f J K c x v := by
  simp only [projectiveCompositionJets, ContinuousMultilinearMap.sum_apply]

theorem projectiveCompositionTerm_extend_none (f : X → Y)
    (J : ProjectiveJetFamily X Y) (K : ProjectiveJetFamily Y Z)
    {n : ℕ} (c : OrderedFinpartition n) (x w : X) (v : Fin n → X) :
    projectiveCompositionTerm f J K (c.extend none) x (Fin.cons w v) =
      K (c.length + 1) (f x)
        (Fin.cons (projectiveFirstJetValue J x w)
          (fun i => J (c.partSize i) x (v ∘ c.emb i))) := by
  simp only [projectiveCompositionTerm_apply, OrderedFinpartition.extend,
    OrderedFinpartition.extendLeft]
  congr 1
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change J 1 x (fun _ => w) = J 1 x (Fin.cons w Fin.elim0)
    congr 1
    funext j
    rw [show j = 0 from Subsingleton.elim _ _]
    rfl
  · rfl

/-- Changing the arity by an equality preserves evaluation of a jet. -/
theorem projectiveJetFamily_congr (J : ProjectiveJetFamily X Y)
    {m n : ℕ} (h : m = n) (x : X) (v : Fin m → X) (w : Fin n → X)
    (hv : ∀ i (hi : i < m) (hi' : i < n), v ⟨i, hi⟩ = w ⟨i, hi'⟩) :
    J m x v = J n x w := by
  subst n
  congr 1
  funext i
  exact hv i i.isLt i.isLt

theorem projectiveCompositionTerm_extend_some (f : X → Y)
    (J : ProjectiveJetFamily X Y) (K : ProjectiveJetFamily Y Z)
    {n : ℕ} (c : OrderedFinpartition n) (i : Fin c.length)
    (x w : X) (v : Fin n → X) :
    projectiveCompositionTerm f J K (c.extend (some i)) x (Fin.cons w v) =
      K c.length (f x)
        (Function.update (fun j => J (c.partSize j) x (v ∘ c.emb j)) i
          (J (c.partSize i + 1) x (Fin.cons w (v ∘ c.emb i)))) := by
  classical
  simp only [projectiveCompositionTerm_apply, OrderedFinpartition.extend,
    OrderedFinpartition.extendMiddle]
  congr 1
  ext j
  rcases eq_or_ne j i with rfl | hji
  · simp only [dite_eq_left, Function.update_self]
    apply projectiveJetFamily_congr J (by simp)
    intro a ha ha'
    cases a with
    | zero => simp
    | succ a => simp [Function.comp_def, Fin.cons]
  · simp only [hji, dite_eq_right, Function.update_of_ne hji]
    apply projectiveJetFamily_congr J (by simp [hji])
    intro a ha ha'
    simp [Function.comp_def]

theorem projectiveCompositionJets_succ (f : X → Y) (J : ProjectiveJetFamily X Y)
    (K : ProjectiveJetFamily Y Z) (n : ℕ) (x w : X) (v : Fin n → X) :
    projectiveCompositionJets f J K (n + 1) x (Fin.cons w v) =
      ∑ c : OrderedFinpartition n,
        (projectiveCompositionTerm f J K (c.extend none) x (Fin.cons w v) +
          ∑ i : Fin c.length,
            projectiveCompositionTerm f J K (c.extend (some i)) x (Fin.cons w v)) := by
  classical
  rw [projectiveCompositionJets_apply, ← (OrderedFinpartition.extendEquiv n).sum_comp]
  simp only [Fintype.sum_sigma, OrderedFinpartition.extendEquiv_apply, Fintype.sum_option]

theorem HasProjectiveJetsOn.continuousOn_compositionTerm
    {f : X → Y} {g : Y → Z} {J : ProjectiveJetFamily X Y}
    {K : ProjectiveJetFamily Y Z} {U : Set X} {V : Set Y}
    (hf : HasProjectiveJetsOn f J U) (hg : HasProjectiveJetsOn g K V)
    (hmap : MapsTo f U V) {n : ℕ} (c : OrderedFinpartition n) :
    ContinuousOn (fun p : X × (Fin n → X) => projectiveCompositionTerm f J K c p.1 p.2)
      (U ×ˢ univ) := by
  have hbase : ContinuousOn (fun p : X × (Fin n → X) => f p.1) (U ×ˢ univ) :=
    hf.continuousOn.comp continuous_fst.continuousOn (fun _ hp => hp.1)
  have hslots : ContinuousOn
      (fun p : X × (Fin n → X) => fun i => J (c.partSize i) p.1 (p.2 ∘ c.emb i))
      (U ×ˢ univ) := by
    apply continuousOn_pi.mpr
    intro i
    have hselect : Continuous (fun z : X × (Fin n → X) => (z.1, z.2 ∘ c.emb i)) :=
      continuous_fst.prodMk (continuous_pi (fun j =>
        (continuous_apply (c.emb i j)).comp continuous_snd))
    exact (hf.2.1 (c.partSize i)).comp
      hselect.continuousOn
      (fun _ hp => ⟨hp.1, mem_univ _⟩)
  exact (hg.2.1 c.length).comp (hbase.prodMk hslots)
    (fun _ hp => ⟨hmap hp.1, mem_univ _⟩)

end PartitionComposition

section GenuineComposition

variable {E F G : ℕ → Type*}
  [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
  [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
  [∀ n, NormedAddCommGroup (G n)] [∀ n, NormedSpace ℝ (G n)]
  [∀ n, CompleteSpace (G n)]
variable {e : ∀ n, E (n + 1) →L[ℝ] E n}
  {f : ∀ n, F (n + 1) →L[ℝ] F n} {g : ∀ n, G (n + 1) →L[ℝ] G n}
variable {u : ProjectiveLimit E e → ProjectiveLimit F f}
  {v : ProjectiveLimit F f → ProjectiveLimit G g}
  {J : ProjectiveJetFamily (ProjectiveLimit E e) (ProjectiveLimit F f)}
  {K : ProjectiveJetFamily (ProjectiveLimit F f) (ProjectiveLimit G g)}
  {U : Set (ProjectiveLimit E e)} {V : Set (ProjectiveLimit F f)}

/-- Differentiating a partition summand either creates a new singleton
block or inserts the new direction into one existing block. -/
theorem HasProjectiveJetsOn.compositionTerm_hasLineDerivAt
    (hU : IsOpen U) (hV : IsOpen V)
    (hu : HasProjectiveJetsOn u J U) (hv : HasProjectiveJetsOn v K V)
    (hmap : MapsTo u U V) {n : ℕ} (c : OrderedFinpartition n)
    {x : ProjectiveLimit E e} (hx : x ∈ U) (w : ProjectiveLimit E e)
    (vs : Fin n → ProjectiveLimit E e) :
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
  have hd := hcurve.jet_eval isOpen_interior hWc.interior hv' hcurve_mem c.length
    (fun t i => J (c.partSize i) (x + t • w) (vs ∘ c.emb i))
    (fun i => J (c.partSize i + 1) x (Fin.cons w (vs ∘ c.emb i))) hslots
  simp only [projectiveCompositionTerm_extend_none, projectiveCompositionTerm_extend_some]
  simpa only [HasProjectiveLineDerivAt, projectiveCompositionTerm_apply,
    zero_smul, add_zero] using hd

/-- The ordered-partition tower is a genuine all-order tower for composition.
The domain is any open set; convexity is used only locally in the curve rule. -/
theorem HasProjectiveJetsOn.comp
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
      (fun c _ => HasProjectiveJetsOn.compositionTerm_hasLineDerivAt
        hU hV hu hv hmap c hx w vs)
    simpa only [HasProjectiveLineDerivAt, projectiveCompositionJets_apply] using h

end GenuineComposition

end ContinuousFlexibility.Analysis
