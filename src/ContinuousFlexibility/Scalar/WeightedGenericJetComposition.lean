import ContinuousFlexibility.Analysis.TameJetComposition

/-!
# Genuine composition through arbitrary locally convex source modules

The Banach-coordinate curve rule already works on arbitrary topological real
modules.  Supplying the actual continuity of the inner curve extends the
ordered-partition construction to the nested product state spaces used by
the weighted scalar problem.  Only the output is required to have complete
Banach coordinates.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {Y : Type*} [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
  [∀ n, CompleteSpace (F n)]
  {fbond : ∀ n, F (n + 1) →L[ℝ] F n}

/-- The genuine curve chain rule with an arbitrary topological-module
source and a projective output, using the actual continuity of the curve. -/
theorem HasProjectiveCurveDerivAt.bastiani_comp_generic
    {U : Set Y} {g : Y → (ProjectiveLimit F fbond)} {D : Y → Y →L[ℝ] (ProjectiveLimit F fbond)}
    (hU : IsOpen U) (hUc : Convex ℝ U)
    (hD : ContinuousOn (fun p : Y × Y => D p.1 p.2) (U ×ˢ univ))
    (hg : ∀ x ∈ U, ∀ v, HasProjectiveLineDerivAt g (D x v) x v)
    {c : ℝ → Y} {dc : Y} {t : ℝ}
    (hc : HasProjectiveCurveDerivAt c dc t) (hcc : ContinuousAt c t) (hct : c t ∈ U) :
    HasProjectiveCurveDerivAt (fun s : ℝ => g (c s)) (D (c t) dc) t := by
  apply (hasProjectiveCurveDerivAt_iff_levels _ _ _).mpr
  intro n
  let P := projectiveCoordinate F fbond n
  have hDn : ContinuousOn
      (fun p : Y × Y => (P.comp (D p.1)) p.2) (U ×ˢ univ) :=
    P.continuous.comp_continuousOn hD
  have hgn : ∀ x ∈ U, ∀ v,
      HasLineDerivAt ℝ (fun y => P (g y)) ((P.comp (D x)) v) x v := by
    intro x hx v
    exact (hasProjectiveLineDerivAt_iff_levels g (D x v) x v).mp (hg x hx v) n
  exact hasDerivAt_bastiani_comp_curve hU hUc hDn hgn hc hcc hct

/-- The actual variable-input jet rule on an arbitrary topological module.
Its input curves are differentiated in their original topology. -/
theorem HasProjectiveCurveDerivAt.jet_eval_generic
    {g : Y → (ProjectiveLimit F fbond)} {J : ProjectiveJetFamily Y (ProjectiveLimit F fbond)} {U : Set Y}
    (hU : IsOpen U) (hUc : Convex ℝ U) (hJ : HasProjectiveJetsOn g J U)
    {c : ℝ → Y} {dc : Y} {t : ℝ}
    (hc : HasProjectiveCurveDerivAt c dc t) (hcc : ContinuousAt c t) (hct : c t ∈ U)
    (n : ℕ) (v : ℝ → Fin n → Y) (dv : Fin n → Y)
    (hv : ∀ i, HasProjectiveCurveDerivAt (fun s => v s i) (dv i) t) :
    HasProjectiveCurveDerivAt (fun s => J n (c s) (v s))
      (J (n + 1) (c t) (Fin.cons dc (v t)) +
        ∑ i : Fin n, J n (c t) (Function.update (v t) i (dv i))) t := by
  have hfixed : HasProjectiveCurveDerivAt (fun s => J n (c s) (v t))
      (J (n + 1) (c t) (Fin.cons dc (v t))) t := by
    have h := hc.bastiani_comp_generic
      (g := fun y => J n y (v t))
      (D := fun y => projectiveJetHeadLinear J n y (v t))
      hU hUc (hJ.continuousOn_headLinear n (v t))
      (fun y hy w => by
        simpa only [projectiveJetHeadLinear_apply] using hJ.2.2 n y hy w (v t))
      hcc hct
    simpa only [projectiveJetHeadLinear_apply] using h
  have hB : ∀ w : Fin n → Y,
      ContinuousAt (fun p : ℝ × (Fin n → Y) => J n (c p.1) p.2) (t, w) := by
    intro w
    have hj : ContinuousAt (fun p : Y × (Fin n → Y) => J n p.1 p.2) (c t, w) :=
      (hJ.2.1 n).continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨hct, mem_univ _⟩)
    have hm : ContinuousAt (fun p : ℝ × (Fin n → Y) => (c p.1, p.2)) (t, w) :=
      (hcc.comp continuousAt_fst).prodMk continuousAt_snd
    exact ContinuousAt.comp
      (f := fun p : ℝ × (Fin n → Y) => (c p.1, p.2))
      (g := fun p : Y × (Fin n → Y) => J n p.1 p.2) (x := (t, w)) hj hm
  exact hasProjectiveCurveDerivAt_variableMultilinear
    (fun s => J n (c s)) v dv (J (n + 1) (c t) (Fin.cons dc (v t))) t hB hv hfixed

section Composition

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [LocallyConvexSpace ℝ Y]


/-- Differentiate one genuine partition term with arbitrary source and
intermediate locally convex modules. -/
theorem HasProjectiveJetsOn.compositionTerm_hasLineDerivAt_generic
    {u : X → Y} {v : Y → (ProjectiveLimit F fbond)}
    {J : ProjectiveJetFamily X Y} {K : ProjectiveJetFamily Y (ProjectiveLimit F fbond)}
    {U : Set X} {V : Set Y}
    (hU : IsOpen U) (hV : IsOpen V)
    (hu : HasProjectiveJetsOn u J U) (hv : HasProjectiveJetsOn v K V)
    (hmap : MapsTo u U V) {n : ℕ} (part : OrderedFinpartition n)
    {x : X} (hx : x ∈ U) (w : X) (vs : Fin n → X) :
    HasProjectiveLineDerivAt (fun y : X => projectiveCompositionTerm (X := X) (Y := Y) (Z := (ProjectiveLimit F fbond)) u J K part y vs)
      (projectiveCompositionTerm (X := X) (Y := Y) (Z := (ProjectiveLimit F fbond)) u J K (part.extend none) x (Fin.cons w vs) +
        ∑ i : Fin part.length,
          projectiveCompositionTerm (X := X) (Y := Y) (Z := (ProjectiveLimit F fbond)) u J K (part.extend (some i)) x (Fin.cons w vs)) x w := by
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
  have hpath : Tendsto (fun t : ℝ => x + t • w) (𝓝 0) (𝓝 x) := by
    have ht : Continuous (fun t : ℝ => x + t • w) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa only [zero_smul, add_zero] using ht.tendsto 0
  have hcc : ContinuousAt (fun t : ℝ => u (x + t • w)) 0 := by
    simpa only [ContinuousAt, Function.comp_def, zero_smul, add_zero] using
      (hu.continuousOn.continuousAt (hU.mem_nhds hx)).tendsto.comp hpath
  have hcurve_mem : (fun t : ℝ => u (x + t • w)) 0 ∈ interior W := by
    simpa only [zero_smul, add_zero] using hux
  have hslots (i : Fin part.length) :
      HasProjectiveCurveDerivAt
        (fun t : ℝ => J (part.partSize i) (x + t • w) (vs ∘ part.emb i))
        (J (part.partSize i + 1) x (Fin.cons w (vs ∘ part.emb i))) 0 :=
    hu.2.2 (part.partSize i) x hx w (vs ∘ part.emb i)
  have hd := hcurve.jet_eval_generic isOpen_interior hWc.interior hv' hcc hcurve_mem part.length
    (fun t i => J (part.partSize i) (x + t • w) (vs ∘ part.emb i))
    (fun i => J (part.partSize i + 1) x (Fin.cons w (vs ∘ part.emb i))) hslots
  simp only [projectiveCompositionTerm_extend_none, projectiveCompositionTerm_extend_some]
  simpa only [HasProjectiveLineDerivAt, projectiveCompositionTerm_apply,
    zero_smul, add_zero] using hd

/-- The actual ordered-partition tower composes through arbitrary locally
convex intermediate modules, including the nested scalar state products. -/
theorem HasProjectiveJetsOn.comp_generic
    {u : X → Y} {v : Y → (ProjectiveLimit F fbond)}
    {J : ProjectiveJetFamily X Y} {K : ProjectiveJetFamily Y (ProjectiveLimit F fbond)}
    {U : Set X} {V : Set Y}
    (hU : IsOpen U) (hV : IsOpen V)
    (hu : HasProjectiveJetsOn u J U) (hv : HasProjectiveJetsOn v K V)
    (hmap : MapsTo u U V) :
    HasProjectiveJetsOn (v ∘ u) (projectiveCompositionJets (X := X) (Y := Y) (Z := (ProjectiveLimit F fbond)) u J K) U := by
  classical
  have hzero : ∀ x ∈ U,
      projectiveCompositionJets (X := X) (Y := Y) (Z := (ProjectiveLimit F fbond)) u J K 0 x Fin.elim0 = v (u x) := by
    intro x hx
    rw [projectiveCompositionJets_apply, Fintype.sum_unique]
    change K 0 (u x) (fun i : Fin 0 => J 1 x (fun _ => Fin.elim0 i)) = v (u x)
    convert hv.1 (u x) (hmap hx) using 2
  have hcont : ∀ n, ContinuousOn
      (fun z : X × (Fin n → X) =>
        projectiveCompositionJets (X := X) (Y := Y) (Z := (ProjectiveLimit F fbond)) u J K n z.1 z.2)
      (U ×ˢ univ) := by
    intro n
    simp only [projectiveCompositionJets_apply]
    exact continuousOn_finsetSum Finset.univ
      (fun part _ => hu.continuousOn_compositionTerm hv hmap part)
  have hderiv : ∀ n (x : X), x ∈ U → ∀ w vs,
      HasProjectiveLineDerivAt
        (fun y : X => projectiveCompositionJets (X := X) (Y := Y) (Z := (ProjectiveLimit F fbond)) u J K n y vs)
        (projectiveCompositionJets (X := X) (Y := Y) (Z := (ProjectiveLimit F fbond)) u J K (n + 1) x
          (Fin.cons w vs)) x w := by
    intro n x hx w vs
    rw [projectiveCompositionJets_succ]
    have h := HasProjectiveCurveDerivAt.finset_sum Finset.univ
      (fun part _ => HasProjectiveJetsOn.compositionTerm_hasLineDerivAt_generic
        hU hV hu hv hmap part hx w vs)
    simpa only [HasProjectiveLineDerivAt, projectiveCompositionJets_apply] using h
  exact ⟨hzero, hcont, hderiv⟩

end Composition

end ContinuousFlexibility.Analysis
