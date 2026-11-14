module

public import ContinuousFlexibility.Analysis.ProjectiveJetEvaluation

/-!
# First and second jets of a composition

The first candidate is a continuous linear map and the second is a
continuous bilinear map. Their joint evaluations are continuous on the
given domain. The actual directional quotient limits hold on arbitrary
open domains, using one convex neighborhood of the outer base point
for both limits.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped Topology

set_option backward.isDefEq.respectTransparency false

section Candidates

variable {X Y Z : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]

/-- The continuous linear first-jet candidate for a composition. -/
def projectiveCompFirst (f : X → Y) (Jf : ProjectiveJetFamily X Y)
    (Jg : ProjectiveJetFamily Y Z) (x : X) : X →L[ℝ] Z :=
  (projectiveJetHeadLinear Jg 0 (f x) Fin.elim0).comp
    (projectiveJetHeadLinear Jf 0 x Fin.elim0)

theorem projectiveCompFirst_apply (f : X → Y) (Jf : ProjectiveJetFamily X Y)
    (Jg : ProjectiveJetFamily Y Z) (x v : X) :
    projectiveCompFirst f Jf Jg x v =
      projectiveFirstJetValue Jg (f x) (projectiveFirstJetValue Jf x v) := by
  simp only [projectiveCompFirst, ContinuousLinearMap.comp_apply,
    projectiveJetHeadLinear_apply, projectiveFirstJetValue]

/-- The continuous bilinear second-jet candidate, with the new direction
in the first slot. -/
def projectiveCompSecond [ContinuousAdd Z] (f : X → Y) (Jf : ProjectiveJetFamily X Y)
    (Jg : ProjectiveJetFamily Y Z) (x : X) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 2 => X) Z :=
  (Jg 2 (f x)).compContinuousLinearMap
      (fun _ => projectiveJetHeadLinear Jf 0 x Fin.elim0) +
    (projectiveJetHeadLinear Jg 0 (f x) Fin.elim0).compContinuousMultilinearMap (Jf 2 x)

theorem projectiveCompSecond_apply [ContinuousAdd Z] (f : X → Y)
    (Jf : ProjectiveJetFamily X Y) (Jg : ProjectiveJetFamily Y Z)
    (x : X) (vs : Fin 2 → X) :
    projectiveCompSecond f Jf Jg x vs =
      Jg 2 (f x) (fun i => projectiveJetHeadLinear Jf 0 x Fin.elim0 (vs i)) +
        projectiveJetHeadLinear Jg 0 (f x) Fin.elim0 (Jf 2 x vs) := rfl

theorem projectiveCompSecond_cons [ContinuousAdd Z] (f : X → Y)
    (Jf : ProjectiveJetFamily X Y) (Jg : ProjectiveJetFamily Y Z) (x u v : X) :
    projectiveCompSecond f Jf Jg x (Fin.cons u (Fin.cons v Fin.elim0)) =
      projectiveSecondJetValue Jg (f x)
          (projectiveFirstJetValue Jf x u) (projectiveFirstJetValue Jf x v) +
        projectiveFirstJetValue Jg (f x) (projectiveSecondJetValue Jf x u v) := by
  have hslots :
      (fun i : Fin 2 => projectiveJetHeadLinear Jf 0 x Fin.elim0
        (Fin.cons (α := fun _ : Fin 2 => X) u (Fin.cons v Fin.elim0) i)) =
      Fin.cons (α := fun _ : Fin 2 => Y) (projectiveJetHeadLinear Jf 0 x Fin.elim0 u)
        (Fin.cons (projectiveJetHeadLinear Jf 0 x Fin.elim0 v) Fin.elim0) := by
    funext i
    fin_cases i <;> rfl
  rw [projectiveCompSecond_apply, hslots]
  simp only [projectiveJetHeadLinear_apply, projectiveFirstJetValue, projectiveSecondJetValue]

/-- The verified order-zero jet gives continuity of the underlying map. -/
theorem HasProjectiveJetsOn.continuousOn
    {f : X → Y} {Jf : ProjectiveJetFamily X Y} {U : Set X}
    (hf : HasProjectiveJetsOn f Jf U) : ContinuousOn f U := by
  have hpair : Continuous (fun x : X => (x, (Fin.elim0 : Fin 0 → X))) :=
    continuous_id.prodMk continuous_const
  have hmap : MapsTo (fun x : X => (x, (Fin.elim0 : Fin 0 → X))) U (U ×ˢ univ) :=
    fun x hx => ⟨hx, mem_univ _⟩
  exact ((hf.2.1 0).comp' hpair.continuousOn hmap).congr
    (fun x hx => (hf.1 x hx).symm)

theorem HasProjectiveJetsOn.continuousOn_compFirst
    {f : X → Y} {g : Y → Z} {Jf : ProjectiveJetFamily X Y}
    {Jg : ProjectiveJetFamily Y Z} {U : Set X} {V : Set Y}
    (hf : HasProjectiveJetsOn f Jf U) (hg : HasProjectiveJetsOn g Jg V)
    (hmap : MapsTo f U V) :
    ContinuousOn (fun p : X × X => projectiveCompFirst f Jf Jg p.1 p.2) (U ×ˢ univ) := by
  have hbase : ContinuousOn (fun p : X × X => f p.1) (U ×ˢ univ) :=
    hf.continuousOn.comp' continuousOn_fst (fun _ hp => hp.1)
  have h := (hg.continuousOn_headLinear 0 Fin.elim0).comp'
    (hbase.prodMk (hf.continuousOn_headLinear 0 Fin.elim0))
    (fun _ hp => ⟨hmap hp.1, mem_univ _⟩)
  simpa only [projectiveCompFirst, ContinuousLinearMap.comp_apply] using h

theorem HasProjectiveJetsOn.continuousOn_compSecond [ContinuousAdd Z]
    {f : X → Y} {g : Y → Z} {Jf : ProjectiveJetFamily X Y}
    {Jg : ProjectiveJetFamily Y Z} {U : Set X} {V : Set Y}
    (hf : HasProjectiveJetsOn f Jf U) (hg : HasProjectiveJetsOn g Jg V)
    (hmap : MapsTo f U V) :
    ContinuousOn (fun p : X × (Fin 2 → X) => projectiveCompSecond f Jf Jg p.1 p.2)
      (U ×ˢ univ) := by
  have hbase : ContinuousOn (fun p : X × (Fin 2 → X) => f p.1) (U ×ˢ univ) :=
    hf.continuousOn.comp' continuousOn_fst (fun _ hp => hp.1)
  have hslots : ContinuousOn (fun p : X × (Fin 2 → X) => fun i : Fin 2 =>
      projectiveJetHeadLinear Jf 0 p.1 Fin.elim0 (p.2 i)) (U ×ˢ univ) := by
    apply continuousOn_pi'
    intro i
    have hpair : Continuous (fun p : X × (Fin 2 → X) => (p.1, p.2 i)) :=
      continuous_fst.prodMk ((continuous_apply i).comp continuous_snd)
    exact (hf.continuousOn_headLinear 0 Fin.elim0).comp' hpair.continuousOn
      (fun _ hp => ⟨hp.1, mem_univ _⟩)
  have houter := (hg.2.1 2).comp' (hbase.prodMk hslots)
    (fun _ hp => ⟨hmap hp.1, mem_univ _⟩)
  have hinner := (hg.continuousOn_headLinear 0 Fin.elim0).comp'
    (hbase.prodMk (hf.2.1 2)) (fun _ hp => ⟨hmap hp.1, mem_univ _⟩)
  apply (houter.add hinner).congr
  intro p _
  simpa only [Pi.add_apply] using projectiveCompSecond_apply f Jf Jg p.1 p.2

private theorem hasProjectiveJetsOn_mono
    {f : X → Y} {Jf : ProjectiveJetFamily X Y} {U W : Set X}
    (hf : HasProjectiveJetsOn f Jf U) (hWU : W ⊆ U) :
    HasProjectiveJetsOn f Jf W :=
  ⟨fun x hx => hf.1 x (hWU hx),
    fun n => (hf.2.1 n).mono (Set.prod_mono hWU (Subset.rfl)),
    fun n x hx v vs => hf.2.2 n x (hWU hx) v vs⟩

end Candidates

section Quotients

variable {E M F : ℕ → Type*}
  [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
  [∀ n, NormedAddCommGroup (M n)] [∀ n, NormedSpace ℝ (M n)]
  [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
  [∀ n, CompleteSpace (F n)]
variable {ebond : ∀ n, E (n + 1) →L[ℝ] E n}
  {mbond : ∀ n, M (n + 1) →L[ℝ] M n}
  {fbond : ∀ n, F (n + 1) →L[ℝ] F n}

local notation "X" => ProjectiveLimit E ebond
local notation "Y" => ProjectiveLimit M mbond
local notation "Z" => ProjectiveLimit F fbond

/-- Composition through order two on open domains of projective limits.
The continuity and quotient limits are on the original source domain. -/
theorem projective_comp_through_two
    {f : X → Y} {g : Y → Z} {Jf : ProjectiveJetFamily X Y}
    {Jg : ProjectiveJetFamily Y Z} {U : Set X} {V : Set Y}
    (hU : IsOpen U) (hV : IsOpen V) (hmap : MapsTo f U V)
    (hf : HasProjectiveJetsOn f Jf U) (hg : HasProjectiveJetsOn g Jg V) :
    ContinuousOn (g ∘ f) U ∧
      ContinuousOn (fun p : X × X => projectiveCompFirst f Jf Jg p.1 p.2) (U ×ˢ univ) ∧
      ContinuousOn (fun p : X × (Fin 2 → X) => projectiveCompSecond f Jf Jg p.1 p.2)
        (U ×ˢ univ) ∧
      (∀ x ∈ U, ∀ v,
        HasProjectiveLineDerivAt (g ∘ f) (projectiveCompFirst f Jf Jg x v) x v) ∧
      (∀ x ∈ U, ∀ u v,
        HasProjectiveLineDerivAt (fun y => projectiveCompFirst f Jf Jg y v)
          (projectiveCompSecond f Jf Jg x (Fin.cons u (Fin.cons v Fin.elim0))) x u) := by
  refine ⟨hg.continuousOn.comp hf.continuousOn hmap, hf.continuousOn_compFirst hg hmap,
    hf.continuousOn_compSecond hg hmap, ?_⟩
  suffices h : ∀ x ∈ U,
      (∀ v, HasProjectiveLineDerivAt (g ∘ f) (projectiveCompFirst f Jf Jg x v) x v) ∧
      (∀ u v, HasProjectiveLineDerivAt (fun y => projectiveCompFirst f Jf Jg y v)
        (projectiveCompSecond f Jf Jg x (Fin.cons u (Fin.cons v Fin.elim0))) x u) from
    ⟨fun x hx => (h x hx).1, fun x hx => (h x hx).2⟩
  intro x hx
  obtain ⟨W, ⟨hW, hWc⟩, hWV⟩ :=
    (LocallyConvexSpace.convex_basis (𝕜 := ℝ) (f x)).mem_iff.mp (hV.mem_nhds (hmap hx))
  have hsub : interior W ⊆ V := interior_subset.trans hWV
  have hfx : f x ∈ interior W := mem_interior_iff_mem_nhds.mpr hW
  have hg' := hasProjectiveJetsOn_mono hg hsub
  constructor
  · intro v
    simpa only [Function.comp_def, projectiveCompFirst_apply] using
      hasProjectiveLineDerivAt_comp_of_jets hU isOpen_interior hWc.interior hf hg' hx hfx v
  · intro u v
    simpa only [projectiveCompFirst_apply, projectiveCompSecond_cons] using
      hasProjectiveLineDerivAt_comp_firstJet hU isOpen_interior hWc.interior hf hg' hx hfx u v

end Quotients

end ContinuousFlexibility.Analysis
