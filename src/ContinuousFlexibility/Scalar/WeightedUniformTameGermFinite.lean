import ContinuousFlexibility.Scalar.WeightedUniformTameGermOperations

/-!
# One common ball for finitely many actual uniform tame germs

The common base and loss are chosen before every derivative order.  An
additional prescribed neighborhood can impose the geometric positivity and
decoded smallness conditions needed by the scalar assembly.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false

section FiniteFamily

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  {ι : Type*} [Fintype ι] {F : ι → Type*}
  [∀ i, TopologicalSpace (F i)] [∀ i, AddCommGroup (F i)] [∀ i, Module ℝ (F i)]
  {p : ℕ → Seminorm ℝ E} {q : ∀ i, ℕ → Seminorm ℝ (F i)}
  {x0 : E} {f : ∀ i, E → F i}

/-- Finitely many genuine germs, together with any additional neighborhood,
admit one common base, loss, and ball of radius strictly less than one.
The statement includes an empty family of output maps. -/
theorem exists_common_uniformTameBall
    (hp : Monotone p) (ht : WithSeminorms p)
    (hf : ∀ i, UniformTameGerm p (q i) x0 (f i))
    {W : Set E} (hW : W ∈ 𝓝 x0) (required : ℕ) :
    ∃ base loss : ℕ, ∃ ε : ℝ,
      required ≤ base ∧ 0 < ε ∧ ε < 1 ∧
      {x | p base (x - x0) < ε} ⊆ W ∧
      ∀ i, FixedNeighborhoodSmoothTame p (q i)
        {x | p base (x - x0) < ε} base loss (f i) := by
  classical
  have hchoice (i : ι) :
      ∃ b ell : ℕ, ∃ δ : ℝ, 0 < δ ∧
        FixedNeighborhoodSmoothTame p (q i) {x | p b (x - x0) < δ} b ell (f i) :=
    hf i
  choose b ell δ hδ hfi using hchoice
  have hall : {x | ∀ i, p (b i) (x - x0) < δ i} ∈ 𝓝 x0 := by
    apply Filter.eventually_all.mpr
    intro i
    obtain ⟨J, _⟩ := (hfi i).2
    apply J.open_domain.mem_nhds
    simpa only [Set.mem_setOf_eq, sub_self, map_zero] using hδ i
  obtain ⟨base, η, hbase, hη, hη1, hsub⟩ :=
    exists_small_uniformTameBall hp ht (inter_mem hW hall)
      (max required (Finset.univ.sup b))
  let ε : ℝ := η / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε < 1 := by dsimp [ε]; linarith
  have hεη : ε ≤ η := by dsimp [ε]; linarith
  have hsub' :
      {x | p base (x - x0) < ε} ⊆
        W ∩ {x | ∀ i, p (b i) (x - x0) < δ i} :=
    fun x hx => hsub (hx.trans_le hεη)
  refine ⟨base, Finset.univ.sup ell, ε,
    (le_max_left _ _).trans hbase, hε, hε1,
    (fun x hx => (hsub' hx).1), ?_⟩
  intro i
  have hbi : b i ≤ base :=
    (Finset.le_sup (Finset.mem_univ i)).trans ((le_max_right _ _).trans hbase)
  have hli : ell i ≤ Finset.univ.sup ell := Finset.le_sup (Finset.mem_univ i)
  exact ((hfi i).restrict (isOpen_uniformTameBall ht base x0 ε)
    (fun x hx => (hsub' hx).2 i)).weaken hp hbi hli

/-- Finite actual outputs use precisely the sum grading prescribed by
`scalarOutputsGrading`. -/
theorem UniformTameGerm.pi
    (hp : Monotone p) (ht : WithSeminorms p)
    (hf : ∀ i, UniformTameGerm p (q i) x0 (f i)) :
    UniformTameGerm p (fun s => ∑ i, (q i s).comp (LinearMap.proj i))
      x0 (fun x i => f i x) := by
  obtain ⟨base, loss, ε, _, hε, _, _, hfi⟩ :=
    exists_common_uniformTameBall hp ht hf (W := univ) univ_mem 0
  exact ⟨base, loss, ε, hε,
    fixedNeighborhoodSmoothTame_pi (isOpen_uniformTameBall ht base x0 ε) hfi⟩

end FiniteFamily

end ContinuousFlexibility.Statements
