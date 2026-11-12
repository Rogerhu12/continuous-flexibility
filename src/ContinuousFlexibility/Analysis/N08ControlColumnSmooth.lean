import ContinuousFlexibility.Analysis.N08ControlColumnJets
import ContinuousFlexibility.Analysis.TameInverseBounds
import ContinuousFlexibility.Analysis.TamePairTopology

/-!
# Joint smooth tameness of the actual control column

Every finite column-jet expression is a locally tame evaluation of an
original residual jet at linear coordinate maps. Multilinear normalization
therefore gives the full smooth-tame estimate on the zero-control slice,
with no restriction on the size of the column input. The final theorem
extracts the column and all-order centered bounds from one actual germ.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false

namespace N08ControlColumnCalculus

section ExpressionBounds

variable {X B A A' : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace B] [AddCommGroup B] [Module ℝ B]
  [TopologicalSpace A] [AddCommGroup A] [Module ℝ A]
  [TopologicalSpace A'] [AddCommGroup A'] [Module ℝ A']

def Expression.IsZeroLoss (p : ℕ → Seminorm ℝ X) (b : ℕ → Seminorm ℝ B)
    (a : ℕ → Seminorm ℝ A) : Expression X B A → Prop
  | .jet _ v c => (∀ i, IsTameLinear a p (v i).toLinearMap 0 0) ∧
      IsTameLinear a b c.toLinearMap 0 0
  | .fiber _ v => ∀ i, IsTameLinear a p (v i).toLinearMap 0 0
  | .add e f => e.IsZeroLoss p b a ∧ f.IsZeroLoss p b a

theorem Expression.IsZeroLoss.diff
    {p : ℕ → Seminorm ℝ X} {b : ℕ → Seminorm ℝ B}
    {a : ℕ → Seminorm ℝ A} {a' : ℕ → Seminorm ℝ A'}
    {e : Expression X B A} (he : e.IsZeroLoss p b a)
    (g : A' →L[ℝ] A) (hg : IsTameLinear a' a g.toLinearMap 0 0)
    (h : A' →L[ℝ] X × B) (hh : IsTameLinear a' (pairGrading p b) h.toLinearMap 0 0) :
    (e.diff g h).IsZeroLoss p b a' := by
  have hfst := inverseTame_comp_zero (inverseTame_fst p b) hh
  have hsnd := inverseTame_comp_zero (inverseTame_snd p b) hh
  induction e with
  | jet n v c =>
      refine ⟨?_, inverseTame_comp_zero he.2 hg⟩
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hfst
      · exact inverseTame_comp_zero (he.1 j) hg
  | fiber n v =>
      refine ⟨?_, (fun i => inverseTame_comp_zero (he i) hg), hsnd⟩
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hfst
      · exact inverseTame_comp_zero (he j) hg
  | add e f ie iff => exact ⟨ie he.1, iff he.2⟩

variable [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [IsTopologicalAddGroup B] [ContinuousSMul ℝ B]

theorem columnExpression_zeroLoss (p : ℕ → Seminorm ℝ X) (b : ℕ → Seminorm ℝ B) :
    ∀ n, (columnExpression (X := X) (B := B) n).IsZeroLoss p b
      (tupleGrading (fun _ : Fin n => pairGrading p b)) := by
  intro n
  induction n with
  | zero => intro i; exact i.elim0
  | succ n ih =>
      exact ih.diff (inverseAuxTail (X × B) n) (inverseTame_tupleTail (pairGrading p b) n)
        (ContinuousLinearMap.proj 0) (inverseTame_tupleProjection (pairGrading p b) 0)

variable {Y : Type*} [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  {U : Set (X × B)} {F : X × B → Y}

theorem Expression.locallyTameOn_eval
    {p : ℕ → Seminorm ℝ X} {b : ℕ → Seminorm ℝ B}
    {q : ℕ → Seminorm ℝ Y} {a : ℕ → Seminorm ℝ A}
    (hp : Monotone p) (hb : Monotone b) (ha : Monotone a)
    (e : Expression X B A) (he : e.IsZeroLoss p b a) (J : SmoothDirections U F)
    (hJ : ∀ k, LocallyTameOn (jetGrading (pairGrading p b) k) q (U ×ˢ univ)
      (fun z => J.D k z.1 z.2)) :
    LocallyTameOn (pairGrading (pairGrading p b) a) q
      ((slice U ×ˢ univ) ×ˢ univ) (fun z => e.eval J z.1 z.2) := by
  let d := pairGrading (pairGrading p b) a
  let W : Set ((X × B) × A) := (slice U ×ˢ univ) ×ˢ univ
  have hd : Monotone d := tamePairGrading_monotone (tamePairGrading_monotone hp hb) ha
  have hstate : LocallyTameOn d (pairGrading p b) W (fun z => z.1) :=
    locallyTameOn_of_isTameLinear (ContinuousLinearMap.fst ℝ (X × B) A)
      (inverseTame_fst (pairGrading p b) a) W
  have hx : LocallyTameOn d p W (fun z => z.1.1) := inverseLocallyTame_fst hstate
  have hc : LocallyTameOn d b W (fun z => z.1.2) := inverseLocallyTame_snd hstate
  have haux : LocallyTameOn d a W (fun z => z.2) :=
    locallyTameOn_of_isTameLinear (ContinuousLinearMap.snd ℝ (X × B) A)
      (inverseTame_snd (pairGrading p b) a) W
  have hjet (n : ℕ) (v : Fin n → A →L[ℝ] X)
      (hv : ∀ i, IsTameLinear a p (v i).toLinearMap 0 0)
      (c : (X × B) × A → B) (hcb : LocallyTameOn d b W c) :
      LocallyTameOn d q W (fun z => orderedJet J n z.1.1 (fun i => v i z.2) (c z)) := by
    have hdirs (i : Fin n) : LocallyTameOn d p W (fun z => v i z.2) :=
      (locallyTameOn_of_isTameLinear (v i) (hv i) univ).comp haux
        (fun _ _ => mem_univ _)
    have hinput (i : Fin (n + 1)) : LocallyTameOn d (pairGrading p b) W
        (fun z => Fin.snoc (α := fun _ : Fin (n + 1) => X × B)
          (fun j => (v j z.2, (0 : B))) ((0 : X), c z) i) := by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.snoc_last] using
          (locallyTameOn_const d p W (0 : X)).prodMk hd hcb
      · simpa only [Fin.snoc_castSucc] using
          (hdirs j).prodMk hd (locallyTameOn_const d b W (0 : B))
    have hargs := (hx.prodMk hd (locallyTameOn_const d b W (0 : B))).prodMk hd
      (LocallyTameOn.pi hd hinput)
    exact (hJ (n + 1)).comp hargs (fun z hz => ⟨hz.1.1, mem_univ _⟩)
  induction e with
  | jet n v c =>
      exact hjet n v he.1 (fun z => c z.2)
        ((locallyTameOn_of_isTameLinear c he.2 univ).comp haux (fun _ _ => mem_univ _))
  | fiber n v => exact hjet n v he (fun z => z.1.2) hc
  | add e f ie iff => exact (ie he.1).add hd (iff he.2)

end ExpressionBounds

end N08ControlColumnCalculus

section SmoothTame

variable {X B Y : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [TopologicalSpace B] [AddCommGroup B] [Module ℝ B]
  [IsTopologicalAddGroup B] [ContinuousSMul ℝ B]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [T2Space Y]
  {p : ℕ → Seminorm ℝ X} {b : ℕ → Seminorm ℝ B} {q : ℕ → Seminorm ℝ Y}
  {U : Set (X × B)} {F : X × B → Y}

/-- Joint smooth tameness holds on the whole zero-control slice times
all control vectors. The theorem uses the specified actual residual tower. -/
theorem n08ControlColumn_smoothTame (hp : Monotone p) (hb : Monotone b)
    (htp : WithSeminorms p) (htb : WithSeminorms b)
    (J : SmoothDirections U F) (hJ : J.TameBounds (pairGrading p b) q) :
    SmoothTameOn (pairGrading p b) q (N08ControlColumnCalculus.slice U ×ˢ univ)
      (fun z : X × B => n08ControlColumn J z.1 z.2) := by
  let hP := tamePairGrading_monotone hp hb
  let htP := withSeminorms_pairGrading htp htb
  apply smoothTameOn_of_locallyTameOn_jets hP htP (n08ControlColumn_smoothDirections J)
  intro n
  have h := (N08ControlColumnCalculus.columnExpression n).locallyTameOn_eval hp hb
    (tupleGrading_monotone _ (fun _ => hP))
    (N08ControlColumnCalculus.columnExpression_zeroLoss p b n) J
    (fun k => locallyTameOn_jetEvaluation htP J hJ k)
  exact h.congr (fun z hz => n08ControlColumn_smoothDirections_apply J n hz.1.1 z.2)

theorem n08ControlColumn_smoothTame_of_uniform (hp : Monotone p) (hb : Monotone b)
    (htp : WithSeminorms p) (htb : WithSeminorms b)
    {base loss : ℕ} (J : SmoothDirections U F)
    (hJ : UniformScalarTowerEstimate (pairGrading p b) q U base loss F J) :
    SmoothTameOn (pairGrading p b) q (N08ControlColumnCalculus.slice U ×ˢ univ)
      (fun z : X × B => n08ControlColumn J z.1 z.2) := by
  apply n08ControlColumn_smoothTame hp hb htp htb J
  intro k x0 hx0
  refine ⟨loss, base, 1, zero_lt_one, ?_⟩
  intro s hs
  obtain ⟨C, hC, hbound⟩ := hJ k s hs
  exact ⟨C, hC, fun x hx _ v => hbound x hx v⟩

end SmoothTame

section Germ

variable {X B Y : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [T2Space Y]
  {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y} {x0 : X} {F : X × B → Y}

private theorem normGrading_topology : WithSeminorms (fun _ : ℕ => normSeminorm ℝ B) := by
  apply (norm_withSeminorms ℝ B).congr
  · intro n
    exact ⟨{()}, 1, by simp⟩
  · intro u
    exact ⟨{0}, 1, by simp⟩

/-- One actual uniform germ produces a continuous linear control column,
its full joint smooth-tame map, and a centered bound at every output order.
The state ball, base and loss are chosen before all output orders. -/
theorem n08ControlColumn_of_uniformTameGerm (hp : Monotone p) (hq : Monotone q)
    (htp : WithSeminorms p)
    (hF : UniformTameGerm (pairGrading p (fun _ => normSeminorm ℝ B)) q (x0, 0) F) :
    ∃ base loss : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∃ column : X → B →L[ℝ] Y,
      (∀ x, p base (x - x0) < ε → ∀ b : B,
        HasProjectiveLineDerivAt (fun a : B => F (x, a)) (column x b) 0 b) ∧
      SmoothTameOn (pairGrading p (fun _ => normSeminorm ℝ B)) q
        ({x | p base (x - x0) < ε} ×ˢ univ) (fun z : X × B => column z.1 z.2) ∧
      (∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, p base (x - x0) < ε → ∀ b : B,
        q s (column x b) ≤ C * (1 + p (s + loss) (x - x0)) * ‖b‖) := by
  obtain ⟨base, loss, ε, hε, _, J, hJ⟩ := hF
  have heq : N08ControlColumnCalculus.slice
      {z | pairGrading p (fun _ => normSeminorm ℝ B) base (z - (x0, 0)) < ε} =
      {x | p base (x - x0) < ε} := by
    ext x
    simp only [N08ControlColumnCalculus.slice, Set.mem_setOf_eq, Prod.mk_sub_mk,
      pairGrading_apply, sub_self, map_zero, add_zero]
  have hmem (x : X) (hx : p base (x - x0) < ε) :
      (x, (0 : B)) ∈
        {z | pairGrading p (fun _ => normSeminorm ℝ B) base (z - (x0, 0)) < ε} := by
    change p base (x - x0) + (normSeminorm ℝ B) (0 - 0) < ε
    simpa only [sub_self, map_zero, add_zero] using hx
  refine ⟨base, base + loss, ε, hε, n08ControlColumn J,
    (fun x hx b => n08ControlColumn_hasLineDerivAt J (hmem x hx) b), ?_, ?_⟩
  · simpa only [heq] using n08ControlColumn_smoothTame_of_uniform hp
      (show Monotone (fun _ : ℕ => normSeminorm ℝ B) from fun _ _ _ => le_rfl)
      htp normGrading_topology J hJ
  · intro s
    obtain ⟨C, hC, hbound⟩ := n08ControlColumn_bound_all_orders hp hq J hJ x0 s
    exact ⟨C, hC, fun x hx b => hbound x (hmem x hx) b⟩

end Germ

end ContinuousFlexibility.Statements
