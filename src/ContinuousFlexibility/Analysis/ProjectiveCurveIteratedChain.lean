module

public import ContinuousFlexibility.Analysis.ProjectiveJetEvaluation
public import ContinuousFlexibility.Analysis.ProjectiveNewtonRecurrence

/-!
# Iterated chain rules along real parameter curves

The source may be the actual product of projective and real parameter
spaces. Each output coordinate uses its genuine Banach derivative. Finite
lists retain the multiplicities of the chain-rule terms.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false

section TopologicalSource

variable {Z : Type*} [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
  [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z]

theorem HasProjectiveCurveDerivAt.continuousAt_topological
    {c : ℝ → Z} {dc : Z} {t : ℝ} (hc : HasProjectiveCurveDerivAt c dc t) :
    ContinuousAt c t := by
  have hshift : ContinuousAt (fun h : ℝ => c (t + h)) 0 := by
    apply continuousAt_iff_punctured_nhds.mpr
    simpa only [add_zero] using hc.tendsto_shift
  have hsub : ContinuousAt (fun s : ℝ => s - t) t :=
    (continuous_id.sub continuous_const).continuousAt
  have hshift' : ContinuousAt (fun h : ℝ => c (t + h)) (t - t) := by
    simpa only [sub_self] using hshift
  have he : (fun s : ℝ => c (t + (s - t))) = c := by
    funext s
    congr 1
    ring
  rw [← he]
  exact ContinuousAt.comp (f := fun s : ℝ => s - t)
    (g := fun h : ℝ => c (t + h)) (x := t) hshift' hsub

variable {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
  [∀ n, CompleteSpace (F n)] {bond : ∀ n, F (n + 1) →L[ℝ] F n}

/-- Compose a genuine curve in a topological real module with a map to a
projective limit. The Banach chain rule applies to each output projection. -/
theorem HasProjectiveCurveDerivAt.bastiani_comp_topological
    {U : Set Z} {g : Z → ProjectiveLimit F bond}
    {D : Z → Z →L[ℝ] ProjectiveLimit F bond}
    (hU : IsOpen U) (hUc : Convex ℝ U)
    (hD : ContinuousOn (fun p : Z × Z => D p.1 p.2) (U ×ˢ univ))
    (hg : ∀ x ∈ U, ∀ v, HasProjectiveLineDerivAt g (D x v) x v)
    {c : ℝ → Z} {dc : Z} {t : ℝ}
    (hc : HasProjectiveCurveDerivAt c dc t) (hct : c t ∈ U) :
    HasProjectiveCurveDerivAt (fun s => g (c s)) (D (c t) dc) t := by
  apply (hasProjectiveCurveDerivAt_iff_levels _ _ _).mpr
  intro n
  let P := projectiveCoordinate F bond n
  have hDn : ContinuousOn (fun p : Z × Z => (P.comp (D p.1)) p.2) (U ×ˢ univ) :=
    P.continuous.comp_continuousOn hD
  have hgn : ∀ x ∈ U, ∀ v,
      HasLineDerivAt ℝ (fun y => P (g y)) ((P.comp (D x)) v) x v := by
    intro x hx v
    exact (hasProjectiveLineDerivAt_iff_levels g (D x v) x v).mp (hg x hx v) n
  exact hasDerivAt_bastiani_comp_curve hU hUc hDn hgn hc hc.continuousAt_topological hct

/-- The actual derivative of a jet with a varying base and varying input
directions. The source can itself be a product with a real parameter. -/
theorem HasProjectiveCurveDerivAt.jet_eval_topological
    {g : Z → ProjectiveLimit F bond} {J : ProjectiveJetFamily Z (ProjectiveLimit F bond)}
    {U : Set Z} (hU : IsOpen U) (hUc : Convex ℝ U) (hJ : HasProjectiveJetsOn g J U)
    {c : ℝ → Z} {dc : Z} {t : ℝ} (hc : HasProjectiveCurveDerivAt c dc t) (hct : c t ∈ U)
    (n : ℕ) (v : ℝ → Fin n → Z) (dv : Fin n → Z)
    (hv : ∀ i, HasProjectiveCurveDerivAt (fun s => v s i) (dv i) t) :
    HasProjectiveCurveDerivAt (fun s => J n (c s) (v s))
      (J (n + 1) (c t) (Fin.cons dc (v t)) +
        ∑ i : Fin n, J n (c t) (Function.update (v t) i (dv i))) t := by
  have hfix : HasProjectiveCurveDerivAt (fun s => J n (c s) (v t))
      (J (n + 1) (c t) (Fin.cons dc (v t))) t := by
    have h := hc.bastiani_comp_topological
      (g := fun y => J n y (v t)) (D := fun y => projectiveJetHeadLinear J n y (v t))
      hU hUc (hJ.continuousOn_headLinear n (v t))
      (fun y hy u => by
        simpa only [projectiveJetHeadLinear_apply] using hJ.2.2 n y hy u (v t)) hct
    simpa only [projectiveJetHeadLinear_apply] using h
  have hB (w : Fin n → Z) :
      ContinuousAt (fun p : ℝ × (Fin n → Z) => J n (c p.1) p.2) (t, w) := by
    have hj : ContinuousAt (fun p : Z × (Fin n → Z) => J n p.1 p.2) (c t, w) :=
      (hJ.2.1 n).continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨hct, mem_univ _⟩)
    have hm : ContinuousAt (fun p : ℝ × (Fin n → Z) => (c p.1, p.2)) (t, w) :=
      (hc.continuousAt_topological.comp continuousAt_fst).prodMk continuousAt_snd
    exact ContinuousAt.comp
      (f := fun p : ℝ × (Fin n → Z) => (c p.1, p.2))
      (g := fun p : Z × (Fin n → Z) => J n p.1 p.2)
      (x := (t, w)) hj hm
  exact hasProjectiveCurveDerivAt_variableMultilinear
    (fun s => J n (c s)) v dv (J (n + 1) (c t) (Fin.cons dc (v t))) t hB hv hfix

end TopologicalSource

theorem HasProjectiveCurveDerivAt.prodMk
    {X Y : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    {c : ℝ → X} {d : ℝ → Y} {dc : X} {dd : Y} {t : ℝ}
    (hc : HasProjectiveCurveDerivAt c dc t) (hd : HasProjectiveCurveDerivAt d dd t) :
    HasProjectiveCurveDerivAt (fun s => (c s, d s)) (dc, dd) t := by
  unfold HasProjectiveCurveDerivAt at hc hd ⊢
  simpa only [Prod.mk_sub_mk, Prod.smul_mk] using hc.prodMk_nhds hd

/-- The orders of the curve derivatives occupying the slots of one jet. -/
abbrev ParameterChainTerm := Σ k : ℕ, Fin k → ℕ

def parameterChainTermWeight (a : ParameterChainTerm) : ℕ :=
  ∑ i : Fin a.1, a.2 i

def parameterChainTermSuccessors (a : ParameterChainTerm) : List ParameterChainTerm :=
  ⟨a.1 + 1, Fin.cons 1 a.2⟩ ::
    List.ofFn (fun i : Fin a.1 => ⟨a.1, Function.update a.2 i (a.2 i + 1)⟩)

/-- Repeated entries in the list count repeated terms in the chain rule. -/
def parameterChainTerms : ℕ → List ParameterChainTerm
  | 0 => [⟨0, Fin.elim0⟩]
  | m + 1 => (parameterChainTerms m).flatMap parameterChainTermSuccessors

private theorem sum_fin_update_succ {k : ℕ} (f : Fin k → ℕ) (i : Fin k) :
    (∑ j : Fin k, Function.update f i (f i + 1) j) = (∑ j : Fin k, f j) + 1 := by
  have hf : Function.update f i (f i + 1) = fun j => f j + if j = i then 1 else 0 := by
    funext j
    by_cases h : j = i
    · subst j
      simp
    · simp only [Function.update_of_ne h, ite_eq_right h, add_zero]
  rw [hf, Finset.sum_add_distrib]
  simp

theorem parameterChainTerm_positive_and_weight
    {m : ℕ} {a : ParameterChainTerm} (ha : a ∈ parameterChainTerms m) :
    (∀ i, 0 < a.2 i) ∧ parameterChainTermWeight a = m := by
  induction m generalizing a with
  | zero =>
    have he : a = (⟨0, Fin.elim0⟩ : ParameterChainTerm) :=
      List.mem_singleton.mp ha
    subst a
    exact ⟨fun i => Fin.elim0 i, Fin.sum_univ_zero _⟩
  | succ m ih =>
    obtain ⟨prev, hprev, hs⟩ := List.mem_flatMap.mp ha
    obtain ⟨hpos, hweight⟩ := ih hprev
    change (∑ j : Fin prev.1, prev.2 j) = m at hweight
    change a ∈ ⟨prev.1 + 1, Fin.cons 1 prev.2⟩ ::
      List.ofFn (fun i : Fin prev.1 => (⟨prev.1, Function.update prev.2 i (prev.2 i + 1)⟩ :
        ParameterChainTerm)) at hs
    rcases List.mem_cons.mp hs with he | he
    · subst a
      constructor
      · intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · exact Nat.zero_lt_one
        · exact hpos i
      · change (∑ j : Fin (prev.1 + 1), Fin.cons 1 prev.2 j) = m + 1
        rw [Fin.sum_cons, hweight, Nat.add_comm]
    · obtain ⟨i, hi⟩ := List.mem_ofFn.mp he
      subst a
      constructor
      · intro j
        change 0 < Function.update prev.2 i (prev.2 i + 1) j
        by_cases hji : j = i
        · subst j
          simpa only [Function.update_self] using Nat.zero_lt_succ (prev.2 i)
        · simpa only [Function.update_of_ne hji] using hpos j
      · change (∑ j : Fin prev.1, Function.update prev.2 i (prev.2 i + 1) j) = m + 1
        rw [sum_fin_update_succ, hweight]

theorem parameterChainTerm_order_le
    {m : ℕ} {a : ParameterChainTerm} (ha : a ∈ parameterChainTerms m) (i : Fin a.1) :
    a.2 i ≤ m := by
  have hweight := (parameterChainTerm_positive_and_weight ha).2
  rw [← hweight]
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (a.2 j)) (Finset.mem_univ i)

theorem parameterChainTerm_arity_le
    {m : ℕ} {a : ParameterChainTerm} (ha : a ∈ parameterChainTerms m) :
    a.1 ≤ m := by
  obtain ⟨hpos, hweight⟩ := parameterChainTerm_positive_and_weight ha
  rw [← hweight]
  calc
    a.1 = ∑ _ : Fin a.1, (1 : ℕ) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun i _ => Nat.succ_le_iff.mpr (hpos i))

/-- A term containing the highest derivative has no other input slots. -/
theorem parameterChainTerm_highest_order_unique
    {m : ℕ} {a : ParameterChainTerm} (ha : a ∈ parameterChainTerms m)
    {i : Fin a.1} (hi : a.2 i = m) (j : Fin a.1) : j = i := by
  obtain ⟨hpos, hweight⟩ := parameterChainTerm_positive_and_weight ha
  by_contra hji
  have hsum : a.2 i + (∑ k ∈ Finset.univ.erase i, a.2 k) = m :=
    (Finset.add_sum_erase Finset.univ a.2 (Finset.mem_univ i)).trans hweight
  have hmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩
  have hle : a.2 j ≤ ∑ k ∈ Finset.univ.erase i, a.2 k :=
    Finset.single_le_sum (fun k _ => Nat.zero_le (a.2 k)) hmem
  have hj := hpos j
  omega

theorem parameterChainTerm_arity_eq_one_of_highest_order
    {m : ℕ} {a : ParameterChainTerm} (ha : a ∈ parameterChainTerms m)
    {i : Fin a.1} (hi : a.2 i = m) : a.1 = 1 := by
  have hcard : (Finset.univ : Finset (Fin a.1)).card ≤ 1 :=
    Finset.card_le_one.mpr (fun j _ k _ =>
      (parameterChainTerm_highest_order_unique ha hi j).trans
        (parameterChainTerm_highest_order_unique ha hi k).symm)
  have hle : a.1 ≤ 1 := by simpa only [Finset.card_univ, Fintype.card_fin] using hcard
  have hlt := i.isLt
  omega

section Evaluation

variable {Z W : Type*} [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
  [TopologicalSpace W] [AddCommGroup W] [Module ℝ W]

def parameterChainTermEval (J : ProjectiveJetFamily Z W) (c : ℕ → ℝ → Z)
    (a : ParameterChainTerm) (t : ℝ) : W :=
  J a.1 (c 0 t) (fun i => c (a.2 i) t)

def parameterChainSum (J : ProjectiveJetFamily Z W) (c : ℕ → ℝ → Z)
    (terms : List ParameterChainTerm) (t : ℝ) : W :=
  (terms.map (fun a => parameterChainTermEval J c a t)).sum

def parameterChainEval (J : ProjectiveJetFamily Z W) (c : ℕ → ℝ → Z)
    (m : ℕ) (t : ℝ) : W :=
  parameterChainSum J c (parameterChainTerms m) t

private theorem parameterChainSum_successors (J : ProjectiveJetFamily Z W) (c : ℕ → ℝ → Z)
    (a : ParameterChainTerm) (t : ℝ) :
    parameterChainSum J c (parameterChainTermSuccessors a) t =
      J (a.1 + 1) (c 0 t) (Fin.cons (c 1 t) (fun j => c (a.2 j) t)) +
        ∑ i : Fin a.1, J a.1 (c 0 t)
          (Function.update (fun j => c (a.2 j) t) i (c (a.2 i + 1) t)) := by
  have hhead : (fun j : Fin (a.1 + 1) => c ((Fin.cons 1 a.2 : Fin (a.1 + 1) → ℕ) j) t) =
      Fin.cons (c 1 t) (fun j => c (a.2 j) t) := by
    simpa only [Function.comp_def] using Fin.comp_cons (fun k : ℕ => c k t) 1 a.2
  have hslot (i : Fin a.1) : (fun j : Fin a.1 => c (Function.update a.2 i (a.2 i + 1) j) t) =
      Function.update (fun j => c (a.2 j) t) i (c (a.2 i + 1) t) := by
    simpa only [Function.comp_def] using Function.comp_update (fun k : ℕ => c k t) a.2 i (a.2 i + 1)
  simp only [parameterChainSum, parameterChainTermSuccessors, List.map_cons, List.sum_cons,
    List.map_ofFn, List.sum_ofFn, Function.comp_def, parameterChainTermEval, hhead, hslot]

private theorem parameterChainSum_flatMap (J : ProjectiveJetFamily Z W) (c : ℕ → ℝ → Z)
    (terms : List ParameterChainTerm) (t : ℝ) :
    parameterChainSum J c (terms.flatMap parameterChainTermSuccessors) t =
      (terms.map (fun a => parameterChainSum J c (parameterChainTermSuccessors a) t)).sum := by
  induction terms with
  | nil => rfl
  | cons a terms ih =>
    simp only [parameterChainSum, List.flatMap_cons, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]

private theorem hasProjectiveCurveDerivAt_list_sum
    {ι : Type*} [IsTopologicalAddGroup W]
    (terms : List ι) {f : ι → ℝ → W} {df : ι → W} {t : ℝ}
    (h : ∀ i, HasProjectiveCurveDerivAt (f i) (df i) t) :
    HasProjectiveCurveDerivAt (fun s => (terms.map (fun i => f i s)).sum)
      (terms.map df).sum t := by
  induction terms with
  | nil => exact hasProjectiveCurveDerivAt_const 0 t
  | cons a terms ih =>
    simpa only [List.map_cons, List.sum_cons] using (h a).add ih

theorem parameterChainEval_zero_eq {g : Z → W} {J : ProjectiveJetFamily Z W} {U : Set Z}
    (hJ : HasProjectiveJetsOn g J U) {c : ℕ → ℝ → Z} {t : ℝ} (ht : c 0 t ∈ U) :
    parameterChainEval J c 0 t = g (c 0 t) := by
  change J 0 (c 0 t) (fun i : Fin 0 => c (Fin.elim0 i) t) + 0 = g (c 0 t)
  have he : (fun i : Fin 0 => c (Fin.elim0 i) t) = (Fin.elim0 : Fin 0 → Z) :=
    Subsingleton.elim _ _
  rw [he, add_zero, hJ.1 _ ht]

end Evaluation

section IteratedChain

variable {Z : Type*} [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
  [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z]
variable {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
  [∀ n, CompleteSpace (F n)] {bond : ∀ n, F (n + 1) →L[ℝ] F n}

private theorem hasProjectiveCurveDerivAt_parameterChainTerm
    {g : Z → ProjectiveLimit F bond} {J : ProjectiveJetFamily Z (ProjectiveLimit F bond)}
    {U : Set Z} (hU : IsOpen U) (hUc : Convex ℝ U) (hJ : HasProjectiveJetsOn g J U)
    {c : ℕ → ℝ → Z} {t : ℝ} (hc : ∀ k, HasProjectiveCurveDerivAt (c k) (c (k + 1) t) t)
    (ht : c 0 t ∈ U) (a : ParameterChainTerm) :
    HasProjectiveCurveDerivAt (parameterChainTermEval J c a)
      (parameterChainSum J c (parameterChainTermSuccessors a) t) t := by
  rw [parameterChainSum_successors]
  exact (hc 0).jet_eval_topological hU hUc hJ ht a.1 (fun s i => c (a.2 i) s)
    (fun i => c (a.2 i + 1) t) (fun i => hc (a.2 i))

/-- Differentiating the finite formula at any order gives the next formula. -/
theorem hasProjectiveCurveDerivAt_parameterChainEval
    {g : Z → ProjectiveLimit F bond} {J : ProjectiveJetFamily Z (ProjectiveLimit F bond)}
    {U : Set Z} (hU : IsOpen U) (hUc : Convex ℝ U) (hJ : HasProjectiveJetsOn g J U)
    {c : ℕ → ℝ → Z} {t : ℝ} (hc : ∀ k, HasProjectiveCurveDerivAt (c k) (c (k + 1) t) t)
    (ht : c 0 t ∈ U) (m : ℕ) :
    HasProjectiveCurveDerivAt (parameterChainEval J c m) (parameterChainEval J c (m + 1) t) t := by
  change HasProjectiveCurveDerivAt (parameterChainSum J c (parameterChainTerms m))
    (parameterChainSum J c ((parameterChainTerms m).flatMap parameterChainTermSuccessors) t) t
  rw [parameterChainSum_flatMap]
  exact hasProjectiveCurveDerivAt_list_sum (parameterChainTerms m)
    (hasProjectiveCurveDerivAt_parameterChainTerm hU hUc hJ hc ht)

end IteratedChain

/-- The zeroth function is the original composition, and all positive
orders are given by the finite chain-rule lists. -/
def projectiveCurveCompositionTower
    {Z W : Type*} [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
    [TopologicalSpace W] [AddCommGroup W] [Module ℝ W]
    (g : Z → W) (J : ProjectiveJetFamily Z W) (c : ℕ → ℝ → Z) : ℕ → ℝ → W
  | 0 => fun t => g (c 0 t)
  | m + 1 => parameterChainEval J c (m + 1)

/-- The finite formula is a genuine derivative tower for the original
composition at every parameter where the source curve has a derivative
tower and lies in the open convex domain. -/
theorem hasProjectiveCurveDerivAt_compositionTower
    {Z : Type*} [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z]
    [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z]
    {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
    [∀ n, CompleteSpace (F n)] {bond : ∀ n, F (n + 1) →L[ℝ] F n}
    {g : Z → ProjectiveLimit F bond} {J : ProjectiveJetFamily Z (ProjectiveLimit F bond)}
    {U : Set Z} (hU : IsOpen U) (hUc : Convex ℝ U) (hJ : HasProjectiveJetsOn g J U)
    {c : ℕ → ℝ → Z} {t : ℝ} (hc : ∀ k, HasProjectiveCurveDerivAt (c k) (c (k + 1) t) t)
    (ht : c 0 t ∈ U) (m : ℕ) :
    HasProjectiveCurveDerivAt (projectiveCurveCompositionTower g J c m)
      (projectiveCurveCompositionTower g J c (m + 1) t) t := by
  cases m with
  | zero =>
    change HasProjectiveCurveDerivAt (fun s => g (c 0 s)) (parameterChainEval J c 1 t) t
    have hsingle : parameterChainEval J c 1 t =
        parameterChainSum J c (parameterChainTermSuccessors ⟨0, Fin.elim0⟩) t := by
      simp only [parameterChainEval, parameterChainTerms, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
    have hfirst : parameterChainEval J c 1 t = projectiveJetHeadLinear J 0 (c 0 t) Fin.elim0 (c 1 t) := by
      rw [hsingle, parameterChainSum_successors, Fin.sum_univ_zero, add_zero, projectiveJetHeadLinear_apply]
      have he : (fun j : Fin 0 => c (Fin.elim0 j) t) = (Fin.elim0 : Fin 0 → Z) := Subsingleton.elim _ _
      rw [he]
    rw [hfirst]
    exact (hc 0).bastiani_comp_topological
      (g := g) (D := fun x : Z => projectiveJetHeadLinear J 0 x (Fin.elim0 : Fin 0 → Z))
      hU hUc (hJ.continuousOn_headLinear 0 Fin.elim0)
      (fun x hx v => by
        simpa only [projectiveJetHeadLinear_apply, projectiveFirstJetValue] using hJ.hasLineDerivAt hU hx v) ht
  | succ m => exact hasProjectiveCurveDerivAt_parameterChainEval hU hUc hJ hc ht (m + 1)

theorem HasProjectiveCurveDerivAt.sub
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X]
    {c d : ℝ → X} {dc dd : X} {t : ℝ}
    (hc : HasProjectiveCurveDerivAt c dc t) (hd : HasProjectiveCurveDerivAt d dd t) :
    HasProjectiveCurveDerivAt (fun s => c s - d s) (dc - dd) t := by
  unfold HasProjectiveCurveDerivAt at hc hd ⊢
  apply (hc.sub hd).congr'
  filter_upwards with h
  rw [← smul_sub]
  congr 1
  abel

/-- The unchanged real parameter, with its actual first derivative and
zero higher derivatives. -/
def realParameterTower : ℕ → ℝ → ℝ
  | 0 => id
  | 1 => fun _ => 1
  | _ + 2 => fun _ => 0

theorem hasProjectiveCurveDerivAt_realParameterTower (m : ℕ) (t : ℝ) :
    HasProjectiveCurveDerivAt (realParameterTower m) (realParameterTower (m + 1) t) t := by
  cases m with
  | zero => exact hasDerivAt_iff_tendsto_slope_zero.mp (hasDerivAt_id t)
  | succ m =>
    cases m with
    | zero => exact hasProjectiveCurveDerivAt_const 1 t
    | succ m => exact hasProjectiveCurveDerivAt_const 0 t

section NewtonParameterTowers

variable {E F : ℕ → Type*}
  [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
  [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
  {ebond : ∀ n, E (n + 1) →L[ℝ] E n} {fbond : ∀ n, F (n + 1) →L[ℝ] F n}

local notation "X" => ProjectiveLimit E ebond
local notation "Y" => ProjectiveLimit F fbond

/-- All parameter derivatives of the Newton updates, with the same
smoothing maps and indices as the actual iteration. -/
def projectiveNewtonParameterTower
    (R : X × ℝ → Y) (V : X × ℝ → Y →ₗ[ℝ] X)
    (JR : ProjectiveJetFamily (X × ℝ) Y) (JV : ProjectiveJetFamily ((X × ℝ) × Y) X)
    (S : ℕ → X →L[ℝ] X) (N : ℕ → ℕ) (x₀ : X) : ℕ → ℕ → ℝ → X
  | 0 => fun
    | 0 => fun _ => x₀
    | _ + 1 => fun _ => 0
  | n + 1 =>
    let x := projectiveNewtonParameterTower R V JR JV S N x₀ n
    let z := fun k t => (x k t, realParameterTower k t)
    let r := projectiveCurveCompositionTower R JR z
    let w := fun k t => (z k t, r k t)
    let v := projectiveCurveCompositionTower (fun p : (X × ℝ) × Y => V p.1 p.2) JV w
    fun k t => x k t - S (N n) (v k t)

theorem projectiveNewtonParameterTower_zero
    (R : X × ℝ → Y) (V : X × ℝ → Y →ₗ[ℝ] X)
    (JR : ProjectiveJetFamily (X × ℝ) Y) (JV : ProjectiveJetFamily ((X × ℝ) × Y) X)
    (S : ℕ → X →L[ℝ] X) (N : ℕ → ℕ) (x₀ : X) (n : ℕ) (t : ℝ) :
    projectiveNewtonParameterTower R V JR JV S N x₀ n 0 t =
      (projectiveSmoothedNewtonIterates R V S N (x₀, t) n).1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let z := projectiveSmoothedNewtonIterates R V S N (x₀, t) n
    let x := projectiveNewtonParameterTower R V JR JV S N x₀ n 0 t
    have hx : x = z.1 := ih
    have hparam : z.2 = t := projectiveSmoothedNewtonIterates_parameter R V S N (x₀, t) n
    have he : (x, t) = z := Prod.ext hx hparam.symm
    change x - S (N n) (V (x, t) (R (x, t))) = z.1 - S (N n) (V z (R z))
    rw [he, hx]

/-- The actual Newton iterates have genuine parameter derivatives of all
orders on the parameter set where every iterate stays in the domain. -/
theorem hasProjectiveCurveDerivAt_projectiveNewtonParameterTower
    [∀ n, CompleteSpace (E n)] [∀ n, CompleteSpace (F n)]
    (R : X × ℝ → Y) (V : X × ℝ → Y →ₗ[ℝ] X)
    {JR : ProjectiveJetFamily (X × ℝ) Y} {JV : ProjectiveJetFamily ((X × ℝ) × Y) X}
    {U : Set (X × ℝ)} (hU : IsOpen U) (hUc : Convex ℝ U)
    (hR : HasProjectiveJetsOn R JR U)
    (hV : HasProjectiveJetsOn (fun p : (X × ℝ) × Y => V p.1 p.2) JV (U ×ˢ univ))
    (S : ℕ → X →L[ℝ] X) (N : ℕ → ℕ) (x₀ : X) {I : Set ℝ}
    (hiter : ∀ n t, t ∈ I → projectiveSmoothedNewtonIterates R V S N (x₀, t) n ∈ U)
    (n m : ℕ) {t : ℝ} (ht : t ∈ I) :
    HasProjectiveCurveDerivAt (projectiveNewtonParameterTower R V JR JV S N x₀ n m)
      (projectiveNewtonParameterTower R V JR JV S N x₀ n (m + 1) t) t := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => exact hasProjectiveCurveDerivAt_const x₀ t
    | succ m => exact hasProjectiveCurveDerivAt_const 0 t
  | succ n ih =>
    let x := projectiveNewtonParameterTower R V JR JV S N x₀ n
    let z := fun k s => (x k s, realParameterTower k s)
    let r := projectiveCurveCompositionTower R JR z
    let w := fun k s => (z k s, r k s)
    let v := projectiveCurveCompositionTower (fun p : (X × ℝ) × Y => V p.1 p.2) JV w
    have hz (k : ℕ) : HasProjectiveCurveDerivAt (z k) (z (k + 1) t) t :=
      (ih k).prodMk (hasProjectiveCurveDerivAt_realParameterTower k t)
    have hz₀ : z 0 t ∈ U := by
      have he : z 0 t = projectiveSmoothedNewtonIterates R V S N (x₀, t) n :=
        Prod.ext (projectiveNewtonParameterTower_zero R V JR JV S N x₀ n t)
          (projectiveSmoothedNewtonIterates_parameter R V S N (x₀, t) n).symm
      rw [he]
      exact hiter n t ht
    have hr (k : ℕ) : HasProjectiveCurveDerivAt (r k) (r (k + 1) t) t :=
      hasProjectiveCurveDerivAt_compositionTower hU hUc hR hz hz₀ k
    have hw (k : ℕ) : HasProjectiveCurveDerivAt (w k) (w (k + 1) t) t :=
      (hz k).prodMk (hr k)
    have hw₀ : w 0 t ∈ U ×ˢ (univ : Set Y) := ⟨hz₀, mem_univ _⟩
    have hv (k : ℕ) : HasProjectiveCurveDerivAt (v k) (v (k + 1) t) t :=
      hasProjectiveCurveDerivAt_compositionTower (hU.prod isOpen_univ) (hUc.prod convex_univ)
        hV hw hw₀ k
    exact (ih m).sub ((hv m).clm_comp (S (N n)))

end NewtonParameterTowers

end ContinuousFlexibility.Analysis
