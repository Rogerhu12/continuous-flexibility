module

public import ContinuousFlexibility.Analysis.BastianiCurveChain
public import ContinuousFlexibility.Analysis.ProjectiveMultilinearCalculus

/-!
# Actual derivatives of projective jets evaluated on varying curves

The jet recursion supplies the derivative of a coefficient at fixed
inputs. The genuine projective curve chain rule transports this
derivative along the base curve. The variable multilinear product rule
then accounts for all varying input curves. No norm on a projective
source or symmetry of the higher jets is assumed.

The second-order formula below differentiates the actual first
directional derivative of a composition. General all-order composition
jets, Schwarz symmetry, and tame bounds remain separate obligations.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false

section HeadSlot

variable {V W : Type*} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
  [TopologicalSpace W] [AddCommGroup W] [Module ℝ W]

/-- The actual continuous linear map in the new, first direction slot. -/
def projectiveJetHeadLinear (J : ProjectiveJetFamily V W) (n : ℕ)
    (x : V) (vs : Fin n → V) : V →L[ℝ] W :=
  (J (n + 1) x).toContinuousLinearMap (Fin.cons 0 vs) 0

@[simp] theorem projectiveJetHeadLinear_apply (J : ProjectiveJetFamily V W)
    (n : ℕ) (x : V) (vs : Fin n → V) (v : V) :
    projectiveJetHeadLinear J n x vs v = J (n + 1) x (Fin.cons v vs) := by
  change J (n + 1) x (Function.update (Fin.cons 0 vs) 0 v) =
    J (n + 1) x (Fin.cons v vs)
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp

/-- Joint jet continuity gives the jointly continuous partial differential. -/
theorem HasProjectiveJetsOn.continuousOn_headLinear
    {f : V → W} {J : ProjectiveJetFamily V W} {U : Set V}
    (hJ : HasProjectiveJetsOn f J U) (n : ℕ) (vs : Fin n → V) :
    ContinuousOn (fun p : V × V => projectiveJetHeadLinear J n p.1 vs p.2)
      (U ×ˢ univ) := by
  have hcons : Continuous
      (fun p : V × V => Fin.cons (α := fun _ : Fin (n + 1) => V) p.2 vs) := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_snd
    · exact continuous_const
  have hmap : Continuous (fun p : V × V =>
      (p.1, Fin.cons (α := fun _ : Fin (n + 1) => V) p.2 vs)) :=
    continuous_fst.prodMk hcons
  have h := (hJ.2.1 (n + 1)).comp hmap.continuousOn
    (show MapsTo (fun p : V × V =>
      (p.1, Fin.cons (α := fun _ : Fin (n + 1) => V) p.2 vs))
      (U ×ˢ univ) (U ×ˢ univ) from fun p hp => ⟨hp.1, mem_univ _⟩)
  simpa only [projectiveJetHeadLinear_apply, Function.comp_def] using h

def projectiveFirstJetValue (J : ProjectiveJetFamily V W) (x v : V) : W :=
  J 1 x (Fin.cons v Fin.elim0)

def projectiveSecondJetValue (J : ProjectiveJetFamily V W) (x u v : V) : W :=
  J 2 x (Fin.cons u (Fin.cons v Fin.elim0))

end HeadSlot

section Evaluation

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
variable {bond : ∀ n, E (n + 1) →L[ℝ] E n}
variable {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
  [∀ n, CompleteSpace (F n)]
variable {fbond : ∀ n, F (n + 1) →L[ℝ] F n}

/-- The coefficient derivative along a genuine projective curve, at any
fixed list of inputs, follows from the actual jet recursion. -/
theorem HasProjectiveCurveDerivAt.jet_eval_fixed
    {g : ProjectiveLimit E bond → ProjectiveLimit F fbond}
    {J : ProjectiveJetFamily (ProjectiveLimit E bond) (ProjectiveLimit F fbond)}
    {U : Set (ProjectiveLimit E bond)} (hU : IsOpen U) (hUc : Convex ℝ U)
    (hJ : HasProjectiveJetsOn g J U)
    {c : ℝ → ProjectiveLimit E bond} {dc : ProjectiveLimit E bond} {t : ℝ}
    (hc : HasProjectiveCurveDerivAt c dc t) (hct : c t ∈ U)
    (n : ℕ) (vs : Fin n → ProjectiveLimit E bond) :
    HasProjectiveCurveDerivAt (fun s => J n (c s) vs)
      (J (n + 1) (c t) (Fin.cons dc vs)) t := by
  have h := hc.bastiani_comp
    (g := fun y => J n y vs)
    (D := fun y => projectiveJetHeadLinear J n y vs)
    hU hUc (hJ.continuousOn_headLinear n vs)
    (fun y hy v => by
      simpa only [projectiveJetHeadLinear_apply] using hJ.2.2 n y hy v vs) hct
  simpa only [projectiveJetHeadLinear_apply] using h

/-- Every order has the true curve product rule, in the original
projective topologies and on the same fixed open convex domain. -/
theorem HasProjectiveCurveDerivAt.jet_eval
    {g : ProjectiveLimit E bond → ProjectiveLimit F fbond}
    {J : ProjectiveJetFamily (ProjectiveLimit E bond) (ProjectiveLimit F fbond)}
    {U : Set (ProjectiveLimit E bond)} (hU : IsOpen U) (hUc : Convex ℝ U)
    (hJ : HasProjectiveJetsOn g J U)
    {c : ℝ → ProjectiveLimit E bond} {dc : ProjectiveLimit E bond} {t : ℝ}
    (hc : HasProjectiveCurveDerivAt c dc t) (hct : c t ∈ U)
    (n : ℕ) (v : ℝ → Fin n → ProjectiveLimit E bond)
    (dv : Fin n → ProjectiveLimit E bond)
    (hv : ∀ i, HasProjectiveCurveDerivAt (fun s => v s i) (dv i) t) :
    HasProjectiveCurveDerivAt (fun s => J n (c s) (v s))
      (J (n + 1) (c t) (Fin.cons dc (v t)) +
        ∑ i : Fin n, J n (c t) (Function.update (v t) i (dv i))) t := by
  have hB : ∀ w : Fin n → ProjectiveLimit E bond,
      ContinuousAt (fun p : ℝ × (Fin n → ProjectiveLimit E bond) =>
        J n (c p.1) p.2) (t, w) := by
    intro w
    have hj : ContinuousAt
        (fun p : ProjectiveLimit E bond × (Fin n → ProjectiveLimit E bond) =>
          J n p.1 p.2) (c t, w) :=
      (hJ.2.1 n).continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨hct, mem_univ _⟩)
    have hm : ContinuousAt
        (fun p : ℝ × (Fin n → ProjectiveLimit E bond) => (c p.1, p.2)) (t, w) :=
      (hc.continuousAt.comp continuousAt_fst).prodMk continuousAt_snd
    exact ContinuousAt.comp
      (f := fun p : ℝ × (Fin n → ProjectiveLimit E bond) => (c p.1, p.2))
      (g := fun p : ProjectiveLimit E bond × (Fin n → ProjectiveLimit E bond) =>
        J n p.1 p.2)
      (x := (t, w)) hj hm
  exact hasProjectiveCurveDerivAt_variableMultilinear
    (fun s => J n (c s)) v dv
    (J (n + 1) (c t) (Fin.cons dc (v t))) t hB hv
    (hc.jet_eval_fixed hU hUc hJ hct n (v t))

/-- The arity-one specialization is the real derivative of the
differential field applied to a varying direction. -/
theorem HasProjectiveCurveDerivAt.firstJet_eval
    {g : ProjectiveLimit E bond → ProjectiveLimit F fbond}
    {J : ProjectiveJetFamily (ProjectiveLimit E bond) (ProjectiveLimit F fbond)}
    {U : Set (ProjectiveLimit E bond)} (hU : IsOpen U) (hUc : Convex ℝ U)
    (hJ : HasProjectiveJetsOn g J U)
    {c v : ℝ → ProjectiveLimit E bond} {dc dv : ProjectiveLimit E bond} {t : ℝ}
    (hc : HasProjectiveCurveDerivAt c dc t) (hct : c t ∈ U)
    (hv : HasProjectiveCurveDerivAt v dv t) :
    HasProjectiveCurveDerivAt (fun s => projectiveFirstJetValue J (c s) (v s))
      (projectiveSecondJetValue J (c t) dc (v t) +
        projectiveFirstJetValue J (c t) dv) t := by
  have h := hc.jet_eval hU hUc hJ hct 1
    (fun s => Fin.cons (v s) Fin.elim0) (Fin.cons dv Fin.elim0)
    (fun i => by fin_cases i; exact hv)
  have hu : Function.update
      (Fin.cons (α := fun _ : Fin 1 => ProjectiveLimit E bond) (v t) Fin.elim0)
      (0 : Fin 1) dv =
      Fin.cons (α := fun _ : Fin 1 => ProjectiveLimit E bond) dv Fin.elim0 := by
    funext i
    fin_cases i
    simp
  simpa only [Fin.sum_univ_one, Fin.cons_zero, hu,
    projectiveFirstJetValue, projectiveSecondJetValue] using h

end Evaluation

section ActualFirstDerivative

variable {V W : Type*} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  [TopologicalSpace W] [AddCommGroup W] [Module ℝ W]

/-- Order zero agrees with the actual function on the open domain,
so the recursive first jet is its genuine directional derivative. -/
theorem HasProjectiveJetsOn.hasLineDerivAt
    {f : V → W} {J : ProjectiveJetFamily V W} {U : Set V}
    (hJ : HasProjectiveJetsOn f J U) (hU : IsOpen U)
    {x : V} (hx : x ∈ U) (v : V) :
    HasProjectiveLineDerivAt f (projectiveFirstJetValue J x v) x v := by
  have heq : f =ᶠ[𝓝 x] (fun y => J 0 y Fin.elim0) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (hJ.1 y hy).symm
  exact (hJ.2.2 0 x hx v Fin.elim0).congr_germ heq

end ActualFirstDerivative

section SecondComposition

variable {E M F : ℕ → Type*}
  [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
  [∀ n, NormedAddCommGroup (M n)] [∀ n, NormedSpace ℝ (M n)]
  [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
  [∀ n, CompleteSpace (F n)]
variable {ebond : ∀ n, E (n + 1) →L[ℝ] E n}
  {mbond : ∀ n, M (n + 1) →L[ℝ] M n}
  {fbond : ∀ n, F (n + 1) →L[ℝ] F n}

/-- The actual first derivative of a nonlinear composition, expressed
by the verified jets of its two factors. -/
theorem hasProjectiveLineDerivAt_comp_of_jets
    {f : ProjectiveLimit E ebond → ProjectiveLimit M mbond}
    {g : ProjectiveLimit M mbond → ProjectiveLimit F fbond}
    {Jf : ProjectiveJetFamily (ProjectiveLimit E ebond) (ProjectiveLimit M mbond)}
    {Jg : ProjectiveJetFamily (ProjectiveLimit M mbond) (ProjectiveLimit F fbond)}
    {U : Set (ProjectiveLimit E ebond)} {V : Set (ProjectiveLimit M mbond)}
    (hU : IsOpen U) (hV : IsOpen V) (hVc : Convex ℝ V)
    (hf : HasProjectiveJetsOn f Jf U) (hg : HasProjectiveJetsOn g Jg V)
    {x : ProjectiveLimit E ebond} (hx : x ∈ U) (hfx : f x ∈ V)
    (v : ProjectiveLimit E ebond) :
    HasProjectiveLineDerivAt (fun y => g (f y))
      (projectiveFirstJetValue Jg (f x) (projectiveFirstJetValue Jf x v)) x v := by
  have h := (hf.hasLineDerivAt hU hx v).bastiani_comp
    (D := fun y => projectiveJetHeadLinear Jg 0 y Fin.elim0)
    hV hVc (hg.continuousOn_headLinear 0 Fin.elim0)
    (fun y hy w => by
      simpa only [projectiveJetHeadLinear_apply, projectiveFirstJetValue] using
        hg.hasLineDerivAt hV hy w) hfx
  simpa only [projectiveJetHeadLinear_apply, projectiveFirstJetValue] using h

/-- Differentiate the actual first-derivative field of a composition.
The order of the two new directions is retained; Schwarz symmetry is
not needed or asserted. -/
theorem hasProjectiveLineDerivAt_comp_firstJet
    {f : ProjectiveLimit E ebond → ProjectiveLimit M mbond}
    {g : ProjectiveLimit M mbond → ProjectiveLimit F fbond}
    {Jf : ProjectiveJetFamily (ProjectiveLimit E ebond) (ProjectiveLimit M mbond)}
    {Jg : ProjectiveJetFamily (ProjectiveLimit M mbond) (ProjectiveLimit F fbond)}
    {U : Set (ProjectiveLimit E ebond)} {V : Set (ProjectiveLimit M mbond)}
    (hU : IsOpen U) (hV : IsOpen V) (hVc : Convex ℝ V)
    (hf : HasProjectiveJetsOn f Jf U) (hg : HasProjectiveJetsOn g Jg V)
    {x : ProjectiveLimit E ebond} (hx : x ∈ U) (hfx : f x ∈ V)
    (u v : ProjectiveLimit E ebond) :
    HasProjectiveLineDerivAt
      (fun y => projectiveFirstJetValue Jg (f y) (projectiveFirstJetValue Jf y v))
      (projectiveSecondJetValue Jg (f x)
          (projectiveFirstJetValue Jf x u) (projectiveFirstJetValue Jf x v) +
        projectiveFirstJetValue Jg (f x) (projectiveSecondJetValue Jf x u v)) x u := by
  have hc : HasProjectiveCurveDerivAt
      (fun t : ℝ => f (x + t • u)) (projectiveFirstJetValue Jf x u) 0 :=
    hf.hasLineDerivAt hU hx u
  have hv : HasProjectiveCurveDerivAt
      (fun t : ℝ => projectiveFirstJetValue Jf (x + t • u) v)
      (projectiveSecondJetValue Jf x u v) 0 :=
    hf.2.2 1 x hx u (Fin.cons v Fin.elim0)
  have hbase : (fun t : ℝ => f (x + t • u)) 0 ∈ V := by
    simpa only [zero_smul, add_zero] using hfx
  have h := hc.firstJet_eval hV hVc hg hbase hv
  simpa only [HasProjectiveLineDerivAt, zero_smul, add_zero] using h

end SecondComposition

end ContinuousFlexibility.Analysis
