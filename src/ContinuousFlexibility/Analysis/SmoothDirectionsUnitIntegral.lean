import ContinuousFlexibility.Analysis.ProjectiveUnitIntegral
import ContinuousFlexibility.Analysis.SolveNewtonBridge
import ContinuousFlexibility.Analysis.TameElementaryCalculus

/-!
# Actual directional towers under compact parameter integration

Joint continuity of every evaluated jet gives continuity and local
domination in each Banach level. Differentiating the level integrals
therefore constructs a genuine projective directional tower.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped Topology

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)]
  [∀ n, NormedSpace ℝ (F n)] [∀ n, CompleteSpace (F n)]
  {bond : ∀ n, F (n + 1) →L[ℝ] F n}

theorem continuous_smoothDirections_univ
    {f : E → ProjectiveLimit F bond} (J : SmoothDirections univ f) : Continuous f :=
  continuousOn_univ.mp J.continuousOn

theorem smoothDirections_hasDerivAt_line_level
    {f : E → ProjectiveLimit F bond} (J : SmoothDirections univ f)
    (n s : ℕ) (x w : E) (v : Fin n → E) (t : ℝ) :
    HasDerivAt (fun u : ℝ => (J.D n (x + u • w) v).val s)
      ((J.D (n + 1) (x + t • w) (Fin.cons w v)).val s) t := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have hd := (J.derivative n (x + t • w) (mem_univ _) v w).clm_comp
    (projectiveCoordinate F bond s)
  simpa only [HasProjectiveLineDerivAt, HasProjectiveCurveDerivAt,
    projectiveCoordinate_apply, zero_add, zero_smul, add_zero, add_smul, add_assoc] using hd

section Family

variable {f : ℝ → E → ProjectiveLimit F bond}
  (J : ∀ a, SmoothDirections univ (f a))
  (hJ : ∀ n, Continuous (fun p : ℝ × (E × (Fin n → E)) =>
    (J p.1).D n p.2.1 p.2.2))

include hJ in
theorem continuous_smoothDirectionsFamily :
    Continuous (fun p : ℝ × E => f p.1 p.2) := by
  have hm : Continuous (fun p : ℝ × E =>
      (p.1, (p.2, (Fin.elim0 : Fin 0 → E)))) :=
    continuous_fst.prodMk (continuous_snd.prodMk continuous_const)
  have hc := (hJ 0).comp hm
  exact hc.congr (fun p => (J p.1).zero p.2 (mem_univ _))

def smoothDirectionsUnitIntegral :
    SmoothDirections univ
      (fun x => projectiveUnitIntegral (fun a => f a x)
        (by simpa only [Function.comp_def, id_eq] using
          ((continuous_smoothDirectionsFamily J hJ).comp
            (continuous_id.prodMk (continuous_const (y := x)))))) where
  open_domain := isOpen_univ
  D n x := projectiveUnitIntegralMultilinear (fun a => (J a).D n x)
    (by simpa only [Function.comp_def] using
      (hJ n).comp (continuous_fst.prodMk
        ((continuous_const (y := x)).prodMk continuous_snd)))
  zero x hx := by
    exact projectiveUnitIntegral_congr
      ((hJ 0).comp
        (continuous_id.prodMk (continuous_const (y := (x, (Fin.elim0 : Fin 0 → E))))))
      ((continuous_smoothDirectionsFamily J hJ).comp
        (continuous_id.prodMk (continuous_const (y := x))))
      (fun a _ => (J a).zero x (mem_univ _))
  continuous n := by
    have hc : Continuous (fun z : E × (Fin n → E) =>
        projectiveUnitIntegral (fun a => (J a).D n z.1 z.2)
          (by simpa only [Function.comp_def, id_eq] using
            ((hJ n).comp (continuous_id.prodMk (continuous_const (y := z)))))) :=
      continuous_projectiveUnitIntegral
        ((hJ n).comp (continuous_snd.prodMk continuous_fst))
    exact hc.continuousOn
  derivative n x hx v w := by
    apply (hasProjectiveLineDerivAt_iff_levels _ _ _ _).mpr
    intro s
    have hmap : Continuous (fun p : ℝ × ℝ => (p.1, (x + p.2 • w, v))) :=
      continuous_fst.prodMk
        ((continuous_const.add (continuous_snd.smul continuous_const)).prodMk continuous_const)
    have hmap' : Continuous (fun p : ℝ × ℝ =>
        (p.1, (x + p.2 • w, (Fin.cons w v : Fin (n + 1) → E)))) :=
      continuous_fst.prodMk
        ((continuous_const.add (continuous_snd.smul continuous_const)).prodMk continuous_const)
    have hd := unitParameterIntegral_hasDerivAt
      ((projectiveCoordinate F bond s).continuous.comp ((hJ n).comp hmap))
      ((projectiveCoordinate F bond s).continuous.comp ((hJ (n + 1)).comp hmap'))
      (fun a t => smoothDirections_hasDerivAt_line_level (J a) n s x w v t) 0
    simpa only [projectiveUnitIntegralMultilinear_apply,
      projectiveUnitIntegral_coordinate, projectiveCoordinate_apply,
      zero_smul, add_zero] using hd

theorem smoothDirectionsUnitIntegral_jet
    (n : ℕ) (x : E) (v : Fin n → E) :
    (smoothDirectionsUnitIntegral J hJ).D n x v =
      projectiveUnitIntegral (fun a => (J a).D n x v)
        (by simpa only [Function.comp_def, id_eq] using
          ((hJ n).comp (continuous_id.prodMk (continuous_const (y := (x, v)))))) := by
  change projectiveUnitIntegralMultilinear (fun a => (J a).D n x) _ v = _
  exact projectiveUnitIntegralMultilinear_apply (fun a => (J a).D n x) _ v

end Family

section LinearFamily

variable {f : E → ProjectiveLimit F bond} (J : SmoothDirections univ f)
  (L : ℝ → E →L[ℝ] E)
  (hL : Continuous (fun p : ℝ × E => L p.1 p.2))

include hL in
theorem continuous_linearFamily_precomp_jets (n : ℕ) :
    Continuous (fun p : ℝ × (E × (Fin n → E)) =>
      (solveSmoothDirectionsPrecomp J (L p.1)).D n p.2.1 p.2.2) := by
  have hbase : Continuous (fun p : ℝ × (E × (Fin n → E)) => L p.1 p.2.1) :=
    hL.comp (continuous_fst.prodMk continuous_snd.fst)
  have hdirs : Continuous (fun p : ℝ × (E × (Fin n → E)) =>
      fun i => L p.1 (p.2.2 i)) :=
    continuous_pi fun i => hL.comp
      (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd.snd))
  have hc : Continuous (fun z : E × (Fin n → E) => J.D n z.1 z.2) := by
    simpa only [univ_prod_univ, continuousOn_univ] using J.continuous n
  change Continuous (fun p : ℝ × (E × (Fin n → E)) =>
    J.D n (L p.1 p.2.1) (fun i => L p.1 (p.2.2 i)))
  simpa only [Function.comp_def] using hc.comp (hbase.prodMk hdirs)

def smoothDirectionsUnitIntegralLinearFamily :
    SmoothDirections univ
      (fun x => projectiveUnitIntegral (fun a => f (L a x))
        (by simpa only [Function.comp_def, id_eq] using
          ((continuous_smoothDirections_univ J).comp
            (hL.comp (continuous_id.prodMk (continuous_const (y := x))))))) :=
  smoothDirectionsUnitIntegral (fun a => solveSmoothDirectionsPrecomp J (L a))
    (continuous_linearFamily_precomp_jets J L hL)

theorem smoothDirectionsUnitIntegralLinearFamily_jet
    (n : ℕ) (x : E) (v : Fin n → E) :
    (smoothDirectionsUnitIntegralLinearFamily J L hL).D n x v =
      projectiveUnitIntegral (fun a => J.D n (L a x) (fun i => L a (v i)))
        (by simpa only [Function.comp_def, id_eq, solveSmoothDirectionsPrecomp,
            ContinuousMultilinearMap.compContinuousLinearMap_apply] using
          ((continuous_linearFamily_precomp_jets J L hL n).comp
            (continuous_id.prodMk (continuous_const (y := (x, v)))))) := by
  exact smoothDirectionsUnitIntegral_jet
    (fun a => solveSmoothDirectionsPrecomp J (L a))
    (continuous_linearFamily_precomp_jets J L hL) n x v

end LinearFamily

end ContinuousFlexibility.Analysis
