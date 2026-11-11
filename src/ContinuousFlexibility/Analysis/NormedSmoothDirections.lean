import ContinuousFlexibility.Analysis.TameElementaryCalculus
import ContinuousFlexibility.Analysis.ProjectiveCurveIteratedChain
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Tactic.FunProp

/-!
# Normed smooth maps as genuine directional towers

On an open set, the ordinary Taylor derivatives give the exact
topological directional tower. Evaluating such a jet on varying curves
uses its actual Fréchet derivative and the multilinear product rule.
No norm is introduced on any later parameter space.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def normedMultilinearEvalLinear {n : ℕ} (v : Fin n → F) :
    (F [×n]→L[ℝ] G) →L[ℝ] G where
  toFun A := A v
  map_add' A B := rfl
  map_smul' a A := rfl
  cont := by fun_prop

@[simp] theorem normedMultilinearEvalLinear_apply {n : ℕ} (v : Fin n → F)
    (A : F [×n]→L[ℝ] G) : normedMultilinearEvalLinear v A = A v := rfl

def contDiffOnJetFamily (g : F → G) (V : Set F) : ProjectiveJetFamily F G :=
  fun n y => ftaylorSeriesWithin ℝ g V y n

theorem contDiffOnJetFamily_continuousOn {g : F → G} {V : Set F}
    (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V) (n : ℕ) :
    ContinuousOn (fun p : F × (Fin n → F) => contDiffOnJetFamily g V n p.1 p.2)
      (V ×ˢ univ) := by
  have hs := hg.ftaylorSeriesWithin hV.uniqueDiffOn
  have hc : ContinuousOn (fun p : F × (Fin n → F) =>
      ftaylorSeriesWithin ℝ g V p.1 n) (V ×ˢ univ) :=
    (hs.cont n (by simp)).comp continuous_fst.continuousOn (fun p hp => hp.1)
  have heval : Continuous (fun p : (F [×n]→L[ℝ] G) × (Fin n → F) => p.1 p.2) :=
    continuous_eval
  exact heval.comp_continuousOn (hc.prodMk continuous_snd.continuousOn)

theorem hasDerivAt_contDiffOnJet_fixed {g : F → G} {V : Set F}
    (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V)
    {c : ℝ → F} {dc : F} {t : ℝ} (hc : HasDerivAt c dc t) (ht : c t ∈ V)
    (n : ℕ) (v : Fin n → F) :
    HasDerivAt (fun s => contDiffOnJetFamily g V n (c s) v)
      (contDiffOnJetFamily g V (n + 1) (c t) (Fin.cons dc v)) t := by
  have hs := hg.ftaylorSeriesWithin hV.uniqueDiffOn
  have hn : (n : ℕ∞ω) < ∞ := WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)
  have hd : HasFDerivAt (fun y => ftaylorSeriesWithin ℝ g V y n)
      (ftaylorSeriesWithin ℝ g V (c t) (n + 1)).curryLeft (c t) :=
    (hs.fderivWithin n hn (c t) ht).hasFDerivAt (hV.mem_nhds ht)
  have hcurve := hd.comp_hasDerivAt t hc
  have heval := (normedMultilinearEvalLinear (G := G) v).hasFDerivAt.comp_hasDerivAt t hcurve
  simpa only [contDiffOnJetFamily, Function.comp_def,
    normedMultilinearEvalLinear_apply, ContinuousMultilinearMap.curryLeft_apply] using heval

theorem hasProjectiveJetsOn_contDiffOn {g : F → G} {V : Set F}
    (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V) :
    HasProjectiveJetsOn g (contDiffOnJetFamily g V) V := by
  refine ⟨?_, contDiffOnJetFamily_continuousOn hV hg, ?_⟩
  · intro y hy
    change ftaylorSeriesWithin ℝ g V y 0 Fin.elim0 = g y
    rw [show (Fin.elim0 : Fin 0 → F) = 0 from Subsingleton.elim _ _]
    exact (hg.ftaylorSeriesWithin hV.uniqueDiffOn).zero_eq y hy
  · intro n y hy w v
    have hline : HasDerivAt (fun t : ℝ => y + t • w) w 0 := by
      simpa only [zero_add, one_smul, Pi.add_apply] using
        (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id' (0 : ℝ)).smul_const w)
    have hd := hasDerivAt_contDiffOnJet_fixed hV hg hline
      (by simpa only [zero_smul, add_zero] using hy) n v
    simpa only [HasProjectiveLineDerivAt, HasProjectiveCurveDerivAt,
      zero_add, zero_smul, add_zero] using hasDerivAt_iff_tendsto_slope_zero.mp hd

def smoothDirectionsOfContDiffOn {g : F → G} {V : Set F}
    (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V) : SmoothDirections V g :=
  smoothDirectionsOfJets hV (contDiffOnJetFamily g V) (hasProjectiveJetsOn_contDiffOn hV hg)

/-- The full derivative includes both the varying base and every varying
input of the actual ordinary Taylor jet. -/
theorem hasProjectiveCurveDerivAt_contDiffOnJet_eval
    {g : F → G} {V : Set F} (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V)
    {c : ℝ → F} {dc : F} {t : ℝ}
    (hc : HasProjectiveCurveDerivAt c dc t) (ht : c t ∈ V)
    (n : ℕ) (v : ℝ → Fin n → F) (dv : Fin n → F)
    (hv : ∀ i, HasProjectiveCurveDerivAt (fun s => v s i) (dv i) t) :
    HasProjectiveCurveDerivAt (fun s => contDiffOnJetFamily g V n (c s) (v s))
      (contDiffOnJetFamily g V (n + 1) (c t) (Fin.cons dc (v t)) +
        ∑ i : Fin n, contDiffOnJetFamily g V n (c t) (Function.update (v t) i (dv i))) t := by
  have hcd : HasDerivAt c dc t := hasDerivAt_iff_tendsto_slope_zero.mpr hc
  have hfixed : HasProjectiveCurveDerivAt
      (fun s => contDiffOnJetFamily g V n (c s) (v t))
      (contDiffOnJetFamily g V (n + 1) (c t) (Fin.cons dc (v t))) t :=
    hasDerivAt_iff_tendsto_slope_zero.mp
      (hasDerivAt_contDiffOnJet_fixed hV hg hcd ht n (v t))
  have hB (w : Fin n → F) : ContinuousAt
      (fun p : ℝ × (Fin n → F) => contDiffOnJetFamily g V n (c p.1) p.2) (t, w) := by
    have hj : ContinuousAt (fun p : F × (Fin n → F) => contDiffOnJetFamily g V n p.1 p.2)
        (c t, w) := (contDiffOnJetFamily_continuousOn hV hg n).continuousAt
      ((hV.prod isOpen_univ).mem_nhds (show (c t, w) ∈ V ×ˢ univ from ⟨ht, mem_univ w⟩))
    exact ContinuousAt.comp
      (f := fun p : ℝ × (Fin n → F) => (c p.1, p.2))
      (g := fun p : F × (Fin n → F) => contDiffOnJetFamily g V n p.1 p.2)
      (x := (t, w)) hj ((hcd.continuousAt.comp continuousAt_fst).prodMk continuousAt_snd)
  exact hasProjectiveCurveDerivAt_variableMultilinear
    (fun s => contDiffOnJetFamily g V n (c s)) v dv _ t hB hv hfixed

end ContinuousFlexibility.Analysis
