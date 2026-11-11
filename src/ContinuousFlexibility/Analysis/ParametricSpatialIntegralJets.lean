import ContinuousFlexibility.Analysis.OneHighCircleFlowIntegral
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Actual spatial jets of parameterized functions and compact integrals

The space variable is differentiated while time remains a parameter.
Joint smoothness gives joint continuity of every actual spatial jet.
When only time continuity of those jets is available, differentiation
still commutes with the compact integral at every finite order.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

variable {Q E : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def parametricSpatialJet (f : Q × ℝ → E) (n : ℕ) (z : Q × ℝ) : Q [×n]→L[ℝ] E :=
  iteratedFDeriv ℝ n (fun q : Q => f (q, z.2)) z.1

/-- All actual spatial jets vary smoothly with the parameters. -/
theorem contDiff_parametricSpatialJet {f : Q × ℝ → E}
    (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (parametricSpatialJet f n) := by
  induction n with
  | zero =>
    have he : parametricSpatialJet f 0 =
        (continuousMultilinearCurryFin0 ℝ Q E).symm ∘ f := by
      funext z
      simp only [parametricSpatialJet, iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    rw [he]
    exact (continuousMultilinearCurryFin0 ℝ Q E).symm.contDiff.comp hf
  | succ n ih =>
    have haux : ContDiff ℝ ∞
        (fun z : (Q × ℝ) × Q => parametricSpatialJet f n (z.2, z.1.2)) :=
      ih.comp (contDiff_snd.prodMk contDiff_fst.snd)
    have hd : ContDiff ℝ ∞
        (fun z : Q × ℝ =>
          fderiv ℝ (fun q : Q => parametricSpatialJet f n (q, z.2)) z.1) :=
      haux.fderiv contDiff_fst (by simp)
    let L := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => Q) E).symm
    have he : parametricSpatialJet f (n + 1) =
        L ∘ (fun z : Q × ℝ =>
          fderiv ℝ (fun q : Q => parametricSpatialJet f n (q, z.2)) z.1) := by
      funext z
      simpa only [parametricSpatialJet, Function.comp_apply, L] using
        congr_fun (iteratedFDeriv_succ_eq_comp_left
          (𝕜 := ℝ) (f := fun q : Q => f (q, z.2)) (n := n)) z.1
    rw [he]
    exact L.contDiff.comp hd

theorem hasFDerivAt_parametricSpatialJet {f : Q × ℝ → E}
    (hf : ∀ t : ℝ, ContDiff ℝ ∞ (fun q : Q => f (q, t)))
    (n : ℕ) (q : Q) (t : ℝ) :
    HasFDerivAt (fun y : Q => parametricSpatialJet f n (y, t))
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => Q) E)
        (parametricSpatialJet f (n + 1) (q, t))) q := by
  have hn : (n : ℕ∞ω) < ∞ :=
    WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)
  have hd := ((hf t).differentiable_iteratedFDeriv hn q).hasFDerivAt
  simpa only [parametricSpatialJet, fderiv_iteratedFDeriv, Function.comp_apply] using hd

variable [FiniteDimensional ℝ Q] [CompleteSpace E]

/-- Every actual spatial derivative commutes with a compact interval
integral. Only joint continuity in time of the true spatial jets is
required, so a continuous time clamp is allowed. -/
theorem parametricIntervalIntegral_contDiff_and_iteratedFDeriv
    (f : Q × ℝ → E)
    (hf : ∀ t : ℝ, ContDiff ℝ ∞ (fun q : Q => f (q, t)))
    (hj : ∀ n : ℕ, Continuous (parametricSpatialJet f n))
    (a b : ℝ) :
    ContDiff ℝ ∞ (fun q : Q => ∫ t in a..b, f (q, t)) ∧
      ∀ n : ℕ, ∀ q : Q,
        iteratedFDeriv ℝ n (fun y : Q => ∫ t in a..b, f (y, t)) q =
          ∫ t in a..b, parametricSpatialJet f n (q, t) := by
  let J (n : ℕ) (q : Q) : Q [×n]→L[ℝ] E :=
    ∫ t in a..b, parametricSpatialJet f n (q, t)
  have hd (n : ℕ) (q : Q) :
      HasFDerivAt (J n)
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => Q) E)
          (J (n + 1) q)) q := by
    let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => Q) E
    have hc' : Continuous (fun z : Q × ℝ => L (parametricSpatialJet f (n + 1) z)) :=
      L.continuous.comp (hj (n + 1))
    have hh := hasFDerivAt_parametric_intervalIntegral
      (hj n) hc' (hasFDerivAt_parametricSpatialJet hf n) a b q
    have hI : (∫ t in a..b, L (parametricSpatialJet f (n + 1) (q, t))) =
        L (∫ t in a..b, parametricSpatialJet f (n + 1) (q, t)) := by
      have hc : Continuous (fun t : ℝ => parametricSpatialJet f (n + 1) (q, t)) :=
        (hj (n + 1)).comp (continuous_const.prodMk continuous_id)
      exact L.toContinuousLinearEquiv.toContinuousLinearMap.intervalIntegral_comp_comm
        (𝕜 := ℝ) (hc.intervalIntegrable a b)
    rw [hI] at hh
    exact hh
  have hjet : ∀ n : ℕ, ∀ q : Q,
      iteratedFDeriv ℝ n (fun y : Q => ∫ t in a..b, f (y, t)) q = J n q := by
    intro n
    induction n with
    | zero =>
      intro q
      let L := (continuousMultilinearCurryFin0 ℝ Q E).symm
      have hI := L.toLinearIsometry.intervalIntegral_comp_comm
        (a := a) (b := b) (μ := volume) (fun t => f (q, t))
      simpa only [J, parametricSpatialJet, iteratedFDeriv_zero_eq_comp,
        Function.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry, L] using hI.symm
    | succ n ih =>
      have he : iteratedFDeriv ℝ n (fun y : Q => ∫ t in a..b, f (y, t)) = J n :=
        funext ih
      intro q
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, he, (hd n q).fderiv]
      exact (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (n + 1) => Q) E).symm_apply_apply _
  refine ⟨?_, hjet⟩
  apply contDiff_of_differentiable_iteratedFDeriv
  intro n _
  have he : iteratedFDeriv ℝ n (fun y : Q => ∫ t in a..b, f (y, t)) = J n :=
    funext (hjet n)
  rw [he]
  exact fun q => (hd n q).differentiableAt

end ContinuousFlexibility.Analysis
