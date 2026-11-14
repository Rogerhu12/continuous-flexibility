module

public import ContinuousFlexibility.Analysis.OneHighCylinderSobolevJetsBasic
public import Mathlib.Analysis.Calculus.FDeriv.Partial
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# Smoothness and actual coordinate derivatives of cylinder jets

The continuous coordinate derivative tower implies ordinary joint smoothness
of its periodic lift. This supplies smooth-composition arguments without a
new smoothness assumption or an extra family of formal derivatives.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter
open scoped ContDiff Topology

variable {P : ℝ} {E F : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The ordinary periodic lift of one of the actual cylinder jets. -/
def CylinderSmoothJet.lift (u : CylinderSmoothJet P E) (i j : ℕ) (p : ℝ × ℝ) : E :=
  u.jet i j (p.1, (p.2 : AddCircle P))

theorem CylinderSmoothJet.continuous_lift (u : CylinderSmoothJet P E) (i j : ℕ) :
    Continuous (u.lift i j) :=
  (u.continuous i j).comp
    (continuous_fst.prodMk ((AddCircle.continuous_mk' P).comp continuous_snd))

/-- Continuous actual partial derivatives give the full derivative. -/
theorem CylinderSmoothJet.hasFDerivAt_lift (u : CylinderSmoothJet P E)
    (i j : ℕ) (p : ℝ × ℝ) :
    HasFDerivAt (u.lift i j)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (u.lift (i + 1) j p) +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (u.lift i (j + 1) p)) p := by
  let fr : ℝ → ℝ → ℝ →L[ℝ] E := fun r θ =>
    ContinuousLinearMap.toSpanSingleton ℝ (u.jet (i + 1) j (r, (θ : AddCircle P)))
  let ft : ℝ → ℝ → ℝ →L[ℝ] E := fun r θ =>
    ContinuousLinearMap.toSpanSingleton ℝ (u.jet i (j + 1) (r, (θ : AddCircle P)))
  have hcr : Continuous (fun q : ℝ × ℝ => fr q.1 q.2) :=
    (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := E)).continuous.comp
      (u.continuous_lift (i + 1) j)
  have hct : Continuous (fun q : ℝ × ℝ => ft q.1 q.2) :=
    (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := E)).continuous.comp
      (u.continuous_lift i (j + 1))
  have h := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := p)
    (f := fun r θ => u.jet i j (r, (θ : AddCircle P))) (f₁ := fr) (f₂ := ft)
    (Eventually.of_forall fun q => (u.radial i j q.1 (q.2 : AddCircle P)).hasFDerivAt)
    (Eventually.of_forall fun q => (u.angular i j q.1 q.2).hasFDerivAt)
    hcr.continuousAt hct.continuousAt
  have he : (fr p.1 p.2).coprod (ft p.1 p.2) =
      (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (u.lift (i + 1) j p) +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (u.lift i (j + 1) p) := by
    apply ContinuousLinearMap.ext
    intro z
    simp [fr, ft, CylinderSmoothJet.lift, ContinuousLinearMap.coprod_apply]
  have h' : HasFDerivAt (u.lift i j) ((fr p.1 p.2).coprod (ft p.1 p.2)) p :=
    h.hasFDerivAt
  rw [he] at h'
  exact h'

private theorem cylinderSmoothJet_contDiff_lift_nat (u : CylinderSmoothJet P E)
    (n : ℕ) : ∀ i j, ContDiff ℝ n (u.lift i j) := by
  induction n with
  | zero =>
      intro i j
      exact contDiff_zero.mpr (u.continuous_lift i j)
  | succ n ih =>
      intro i j
      apply contDiff_succ_iff_hasFDerivAt.mpr
      refine ⟨fun p =>
        (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (u.lift (i + 1) j p) +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (u.lift i (j + 1) p), ?_,
        u.hasFDerivAt_lift i j⟩
      exact (contDiff_const.smulRight (ih (i + 1) j)).add
        (contDiff_const.smulRight (ih i (j + 1)))

/-- Every lifted jet is genuinely jointly smooth. -/
theorem CylinderSmoothJet.contDiff_lift (u : CylinderSmoothJet P E) (i j : ℕ) :
    ContDiff ℝ ∞ (u.lift i j) :=
  contDiff_infty.mpr fun n => cylinderSmoothJet_contDiff_lift_nat u n i j

theorem CylinderSmoothJet.iteratedDeriv_radial (u : CylinderSmoothJet P E)
    (i j n : ℕ) (θ : AddCircle P) :
    iteratedDeriv n (fun r : ℝ => u.jet i j (r, θ)) =
      fun r => u.jet (i + n) j (r, θ) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero, Nat.add_zero]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext r
      simpa only [Nat.add_assoc] using (u.radial (i + n) j r θ).deriv

theorem CylinderSmoothJet.iteratedDeriv_angular (u : CylinderSmoothJet P E)
    (i j n : ℕ) (r : ℝ) :
    iteratedDeriv n (fun θ : ℝ => u.jet i j (r, (θ : AddCircle P))) =
      fun θ : ℝ => u.jet i (j + n) (r, (θ : AddCircle P)) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero, Nat.add_zero]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext θ
      simpa only [Nat.add_assoc] using (u.angular i (j + n) r θ).deriv

/-- Continuous linear maps act on the same actual jet tower. -/
def CylinderSmoothJet.mapCLM (u : CylinderSmoothJet P E) (L : E →L[ℝ] F) :
    CylinderSmoothJet P F where
  jet i j p := L (u.jet i j p)
  continuous i j := L.continuous.comp (u.continuous i j)
  radial i j r θ := by
    simpa only [Function.comp_def] using
      L.hasFDerivAt.comp_hasDerivAt r (u.radial i j r θ)
  angular i j r θ := by
    simpa only [Function.comp_def] using
      L.hasFDerivAt.comp_hasDerivAt θ (u.angular i j r θ)

@[simp] theorem CylinderSmoothJet.mapCLM_jet (u : CylinderSmoothJet P E)
    (L : E →L[ℝ] F) (i j : ℕ) (p : ℝ × AddCircle P) :
    (u.mapCLM L).jet i j p = L (u.jet i j p) := rfl

def CylinderSmoothJet.complexify (u : CylinderSmoothJet P ℝ) : CylinderSmoothJet P :=
  u.mapCLM Complex.ofRealCLM

@[simp] theorem CylinderSmoothJet.complexify_jet (u : CylinderSmoothJet P ℝ)
    (i j : ℕ) (p : ℝ × AddCircle P) :
    u.complexify.jet i j p = (u.jet i j p : ℂ) := rfl

def CylinderSmoothJet.component {m : ℕ} (u : CylinderSmoothJet P (Fin m → ℝ))
    (k : Fin m) : CylinderSmoothJet P ℝ :=
  u.mapCLM (ContinuousLinearMap.proj k)

@[simp] theorem CylinderSmoothJet.component_jet {m : ℕ}
    (u : CylinderSmoothJet P (Fin m → ℝ)) (k : Fin m) (i j : ℕ)
    (p : ℝ × AddCircle P) : (u.component k).jet i j p = u.jet i j p k := rfl

end ContinuousFlexibility.Analysis
