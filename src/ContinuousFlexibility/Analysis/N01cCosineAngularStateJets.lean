module

public import ContinuousFlexibility.Analysis.N01cCosineSignedSpeed
public import ContinuousFlexibility.Analysis.N01cMixedPowerAlgebra
public import ContinuousFlexibility.Analysis.N01cStateAngleSmoothDirections

/-!
# Actual angular state towers of a signed cosine speed

Only the two genuine physical mixed-jet towers are inputs. Their exact
signed cosine identity determines the state tower at every external
time. At a sine zero the actual angular family is identically zero.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

def MixedJetRegularity.angularStateJets
    {U : Set X} {I : Set ℝ} {f : X → PolarPoint → ℝ}
    (R : MixedJetRegularity U (I ×ˢ univ) f)
    (b : ℕ) (r : ℝ) (hr : r ∈ I) (θ : ℝ) :
    SmoothDirections U (fun x => iteratedDeriv b (fun η => f x (r, η)) θ) :=
  (R.parameter 0 b (r, θ) ⟨hr, mem_univ _⟩).congr
    (fun _ _ => by simp only [mixedDerivative, iteratedDeriv_zero])

theorem MixedJetRegularity.angularStateJets_D_apply
    {U : Set X} {I : Set ℝ} {f : X → PolarPoint → ℝ}
    (R : MixedJetRegularity U (I ×ˢ univ) f)
    (b k : ℕ) (r : ℝ) (hr : r ∈ I) (θ : ℝ) (x : X) (v : Fin k → X) :
    (R.angularStateJets b r hr θ).D k x v =
      (R.parameter 0 b (r, θ) ⟨hr, mem_univ _⟩).D k x v := rfl

theorem MixedJetRegularity.contDiff_angularSlice
    {U : Set X} {I : Set ℝ} {f : X → PolarPoint → ℝ}
    (R : MixedJetRegularity U (I ×ˢ univ) f)
    {x : X} (hx : x ∈ U) {r : ℝ} (hr : r ∈ I) :
    ContDiff ℝ ∞ (fun θ : ℝ => f x (r, θ)) :=
  contDiffOn_univ.mp ((R.spatial x hx).comp
    (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun _ _ => ⟨hr, mem_univ _⟩))

/-- Linear postcomposition keeps a literal linear-combination formula
for every actual multilinear jet. -/
def smoothDirections_scalarLinearCombination
    {U : Set X} {f g : X → ℝ} (a b : ℝ)
    (J : SmoothDirections U f) (K : SmoothDirections U g) :
    SmoothDirections U (fun x => a * f x + b * g x) :=
  (smoothDirectionsAdd
    (smoothDirections_postcompCLM J (a • ContinuousLinearMap.id ℝ ℝ))
    (smoothDirections_postcompCLM K (b • ContinuousLinearMap.id ℝ ℝ))).congr
      (fun _ _ => by
        simp only [Function.comp_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.id_apply, smul_eq_mul])

theorem smoothDirections_scalarLinearCombination_D_apply
    {U : Set X} {f g : X → ℝ} (a b : ℝ)
    (J : SmoothDirections U f) (K : SmoothDirections U g)
    (n : ℕ) (x : X) (v : Fin n → X) :
    (smoothDirections_scalarLinearCombination a b J K).D n x v =
      a * J.D n x v + b * K.D n x v := by
  change (smoothDirections_postcompCLM J (a • ContinuousLinearMap.id ℝ ℝ)).D n x v +
    (smoothDirections_postcompCLM K (b • ContinuousLinearMap.id ℝ ℝ)).D n x v = _
  rw [smoothDirections_postcompCLM_D_apply, smoothDirections_postcompCLM_D_apply]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]

private theorem iteratedDeriv_scalarLinearCombination
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (a b : ℝ) (n : ℕ) (θ : ℝ) :
    iteratedDeriv n (fun η => a * f η + b * g η) θ =
      a * iteratedDeriv n f θ + b * iteratedDeriv n g θ := by
  have haf : ContDiff ℝ ∞ (fun η => a * f η) := contDiff_const.mul hf
  have hbg : ContDiff ℝ ∞ (fun η => b * g η) := contDiff_const.mul hg
  rw [iteratedDeriv_fun_add (haf.contDiffAt.of_le (by simp))
    (hbg.contDiffAt.of_le (by simp)),
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]

section SignedFamily

variable {U : Set X} {l h : ℝ} (hU : IsOpen U) (hlh : l < h)
  (F A : X → PolarPoint → ℝ)
  (RF : MixedJetRegularity U (Ioo l h ×ˢ univ) F)
  (RA : MixedJetRegularity U (Ioo l h ×ˢ univ) A)
  (G : X × PolarPoint → ℝ)
  (heq : ∀ x ∈ U, ∀ t θ : ℝ,
    G (x, (t, θ)) =
      ((h - l) / 2 * |Real.sin t|) * F x (rootCosinePath l h t, θ) +
      ((h - l) / 2 * (|Real.sin t| - Real.sin t)) *
        A x (rootCosinePath l h t, θ))

include heq in
theorem signedCosine_angular_zero_of_sin_zero
    (b : ℕ) {t : ℝ} (ht : Real.sin t = 0) (θ : ℝ)
    {x : X} (hx : x ∈ U) :
    iteratedDeriv b (fun η => G (x, (t, η))) θ = 0 := by
  have hz : (fun η => G (x, (t, η))) = fun _ => (0 : ℝ) := by
    funext η
    rw [heq x hx t η]
    simp only [ht, abs_zero, mul_zero, zero_mul, sub_zero, add_zero]
  rw [hz]
  simp

include RF RA heq in
theorem signedCosine_angular_value
    (b : ℕ) {t : ℝ} (hr : rootCosinePath l h t ∈ Ioo l h) (θ : ℝ)
    {x : X} (hx : x ∈ U) :
    iteratedDeriv b (fun η => G (x, (t, η))) θ =
      ((h - l) / 2 * |Real.sin t|) *
        iteratedDeriv b (fun η => F x (rootCosinePath l h t, η)) θ +
      ((h - l) / 2 * (|Real.sin t| - Real.sin t)) *
        iteratedDeriv b (fun η => A x (rootCosinePath l h t, η)) θ := by
  rw [show (fun η => G (x, (t, η))) =
    (fun η => ((h - l) / 2 * |Real.sin t|) * F x (rootCosinePath l h t, η) +
      ((h - l) / 2 * (|Real.sin t| - Real.sin t)) *
        A x (rootCosinePath l h t, η)) from funext (heq x hx t)]
  exact iteratedDeriv_scalarLinearCombination
    (RF.contDiff_angularSlice hx hr) (RA.contDiff_angularSlice hx hr) _ _ b θ

/-- The nonzero-sine branch uses the actual physical mixed-jet towers. -/
def signedCosineAngularStateJetsInterior
    (b : ℕ) (q : PolarPoint) (hr : rootCosinePath l h q.1 ∈ Ioo l h) :
    SmoothDirections U (fun x => iteratedDeriv b (fun θ => G (x, (q.1, θ))) q.2) :=
  (smoothDirections_scalarLinearCombination
    ((h - l) / 2 * |Real.sin q.1|)
    ((h - l) / 2 * (|Real.sin q.1| - Real.sin q.1))
    (RF.angularStateJets b _ hr q.2) (RA.angularStateJets b _ hr q.2)).congr
      (fun x hx => (signedCosine_angular_value F A RF RA G heq b hr q.2 hx).symm)

theorem signedCosineAngularStateJetsInterior_D_apply
    (b k : ℕ) (q : PolarPoint) (hr : rootCosinePath l h q.1 ∈ Ioo l h)
    (x : X) (v : Fin k → X) :
    (signedCosineAngularStateJetsInterior F A RF RA G heq b q hr).D k x v =
      ((h - l) / 2 * |Real.sin q.1|) *
        (RF.angularStateJets b _ hr q.2).D k x v +
      ((h - l) / 2 * (|Real.sin q.1| - Real.sin q.1)) *
        (RA.angularStateJets b _ hr q.2).D k x v :=
  smoothDirections_scalarLinearCombination_D_apply _ _ _ _ k x v

/-- A genuine state tower exists at every angle and every real time,
including the zero-sine boundary times. -/
def signedCosineAngularStateJets (b : ℕ) (q : PolarPoint) :
    SmoothDirections U (fun x => iteratedDeriv b (fun θ => G (x, (q.1, θ))) q.2) := by
  classical
  by_cases ht : Real.sin q.1 = 0
  · exact (smoothDirections_constant hU (0 : ℝ)).congr
      (fun x hx => (signedCosine_angular_zero_of_sin_zero F A G heq b ht q.2 hx).symm)
  · exact signedCosineAngularStateJetsInterior F A RF RA G heq b q
      (rootCosinePath_mem_Ioo_of_sin_ne_zero hlh ht)

include hU heq in
/-- Every supplied genuine angular state tower has the same interior
linear-combination jet, independently of how its data were constructed. -/
theorem signedCosineAngularJet_D_apply
    (b k : ℕ) (q : PolarPoint) (hr : rootCosinePath l h q.1 ∈ Ioo l h)
    (J : SmoothDirections U (fun x => iteratedDeriv b (fun θ => G (x, (q.1, θ))) q.2))
    {x : X} (hx : x ∈ U) (v : Fin k → X) :
    J.D k x v =
      ((h - l) / 2 * |Real.sin q.1|) *
        (RF.angularStateJets b _ hr q.2).D k x v +
      ((h - l) / 2 * (|Real.sin q.1| - Real.sin q.1)) *
        (RA.angularStateJets b _ hr q.2).D k x v := by
  let K := signedCosineAngularStateJetsInterior F A RF RA G heq b q hr
  have he := congrArg (fun L : X [×k]→L[ℝ] ℝ => L v)
    (HasProjectiveJetsOn.unique hU J.hasProjectiveJetsOn K.hasProjectiveJetsOn k x hx)
  exact he.trans (signedCosineAngularStateJetsInterior_D_apply F A RF RA G heq b k q hr x v)

include heq in
theorem signedCosineAngularJet_D_zero
    (b k : ℕ) (q : PolarPoint) (ht : Real.sin q.1 = 0)
    (J : SmoothDirections U (fun x => iteratedDeriv b (fun θ => G (x, (q.1, θ))) q.2))
    {x : X} (hx : x ∈ U) (v : Fin k → X) : J.D k x v = 0 := by
  let J0 := J.congr (fun y hy =>
    signedCosine_angular_zero_of_sin_zero F A G heq b ht q.2 hy)
  by_cases hk : k = 0
  · subst k
    exact smoothDirections_D_zero_apply J0 hx v
  · exact smoothDirections_D_constant J0 (Nat.pos_of_ne_zero hk) hx v

end SignedFamily

end ContinuousFlexibility.Analysis
