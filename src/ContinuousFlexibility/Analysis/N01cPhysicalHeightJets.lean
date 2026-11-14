module

public import ContinuousFlexibility.Analysis.N01cHeightParameterJets
public import ContinuousFlexibility.Analysis.MaterialOrdinaryJets

/-!
# Actual physical height jets from material jets

The change of radial coordinate and Leibniz's formula express each physical
mixed derivative as a finite linear combination of the material jets.  The
coefficients depend only on the fixed material geometry and the evaluation
point.  Consequently every physical jet of a decoded height is a genuine
continuous-linear functional, with no regularity or continuity premise
added to the physical-space realization.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem smooth_materialRadius_comp {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo D.a D.b)) :
    ContDiff ℝ ∞ (fun x => f (T.radius x)) := by
  obtain ⟨_, _, _, _, _, _, hradius, hinside, _⟩ := hT
  exact hf.comp_contDiff hradius fun x => (hinside x).1

private theorem smooth_angularJet_slice {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (annularOpen D)) (b : ℕ) (θ : ℝ) :
    ContDiffOn ℝ ∞ (fun r => iteratedDeriv b (fun t => f (r, t)) θ)
      (Ioo D.a D.b) := by
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hs : ContDiff ℝ ∞ (fun r : ℝ => (r, θ)) :=
    contDiff_id.prodMk contDiff_const
  have hm : MapsTo (fun r : ℝ => (r, θ)) (Ioo D.a D.b) (annularOpen D) :=
    fun _ hr => ⟨hr, mem_univ _⟩
  simpa only [Function.comp_def, mixedDerivative, iteratedDeriv_zero] using
    (contDiffOn_mixedDerivative hU hf 0 b).comp hs.contDiffOn hm

/-- The exact Leibniz expansion restoring the physical height from its
weighted material pullback. -/
theorem materialDerivative_angular_slice_eq_materialJets
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (a b : ℕ) (r θ : ℝ) (hr : r ∈ Ioo D.a D.b) :
    materialDerivativeIterate T a
        (fun s => iteratedDeriv b (fun t => f (s, t)) θ) r =
      ∑ i : Fin (a + 1), (a.choose i.val : ℝ) *
        iteratedDeriv i.val (fun x => T.H (T.radius x) ^ γ) (T.rho r) *
        mixedDerivative (a - i.val) b (materialPullback T γ f) (T.rho r, θ) := by
  have hdata := hT
  obtain ⟨hcont, hpos, _, _, _, _, _, hinside, hinv, _⟩ := hdata
  let F : ℝ → ℝ := fun x => T.H (T.radius x) ^ γ
  let g : ℝ → ℝ := fun r => iteratedDeriv b (fun t => f (r, t)) θ
  let G : ℝ → ℝ :=
    fun x => iteratedDeriv b (fun t => materialPullback T γ f (x, t)) θ
  have hp (x : ℝ) : 0 < T.H (T.radius x) := (hpos _ (hinside x).1).2.1
  have hH : ContDiff ℝ ∞ (fun x => T.H (T.radius x)) :=
    smooth_materialRadius_comp hT (hcont T.H (by simp))
  have hF : ContDiff ℝ ∞ F := hH.rpow_const_of_ne (fun x => (hp x).ne')
  have hg : ContDiffOn ℝ ∞ g (Ioo D.a D.b) := smooth_angularJet_slice hf b θ
  have hGform : G = (fun x => T.H (T.radius x) ^ (-γ) * g (T.radius x)) := by
    funext x
    exact iteratedDeriv_const_mul_field (T.H (T.radius x) ^ (-γ))
      (fun t => f (T.radius x, t))
  have hG : ContDiff ℝ ∞ G := by
    rw [hGform]
    exact (hH.rpow_const_of_ne (fun x => (hp x).ne')).mul
      (smooth_materialRadius_comp hT hg)
  have hrestore : (fun x => F x * G x) = (fun x => g (T.radius x)) := by
    funext x
    change T.H (T.radius x) ^ γ * G x = _
    rw [hGform]
    change T.H (T.radius x) ^ γ *
      (T.H (T.radius x) ^ (-γ) * g (T.radius x)) = _
    rw [← mul_assoc, ← Real.rpow_add (hp x), add_neg_cancel, Real.rpow_zero, one_mul]
  let term (i : ℕ) : ℝ := (a.choose i : ℝ) * iteratedDeriv i F (T.rho r) *
    iteratedDeriv (a - i) G (T.rho r)
  have hleibniz : iteratedDeriv a (fun x => F x * G x) (T.rho r) =
      ∑ i : Fin (a + 1), term i.val := by
    rw [Fin.sum_univ_eq_sum_range term]
    exact iteratedDeriv_mul (hF.contDiffAt.of_le (by simp))
      (hG.contDiffAt.of_le (by simp))
  rw [hrestore, iteratedDeriv_comp_materialRadius hT hg, hinv r hr] at hleibniz
  exact hleibniz

/-- Physical radial derivatives are finite linear combinations of the
actual material mixed derivatives, at the matching material point. -/
theorem exists_physicalJet_materialExpansion
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    (γ : ℝ) (a b : ℕ) (p : PolarPoint) (hp : p ∈ annularOpen D) :
    ∃ c : Fin (a + 1) → ℝ, ∀ f : PolarPoint → ℝ,
      ContDiffOn ℝ ∞ f (annularOpen D) →
      mixedDerivative a b f p =
        ∑ j : Fin (a + 1), c j *
          ∑ i : Fin (j.val + 1), (j.val.choose i.val : ℝ) *
            iteratedDeriv i.val (fun x => T.H (T.radius x) ^ γ) (T.rho p.1) *
            mixedDerivative (j.val - i.val) b (materialPullback T γ f)
              (T.rho p.1, p.2) := by
  have hdata := hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hexpansion, _⟩ := hdata
  obtain ⟨c, _, _, hformula⟩ := hexpansion a
  refine ⟨fun j => c j p.1, fun f hf => ?_⟩
  change iteratedDeriv a (fun r => iteratedDeriv b (fun t => f (r, t)) p.2) p.1 = _
  rw [hformula _ (smooth_angularJet_slice hf b p.2) p.1 hp.1]
  apply Finset.sum_congr rfl
  intro j _
  rw [materialDerivative_angular_slice_eq_materialJets hT hf j.val b p.1 p.2 hp.1]

/-- Continuity of physical jet evaluation follows from its finite material
expansion. The witness is built entirely out of the material-jet CLMs. -/
theorem exists_heightPhysicalJetCLM
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : SobolevModelData}
    (hT : IsMaterialData D T) (hM : IsSobolevModel D T γ M)
    (a b : ℕ) (p : PolarPoint) (hp : p ∈ annularOpen D) :
    ∃ L : M.Space →L[ℝ] ℝ, ∀ u,
      L u = mixedDerivative a b (M.decode u) p := by
  obtain ⟨c, hc⟩ := exists_physicalJet_materialExpansion hT γ a b p hp
  let L : M.Space →L[ℝ] ℝ :=
    ∑ j : Fin (a + 1), c j •
      ∑ i : Fin (j.val + 1),
        ((j.val.choose i.val : ℝ) *
          iteratedDeriv i.val (fun x => T.H (T.radius x) ^ γ) (T.rho p.1)) •
          heightMaterialJetCLM hT hM (j.val - i.val) b (T.rho p.1, p.2)
  refine ⟨L, fun u => ?_⟩
  rw [hc (M.decode u) (hM.2.2.2.1 u).1]
  simp only [L, sum_apply, smul_apply, smul_eq_mul, heightMaterialJetCLM_apply]

/-- The actual physical mixed derivative, as a continuous-linear functional. -/
def heightPhysicalJetCLM
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : SobolevModelData}
    (hT : IsMaterialData D T) (hM : IsSobolevModel D T γ M)
    (a b : ℕ) (p : PolarPoint) (hp : p ∈ annularOpen D) : M.Space →L[ℝ] ℝ :=
  (exists_heightPhysicalJetCLM hT hM a b p hp).choose

theorem heightPhysicalJetCLM_apply
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : SobolevModelData}
    (hT : IsMaterialData D T) (hM : IsSobolevModel D T γ M)
    (a b : ℕ) (p : PolarPoint) (hp : p ∈ annularOpen D) (u : M.Space) :
    heightPhysicalJetCLM hT hM a b p hp u = mixedDerivative a b (M.decode u) p :=
  (exists_heightPhysicalJetCLM hT hM a b p hp).choose_spec u

/-- The physical parameter tower is the tower of the genuine linear
functional, transported by its proved evaluation identity. -/
def heightPhysicalJetSmoothDirections
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : SobolevModelData}
    (hT : IsMaterialData D T) (hM : IsSobolevModel D T γ M)
    (a b : ℕ) (p : PolarPoint) (hp : p ∈ annularOpen D) :
    SmoothDirections univ (fun u : M.Space => mixedDerivative a b (M.decode u) p) :=
  (smoothDirectionsLinear (heightPhysicalJetCLM hT hM a b p hp)).congr
    (fun u _ => heightPhysicalJetCLM_apply hT hM a b p hp u)

end ContinuousFlexibility.Statements
