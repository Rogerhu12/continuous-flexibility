import ContinuousFlexibility.Analysis.N01cFlowAffineCompression

/-!
# Genuine smooth state dependence of the classical trajectory family

Finite-dimensional affine germs identify the recursively constructed
continuous multilinear variations with actual Fréchet derivatives.
A plane containing the new direction and all existing direction slots
then proves the true directional recurrence in the original state
topology. This constructs a genuine SmoothDirections tower; no norm on
the state space and no parameter derivative of the flow are assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function
open ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

def finiteDirectionsLinear {m : ℕ} (u : Fin m → E) : (Fin m → ℝ) →L[ℝ] E :=
  ∑ i, ((ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ).smulRight (u i))

theorem finiteDirectionsLinear_apply {m : ℕ} (u : Fin m → E) (q : Fin m → ℝ) :
    finiteDirectionsLinear u q = ∑ i, q i • u i := by
  simp only [finiteDirectionsLinear, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]

@[simp] theorem finiteDirectionsLinear_single {m : ℕ} (u : Fin m → E) (i : Fin m) :
    finiteDirectionsLinear u (Pi.single i 1) = u i := by
  classical
  rw [finiteDirectionsLinear_apply]
  simp

/-- Agreement at zero for every translated affine plane also gives
agreement at every point of any fixed affine plane. -/
theorem affineJet_at_point_of_at_zero
    {U : Set E} {f : E → ℝ} (A : ProjectiveJetFamily E ℝ)
    (hjet : ∀ m : ℕ, ∀ x ∈ U, ∀ L : (Fin m → ℝ) →L[ℝ] E,
      ∀ n : ℕ, ∀ v : Fin n → (Fin m → ℝ),
        iteratedFDeriv ℝ n (fun q => f (x + L q)) 0 v =
          A n x (fun i => L (v i)))
    (m : ℕ) (x : E) (L : (Fin m → ℝ) →L[ℝ] E)
    (q : Fin m → ℝ) (hq : x + L q ∈ U) (n : ℕ) (v : Fin n → (Fin m → ℝ)) :
    iteratedFDeriv ℝ n (fun y => f (x + L y)) q v =
      A n (x + L q) (fun i => L (v i)) := by
  have he : (fun y => f ((x + L q) + L y)) =
      fun y => (fun z => f (x + L z)) (q + y) := by
    funext y
    change f ((x + L q) + L y) = f (x + L (q + y))
    rw [map_add, add_assoc]
  have h := hjet m (x + L q) hq L n v
  rw [he] at h
  rw [iteratedFDeriv_comp_add_left (𝕜 := ℝ)
    (f := fun z : Fin m → ℝ => f (x + L z)) n q (0 : Fin m → ℝ), add_zero] at h
  exact h

/-- Jointly continuous multilinear candidates identified on every
finite affine germ satisfy the actual directional derivative recursion. -/
def smoothDirections_of_finiteAffine_germs
    {U : Set E} {f : E → ℝ} (hU : IsOpen U) (A : ProjectiveJetFamily E ℝ)
    (hzero : ∀ x ∈ U, A 0 x Fin.elim0 = f x)
    (hcontinuous : ∀ n : ℕ, ContinuousOn
      (fun p : E × (Fin n → E) => A n p.1 p.2) (U ×ˢ univ))
    (hsmooth : ∀ m : ℕ, ∀ x ∈ U, ∀ L : (Fin m → ℝ) →L[ℝ] E,
      ContDiffAt ℝ ∞ (fun q => f (x + L q)) 0)
    (hjet : ∀ m : ℕ, ∀ x ∈ U, ∀ L : (Fin m → ℝ) →L[ℝ] E,
      ∀ n : ℕ, ∀ v : Fin n → (Fin m → ℝ),
        iteratedFDeriv ℝ n (fun q => f (x + L q)) 0 v =
          A n x (fun i => L (v i))) : SmoothDirections U f where
  open_domain := hU
  D := A
  zero := hzero
  continuous := hcontinuous
  derivative := by
    intro n x hx v w
    let P := Fin (n + 1) → ℝ
    let L : P →L[ℝ] E := finiteDirectionsLinear (Fin.cons w v)
    let e : P := Pi.single 0 1
    let a : Fin n → P := fun i => Pi.single i.succ 1
    let F : P → ℝ := fun q => f (x + L q)
    have he : L e = w := by
      change finiteDirectionsLinear (Fin.cons w v) (Pi.single (0 : Fin (n + 1)) 1) = w
      exact finiteDirectionsLinear_single (Fin.cons w v) (0 : Fin (n + 1))
    have ha : (fun i => L (a i)) = v := by
      funext i
      change finiteDirectionsLinear (Fin.cons w v) (Pi.single i.succ 1) = v i
      exact finiteDirectionsLinear_single (Fin.cons w v) i.succ
    have hcons : (fun i => L ((Fin.cons e a : Fin (n + 1) → P) i)) =
        Fin.cons w v := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.cons_zero] using he
      · simpa only [Fin.cons_succ] using congrFun ha j
    have hline (s : ℝ) : x + L (s • e) = x + s • w := by rw [map_smul, he]
    have hF : ContDiffAt ℝ ∞ F 0 := hsmooth (n + 1) x hx L
    have hD : DifferentiableAt ℝ (iteratedFDeriv ℝ n F) ((0 : ℝ) • e) := by
      simpa only [zero_smul] using
        hF.differentiableAt_iteratedFDeriv
          (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)
    have hc : HasDerivAt (fun s : ℝ => s • e) e 0 := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const e
    have hd := (hD.continuousMultilinear_apply_const a).hasFDerivAt.comp_hasDerivAt 0 hc
    simp only [zero_smul] at hd
    rw [fderiv_continuousMultilinear_apply_const_apply
      (by simpa only [zero_smul] using hD)] at hd
    change HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ n F (s • e) a)
      (iteratedFDeriv ℝ (n + 1) F 0 (Fin.cons e a)) 0 at hd
    have hnext := hjet (n + 1) x hx L (n + 1) (Fin.cons e a)
    rw [hcons] at hnext
    rw [hnext] at hd
    have hpath : Continuous (fun s : ℝ => x + s • w) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), x + s • w ∈ U := by
      have hUx : U ∈ 𝓝 ((fun s : ℝ => x + s • w) 0) := by
        simpa only [zero_smul, add_zero] using hU.mem_nhds hx
      exact hpath.continuousAt.preimage_mem_nhds hUx
    have heq : (fun s : ℝ => iteratedFDeriv ℝ n F (s • e) a) =ᶠ[𝓝 (0 : ℝ)]
        (fun s => A n (x + s • w) v) := by
      filter_upwards [hnear] with s hs
      have hj := affineJet_at_point_of_at_zero A hjet (n + 1) x L (s • e)
        (by simpa only [hline] using hs) n a
      simpa only [ha, hline] using hj
    exact (hd.congr_of_eventuallyEq heq.symm).tendsto_slope_zero

/-- Genuine parameter smoothness of the actual global-time trajectories
on the original, possibly nonnormable, state space. All-order joint
physical smoothness is required only after finite affine restriction of
the speed. The flow's parameter derivatives are conclusions. -/
def topologicalCircleTrajectorySmoothDirections
    {U : Set E} {G : E × PolarPoint → ℝ} {Θ : E × ℝ → ℝ} {θ₀ : ℝ}
    (hU : IsOpen U) (J : ContinuousTimeSpeedTower U G)
    (hΘ : ContinuousOn Θ (U ×ˢ (univ : Set ℝ)))
    (hinit : ∀ x ∈ U, Θ (x, 0) = θ₀)
    (hflow : ∀ x ∈ U, ∀ t : ℝ,
      HasDerivAt (fun r => Θ (x, r)) (G (x, (t, Θ (x, t)))) t)
    (hspeed : ∀ m : ℕ, ∀ x ∈ U, ∀ L : (Fin m → ℝ) →L[ℝ] E,
      ContDiffOn ℝ ∞ (fun p : (Fin m → ℝ) × PolarPoint => G (x + L p.1, p.2))
        (((fun q => x + L q) ⁻¹' U) ×ˢ (univ : Set PolarPoint)))
    (t : ℝ) : SmoothDirections U (fun x => Θ (x, t)) := by
  let A : ProjectiveJetFamily E ℝ :=
    fun n x => (volterraStateVariation J hΘ n).value (x, t)
  have hcont (n : ℕ) : ContinuousOn
      (fun p : E × (Fin n → E) => A n p.1 p.2) (U ×ˢ univ) :=
    (volterraStateVariation J hΘ n).continuous.comp
      ((continuous_fst.prodMk continuous_const).prodMk continuous_snd).continuousOn
      (fun p hp => ⟨⟨hp.1, mem_univ t⟩, hp.2⟩)
  exact smoothDirections_of_finiteAffine_germs hU A
    (fun x _ => volterraStateVariation_zero_apply J hΘ (x, t)) hcont
    (fun m x hx L =>
      (flow_finiteAffine_germ_jets hU J hΘ hinit hflow x hx L (hspeed m x hx L)).1 t)
    (fun m x hx L n v =>
      (flow_finiteAffine_germ_jets hU J hΘ hinit hflow x hx L (hspeed m x hx L)).2 n t v)

theorem topologicalCircleTrajectorySmoothDirections_D_apply
    {U : Set E} {G : E × PolarPoint → ℝ} {Θ : E × ℝ → ℝ} {θ₀ : ℝ}
    (hU : IsOpen U) (J : ContinuousTimeSpeedTower U G)
    (hΘ : ContinuousOn Θ (U ×ˢ (univ : Set ℝ)))
    (hinit : ∀ x ∈ U, Θ (x, 0) = θ₀)
    (hflow : ∀ x ∈ U, ∀ t : ℝ,
      HasDerivAt (fun r => Θ (x, r)) (G (x, (t, Θ (x, t)))) t)
    (hspeed : ∀ m : ℕ, ∀ x ∈ U, ∀ L : (Fin m → ℝ) →L[ℝ] E,
      ContDiffOn ℝ ∞ (fun p : (Fin m → ℝ) × PolarPoint => G (x + L p.1, p.2))
        (((fun q => x + L q) ⁻¹' U) ×ˢ (univ : Set PolarPoint)))
    (n : ℕ) (t : ℝ) (x : E) (v : Fin n → E) :
    (topologicalCircleTrajectorySmoothDirections hU J hΘ hinit hflow hspeed t).D n x v =
      (volterraStateVariation J hΘ n).value (x, t) v := rfl

end ContinuousFlexibility.Analysis

