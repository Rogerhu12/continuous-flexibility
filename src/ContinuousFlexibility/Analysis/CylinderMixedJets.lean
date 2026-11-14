module

public import ContinuousFlexibility.Statements.Analysis
public import ContinuousFlexibility.Scalar.HeightDerivatives
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Mixed coordinate jets control the actual Fréchet jets on a cylinder

The slice derivatives are identified on the given open set. Commutation
uses the actual second derivative of each smooth iterated partial.
Multilinear expansion in the two coordinate directions gives the
operator-norm bound with constant 2 ^ n in the product max norm.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

private def cylinderPartial (d : PolarPoint) (f : PolarPoint → ℝ) : PolarPoint → ℝ :=
  fun p => fderiv ℝ f p d

private theorem contDiffOn_cylinderPartial {U : Set PolarPoint} {f : PolarPoint → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (d : PolarPoint) :
    ContDiffOn ℝ ∞ (cylinderPartial d f) U :=
  (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

private theorem contDiffOn_iterate_cylinderPartial {U : Set PolarPoint}
    {f : PolarPoint → ℝ} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (d : PolarPoint) (n : ℕ) :
    ContDiffOn ℝ ∞ ((cylinderPartial d)^[n] f) U := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact contDiffOn_cylinderPartial hU ih d

private theorem eqOn_iterate_cylinderPartial {U : Set PolarPoint}
    {f g : PolarPoint → ℝ} (hU : IsOpen U) (h : EqOn f g U)
    (d : PolarPoint) (n : ℕ) :
    EqOn ((cylinderPartial d)^[n] f) ((cylinderPartial d)^[n] g) U := by
  induction n with
  | zero => exact h
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    intro p hp
    have he : ((cylinderPartial d)^[n] f) =ᶠ[𝓝 p] ((cylinderPartial d)^[n] g) := by
      filter_upwards [hU.mem_nhds hp] with y hy
      exact ih hy
    exact congrArg (fun T : PolarPoint →L[ℝ] ℝ => T d) (he.fderiv_eq (𝕜 := ℝ))

private theorem iteratedDeriv_slice {U : Set PolarPoint} {f : PolarPoint → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (σ : ℝ → PolarPoint) (d : PolarPoint)
    (hσ : ∀ t, HasDerivAt σ d t) (n : ℕ) {t : ℝ} (ht : σ t ∈ U) :
    iteratedDeriv n (fun s => f (σ s)) t = ((cylinderPartial d)^[n] f) (σ t) := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    have hnear : ∀ᶠ s in 𝓝 t, σ s ∈ U :=
      (hσ t).continuousAt.preimage_mem_nhds (hU.mem_nhds ht)
    have he : iteratedDeriv n (fun s => f (σ s)) =ᶠ[𝓝 t]
        (fun s => ((cylinderPartial d)^[n] f) (σ s)) := by
      filter_upwards [hnear] with s hs
      exact ih hs
    have hc := contDiffOn_iterate_cylinderPartial hU hf d n
    have hd : DifferentiableAt ℝ ((cylinderPartial d)^[n] f) (σ t) :=
      (hc.differentiableOn (by simp) (σ t) ht).differentiableAt (hU.mem_nhds ht)
    have hs := hd.hasFDerivAt.comp_hasDerivAt t (hσ t)
    rw [iteratedDeriv_succ, he.deriv_eq, Function.iterate_succ_apply']
    simpa only [Function.comp_def, cylinderPartial] using hs.deriv

private theorem hasDerivAt_cylinderRadialSlice (θ t : ℝ) :
    HasDerivAt (fun r : ℝ => (r, θ)) (1, 0) t :=
  (hasDerivAt_id' t).prodMk (hasDerivAt_const t θ)

private theorem hasDerivAt_cylinderAngularSlice (r t : ℝ) :
    HasDerivAt (fun θ : ℝ => (r, θ)) (0, 1) t :=
  (hasDerivAt_const t r).prodMk (hasDerivAt_id' t)

private theorem mixedDerivative_eq_iterates {U : Set PolarPoint} {f : PolarPoint → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (a b : ℕ) {p : PolarPoint} (hp : p ∈ U) :
    mixedDerivative a b f p =
      (radialPartial^[a] (angularPartial^[b] f)) p := by
  let g := angularPartial^[b] f
  have hg : ContDiffOn ℝ ∞ g U := contDiffOn_iterate_cylinderPartial hU hf (0, 1) b
  have hnear : ∀ᶠ r in 𝓝 p.1, (r, p.2) ∈ U :=
    (hasDerivAt_cylinderRadialSlice p.2 p.1).continuousAt.preimage_mem_nhds (hU.mem_nhds hp)
  have he : (fun r => iteratedDeriv b (fun θ => f (r, θ)) p.2) =ᶠ[𝓝 p.1]
      (fun r => g (r, p.2)) := by
    filter_upwards [hnear] with r hr
    exact iteratedDeriv_slice hU hf (fun θ => (r, θ)) (0, 1)
      (hasDerivAt_cylinderAngularSlice r) b hr
  exact (he.iteratedDeriv a).eq_of_nhds.trans
    (iteratedDeriv_slice hU hg (fun r => (r, p.2)) (1, 0)
      (hasDerivAt_cylinderRadialSlice p.2) a hp)

/-- All actual mixed coordinate derivatives are smooth on the original open set. -/
theorem contDiffOn_mixedDerivative {U : Set PolarPoint} {f : PolarPoint → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (a b : ℕ) :
    ContDiffOn ℝ ∞ (mixedDerivative a b f) U := by
  have hs : ContDiffOn ℝ ∞ (radialPartial^[a] (angularPartial^[b] f)) U :=
    contDiffOn_iterate_cylinderPartial hU
      (contDiffOn_iterate_cylinderPartial hU hf (0, 1) b) (1, 0) a
  exact hs.congr (fun _ hp => mixedDerivative_eq_iterates hU hf a b hp)

private theorem angular_iterate_radial_commute {U : Set PolarPoint} {f : PolarPoint → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (b : ℕ) :
    EqOn (angularPartial^[b] (radialPartial f)) (radialPartial (angularPartial^[b] f)) U := by
  induction b with
  | zero => exact fun _ _ => rfl
  | succ b ih =>
    simp only [Function.iterate_succ_apply']
    intro p hp
    have he := eqOn_iterate_cylinderPartial hU ih (0, 1) 1 hp
    have hs : ContDiffAt ℝ 2 (angularPartial^[b] f) p :=
      ((contDiffOn_iterate_cylinderPartial hU hf (0, 1) b).contDiffAt
        (hU.mem_nhds hp)).of_le (by simp)
    exact he.trans (radial_angular_commute hs).symm

theorem mixedDerivative_radialPartial {U : Set PolarPoint} {f : PolarPoint → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (a b : ℕ) {p : PolarPoint} (hp : p ∈ U) :
    mixedDerivative a b (radialPartial f) p = mixedDerivative (a + 1) b f p := by
  have hs : ContDiffOn ℝ ∞ (radialPartial f) U := contDiffOn_cylinderPartial hU hf (1, 0)
  rw [mixedDerivative_eq_iterates hU hs a b hp, mixedDerivative_eq_iterates hU hf (a + 1) b hp,
    Function.iterate_succ_apply]
  exact eqOn_iterate_cylinderPartial hU (angular_iterate_radial_commute hU hf b) (1, 0) a hp

theorem mixedDerivative_angularPartial {U : Set PolarPoint} {f : PolarPoint → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (a b : ℕ) {p : PolarPoint} (hp : p ∈ U) :
    mixedDerivative a b (angularPartial f) p = mixedDerivative a (b + 1) f p := by
  have hs : ContDiffOn ℝ ∞ (angularPartial f) U := contDiffOn_cylinderPartial hU hf (0, 1)
  rw [mixedDerivative_eq_iterates hU hs a b hp, mixedDerivative_eq_iterates hU hf a (b + 1) hp,
    Function.iterate_succ_apply]

/-- The two coordinate unit vectors for the actual cylinder chart. -/
def cylinderBasisVector (j : Fin 2) : PolarPoint := if j = 0 then (1, 0) else (0, 1)

private theorem iteratedFDeriv_apply_last_cylinder {U : Set PolarPoint}
    {f : PolarPoint → ℝ} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (n : ℕ) {p : PolarPoint} (hp : p ∈ U) (v : Fin (n + 1) → PolarPoint) :
    iteratedFDeriv ℝ (n + 1) f p v =
      iteratedFDeriv ℝ n (cylinderPartial (v (Fin.last n)) f) p (Fin.init v) := by
  rw [iteratedFDeriv_succ_apply_right]
  have hs : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  have he := iteratedFDerivWithin_clm_apply_const_apply hU.uniqueDiffOn hs
    (i := n) (by simp) hp (u := v (Fin.last n)) (m := Fin.init v)
  change iteratedFDerivWithin ℝ n (cylinderPartial (v (Fin.last n)) f) U p (Fin.init v) =
    iteratedFDerivWithin ℝ n (fderiv ℝ f) U p (Fin.init v) (v (Fin.last n)) at he
  rw [iteratedFDerivWithin_of_isOpen (f := cylinderPartial (v (Fin.last n)) f) n hU hp,
    iteratedFDerivWithin_of_isOpen (f := fderiv ℝ f) n hU hp] at he
  exact he.symm

/-- Evaluation on any word of coordinate directions is a mixed derivative.
The induction adds one radial or angular index according to the last slot. -/
theorem iteratedFDeriv_cylinderBasis_eq_mixedDerivative {U : Set PolarPoint}
    {f : PolarPoint → ℝ} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (n : ℕ) {p : PolarPoint} (hp : p ∈ U) (w : Fin n → Fin 2) :
    iteratedFDeriv ℝ n f p (fun i => cylinderBasisVector (w i)) =
      mixedDerivative (∑ i, if w i = 0 then 1 else 0) (∑ i, if w i = 0 then 0 else 1) f p := by
  induction n generalizing f with
  | zero => simp [mixedDerivative]
  | succ n ih =>
    have hinit :
        Fin.init (α := fun _ : Fin (n + 1) => PolarPoint) (fun i => cylinderBasisVector (w i)) =
          (fun i : Fin n => cylinderBasisVector (Fin.init w i)) := rfl
    rw [iteratedFDeriv_apply_last_cylinder hU hf n hp, hinit,
      Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    by_cases hw : w (Fin.last n) = 0
    · have hd : cylinderPartial (cylinderBasisVector (w (Fin.last n))) f = radialPartial f := by
        calc
          cylinderPartial (cylinderBasisVector (w (Fin.last n))) f =
              cylinderPartial (1, 0) f := by rw [cylinderBasisVector, ite_eq_left hw]
          _ = radialPartial f := rfl
      rw [hd]
      have hs : ContDiffOn ℝ ∞ (radialPartial f) U := contDiffOn_cylinderPartial hU hf (1, 0)
      simpa only [Fin.init, ite_eq_left hw, add_zero] using
        (ih hs (Fin.init w)).trans (mixedDerivative_radialPartial hU hf _ _ hp)
    · have hd : cylinderPartial (cylinderBasisVector (w (Fin.last n))) f = angularPartial f := by
        calc
          cylinderPartial (cylinderBasisVector (w (Fin.last n))) f =
              cylinderPartial (0, 1) f := by rw [cylinderBasisVector, ite_eq_right hw]
          _ = angularPartial f := rfl
      rw [hd]
      have hs : ContDiffOn ℝ ∞ (angularPartial f) U := contDiffOn_cylinderPartial hU hf (0, 1)
      simpa only [Fin.init, ite_eq_right hw, add_zero] using
        (ih hs (Fin.init w)).trans (mixedDerivative_angularPartial hU hf _ _ hp)

private def cylinderCoordinate (v : PolarPoint) (j : Fin 2) : ℝ :=
  if j = 0 then v.1 else v.2

private theorem cylinderCoordinate_norm_le (v : PolarPoint) (j : Fin 2) :
    ‖cylinderCoordinate v j‖ ≤ ‖v‖ := by
  unfold cylinderCoordinate
  split
  · exact norm_fst_le v
  · exact norm_snd_le v

private theorem cylinder_sum_coordinates (v : PolarPoint) :
    (∑ j : Fin 2, cylinderCoordinate v j • cylinderBasisVector j) = v := by
  rw [Fin.sum_univ_two]
  ext <;> simp [cylinderCoordinate, cylinderBasisVector]

/-- A common bound on the actual mixed derivatives of order n controls
the norm of the actual n-th Fréchet derivative on the same open set. -/
theorem norm_iteratedFDeriv_le_of_mixedDerivative {U : Set PolarPoint}
    {f : PolarPoint → ℝ} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (n : ℕ) {p : PolarPoint} (hp : p ∈ U) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ a b : ℕ, a + b = n → ‖mixedDerivative a b f p‖ ≤ M) :
    ‖iteratedFDeriv ℝ n f p‖ ≤ (2 : ℝ) ^ n * M := by
  classical
  let F := iteratedFDeriv ℝ n f p
  refine F.opNorm_le_bound (by positivity) fun v => ?_
  have hexpand : F v =
      ∑ w : Fin n → Fin 2, (∏ i, cylinderCoordinate (v i) (w i)) •
        F (fun i => cylinderBasisVector (w i)) := by
    have hv : (fun i : Fin n => ∑ j : Fin 2, cylinderCoordinate (v i) j • cylinderBasisVector j) =
        v := funext fun i => cylinder_sum_coordinates (v i)
    have he := F.toMultilinearMap.map_sum
      (fun i : Fin n => fun j : Fin 2 => cylinderCoordinate (v i) j • cylinderBasisVector j)
    change F (fun i => ∑ j : Fin 2, cylinderCoordinate (v i) j • cylinderBasisVector j) =
      ∑ w : Fin n → Fin 2, F (fun i => cylinderCoordinate (v i) (w i) • cylinderBasisVector (w i)) at he
    simpa only [hv, ContinuousMultilinearMap.map_smul_univ] using he
  have hb (w : Fin n → Fin 2) : ‖F (fun i => cylinderBasisVector (w i))‖ ≤ M := by
    change ‖iteratedFDeriv ℝ n f p (fun i => cylinderBasisVector (w i))‖ ≤ M
    rw [iteratedFDeriv_cylinderBasis_eq_mixedDerivative hU hf n hp w]
    apply h
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _ : Fin n, (1 : ℕ) := Finset.sum_congr rfl fun i _ => by
        by_cases hi : w i = 0 <;> simp [hi]
      _ = n := by simp
  rw [hexpand]
  calc
    ‖∑ w : Fin n → Fin 2, (∏ i, cylinderCoordinate (v i) (w i)) •
        F (fun i => cylinderBasisVector (w i))‖
        ≤ ∑ w : Fin n → Fin 2, ‖(∏ i, cylinderCoordinate (v i) (w i)) •
            F (fun i => cylinderBasisVector (w i))‖ := norm_sum_le _ _
    _ ≤ ∑ _w : Fin n → Fin 2, (∏ i, ‖v i‖) * M := by
      apply Finset.sum_le_sum
      intro w _
      rw [norm_smul, norm_prod]
      exact mul_le_mul (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun i _ => cylinderCoordinate_norm_le (v i) (w i))) (hb w)
        (norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = (2 : ℝ) ^ n * M * ∏ i, ‖v i‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring

end ContinuousFlexibility.Statements
