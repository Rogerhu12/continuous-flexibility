module

public import ContinuousFlexibility.Analysis.ProjectiveNewtonLimit
public import ContinuousFlexibility.Analysis.ProjectiveNewtonRapidDecay

/-!
# A common Newton orbit for parameter regularity

Select the smoothing family and schedule once. The forward smoothing
estimates, rapid increments at every grade, and zero-residual limit all
use that selection.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Filter Set
open scoped Topology

theorem exists_projectiveNewton_common_orbit
    {E F : ℕ → Type*}
    [∀ s, NormedAddCommGroup (E s)] [∀ s, NormedSpace ℝ (E s)] [∀ s, CompleteSpace (E s)]
    [∀ s, NormedAddCommGroup (F s)] [∀ s, NormedSpace ℝ (F s)]
    {e : ∀ s, E (s + 1) →L[ℝ] E s} {f : ∀ s, F (s + 1) →L[ℝ] F s}
    (x₀ : ProjectiveLimit E e) (b₀ : ℕ) (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    {U : Set (ProjectiveLimit E e × ℝ)}
    (hU : U = {z | gradedSeminorm E e b₀ (z.1 - x₀) < ε₀ ∧ |z.2| < ε₀})
    (R : ProjectiveLimit E e × ℝ → ProjectiveLimit F f)
    (V : ProjectiveLimit E e × ℝ → ProjectiveLimit F f →ₗ[ℝ] ProjectiveLimit E e)
    (Q : ProjectiveLimit E e × ℝ →
      ProjectiveLimit F f →ₗ[ℝ] ProjectiveLimit F f →ₗ[ℝ] ProjectiveLimit F f)
    (hzero : R (x₀, 0) = 0)
    (hRight : ∀ z ∈ U, ∀ y, HasProjectiveLineDerivAt (fun x => R (x, z.2))
      (y + Q z (R z) y) z.1 (V z y)) :
    let p := gradedSeminorm E e
    let q := gradedSeminorm F f
    let a := Statements.pairGrading p Statements.realGrading
    Statements.HasSmoothing p → Statements.HasSmoothing q →
    Statements.SmoothTameOn a q U R →
    Statements.SmoothTameOn (Statements.pairGrading a q) p (U ×ˢ univ)
      (fun z : (ProjectiveLimit E e × ℝ) × ProjectiveLimit F f => V z.1 z.2) →
    Statements.SmoothTameOn (Statements.pairGrading (Statements.pairGrading a q) q)
      q ((U ×ˢ univ) ×ˢ univ)
      (fun z : ((ProjectiveLimit E e × ℝ) × ProjectiveLimit F f) × ProjectiveLimit F f =>
        Q z.1.1 z.1.2 z.2) →
    ∃ SX : ℕ → ProjectiveLimit E e →L[ℝ] ProjectiveLimit E e,
    ∃ b N₀ : ℕ, ∃ q₀ : ℝ, ∃ x : ℝ → ProjectiveLimit E e,
      let N := newtonSmoothingIndex N₀
      let I := Ioo (-q₀) q₀
      let z := fun n τ => projectiveSmoothedNewtonIterates R V SX N (x₀, τ) n
      0 < N₀ ∧ 0 < q₀ ∧ x 0 = x₀ ∧
      (∀ s, ∃ C γ : ℝ, 0 ≤ C ∧ 0 ≤ γ ∧ ∀ (L : ℕ) u,
        p s (SX L u) ≤ C * Real.exp (γ * (L : ℝ)) * p b u) ∧
      (∀ n τ, τ ∈ I → z n τ ∈ U) ∧
      (∀ τ ∈ I, Tendsto (fun n => z n τ) atTop (𝓝 (x τ, τ)) ∧
        (x τ, τ) ∈ U ∧ R (x τ, τ) = 0) ∧
      (∀ s (δ : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ n τ, τ ∈ I →
        p s ((z (n + 1) τ).1 - (z n τ).1) ≤ C * Real.exp (-δ * (N n : ℝ))) ∧
      ∃ D : ℕ → ℕ → ℝ, (∀ s, Summable (D s)) ∧ (∀ s n, 0 ≤ D s n) ∧
        ∀ s n τ, τ ∈ I → p s ((z (n + 1) τ).1 - (z n τ).1) ≤ D s n := by
  classical
  dsimp only
  intro hSX hSY hR hV hQ
  let X := ProjectiveLimit E e
  let Y := ProjectiveLimit F f
  let p := gradedSeminorm E e
  let q := gradedSeminorm F f
  let a := Statements.pairGrading p Statements.realGrading
  have hp := gradedSeminorm_monotone E e
  have hq := gradedSeminorm_monotone F f
  have ha : Monotone a := pairGrading_monotone hp monotone_const
  obtain ⟨bMin, hsep⟩ := exists_separating_grade_of_hasSmoothing
    (withSeminorms_graded F f) hq hSY
  have hz₀ : (x₀, (0 : ℝ)) ∈ U := by
    rw [hU]
    change p b₀ (x₀ - x₀) < ε₀ ∧ |(0 : ℝ)| < ε₀
    simpa only [sub_self, map_zero, abs_zero] using And.intro hε₀ hε₀
  obtain ⟨bS, σ, SX, SY, _, _, hSmooth⟩ := exists_twoGradeNewtonSmoothingBounds hSX hSY
  obtain ⟨J, b, l, ε, hb, hε, hBounds⟩ :=
    exists_common_newton_tame_data ha hq (max bMin (max b₀ bS)) hR hV hQ hz₀
  have hbMin : bMin ≤ b := (le_max_left _ _).trans hb
  have hb₀ : b₀ ≤ b := (le_max_left _ _).trans ((le_max_right _ _).trans hb)
  have hbS : bS ≤ b := (le_max_right _ _).trans ((le_max_right _ _).trans hb)
  have hforward (s : ℕ) : ∃ C γ : ℝ, 0 ≤ C ∧ 0 ≤ γ ∧ ∀ (L : ℕ) u,
      p s (SX L u) ≤ C * Real.exp (γ * (L : ℝ)) * p b u := by
    obtain ⟨C, hC, H⟩ := hSmooth b l (s + 2 * l) hbS (by omega)
    refine ⟨C, ((s + 2 * l : ℕ) : ℝ) + 2 * (l : ℝ) + σ, hC, by positivity, ?_⟩
    intro L u
    have hs : s ≤ b + (s + 2 * l) + 2 * l := by omega
    exact (hp hs _).trans ((H L u (0 : Y)).1.2.2.1)
  obtain ⟨Kₛ, hKₛ, hSmooth'⟩ := hSmooth b l (20 * l + 15 * σ + 8) hbS (by omega)
  obtain ⟨q₀, μ, hq₀, hqμ, hμ, hμε₀, hμε, hμ₁, N₀, _, hN₀, _, hseed⟩ :=
    projectiveNewton_seed_of_common_bounds p hp x₀ b₀ b l σ hb₀ ε₀ ε hε₀ hε
      hU R V Q J hzero hRight SX SY Kₛ hKₛ hBounds hSmooth'
  let N := newtonSmoothingIndex N₀
  let I := Ioo (-q₀) q₀
  let z := fun n τ => projectiveSmoothedNewtonIterates R V SX N (x₀, τ) n
  let c := fun n τ => SX (N n) (V (z n τ) (R (z n τ)))
  have hrapid := projectiveNewton_rapid_decay_of_seed p hp x₀ b₀ b l σ N₀ hb₀ hN₀
    ε₀ ε μ q₀ hμ hμε₀ hμε hμ₁ hqμ hU R V Q J hRight SX SY hBounds
    (fun h hh => hSmooth b l h hbS hh)
    (fun τ hτ n => by
      obtain ⟨hz, _, hdisp, hnear, hlow, hr, _⟩ := hseed τ hτ n
      exact ⟨hz, hdisp, hnear, hlow, hr⟩)
  have hiter (n : ℕ) (τ : ℝ) (hτ : τ ∈ I) : z n τ ∈ U :=
    (hseed τ (abs_lt.mpr hτ) n).1
  have hdiff (s n : ℕ) (τ : ℝ) :
      p s ((z (n + 1) τ).1 - (z n τ).1) = p s (c n τ) := by
    change p s ((z n τ).1 - c n τ - (z n τ).1) = _
    rw [show (z n τ).1 - c n τ - (z n τ).1 = -c n τ by abel, map_neg_eq_map]
  have hincRapid (s : ℕ) (δ : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n τ, τ ∈ I →
      p s ((z (n + 1) τ).1 - (z n τ).1) ≤ C * Real.exp (-δ * (N n : ℝ)) := by
    obtain ⟨C, hC, H⟩ := hrapid.2 s δ
    exact ⟨C, hC, fun n τ hτ => (hdiff s n τ).le.trans (H n τ (abs_lt.mpr hτ))⟩
  choose C hC HC using fun s => hrapid.2 s 1
  let D := fun s n => C s * Real.exp (-(1 : ℝ) * (N n : ℝ))
  have hD (s : ℕ) : Summable (D s) :=
    (newton_summable_exponential hN₀ zero_lt_one).mul_left (C s)
  have hD₀ (s n : ℕ) : 0 ≤ D s n := mul_nonneg (hC s) (Real.exp_pos _).le
  have hinc (s n : ℕ) (τ : ℝ) (hτ : τ ∈ I) :
      p s ((z (n + 1) τ).1 - (z n τ).1) ≤ D s n :=
    (hdiff s n τ).le.trans (HC s n τ (abs_lt.mpr hτ))
  have hRcont : ContinuousOn R U := by
    have hc : Continuous (fun z : X × ℝ => (z, (Fin.elim0 : Fin 0 → X × ℝ))) :=
      continuous_id.prodMk continuous_const
    exact ((J.continuous 0).comp hc.continuousOn
      (fun z hz => ⟨hz, mem_univ _⟩)).congr (fun z hz => (J.zero z hz).symm)
  have hμlt : μ < ε₀ := by linarith only [hμ, hμε₀]
  have hbmargin : b₀ ≤ b + l + l := by omega
  have hsep' : ∀ y, q (b + l) y = 0 → y = 0 := hsep _ (by omega)
  have hpoint (τ : ℝ) (hτ : τ ∈ I) : ∃ x : X,
      Tendsto (fun n => z n τ) atTop (𝓝 (x, τ)) ∧ (x, τ) ∈ U ∧ R (x, τ) = 0 := by
    have hτ' : |τ| < q₀ := abs_lt.mpr hτ
    have hsum (s : ℕ) : Summable (fun n => p s (c n τ)) :=
      Summable.of_nonneg_of_le (f := D s) (fun _ => apply_nonneg _ _)
        (fun n => HC s n τ hτ') (hD s)
    have hclosed (n : ℕ) : p b₀ ((z n τ).1 - x₀) ≤ μ ∧ |(z n τ).2| ≤ μ := by
      obtain ⟨_, hparam, hdisp, _, _, _, _⟩ := hseed τ hτ' n
      refine ⟨(hp hbmargin _).trans hdisp.le, ?_⟩
      change |(projectiveSmoothedNewtonIterates R V SX N (x₀, τ) n).2| ≤ μ
      rw [hparam]
      exact hτ'.le.trans hqμ
    let α₀ : ℝ := 4 * (l : ℝ) + 4 * (σ : ℝ) + 2
    have hα : 0 < α₀ := by positivity
    have hdecay : Tendsto (fun n => q (b + l) (R (z n τ))) atTop (𝓝 0) :=
      squeeze_zero (fun _ => apply_nonneg _ _) (fun n => by
        obtain ⟨_, _, _, _, _, hr, _⟩ := hseed τ hτ' n
        exact hr)
        (newton_summable_exponential hN₀ hα).tendsto_atTop_zero
    rw [hU] at hRcont ⊢
    exact exists_projectiveSmoothedNewton_limit_zero R V SX N (x₀, τ) (p b₀)
      (continuous_gradedSeminorm E e b₀) x₀ hμlt (q (b + l))
      (continuous_gradedSeminorm F f (b + l)) hsep' hRcont hsum hclosed hdecay
  let x : ℝ → X := fun τ => if hτ : τ ∈ I then (hpoint τ hτ).choose else x₀
  have hx (τ : ℝ) (hτ : τ ∈ I) :
      Tendsto (fun n => z n τ) atTop (𝓝 (x τ, τ)) ∧ (x τ, τ) ∈ U ∧ R (x τ, τ) = 0 := by
    simpa only [x, dite_eq_left hτ] using (hpoint τ hτ).choose_spec
  have hzstat (n : ℕ) : z n 0 = (x₀, 0) := by
    change projectiveSmoothedNewtonIterates R V SX N (x₀, 0) n = (x₀, 0)
    induction n with
    | zero => rfl
    | succ n ih => simp [projectiveSmoothedNewtonIterates, projectiveSmoothedNewtonStep, ih, hzero]
  have hzeroI : (0 : ℝ) ∈ I := ⟨neg_lt_zero.mpr hq₀, hq₀⟩
  have hlim := (hx 0 hzeroI).1
  rw [show (fun n => z n 0) = fun _ => (x₀, 0) from funext hzstat] at hlim
  have hx₀ : x 0 = x₀ :=
    congrArg Prod.fst (tendsto_nhds_unique hlim tendsto_const_nhds)
  exact ⟨SX, b, N₀, q₀, x, hN₀, hq₀, hx₀, hforward, hiter, hx, hincRapid, D, hD, hD₀, hinc⟩

end ContinuousFlexibility.Analysis
