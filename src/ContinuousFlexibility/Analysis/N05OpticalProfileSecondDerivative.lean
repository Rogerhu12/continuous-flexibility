import ContinuousFlexibility.Analysis.N05OpticalProfileLipschitz

/-!
# Second derivative bounds for the actual optical radicand

Two ordinary product rules express the actual second derivative using
the profile, reciprocal profile and reciprocal radius jets. The resulting
coefficient bound also holds at the endpoints of an interval carried by
one physical cell, provided those endpoints lie in the radial core.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Radial

set_option backward.isDefEq.respectTransparency false

/-- The actual optical radicand has a moderate second ordinary derivative. -/
theorem n05_referenceModerate_opticalRadicand_secondDerivative {D : ReferenceData}
    (hD : IsAccumulatingProfile D) :
    ReferenceModerate D (deriv (deriv (fun r => -deriv D.w r / (r * D.w r)))) := by
  let F : ℝ → ℝ := fun r => -deriv D.w r / (r * D.w r)
  let u : ℝ → ℝ := deriv D.w
  let v : ℝ → ℝ := fun r => r⁻¹
  let z : ℝ → ℝ := fun r => (D.w r)⁻¹
  have hu : ReferenceModerate D u := by
    simpa only [u, iteratedDeriv_one] using referenceModerate_profile_jet hD 1
  have hu' : ReferenceModerate D (deriv u) := by
    simpa only [u, iteratedDeriv_succ, iteratedDeriv_zero] using
      referenceModerate_profile_jet hD 2
  have hu'' : ReferenceModerate D (deriv (deriv u)) := by
    simpa only [u, iteratedDeriv_succ, iteratedDeriv_zero] using
      referenceModerate_profile_jet hD 3
  have hv : ReferenceModerate D v := by
    simpa only [v, iteratedDeriv_zero] using referenceModerate_reciprocal_radius_jet hD 0
  have hv' : ReferenceModerate D (deriv v) := by
    simpa only [v, iteratedDeriv_one] using referenceModerate_reciprocal_radius_jet hD 1
  have hv'' : ReferenceModerate D (deriv (deriv v)) := by
    simpa only [v, iteratedDeriv_succ, iteratedDeriv_zero] using
      referenceModerate_reciprocal_radius_jet hD 2
  have hz : ReferenceModerate D z := by
    simpa only [z, iteratedDeriv_zero] using referenceModerate_reciprocal_profile_jet hD 0
  have hz' : ReferenceModerate D (deriv z) := by
    simpa only [z, iteratedDeriv_one] using referenceModerate_reciprocal_profile_jet hD 1
  have hz'' : ReferenceModerate D (deriv (deriv z)) := by
    simpa only [z, iteratedDeriv_succ, iteratedDeriv_zero] using
      referenceModerate_reciprocal_profile_jet hD 2
  have heq : F = fun r => -(u r * v r * z r) := by
    funext r
    dsimp only [F, u, v, z]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  let G : ℝ → ℝ := fun r =>
    -((deriv u r * v r + u r * deriv v r) * z r +
      (u r * v r) * deriv z r)
  let H : ℝ → ℝ := fun r =>
    -((((deriv (deriv u) r * v r + deriv u r * deriv v r) +
        (deriv u r * deriv v r + u r * deriv (deriv v) r)) * z r +
        (deriv u r * v r + u r * deriv v r) * deriv z r) +
      ((deriv u r * v r + u r * deriv v r) * deriv z r +
        (u r * v r) * deriv (deriv z) r))
  have hH : ReferenceModerate D H := by
    have ha := (hu'.mul hv).add (hu.mul hv')
    have ha' := ((hu''.mul hv).add (hu'.mul hv')).add
      ((hu'.mul hv').add (hu.mul hv''))
    have hfirst := (ha'.mul hz).add (ha.mul hz')
    have hsecond := (ha.mul hz').add ((hu.mul hv).mul hz'')
    simpa only [H, neg_one_mul] using
      (ReferenceModerate.const D (-1)).mul (hfirst.add hsecond)
  have hdiff {g : ℝ → ℝ} (hg : ReferenceModerate D g)
      (r : ℝ) (hr : r ∈ radialCore D) : HasDerivAt g (deriv g r) r :=
    ((hg.1.contDiffAt (isOpen_Ioo.mem_nhds hr)).differentiableAt (by simp)).hasDerivAt
  have hfirst (r : ℝ) (hr : r ∈ radialCore D) : deriv F r = G r := by
    rw [heq]
    exact (((hdiff hu r hr).mul (hdiff hv r hr)).mul (hdiff hz r hr)).neg.deriv
  have hsecond (r : ℝ) (hr : r ∈ radialCore D) : deriv (deriv F) r = H r := by
    have hcore : ∀ᶠ x in 𝓝 r, x ∈ radialCore D := isOpen_Ioo.mem_nhds hr
    have hlocal : deriv F =ᶠ[𝓝 r] G :=
      hcore.mono fun x hx => hfirst x hx
    rw [hlocal.deriv_eq]
    have du := hdiff hu r hr
    have du' := hdiff hu' r hr
    have dv := hdiff hv r hr
    have dv' := hdiff hv' r hr
    have dz := hdiff hz r hr
    have dz' := hdiff hz' r hr
    exact ((((du'.mul dv).add (du.mul dv')).mul dz).add
      ((du.mul dv).mul dz')).neg.deriv
  have hF' : ReferenceModerate D (deriv F) :=
    (n05_referenceModerate_opticalRadicand hD).2
  obtain ⟨B, A, hB, hbound⟩ := hH.2
  refine ⟨((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).mp hF'.1).2,
    B, A, hB, fun m r hr => ?_⟩
  rw [hsecond r (hD.choose_spec.2.1.2.2.2.1 m hr)]
  exact hbound m r hr

/-- The same physical-cell coefficient power controls the radicand and
its first two derivatives on every carried closed interval in the core. -/
theorem n05_opticalRadicand_cell_derivatives_bound {D : ReferenceData}
    (hD : IsAccumulatingProfile D) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ (m : ℕ) (l b : ℝ),
      l < b → Ioo l b ⊆ D.cells m → Icc l b ⊆ radialCore D →
      ∀ r ∈ Icc l b,
        |(-deriv D.w r / (r * D.w r))| ≤ C * radialE (D.cellIndex m) ^ A ∧
          |deriv (fun x => -deriv D.w x / (x * D.w x)) r| ≤
            C * radialE (D.cellIndex m) ^ A ∧
          |deriv (deriv (fun x => -deriv D.w x / (x * D.w x))) r| ≤
            C * radialE (D.cellIndex m) ^ A := by
  let F : ℝ → ℝ := fun r => -deriv D.w r / (r * D.w r)
  have hF : ReferenceModerate D F := (n05_referenceModerate_opticalRadicand hD).1
  have hF' : ReferenceModerate D (deriv F) :=
    (n05_referenceModerate_opticalRadicand hD).2
  have hF'' : ReferenceModerate D (deriv (deriv F)) :=
    n05_referenceModerate_opticalRadicand_secondDerivative hD
  obtain ⟨C₀, A₀, hC₀, hb₀⟩ := hF.2
  obtain ⟨C₁, A₁, hC₁, hb₁⟩ := hF'.2
  obtain ⟨C₂, A₂, hC₂, hb₂⟩ := hF''.2
  let C : ℝ := C₀ + C₁ + C₂ + 1
  let A : ℝ := |A₀| + |A₁| + |A₂| + 1
  have hC : 0 < C := by dsimp only [C]; linarith only [hC₀, hC₁, hC₂]
  have hA : 0 < A := by dsimp only [A]; positivity
  have hA₀ : A₀ ≤ A := by
    dsimp only [A]
    linarith only [le_abs_self A₀, abs_nonneg A₁, abs_nonneg A₂]
  have hA₁ : A₁ ≤ A := by
    dsimp only [A]
    linarith only [abs_nonneg A₀, le_abs_self A₁, abs_nonneg A₂]
  have hA₂ : A₂ ≤ A := by
    dsimp only [A]
    linarith only [abs_nonneg A₀, abs_nonneg A₁, le_abs_self A₂]
  refine ⟨C, A, hC, hA, fun m l b hlb hcell hcore r hr => ?_⟩
  have hexp {a : ℝ} (ha : a ≤ A) :
      Real.exp (a * radialQ (D.cellIndex m)) ≤
        Real.exp (A * radialQ (D.cellIndex m)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ha (radialQ_nonneg _))
  have ho (x : ℝ) (hx : x ∈ Ioo l b) :
      |F x| + |deriv F x| + |deriv (deriv F) x| ≤
        C * radialE (D.cellIndex m) ^ A := by
    have h₀ := (hb₀ m x (hcell hx)).trans
      (mul_le_mul_of_nonneg_left (hexp hA₀) hC₀)
    have h₁ := (hb₁ m x (hcell hx)).trans
      (mul_le_mul_of_nonneg_left (hexp hA₁) hC₁)
    have h₂ := (hb₂ m x (hcell hx)).trans
      (mul_le_mul_of_nonneg_left (hexp hA₂) hC₂)
    calc
      _ ≤ (C₀ * Real.exp (A * radialQ (D.cellIndex m)) +
          C₁ * Real.exp (A * radialQ (D.cellIndex m))) +
          C₂ * Real.exp (A * radialQ (D.cellIndex m)) :=
        add_le_add (add_le_add h₀ h₁) h₂
      _ = (C₀ + C₁ + C₂) * Real.exp (A * radialQ (D.cellIndex m)) := by ring
      _ ≤ C * Real.exp (A * radialQ (D.cellIndex m)) :=
        mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) (Real.exp_pos _).le
      _ = C * radialE (D.cellIndex m) ^ A := by
        rw [radialE, ← Real.exp_mul]
        congr 1
        congr 1
        ring
  have hc : ContinuousOn (fun x => |F x| + |deriv F x| + |deriv (deriv F) x|)
      (closure (Ioo l b)) := by
    rw [closure_Ioo hlb.ne]
    exact ((hF.1.continuousOn.abs.add hF'.1.continuousOn.abs).add
      hF''.1.continuousOn.abs).mono hcore
  have hsum : |F r| + |deriv F r| + |deriv (deriv F) r| ≤
      C * radialE (D.cellIndex m) ^ A :=
    le_on_closure ho hc continuousOn_const (by simpa only [closure_Ioo hlb.ne] using hr)
  change |F r| ≤ C * radialE (D.cellIndex m) ^ A ∧
    |deriv F r| ≤ C * radialE (D.cellIndex m) ^ A ∧
    |deriv (deriv F) r| ≤ C * radialE (D.cellIndex m) ^ A
  have hn₀ := abs_nonneg (F r)
  have hn₁ := abs_nonneg (deriv F r)
  have hn₂ := abs_nonneg (deriv (deriv F) r)
  refine ⟨?_, ?_, ?_⟩ <;> linarith only [hsum, hn₀, hn₁, hn₂]

end ContinuousFlexibility.Statements
