import ContinuousFlexibility.Analysis.CylinderMixedJets

/-!
# Smooth physical gluing from matching coordinate jets

The two globally smooth functions are glued across one radial circle.
Equality of every mixed coordinate derivative gives equality of the actual
Fréchet derivatives.  Their piecewise Taylor series is then a Taylor series
for the glued function: at the circle the first derivatives on the two
half-spaces agree, and away from it the glued function is locally one branch.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology BigOperators

private def transmissionCoordinate (v : PolarPoint) (j : Fin 2) : ℝ :=
  if j = 0 then v.1 else v.2

private theorem transmission_sum_coordinates (v : PolarPoint) :
    (∑ j : Fin 2, transmissionCoordinate v j • cylinderBasisVector j) = v := by
  rw [Fin.sum_univ_two]
  ext <;> simp [transmissionCoordinate, cylinderBasisVector]

private theorem transmission_multilinear_ext {n : ℕ}
    (P Q : ContinuousMultilinearMap ℝ (fun _ : Fin n => PolarPoint) ℝ)
    (h : ∀ w : Fin n → Fin 2,
      P (fun i => cylinderBasisVector (w i)) = Q (fun i => cylinderBasisVector (w i))) :
    P = Q := by
  classical
  apply ContinuousMultilinearMap.ext
  intro d
  have hexpand (F : ContinuousMultilinearMap ℝ (fun _ : Fin n => PolarPoint) ℝ) :
      F d = ∑ w : Fin n → Fin 2, (∏ i, transmissionCoordinate (d i) (w i)) •
        F (fun i => cylinderBasisVector (w i)) := by
    have hd : (fun i : Fin n => ∑ j : Fin 2,
        transmissionCoordinate (d i) j • cylinderBasisVector j) = d :=
      funext fun i => transmission_sum_coordinates (d i)
    have he := F.toMultilinearMap.map_sum
      (fun i : Fin n => fun j : Fin 2 => transmissionCoordinate (d i) j • cylinderBasisVector j)
    change F (fun i => ∑ j : Fin 2, transmissionCoordinate (d i) j • cylinderBasisVector j) =
      ∑ w : Fin n → Fin 2,
        F (fun i => transmissionCoordinate (d i) (w i) • cylinderBasisVector (w i)) at he
    simpa only [hd, ContinuousMultilinearMap.map_smul_univ] using he
  rw [hexpand P, hexpand Q]
  exact Finset.sum_congr rfl fun w _ =>
    congrArg (fun z : ℝ => (∏ i, transmissionCoordinate (d i) (w i)) • z) (h w)

private theorem transmission_iteratedFDeriv_match (r0 : ℝ)
    {u v : PolarPoint → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hjets : ∀ i j : ℕ, ∀ θ,
      mixedDerivative i j u (r0, θ) = mixedDerivative i j v (r0, θ))
    (n : ℕ) (θ : ℝ) :
    iteratedFDeriv ℝ n u (r0, θ) = iteratedFDeriv ℝ n v (r0, θ) := by
  apply transmission_multilinear_ext
  intro w
  rw [iteratedFDeriv_cylinderBasis_eq_mixedDerivative isOpen_univ hu.contDiffOn n (mem_univ _) w,
    iteratedFDeriv_cylinderBasis_eq_mixedDerivative isOpen_univ hv.contDiffOn n (mem_univ _) w]
  exact hjets _ _ θ

private theorem hasFDerivAt_transmission {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (r0 : ℝ) (u v : PolarPoint → F)
    (u' v' : PolarPoint → PolarPoint →L[ℝ] F)
    (hu : ∀ p, HasFDerivAt u (u' p) p) (hv : ∀ p, HasFDerivAt v (v' p) p)
    (hvalue : ∀ θ, u (r0, θ) = v (r0, θ))
    (hderiv : ∀ θ, u' (r0, θ) = v' (r0, θ)) (p : PolarPoint) :
    HasFDerivAt (fun q : PolarPoint => if q.1 ≤ r0 then u q else v q)
      (if p.1 ≤ r0 then u' p else v' p) p := by
  rcases p with ⟨r, θ⟩
  rcases lt_trichotomy r r0 with hlt | heq | hgt
  · rw [if_pos hlt.le]
    apply (hu (r, θ)).congr_of_eventuallyEq
    have hnear : ∀ᶠ q : PolarPoint in 𝓝 (r, θ), q.1 < r0 :=
      (isOpen_lt continuous_fst continuous_const).mem_nhds hlt
    filter_upwards [hnear] with q hq
    exact if_pos hq.le
  · subst r
    rw [if_pos (le_refl r0)]
    let S : Set PolarPoint := {q | q.1 ≤ r0}
    have hleft : HasFDerivWithinAt
        (fun q : PolarPoint => if q.1 ≤ r0 then u q else v q) (u' (r0, θ)) S (r0, θ) :=
      (hu (r0, θ)).hasFDerivWithinAt.congr
        (fun q hq => if_pos (show q.1 ≤ r0 from hq)) (if_pos (le_refl r0))
    have hv' : HasFDerivAt v (u' (r0, θ)) (r0, θ) :=
      (hv (r0, θ)).congr_fderiv (hderiv θ).symm
    have hright : HasFDerivWithinAt
        (fun q : PolarPoint => if q.1 ≤ r0 then u q else v q) (u' (r0, θ)) Sᶜ (r0, θ) :=
      hv'.hasFDerivWithinAt.congr
        (fun q hq => if_neg (show ¬ q.1 ≤ r0 from hq))
        ((if_pos (le_refl r0)).trans (hvalue θ))
    simpa only [union_compl_self, hasFDerivWithinAt_univ] using hleft.union hright
  · rw [if_neg (not_le_of_gt hgt)]
    apply (hv (r, θ)).congr_of_eventuallyEq
    have hnear : ∀ᶠ q : PolarPoint in 𝓝 (r, θ), r0 < q.1 :=
      (isOpen_lt continuous_const continuous_fst).mem_nhds hgt
    filter_upwards [hnear] with q hq
    exact if_neg (not_le_of_gt hq)

/-- Matching all mixed physical jets along a radial circle makes the
piecewise function smooth on the entire physical coordinate plane. -/
theorem contDiff_physicalTransmission (r0 : ℝ)
    {u v : PolarPoint → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hjets : ∀ i j : ℕ, ∀ θ,
      mixedDerivative i j u (r0, θ) = mixedDerivative i j v (r0, θ)) :
    ContDiff ℝ ∞ (fun p : PolarPoint => if p.1 ≤ r0 then u p else v p) := by
  let P : PolarPoint → FormalMultilinearSeries ℝ PolarPoint ℝ := fun p n =>
    if p.1 ≤ r0 then ftaylorSeries ℝ u p n else ftaylorSeries ℝ v p n
  have hmatch (n : ℕ) (θ : ℝ) :
      ftaylorSeries ℝ u (r0, θ) n = ftaylorSeries ℝ v (r0, θ) n :=
    transmission_iteratedFDeriv_match r0 hu hv hjets n θ
  have hdiff (n : ℕ) (p : PolarPoint) :
      HasFDerivAt (fun q => P q n) (P p (n + 1)).curryLeft p := by
    have h := hasFDerivAt_transmission r0
      (fun q => ftaylorSeries ℝ u q n) (fun q => ftaylorSeries ℝ v q n)
      (fun q => (ftaylorSeries ℝ u q (n + 1)).curryLeft)
      (fun q => (ftaylorSeries ℝ v q (n + 1)).curryLeft)
      (hu.ftaylorSeries.fderiv n (by simp)) (hv.ftaylorSeries.fderiv n (by simp))
      (hmatch n) (fun θ => congrArg ContinuousMultilinearMap.curryLeft (hmatch (n + 1) θ)) p
    by_cases hp : p.1 ≤ r0
    · simpa only [P, if_pos hp] using h
    · simpa only [P, if_neg hp] using h
  have hTaylor : HasFTaylorSeriesUpTo ∞
      (fun p : PolarPoint => if p.1 ≤ r0 then u p else v p) P := by
    refine ⟨?_, fun n _ p => hdiff n p, ?_⟩
    · intro p
      by_cases hp : p.1 ≤ r0
      · simpa only [P, if_pos hp] using hu.ftaylorSeries.zero_eq p
      · simpa only [P, if_neg hp] using hv.ftaylorSeries.zero_eq p
    · intro n _
      have hD : Differentiable ℝ (fun p => P p n) := fun p => (hdiff n p).differentiableAt
      exact hD.continuous
  exact hTaylor.contDiff

end ContinuousFlexibility.Statements
