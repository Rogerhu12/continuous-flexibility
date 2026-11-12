import ContinuousFlexibility.Radial.ReferenceCosineTestCalculus

/-!
# Fourier commutation for the actual two-dimensional test operator

Two ordinary integrations by parts on one full angular period move the
angular second derivative to the cosine eigenfunction. Combined with
the genuine parameter-integral radial derivatives, this proves the exact
Jacobi equation for every test coefficient, including the zero mode.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

theorem reference_periodic_deriv {f : ℝ → ℝ} {T : ℝ}
    (hf : Function.Periodic f T) : Function.Periodic (deriv f) T := by
  intro x
  have heq : (fun t => f (t + T)) = f := funext hf
  have hd := deriv_comp_add_const f T x
  rw [heq] at hd
  exact hd.symm

theorem referenceCircleCosine_full_periodic (n : ℕ) :
    Function.Periodic
      (fun θ : ℝ => referenceCircleCosine n (θ : AddCircle Real.pi)) (2 * Real.pi) := by
  intro θ
  change referenceCircleCosine n ((θ + 2 * Real.pi : ℝ) : AddCircle Real.pi) =
    referenceCircleCosine n (θ : AddCircle Real.pi)
  have h₁ :
      referenceCircleCosine n (((θ + Real.pi) + Real.pi : ℝ) : AddCircle Real.pi) =
        referenceCircleCosine n ((θ + Real.pi : ℝ) : AddCircle Real.pi) :=
    referenceCircleCosine_periodic n (θ + Real.pi)
  have h₂ :
      referenceCircleCosine n ((θ + Real.pi : ℝ) : AddCircle Real.pi) =
        referenceCircleCosine n (θ : AddCircle Real.pi) :=
    referenceCircleCosine_periodic n θ
  rw [show θ + 2 * Real.pi = (θ + Real.pi) + Real.pi by ring]
  exact h₁.trans h₂

theorem referenceCircleCosine_deriv_deriv (n : ℕ) (θ : ℝ) :
    deriv (deriv (fun t : ℝ => referenceCircleCosine n (t : AddCircle Real.pi))) θ =
      -(((2 * n : ℕ) : ℝ) ^ 2) * referenceCircleCosine n (θ : AddCircle Real.pi) := by
  cases n with
  | zero =>
    have hz : deriv (fun _ : ℝ => (1 : ℝ)) = fun _ => 0 := by
      funext x
      exact deriv_const x (1 : ℝ)
    change deriv (deriv (fun _ : ℝ => (1 : ℝ))) θ = -(((2 * 0 : ℕ) : ℝ) ^ 2) * 1
    rw [hz, deriv_const]
    norm_num
  | succ n =>
    have heq : (fun t : ℝ => referenceCircleCosine (n + 1) (t : AddCircle Real.pi)) =
        Radial.cosineMode (2 * (n + 1)) :=
      funext (referenceCircleCosine_succ_coe n)
    simpa only [heq, referenceCircleCosine_succ_coe] using
      Radial.deriv_deriv_cosineMode (2 * (n + 1)) θ

theorem radialAngularMean_deriv_mul {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfp : Function.Periodic f (2 * Real.pi))
    (hgp : Function.Periodic g (2 * Real.pi)) :
    radialAngularMean (fun θ => deriv f θ * g θ) =
      -radialAngularMean (fun θ => f θ * deriv g θ) := by
  have hfe : f (2 * Real.pi) = f 0 := by
    simpa only [zero_add] using hfp 0
  have hge : g (2 * Real.pi) = g 0 := by
    simpa only [zero_add] using hgp 0
  have hb := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := 2 * Real.pi)
    (fun x _ => (hf.differentiable (by simp) x).hasDerivAt)
    (fun x _ => (hg.differentiable (by simp) x).hasDerivAt)
    ((contDiff_infty_iff_deriv.mp hf).2.continuous.intervalIntegrable 0 (2 * Real.pi))
    ((contDiff_infty_iff_deriv.mp hg).2.continuous.intervalIntegrable 0 (2 * Real.pi))
  rw [hfe, hge, sub_self, zero_sub] at hb
  unfold radialAngularMean
  rw [hb]
  ring

theorem radialAngularMean_deriv_deriv_mul {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfp : Function.Periodic f (2 * Real.pi))
    (hgp : Function.Periodic g (2 * Real.pi)) :
    radialAngularMean (fun θ => deriv (deriv f) θ * g θ) =
      radialAngularMean (fun θ => f θ * deriv (deriv g) θ) := by
  calc
    _ = -radialAngularMean (fun θ => deriv f θ * deriv g θ) :=
      radialAngularMean_deriv_mul (contDiff_infty_iff_deriv.mp hf).2 hg
        (reference_periodic_deriv hfp) hgp
    _ = _ := by
      rw [radialAngularMean_deriv_mul hf (contDiff_infty_iff_deriv.mp hg).2
        hfp (reference_periodic_deriv hgp)]
      ring

theorem referenceCosineCoefficient_angularPartial_two
    {ψ : PolarPoint → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hp : Function.Periodic ψ (0, 2 * Real.pi)) (n : ℕ) (r : ℝ) :
    referenceCosineCoefficient (angularPartial (angularPartial ψ)) n r =
      -(((2 * n : ℕ) : ℝ) ^ 2) * referenceCosineCoefficient ψ n r := by
  have hθ : ContDiff ℝ ∞ (fun θ : ℝ => ψ (r, θ)) :=
    hψ.comp (contDiff_const.prodMk contDiff_id)
  have hθp : Function.Periodic (fun θ : ℝ => ψ (r, θ)) (2 * Real.pi) := by
    intro θ
    have hh := hp (r, θ)
    change ψ (r + 0, θ + 2 * Real.pi) = ψ (r, θ) at hh
    simpa only [add_zero] using hh
  have ht := reference_contDiff_angularPartial hψ
  have hd : deriv (fun θ : ℝ => ψ (r, θ)) =
      (fun θ => angularPartial ψ (r, θ)) := by
    funext θ
    exact (Radial.hasDerivAt_angularSlice (hψ.differentiable (by simp) (r, θ))).deriv
  have hdd : deriv (deriv (fun θ : ℝ => ψ (r, θ))) =
      (fun θ => angularPartial (angularPartial ψ) (r, θ)) := by
    rw [hd]
    funext θ
    exact (Radial.hasDerivAt_angularSlice (ht.differentiable (by simp) (r, θ))).deriv
  have hIBP := radialAngularMean_deriv_deriv_mul hθ (referenceCircleCosine_contDiff n)
    hθp (referenceCircleCosine_full_periodic n)
  rw [hdd] at hIBP
  simp_rw [referenceCircleCosine_deriv_deriv] at hIBP
  rw [referenceCosineCoefficient_eq_angularMean,
    referenceCosineCoefficient_eq_angularMean]
  calc
    _ = radialAngularMean (fun θ => ψ (r, θ) *
        (-(((2 * n : ℕ) : ℝ) ^ 2) *
          referenceCircleCosine n (θ : AddCircle Real.pi))) := hIBP
    _ = _ := by
      have heq : (fun θ : ℝ => ψ (r, θ) *
          (-(((2 * n : ℕ) : ℝ) ^ 2) *
            referenceCircleCosine n (θ : AddCircle Real.pi))) =
          (fun θ => -(((2 * n : ℕ) : ℝ) ^ 2) *
            (ψ (r, θ) * referenceCircleCosine n (θ : AddCircle Real.pi))) := by
        funext θ
        ring
      rw [heq, radialAngularMean_const_mul]

theorem radialAngularMean_add_of_continuous {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    radialAngularMean (fun θ => f θ + g θ) =
      radialAngularMean f + radialAngularMean g := by
  unfold radialAngularMean
  rw [intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  ring

/-- Fourier projection commutes with the actual radial Jacobi test expression. -/
theorem referenceCosineCoefficient_radialPDE {w : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) {ψ : PolarPoint → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hp : Function.Periodic ψ (0, 2 * Real.pi)) (n : ℕ) (r : ℝ) :
    referenceCosineCoefficient
      (fun x : PolarPoint => Radial.radialPDE w (fun t θ => ψ (t, θ)) x.1 x.2) n r =
      Radial.radialJacobi (((2 * n : ℕ) : ℝ) ^ 2) w
        (referenceCosineCoefficient ψ n) r := by
  have hr := reference_contDiff_radialPartial hψ
  have hrr := reference_contDiff_radialPartial hr
  have htt := reference_contDiff_angularPartial (reference_contDiff_angularPartial hψ)
  have hc := (referenceCircleCosine_contDiff n).continuous
  have hc₁ : Continuous (fun θ : ℝ =>
      radialPartial ψ (r, θ) * referenceCircleCosine n (θ : AddCircle Real.pi)) :=
    (hr.continuous.comp (continuous_const.prodMk continuous_id)).mul hc
  have hc₂ : Continuous (fun θ : ℝ =>
      radialPartial (radialPartial ψ) (r, θ) *
        referenceCircleCosine n (θ : AddCircle Real.pi)) :=
    (hrr.continuous.comp (continuous_const.prodMk continuous_id)).mul hc
  have hc₃ : Continuous (fun θ : ℝ =>
      angularPartial (angularPartial ψ) (r, θ) *
        referenceCircleCosine n (θ : AddCircle Real.pi)) :=
    (htt.continuous.comp (continuous_const.prodMk continuous_id)).mul hc
  have hcoef :
      referenceCosineCoefficient
        (fun x : PolarPoint => Radial.radialPDE w (fun t θ => ψ (t, θ)) x.1 x.2) n r =
      deriv w r * referenceCosineCoefficient (radialPartial ψ) n r +
        w r * referenceCosineCoefficient (radialPartial (radialPartial ψ)) n r +
        deriv w r / r * referenceCosineCoefficient (angularPartial (angularPartial ψ)) n r := by
    simp only [referenceCosineCoefficient_eq_angularMean]
    change radialAngularMean (fun θ =>
      Radial.radialPDE w (fun t φ => ψ (t, φ)) r θ *
        referenceCircleCosine n (θ : AddCircle Real.pi)) = _
    have heq : (fun θ : ℝ =>
        Radial.radialPDE w (fun t φ => ψ (t, φ)) r θ *
          referenceCircleCosine n (θ : AddCircle Real.pi)) =
        (fun θ => deriv w r *
            (radialPartial ψ (r, θ) * referenceCircleCosine n (θ : AddCircle Real.pi)) +
          w r * (radialPartial (radialPartial ψ) (r, θ) *
            referenceCircleCosine n (θ : AddCircle Real.pi)) +
          deriv w r / r * (angularPartial (angularPartial ψ) (r, θ) *
            referenceCircleCosine n (θ : AddCircle Real.pi))) := by
      funext θ
      rw [Radial.radialPDE_eq_polar_jets (x := (r, θ))
        (hw.differentiable (by simp) r) hψ]
      ring
    rw [heq,
      radialAngularMean_add_of_continuous
        (f := fun θ => deriv w r *
          (radialPartial ψ (r, θ) * referenceCircleCosine n (θ : AddCircle Real.pi)) +
          w r * (radialPartial (radialPartial ψ) (r, θ) *
            referenceCircleCosine n (θ : AddCircle Real.pi)))
        (g := fun θ => deriv w r / r *
          (angularPartial (angularPartial ψ) (r, θ) *
            referenceCircleCosine n (θ : AddCircle Real.pi)))
        ((continuous_const.mul hc₁).add (continuous_const.mul hc₂))
        (continuous_const.mul hc₃),
      radialAngularMean_add_of_continuous
        (f := fun θ => deriv w r *
          (radialPartial ψ (r, θ) * referenceCircleCosine n (θ : AddCircle Real.pi)))
        (g := fun θ => w r * (radialPartial (radialPartial ψ) (r, θ) *
          referenceCircleCosine n (θ : AddCircle Real.pi)))
        (continuous_const.mul hc₁) (continuous_const.mul hc₂)]
    simp only [radialAngularMean_const_mul]
  have hφ := contDiff_referenceCosineCoefficient hψ n
  have hφ' := (contDiff_infty_iff_deriv.mp hφ).2
  have hflux := (hw.differentiable (by simp) r).hasDerivAt.mul
    (hφ'.differentiable (by simp) r).hasDerivAt
  change HasDerivAt
    (fun t : ℝ => w t * deriv (referenceCosineCoefficient ψ n) t) _ r at hflux
  rw [hcoef, referenceCosineCoefficient_angularPartial_two hψ hp n r]
  unfold Radial.radialJacobi
  rw [hflux.deriv, deriv_deriv_referenceCosineCoefficient hψ n,
    deriv_referenceCosineCoefficient hψ n]
  ring

end ContinuousFlexibility.Statements
