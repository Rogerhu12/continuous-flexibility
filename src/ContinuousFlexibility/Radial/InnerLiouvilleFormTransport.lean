import ContinuousFlexibility.Radial.InnerLiouvilleGradientPairing
import ContinuousFlexibility.Radial.InnerLiouvillePotentialTransport
import ContinuousFlexibility.Radial.InnerLiouvilleTestTransport
import ContinuousFlexibility.Radial.InnerLiouvilleBorderTransport
import ContinuousFlexibility.Radial.InnerEnergyFirstOrderPairing
import ContinuousFlexibility.Radial.InnerModelCoreCoordinates

/-!
# The actual closed weak form under Liouville transport

The normalized gradient produces the density drift. First-order
integration by parts on the original closed model domain restores
s''/s. Together with the actual signed-potential identity this gives
the original model form, with the same physical source and scalar row.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff InnerProductSpace

variable (D : ReferenceData) {R s : ℝ → ℝ} {a b lam : ℝ}
  (hab : a < b) (hlam : 0 < lam) (hR : ContDiff ℝ ∞ R)
  (hs : ContDiff ℝ ∞ s)
  (hp : ∀ x ∈ Icc a b, 0 < R x ∧ 0 < deriv R x ∧ 0 < s x)
  (hcore : Ioo (R a) (R b) ⊆ radialCore D)
  (hw : ∀ x ∈ Icc a b, D.w (R x) = lam * s x ^ 2 * deriv R x)
  (U : ℝ) (hU : 0 ≤ U)
  (hv : ∀ x ∈ Icc a b, |deriv R x / R x| ≤ U)
  (hDw : ContDiff ℝ ∞ D.w) (j : ℝ)
  (hpos : ∀ r ∈ Icc (R a) (R b), 0 < D.w r)

theorem innerLiouville_energy_form {V p : ℝ → ℝ}
    (hV : ContinuousOn V (Icc a b))
    (hcoeff : ∀ x ∈ Ioo a b, V x = liouvilleV0 s x - j ^ 2 * liouvilleRho R s x)
    {f d q P Pd : RadialL2}
    (hclosure : (f, d, q) ∈ closure (IntervalEnergyCore V a b))
    (hpp : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ p x)
    (hP : (P : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator p)
    (hPd : (Pd : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator (deriv p)) :
    ⟪innerLiouvilleGradientLift D hab.le hlam hR hs hp hcore hw (f, d),
      innerLiouvilleGradientLift D hab.le hlam hR hs hp hcore hw (P, Pd)⟫_ℝ +
      ⟪innerRadialPotentialMultiplier D hDw j hpos
          (innerLiouvilleFieldLift D hab.le hlam hR hs hp hcore hw U hU hv f),
        innerLiouvilleFieldLift D hab.le hlam hR hs hp hcore hw U hU hv P⟫_ℝ =
      ⟪d, Pd⟫_ℝ + ∫ x : ℝ, V x * f x * P x := by
  let M : RadialL2 →L[ℝ] RadialL2 :=
    innerLiouvilleDriftMultiplier s a b hs (fun x hx => (hp x hx).2.2)
  let N : RadialL2 := innerLiouvilleSource D hab.le hlam hR hs hp hcore hw U hU hv
    (innerRadialPotentialMultiplier D hDw j hpos
      (innerLiouvilleFieldLift D hab.le hlam hR hs hp hcore hw U hU hv P))
  let w : ℝ → ℝ := fun x => (deriv s x / s x) * p x
  have hwr : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ w x :=
    fun x hx => (innerLiouville_densityDrift_contDiffAt hs (hp x hx).2.2.ne').mul (hpp x hx)
  have hwd := innerDirichlet_indicator_memLp (innerDirichlet_deriv_continuousOn hwr)
  let Qd : RadialL2 := hwd.toLp ((Ioo a b).indicator (deriv w))
  have hQd : (Qd : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator (deriv w) :=
    MemLp.coeFn_toLp hwd
  have hQ : (M P : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator w := by
    filter_upwards [innerLiouvilleDriftMultiplier_ae s a b hs
      (fun x hx => (hp x hx).2.2) P, hP] with x hm hpx
    rw [hm, hpx]
    by_cases hx : x ∈ Ioo a b
    · simp only [innerLiouvilleModelVelocity, indicator_of_mem hx, w]
    · simp only [innerLiouvilleModelVelocity, indicator_of_notMem hx, zero_mul]
  have hibp := innerEnergyClosure_firstOrder_pairing hab hwr hQ hQd hclosure
  obtain ⟨Pv, hPv⟩ := innerWeakGreen_potential_class hV
    (fun x hx => (hpp x hx).continuousAt.continuousWithinAt) hP
  have hN := innerLiouvilleSource_potential_field_ae D hab.le hlam hR hs hp hcore hw U hU hv
    hDw j hpos P
  have hvector : Qd - M (Pd - M P) + N = Pv := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (Qd - M (Pd - M P)) N,
      Lp.coeFn_sub Qd (M (Pd - M P)), hQd,
      innerLiouvilleDriftMultiplier_ae s a b hs (fun x hx => (hp x hx).2.2) (Pd - M P),
      Lp.coeFn_sub Pd (M P), hPd, hQ, hN, hPv, hP]
      with x hadd hsub hqd hmt ht hpd hqp hn hpv hpx
    simp only [Pi.add_apply] at hadd
    simp only [Pi.sub_apply] at hsub ht
    rw [hadd, hsub, hqd, hmt, ht, hpd, hqp, hn, hpv, hpx]
    by_cases hx : x ∈ Ioo a b
    · simp only [innerLiouvilleModelVelocity, indicator_of_mem hx]
      have hdw := innerLiouville_densityDrift_prod_deriv
        (hs.differentiable (by simp) x)
        ((contDiff_infty_iff_deriv.mp hs).2.differentiable (by simp) x)
        (hp x (Ioo_subset_Icc_self hx)).2.2.ne'
        ((hpp x (Ioo_subset_Icc_self hx)).differentiableAt (by simp))
      change deriv w x - (deriv s x / s x) * (deriv p x - w x) +
        (-j ^ 2 * liouvilleRho R s x) * p x = V x * p x
      rw [hdw, hcoeff x hx]
      dsimp only [w]
      ring
    · simp only [innerLiouvilleModelVelocity, indicator_of_notMem hx,
        zero_mul, mul_zero, sub_self, sub_zero, zero_add]
  have hPdout : (Pd : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo a b)ᶜ)] (fun _ => 0) := by
    filter_upwards [ae_restrict_of_ae hPd, ae_restrict_mem measurableSet_Ioo.compl] with x hx hout
    rw [hx, indicator_of_notMem hout]
  have hgrad := innerLiouvilleGradientLift_pairing D hab.le hlam hR hs hp hcore hw f d P Pd hPdout
  have hpotential := innerLiouvillePotential_pairing D hab.le hlam hR hs hp hcore hw U hU hv
    hDw j hpos f P
  have hMp : ⟪M f, Pd - M P⟫_ℝ = ⟪f, M (Pd - M P)⟫_ℝ :=
    innerLiouvilleDriftMultiplier_inner s a b hs (fun x hx => (hp x hx).2.2) f (Pd - M P)
  have hVpair : (∫ x : ℝ, V x * f x * P x) = ⟪f, Pv⟫_ℝ :=
    (innerWeakGreen_potential_pairing hPv f).symm.trans (real_inner_comm f Pv)
  have hvpair := congrArg (fun z : RadialL2 => ⟪f, z⟫_ℝ) hvector
  rw [inner_add_right, inner_sub_right] at hvpair
  rw [hgrad, hpotential]
  change ⟪d - M f, Pd - M P⟫_ℝ + ⟪f, N⟫_ℝ = ⟪d, Pd⟫_ℝ + _
  rw [inner_sub_left, inner_sub_right, hMp, hVpair]
  linarith only [hibp, hvpair]

/-- The original model weak equation gives the physical weak equation
on each actual compact radial test. -/
theorem innerLiouvilleWeakResidual_on_core {V : ℝ → ℝ}
    (hV : Continuous V)
    (hcoeff : ∀ x ∈ Ioo a b, V x = liouvilleV0 s x - j ^ 2 * liouvilleRho R s x)
    {f d q g : RadialL2} (F : RadialModeL2 D) (scalar : ℝ)
    (hg : (g : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo a b)ᶜ)] (fun _ => 0))
    (hclosure : (f, d, q) ∈ closure (IntervalEnergyCore V a b))
    (hform : ∀ t ∈ closure (IntervalEnergyCore V a b),
      ⟪innerLiouvilleSource D hab.le hlam hR hs hp hcore hw U hU hv F - scalar • g,
        t.1⟫_ℝ = ⟪d, t.2.1⟫_ℝ + ∫ x : ℝ, V x * f x * t.1 x)
    {T : InnerRadialH1Pair D} (hT : T ∈ InnerRadialH1Core D (R a) (R b)) :
    innerRadialWeakResidual D
      (innerLiouvilleFieldLift D hab.le hlam hR hs hp hcore hw U hU hv f,
        innerLiouvilleGradientLift D hab.le hlam hR hs hp hcore hw (f, d))
      (innerRadialPotentialMultiplier D hDw j hpos
        (innerLiouvilleFieldLift D hab.le hlam hR hs hp hcore hw U hU hv f))
      F (innerLiouvilleColumnLift D hab.le hlam hR hs hp hcore hw g) scalar T = 0 := by
  obtain ⟨⟨P, Pd, Pq⟩, ht, he⟩ := innerRadialH1Core_energyLift_preimage D hab.le
    hlam hR hs hp hcore hw U hU hv hV hT
  obtain ⟨p, hpp, _hcp, _hpout, hP, hPd⟩ := innerModelCore_indicator_representatives hab ht
  have henergy := innerLiouville_energy_form D hab hlam hR hs hp hcore hw U hU hv hDw j hpos
    hV.continuousOn hcoeff hclosure (fun _ _ => hpp.contDiffAt) hP hPd
  have hmodel := hform (P, Pd, Pq) (subset_closure ht)
  dsimp only at hmodel
  rw [inner_sub_left, real_inner_smul_left] at hmodel
  rw [← he, innerLiouvilleEnergyLift_apply]
  change (⟪innerLiouvilleGradientLift D hab.le hlam hR hs hp hcore hw (f, d),
      innerLiouvilleGradientLift D hab.le hlam hR hs hp hcore hw (P, Pd)⟫_ℝ +
    ⟪innerRadialPotentialMultiplier D hDw j hpos
        (innerLiouvilleFieldLift D hab.le hlam hR hs hp hcore hw U hU hv f),
      innerLiouvilleFieldLift D hab.le hlam hR hs hp hcore hw U hU hv P⟫_ℝ) +
    scalar * ⟪innerLiouvilleColumnLift D hab.le hlam hR hs hp hcore hw g,
      innerLiouvilleFieldLift D hab.le hlam hR hs hp hcore hw U hU hv P⟫_ℝ -
    ⟪F, innerLiouvilleFieldLift D hab.le hlam hR hs hp hcore hw U hU hv P⟫_ℝ = 0
  rw [henergy, innerLiouvilleColumnLift_field_pairing D hab.le hlam hR hs hp hcore hw
    U hU hv g P hg, ← innerLiouvilleSource_inner D hab.le hlam hR hs hp hcore hw U hU hv F P]
  linarith only [hmodel]

/-- Continuity extends the transported equation to the full actual
physical zero-endpoint closure, not just smooth tests. -/
theorem innerLiouvilleWeakResidual_on_zeroDomain {V : ℝ → ℝ}
    (hV : Continuous V)
    (hcoeff : ∀ x ∈ Ioo a b, V x = liouvilleV0 s x - j ^ 2 * liouvilleRho R s x)
    {f d q g : RadialL2} (F : RadialModeL2 D) (scalar : ℝ)
    (hg : (g : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo a b)ᶜ)] (fun _ => 0))
    (hclosure : (f, d, q) ∈ closure (IntervalEnergyCore V a b))
    (hform : ∀ t ∈ closure (IntervalEnergyCore V a b),
      ⟪innerLiouvilleSource D hab.le hlam hR hs hp hcore hw U hU hv F - scalar • g,
        t.1⟫_ℝ = ⟪d, t.2.1⟫_ℝ + ∫ x : ℝ, V x * f x * t.1 x)
    {T : InnerRadialH1Pair D} (hT : T ∈ innerRadialH1Zero D (R a) (R b)) :
    innerRadialWeakResidual D
      (innerLiouvilleFieldLift D hab.le hlam hR hs hp hcore hw U hU hv f,
        innerLiouvilleGradientLift D hab.le hlam hR hs hp hcore hw (f, d))
      (innerRadialPotentialMultiplier D hDw j hpos
        (innerLiouvilleFieldLift D hab.le hlam hR hs hp hcore hw U hU hv f))
      F (innerLiouvilleColumnLift D hab.le hlam hR hs hp hcore hw g) scalar T = 0 := by
  let L := innerRadialWeakResidual D
    (innerLiouvilleFieldLift D hab.le hlam hR hs hp hcore hw U hU hv f,
      innerLiouvilleGradientLift D hab.le hlam hR hs hp hcore hw (f, d))
    (innerRadialPotentialMultiplier D hDw j hpos
      (innerLiouvilleFieldLift D hab.le hlam hR hs hp hcore hw U hU hv f))
    F (innerLiouvilleColumnLift D hab.le hlam hR hs hp hcore hw g) scalar
  have hcont : Continuous (fun T : InnerRadialH1Pair D => L T) := by
    change Continuous (fun T : InnerRadialH1Pair D =>
      ⟪innerLiouvilleGradientLift D hab.le hlam hR hs hp hcore hw (f, d), T.2⟫_ℝ +
      ⟪innerRadialPotentialMultiplier D hDw j hpos
        (innerLiouvilleFieldLift D hab.le hlam hR hs hp hcore hw U hU hv f), T.1⟫_ℝ +
      scalar * ⟪innerLiouvilleColumnLift D hab.le hlam hR hs hp hcore hw g, T.1⟫_ℝ -
      ⟪F, T.1⟫_ℝ)
    exact (((continuous_const.inner continuous_snd).add
      (continuous_const.inner continuous_fst)).add
      (continuous_const.mul (continuous_const.inner continuous_fst))).sub
      (continuous_const.inner continuous_fst)
  have hsub : InnerRadialH1Core D (R a) (R b) ⊆ {T | L T = 0} := by
    intro T hT
    exact innerLiouvilleWeakResidual_on_core D hab hlam hR hs hp hcore hw U hU hv hDw j hpos
      hV hcoeff F scalar hg hclosure hform hT
  exact closure_minimal hsub (isClosed_eq hcont continuous_const)
    ((mem_innerRadialH1Zero D (R a) (R b) T).mp hT)

end ContinuousFlexibility.Radial
