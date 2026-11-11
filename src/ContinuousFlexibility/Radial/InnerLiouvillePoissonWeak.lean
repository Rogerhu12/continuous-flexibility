import ContinuousFlexibility.Radial.InnerLiouvilleFormTransport
import ContinuousFlexibility.Radial.InnerRadialWeakLinearity
import ContinuousFlexibility.Radial.InnerRadialPotentialGraph

/-!
# Actual model Poisson fields satisfy the physical weak equation

The model field may have nonzero endpoint values. The zero-endpoint
argument in the exact form identity is the genuine compact physical
test pulled back to the original model core. Symmetry then puts the
Poisson field in the solution slot, with its original scalar column.
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

theorem innerLiouvillePoissonWeak_on_core {V p column : ℝ → ℝ}
    (hV : Continuous V)
    (hcoeff : ∀ x ∈ Ioo a b, V x = liouvilleV0 s x - j ^ 2 * liouvilleRho R s x)
    {g P Pd : RadialL2} (scalar : ℝ)
    (hpp : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ p x)
    (hg : (g : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator column)
    (hP : (P : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator p)
    (hPd : (Pd : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator (deriv p))
    (heq : ∀ x ∈ Ioo a b, -deriv (deriv p) x + V x * p x + scalar * column x = 0)
    {T : InnerRadialH1Pair D} (hT : T ∈ InnerRadialH1Core D (R a) (R b)) :
    innerRadialWeakResidual D
      (innerLiouvilleFieldLift D hab.le hlam hR hs hp hcore hw U hU hv P,
        innerLiouvilleGradientLift D hab.le hlam hR hs hp hcore hw (P, Pd))
      (innerRadialPotentialMultiplier D hDw j hpos
        (innerLiouvilleFieldLift D hab.le hlam hR hs hp hcore hw U hU hv P))
      0 (innerLiouvilleColumnLift D hab.le hlam hR hs hp hcore hw g) scalar T = 0 := by
  obtain ⟨⟨f, d, q⟩, ht, he⟩ := innerRadialH1Core_energyLift_preimage D hab.le
    hlam hR hs hp hcore hw U hU hv hV hT
  have henergy := innerLiouville_energy_form D hab hlam hR hs hp hcore hw U hU hv hDw j hpos
    hV.continuousOn hcoeff (subset_closure ht) hpp hP hPd
  have hmodel := innerEnergyClosure_poisson_pairing hab hV.continuousOn hpp
    hg hP hPd heq (subset_closure ht)
  have hgout : (g : ℝ → ℝ) =ᵐ[volume.restrict ((Ioo a b)ᶜ)] (fun _ => 0) := by
    filter_upwards [ae_restrict_of_ae hg, ae_restrict_mem measurableSet_Ioo.compl] with x hx hout
    rw [hx, indicator_of_notMem hout]
  have hsym := (innerRadialPotentialMultiplier_class D hDw j hpos
    (innerLiouvilleFieldLift D hab.le hlam hR hs hp hcore hw U hU hv P)).inner_symm
      (innerRadialPotentialMultiplier_class D hDw j hpos
        (innerLiouvilleFieldLift D hab.le hlam hR hs hp hcore hw U hU hv f))
  rw [← he, innerLiouvilleEnergyLift_apply]
  change (⟪innerLiouvilleGradientLift D hab.le hlam hR hs hp hcore hw (P, Pd),
      innerLiouvilleGradientLift D hab.le hlam hR hs hp hcore hw (f, d)⟫_ℝ +
    ⟪innerRadialPotentialMultiplier D hDw j hpos
        (innerLiouvilleFieldLift D hab.le hlam hR hs hp hcore hw U hU hv P),
      innerLiouvilleFieldLift D hab.le hlam hR hs hp hcore hw U hU hv f⟫_ℝ) +
    scalar * ⟪innerLiouvilleColumnLift D hab.le hlam hR hs hp hcore hw g,
      innerLiouvilleFieldLift D hab.le hlam hR hs hp hcore hw U hU hv f⟫_ℝ -
    ⟪(0 : RadialModeL2 D),
      innerLiouvilleFieldLift D hab.le hlam hR hs hp hcore hw U hU hv f⟫_ℝ = 0
  rw [inner_zero_left, sub_zero, real_inner_comm
    (innerLiouvilleGradientLift D hab.le hlam hR hs hp hcore hw (f, d))
    (innerLiouvilleGradientLift D hab.le hlam hR hs hp hcore hw (P, Pd)),
    hsym, henergy, innerLiouvilleColumnLift_field_pairing D hab.le hlam hR hs hp hcore hw
      U hU hv g f hgout]
  linarith only [hmodel]

theorem innerLiouvillePoissonWeak_on_zeroDomain {V p column : ℝ → ℝ}
    (hV : Continuous V)
    (hcoeff : ∀ x ∈ Ioo a b, V x = liouvilleV0 s x - j ^ 2 * liouvilleRho R s x)
    {g P Pd : RadialL2} (scalar : ℝ)
    (hpp : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ p x)
    (hg : (g : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator column)
    (hP : (P : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator p)
    (hPd : (Pd : ℝ → ℝ) =ᵐ[volume] (Ioo a b).indicator (deriv p))
    (heq : ∀ x ∈ Ioo a b, -deriv (deriv p) x + V x * p x + scalar * column x = 0)
    {T : InnerRadialH1Pair D} (hT : T ∈ innerRadialH1Zero D (R a) (R b)) :
    innerRadialWeakResidual D
      (innerLiouvilleFieldLift D hab.le hlam hR hs hp hcore hw U hU hv P,
        innerLiouvilleGradientLift D hab.le hlam hR hs hp hcore hw (P, Pd))
      (innerRadialPotentialMultiplier D hDw j hpos
        (innerLiouvilleFieldLift D hab.le hlam hR hs hp hcore hw U hU hv P))
      0 (innerLiouvilleColumnLift D hab.le hlam hR hs hp hcore hw g) scalar T = 0 := by
  let L := innerRadialWeakResidual D
    (innerLiouvilleFieldLift D hab.le hlam hR hs hp hcore hw U hU hv P,
      innerLiouvilleGradientLift D hab.le hlam hR hs hp hcore hw (P, Pd))
    (innerRadialPotentialMultiplier D hDw j hpos
      (innerLiouvilleFieldLift D hab.le hlam hR hs hp hcore hw U hU hv P))
    0 (innerLiouvilleColumnLift D hab.le hlam hR hs hp hcore hw g) scalar
  have hsub : InnerRadialH1Core D (R a) (R b) ⊆ {T | L T = 0} := by
    intro T hT
    exact innerLiouvillePoissonWeak_on_core D hab hlam hR hs hp hcore hw U hU hv hDw j hpos
      hV hcoeff scalar hpp hg hP hPd heq hT
  exact closure_minimal hsub
    (isClosed_eq (innerRadialWeakResidual_continuous D _ _ _ _ _) continuous_const)
    ((mem_innerRadialH1Zero D (R a) (R b) T).mp hT)

end ContinuousFlexibility.Radial
