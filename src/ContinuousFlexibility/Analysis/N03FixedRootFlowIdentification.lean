import ContinuousFlexibility.Analysis.N03FixedCutoffRootCollar
import ContinuousFlexibility.Analysis.RootLocalizedCharacteristicSpeed
import ContinuousFlexibility.Analysis.RootRescaledStoredFlow

/-!
# The same controlled flow on a fixed root collar

A fixed cutoff gives an uncorrected physical band before the state or
initial angle is chosen. The stored N03 trajectories solve the original
root equation on that entire band. Uniqueness identifies every one with
the supplied controlled family. Its scale δ is unchanged: only the
normalized interval is restricted to [0, ρ / δ].
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def RootStoredFlowAgreementOn {S : PhysicalSpacesData}
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S)
    (z : AnnularState S × ℝ) (m : ℕ) (rightEnd : Bool) (δ η : ℝ)
    (Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ) : Prop :=
  let r := n01ComponentRoot C m rightEnd
  let σ := n01ComponentRootOrientation rightEnd
  ∀ ι x : ℝ, x ∈ Icc (0 : ℝ) η →
    Θ (x, (-σ * Real.sqrt δ) * x ^ (3 / 2 : ℝ)) 1 (L.minusFlow z m r ι) =
      L.minusFlow z m (r + σ * (δ * x)) ι

def N03FixedRootFlowIdentification
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (L : ReturnCorrectionData S) (base : ℕ) (ε : ℝ)
    (m : ℕ) (rightEnd : Bool) (g : ℝ → ℝ) {R : ℝ} (hR : 0 < R)
    (δ η : ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
    ∀ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
      N04FlowEquations
        (rootRescaledField
          (localizedRootDrift D S C (n01ComponentRoot C m rightEnd)
            (n01ComponentRootOrientation rightEnd) hR z)
          (localizedRootSpeed D S C g (n01ComponentRoot C m rightEnd)
            (n01ComponentRootOrientation rightEnd) hR z) δ) Θ →
      RootStoredFlowAgreementOn C L z m rightEnd δ η Θ

private theorem rootStoredFlowAgreement_of_fixed_band
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hL : N03Properties D T S C E L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (rightEnd : Bool)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) {R δ ρ : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (hρ : 0 < ρ)
    (hρw : ρ < C.right m - C.left m) (hρR : ρ ≤ R / 4)
    (hstrip : RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) (n01ComponentRoot C m rightEnd)
      (n01ComponentRootOrientation rightEnd) R)
    (hcoeff : ∀ t ∈ Icc (0 : ℝ) ρ, ∀ θ : ℝ,
      let p : PolarPoint := (n01ComponentRoot C m rightEnd +
        n01ComponentRootOrientation rightEnd * t, θ)
      (L.coefficients z).a p = (originalCoefficients D S C z).a p ∧
        (L.coefficients z).b p = (originalCoefficients D S C z).b p ∧
        (L.coefficients z).c p = (originalCoefficients D S C z).c p)
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hΘ : N04FlowEquations
      (rootRescaledField
        (localizedRootDrift D S C (n01ComponentRoot C m rightEnd)
          (n01ComponentRootOrientation rightEnd) hR z)
        (localizedRootSpeed D S C g (n01ComponentRoot C m rightEnd)
          (n01ComponentRootOrientation rightEnd) hR z) δ) Θ) :
    RootStoredFlowAgreementOn C L z m rightEnd δ (ρ / δ) Θ := by
  let r := n01ComponentRoot C m rightEnd
  let σ := n01ComponentRootOrientation rightEnd
  let η := ρ / δ
  have hη : 0 < η := div_pos hρ hδ
  have hscale : δ * η = ρ := by dsimp [η]; field_simp [hδ.ne']
  have hregular := contDiff_localizedRootFields_of_n01 hS hT hN hg hR hstrip
  have hperiod := periodic_localizedRootFields hS C g r σ hR z
  intro ι x hx
  let f : ℝ → ℝ := fun t => L.minusFlow z m (r + σ * t) ι
  have hstored := hL.2.2.2.2.1 z hz hs m ι
  have hmap : MapsTo (fun t : ℝ => r + σ * t)
      (Icc (0 : ℝ) ρ) (Icc (C.left m) (C.right m)) := by
    intro t ht
    have htwidth : t < C.right m - C.left m := ht.2.trans_lt hρw
    cases rightEnd <;>
      simp only [r, σ, n01ComponentRoot, n01ComponentRootOrientation,
        Bool.false_eq_true, ite_false, ite_true, one_mul, neg_one_mul] <;>
      constructor <;> linarith only [ht.1, htwidth]
  have hcont : ContinuousOn f (Icc (0 : ℝ) ρ) :=
    hstored.2.1.comp (continuous_const.add
      (continuous_const.mul continuous_id)).continuousOn hmap
  have hode : ∀ t ∈ Ioo (0 : ℝ) ρ,
      HasDerivAt f (rootPhysicalSpeed (localizedRootDrift D S C r σ hR z)
        (localizedRootSpeed D S C g r σ hR z) (-σ) (t, f t)) t := by
    intro t ht
    have htwidth : t < C.right m - C.left m := ht.2.trans hρw
    have hp : r + σ * t ∈ Ioo (C.left m) (C.right m) := by
      cases rightEnd <;>
        simp only [r, σ, n01ComponentRoot, n01ComponentRootOrientation,
          Bool.false_eq_true, ite_false, ite_true, one_mul, neg_one_mul] <;>
        constructor <;> linarith only [ht.1, htwidth]
    have hv :
        (L.coefficients z).a (r + σ * t, f t) =
            (originalCoefficients D S C z).a (r + σ * t, f t) ∧
          (L.coefficients z).b (r + σ * t, f t) =
            (originalCoefficients D S C z).b (r + σ * t, f t) ∧
          (L.coefficients z).c (r + σ * t, f t) =
            (originalCoefficients D S C z).c (r + σ * t, f t) :=
      hcoeff t (Ioo_subset_Icc_self ht) (f t)
    have heq : minusCharacteristicSpeed (L.coefficients z) (r + σ * t, f t) =
        minusCharacteristicSpeed (originalCoefficients D S C z) (r + σ * t, f t) := by
      simp only [minusCharacteristicSpeed, hv.1, hv.2.1, hv.2.2]
    have hraw := rootPhysicalSpeed_localization_eq_oriented_polarMinus
      (contDiff_stateProfile_of_n01 hS hT hN z.1)
      (contDiff_stateHeight_of_n01 hS hT hN z) hR hstrip
      (p := (t, f t)) ⟨ht.1.le, ht.2.le.trans hρR⟩
    have hraw' : rootPhysicalSpeed (localizedRootDrift D S C r σ hR z)
        (localizedRootSpeed D S C g r σ hR z) (-σ) (t, f t) =
        σ * minusCharacteristicSpeed (originalCoefficients D S C z) (r + σ * t, f t) :=
      hraw
    have hlin : HasDerivAt (fun s : ℝ => r + σ * s) σ t := by
      simpa only [mul_one, id_eq] using ((hasDerivAt_id t).const_mul σ).const_add r
    have hd := (hstored.2.2.1 (r + σ * t) hp).comp t hlin
    have hf : (fun u => L.minusFlow z m u ι) ∘ (fun s : ℝ => r + σ * s) = f := by
      funext s
      exact Function.comp_apply
    rw [hf] at hd
    change HasDerivAt f
      (minusCharacteristicSpeed (L.coefficients z) (r + σ * t, f t) * σ) t at hd
    apply hd.congr_deriv
    rw [hraw', heq]
    ring
  have hinit : f 0 = L.minusFlow z m r ι := by simp only [f, mul_zero, add_zero]
  exact rootRescaledFlow_eq_storedTrajectory (f := f) hη hδ Real.pi_ne_zero
    hregular.1 hregular.2 hperiod.1 hperiod.2 hΘ hinit
    (by simpa only [hscale] using hcont)
    (fun t ht => hode t (by simpa only [hscale] using ht)) hx

/-- The normalized subcollar is fixed before every state and initial
angle. Every supplied actual flow, in particular the one whose jets
were already controlled, agrees with the stored flow there. -/
theorem n03_exists_fixed_rootFlow_identification
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hL : N03Properties D T S C E L base ε)
    (χ : ℕ → ℝ → ℝ)
    (hend : ∀ m, χ m =ᶠ[𝓝 (C.left m)] (fun _ => 0) ∧
      χ m =ᶠ[𝓝 (C.right m)] (fun _ => 1))
    (hcoeff : L.coefficients = returnCorrectedCoefficients D S C χ)
    (m : ℕ) (rightEnd : Bool) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hδR : δ ≤ R / 4)
    (hstrip : ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
        (stateHeight D S C z) (n01ComponentRoot C m rightEnd)
        (n01ComponentRootOrientation rightEnd) R) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧
      δ * η < C.right m - C.left m ∧ δ * η ≤ R / 4 ∧
      N03FixedRootFlowIdentification D S C L base ε m rightEnd g hR δ η := by
  obtain ⟨ρ, hρ, hρδ, hρw, _, hband⟩ :=
    n01_exists_fixedCutoff_root_collar hN χ hend m rightEnd hδ
  have hη : 0 < ρ / δ := div_pos hρ hδ
  have hηone : ρ / δ < 1 :=
    (div_lt_iff₀ hδ).mpr (by simpa only [one_mul] using hρδ)
  have hscale : δ * (ρ / δ) = ρ := by field_simp [hδ.ne']
  refine ⟨ρ / δ, hη, hηone, (by simpa only [hscale] using hρw),
    (by simpa only [hscale] using hρδ.le.trans hδR), ?_⟩
  intro z hz hs Θ hΘ
  apply rootStoredFlowAgreement_of_fixed_band hS hT hN hL hz hs m rightEnd
    hg hR hδ hρ hρw (hρδ.le.trans hδR) (hstrip z hz hs) (hΘ := hΘ)
  intro t ht θ
  let p : PolarPoint := (n01ComponentRoot C m rightEnd +
    n01ComponentRootOrientation rightEnd * t, θ)
  have hv := hband z θ t ht
  exact ⟨(congrArg (fun F => (F z).a p) hcoeff).trans hv.1,
    (congrArg (fun F => (F z).b p) hcoeff).trans hv.2.1,
    (congrArg (fun F => (F z).c p) hcoeff).trans hv.2.2⟩

end ContinuousFlexibility.Analysis
