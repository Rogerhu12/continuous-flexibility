import ContinuousFlexibility.Analysis.N04bRootFlowIdentification
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Closed joint regularity of the actual root flow and its inverse

The complete Picard representation retains joint continuity in time,
which is needed by the genuine boundary derivative theorem. The actual
stored flow and its chosen inverse are continuous jointly on the closed
physical collar. The inverse is jointly smooth at positive radial
points. All statements follow from the actual root equation.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The physical root substitution is continuous even at its zero
radial endpoint. -/
theorem n04b_rootCharacteristicCoordinate_continuous
    {G : ℝ × ℝ × ℝ → ℝ} (hG : Continuous G) (σ : ℝ) :
    Continuous (rootCharacteristicCoordinate G σ) := by
  have hp : Continuous (fun p : PolarPoint => p.1 ^ (3 / 2 : ℝ)) :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 2)).comp continuous_fst
  exact hG.comp (continuous_fst.prodMk
    ((continuous_const.mul hp).prodMk continuous_snd))

section StoredRootFlow

variable {d c₀ : PolarPoint → ℝ} {T R σ : ℝ} {Φ : ℝ → ℝ → ℝ}
    (hR : 0 < R) (hT : T ≠ 0)
    (hd : ContDiff ℝ ∞ d) (hc₀ : ContDiff ℝ ∞ c₀)
    (hdperiod : ∀ r, Function.Periodic (fun θ => d (r, θ)) T)
    (hc₀period : ∀ r, Function.Periodic (fun θ => c₀ (r, θ)) T)
    (hΦinit : ∀ θ, Φ θ 0 = θ)
    (hΦcont : ∀ θ, ContinuousOn (Φ θ) (Icc (0 : ℝ) R))
    (hΦflow : ∀ θ r, r ∈ Ioo (0 : ℝ) R →
      HasDerivAt (Φ θ) (rootPhysicalSpeed d c₀ σ (r, Φ θ r)) r)

include hR hT hd hc₀ hdperiod hc₀period hΦinit hΦcont hΦflow

/-- The constructed regularized family retains its genuine time
continuity as well as its smooth endpoint and its identification with
the stored physical flow on the entire closed collar. -/
theorem n04b_exists_complete_rootFlow_identification :
    ∃ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
      (∀ p θ, Θ p 0 θ = θ) ∧
      (∀ p θ t, t ∈ Icc (0 : ℝ) 1 →
        HasDerivWithinAt (fun s => Θ p s θ)
          (rootRegularizedField d c₀ (t, (p, Θ p t θ)))
          (Icc (0 : ℝ) 1) t) ∧
      ContinuousOn (fun q : ((ℝ × ℝ) × ℝ) × ℝ => Θ q.1.1 q.2 q.1.2)
        (univ ×ˢ Icc (0 : ℝ) 1) ∧
      ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => Θ q.1 1 q.2) ∧
      (∀ p θ, 0 < deriv (fun η => Θ p 1 η) θ) ∧
      (∀ p θ, Θ p 1 (θ + T) = Θ p 1 θ + T) ∧
      (∀ x ∈ Icc (0 : ℝ) R, ∀ θ,
        Φ θ x = Θ (x, σ * x ^ (3 / 2 : ℝ)) 1 θ) := by
  obtain ⟨Θ, hi, hf, hp, hcont, hs, hpos⟩ :=
    exists_smooth_periodicScalarFlowFamily
      (F := rootRegularizedField d c₀) (a := 0) (b := 1)
      zero_le_one hT (contDiff_rootRegularizedField hd hc₀)
      (fun t _ p => rootRegularizedField_periodic hdperiod hc₀period t p)
  refine ⟨Θ, hi, hf, hcont, hs, hpos,
    fun p θ => hp p θ 1 ⟨zero_le_one, le_rfl⟩, ?_⟩
  intro x hx θ
  exact (n04b_rootRegularizedFlow_eq_storedFlow hR hT hd hc₀ hdperiod hc₀period
    hi hf hΦinit hΦcont hΦflow hx θ).symm

/-- Closed joint continuity and open joint smoothness for the actual
chosen inverse. No joint regularity of the stored family is assumed. -/
theorem n04b_rootStoredFlow_joint_regularity :
    ContinuousOn (fun p : PolarPoint => Φ p.2 p.1)
        (Icc (0 : ℝ) R ×ˢ univ) ∧
      ContinuousOn (fun p : PolarPoint => Function.invFun (fun θ => Φ θ p.1) p.2)
        (Icc (0 : ℝ) R ×ˢ univ) ∧
      ContDiffOn ℝ ∞ (fun p : PolarPoint => Function.invFun (fun θ => Φ θ p.1) p.2)
        (Ioo (0 : ℝ) R ×ˢ univ) := by
  obtain ⟨Θ, _, _, _, hEndpoint, hpositive, hperiod, heq⟩ :=
    n04b_exists_complete_rootFlow_identification hR hT hd hc₀ hdperiod hc₀period
      hΦinit hΦcont hΦflow
  let F : ℝ × ℝ × ℝ → ℝ := fun q => Θ (q.1, q.2.1) 1 q.2.2
  let G : ℝ × ℝ × ℝ → ℝ := rootInverseCoordinate Θ id
  have hF : ContDiff ℝ ∞ F :=
    hEndpoint.comp ((contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd)
  have hG : ContDiff ℝ ∞ G :=
    contDiff_rootInverseCoordinate hT hEndpoint hpositive hperiod contDiff_id
  have hforward :
      EqOn (fun p : PolarPoint => Φ p.2 p.1) (rootCharacteristicCoordinate F σ)
        (Icc (0 : ℝ) R ×ˢ univ) :=
    fun p hp => heq p.1 hp.1 p.2
  have hinverse :
      EqOn (fun p : PolarPoint => Function.invFun (fun θ => Φ θ p.1) p.2)
        (rootCharacteristicCoordinate G σ) (Icc (0 : ℝ) R ×ˢ univ) := by
    intro p hp
    change Function.invFun (fun θ => Φ θ p.1) p.2 =
      Function.invFun (fun θ => Θ (p.1, σ * p.1 ^ (3 / 2 : ℝ)) 1 θ) p.2
    rw [show (fun θ => Φ θ p.1) =
      (fun θ => Θ (p.1, σ * p.1 ^ (3 / 2 : ℝ)) 1 θ) from funext (heq p.1 hp.1)]
  refine ⟨(n04b_rootCharacteristicCoordinate_continuous hF.continuous σ).continuousOn.congr
    hforward, (n04b_rootCharacteristicCoordinate_continuous hG.continuous σ).continuousOn.congr
    hinverse, ?_⟩
  have hs : ContDiffOn ℝ ∞ (rootCharacteristicCoordinate G σ)
      (Ioo (0 : ℝ) R ×ˢ univ) :=
    fun p hp => (contDiffAt_rootCharacteristicCoordinate hG hp.1.1).contDiffWithinAt
  apply hs.congr
  intro p hp
  exact hinverse ⟨Ioo_subset_Icc_self hp.1, hp.2⟩

end StoredRootFlow

end ContinuousFlexibility.Analysis
