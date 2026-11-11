import ContinuousFlexibility.Analysis.CharacteristicODEUniqueness
import ContinuousFlexibility.Analysis.RootPhysicalTransport
import ContinuousFlexibility.Analysis.SmoothPeriodicScalarFlowEndpoint

/-!
# Identifying a stored physical root flow with the constructed flow

The stored physical family is assumed only continuous in radial time on
the closed collar, with the correct initial value and the actual ODE on
its interior. Its angular regularity is not an input. Ordinary uniqueness
identifies it with the physical Picard flow, and hence with the smooth
root-regularized endpoint flow.

The resulting angular derivatives, circle inverses, and interior joint
smoothness concern the original stored family. The coefficient inputs are
the smooth periodic factors in the actual root speed
d(r, θ) + σ sqrt(r) c₀(r, θ). Producing such extended factors from a
corrected physical coefficient germ remains a separate construction.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Closed continuity and the interior root ODE suffice for uniqueness.
There is no differentiability hypothesis at the turning endpoint. -/
theorem n04b_rootPhysicalFlow_unique
    {d c₀ : PolarPoint → ℝ} {f g : ℝ → ℝ} {R σ : ℝ}
    (hR : 0 < R) (hd : ContDiff ℝ ∞ d) (hc₀ : ContDiff ℝ ∞ c₀)
    (hf : ContinuousOn f (Icc (0 : ℝ) R))
    (hdf : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt f (rootPhysicalSpeed d c₀ σ (r, f r)) r)
    (hg : ContinuousOn g (Icc (0 : ℝ) R))
    (hdg : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt g (rootPhysicalSpeed d c₀ σ (r, g r)) r)
    (hinit : f 0 = g 0) : EqOn f g (Icc (0 : ℝ) R) := by
  apply ode_solution_unique_of_separated_radial_speed
    (A := d) (B := fun p => -σ * c₀ p) (k := Real.sqrt)
    hR Real.continuous_sqrt.continuousOn
    (fun p _ => hd.contDiffAt)
    (fun p _ => (contDiff_const.mul hc₀).contDiffAt)
    hf _ hg _ hinit
  · intro r hr
    apply (hdf r hr).congr_deriv
    dsimp only [rootPhysicalSpeed]
    ring
  · intro r hr
    apply (hdg r hr).congr_deriv
    dsimp only [rootPhysicalSpeed]
    ring

/-- The actual regularized endpoint equals any stored physical trajectory
satisfying the ordinary open-interval equation and closed continuity. -/
theorem n04b_rootRegularizedFlow_eq_storedFlow
    {d c₀ : PolarPoint → ℝ} {T R σ : ℝ}
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ} {Φ : ℝ → ℝ → ℝ}
    (hR : 0 < R) (hT : T ≠ 0)
    (hd : ContDiff ℝ ∞ d) (hc₀ : ContDiff ℝ ∞ c₀)
    (hdperiod : ∀ r, Function.Periodic (fun θ => d (r, θ)) T)
    (hc₀period : ∀ r, Function.Periodic (fun θ => c₀ (r, θ)) T)
    (hinit : ∀ p θ, Θ p 0 θ = θ)
    (hflow : ∀ p θ t, t ∈ Icc (0 : ℝ) 1 →
      HasDerivWithinAt (fun s => Θ p s θ)
        (rootRegularizedField d c₀ (t, (p, Θ p t θ)))
        (Icc (0 : ℝ) 1) t)
    (hΦinit : ∀ θ, Φ θ 0 = θ)
    (hΦcont : ∀ θ, ContinuousOn (Φ θ) (Icc (0 : ℝ) R))
    (hΦflow : ∀ θ r, r ∈ Ioo (0 : ℝ) R →
      HasDerivAt (Φ θ) (rootPhysicalSpeed d c₀ σ (r, Φ θ r)) r)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) R) (θ : ℝ) :
    Θ (x, σ * x ^ (3 / 2 : ℝ)) 1 θ = Φ θ x := by
  obtain ⟨Ψ, hΨinit, hΨflow, _⟩ :=
    exists_rootPhysicalFlow_on_Icc hR.le hT hd hc₀ hdperiod hc₀period σ
  have heq : EqOn (Ψ θ) (Φ θ) (Icc (0 : ℝ) R) :=
    n04b_rootPhysicalFlow_unique hR hd hc₀
      (HasDerivWithinAt.continuousOn (hΨflow θ))
      (fun r hr => (hΨflow θ r (Ioo_subset_Icc_self hr)).hasDerivAt
        (Icc_mem_nhds hr.1 hr.2))
      (hΦcont θ) (hΦflow θ)
      ((hΨinit θ).trans (hΦinit θ).symm)
  exact (rootRegularizedFlow_eq_physicalFlow hT hd hc₀ hdperiod hc₀period
    hinit hflow hΨinit hΨflow hx θ).trans (heq hx)

/-- Construct a smooth periodic regularized flow which identifies the
stored physical family on its entire closed collar. In particular, the
positive endpoint angular derivative is a conclusion of the actual ODE. -/
theorem n04b_exists_rootFlow_identification
    {d c₀ : PolarPoint → ℝ} {T R σ : ℝ} {Φ : ℝ → ℝ → ℝ}
    (hR : 0 < R) (hT : T ≠ 0)
    (hd : ContDiff ℝ ∞ d) (hc₀ : ContDiff ℝ ∞ c₀)
    (hdperiod : ∀ r, Function.Periodic (fun θ => d (r, θ)) T)
    (hc₀period : ∀ r, Function.Periodic (fun θ => c₀ (r, θ)) T)
    (hΦinit : ∀ θ, Φ θ 0 = θ)
    (hΦcont : ∀ θ, ContinuousOn (Φ θ) (Icc (0 : ℝ) R))
    (hΦflow : ∀ θ r, r ∈ Ioo (0 : ℝ) R →
      HasDerivAt (Φ θ) (rootPhysicalSpeed d c₀ σ (r, Φ θ r)) r) :
    ∃ Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ,
      (∀ p θ, Θ p 0 θ = θ) ∧
      (∀ p θ t, t ∈ Icc (0 : ℝ) 1 →
        HasDerivWithinAt (fun s => Θ p s θ)
          (rootRegularizedField d c₀ (t, (p, Θ p t θ)))
          (Icc (0 : ℝ) 1) t) ∧
      ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => Θ z.1 1 z.2) ∧
      (∀ p θ, 0 < deriv (fun η => Θ p 1 η) θ) ∧
      (∀ p θ, Θ p 1 (θ + T) = Θ p 1 θ + T) ∧
      (∀ x ∈ Icc (0 : ℝ) R, ∀ θ,
        Φ θ x = Θ (x, σ * x ^ (3 / 2 : ℝ)) 1 θ) := by
  obtain ⟨Θ, hi, hf, hp, _, hs, hpos⟩ :=
    exists_smooth_periodicScalarFlowFamily
      (F := rootRegularizedField d c₀) (a := 0) (b := 1)
      zero_le_one hT (contDiff_rootRegularizedField hd hc₀)
      (fun t _ p => rootRegularizedField_periodic hdperiod hc₀period t p)
  refine ⟨Θ, hi, hf, hs, hpos,
    fun p θ => hp p θ 1 ⟨zero_le_one, le_rfl⟩, ?_⟩
  intro x hx θ
  exact (n04b_rootRegularizedFlow_eq_storedFlow hR hT hd hc₀
    hdperiod hc₀period hi hf hΦinit hΦcont hΦflow hx θ).symm

/-- Every angular slice of the stored physical flow is a genuine smooth
increasing circle lift. Its chosen inverse is smooth, has positive actual
derivative, and satisfies both inverse identities, including at the root. -/
theorem n04b_rootStoredFlow_angular_geometry
    {d c₀ : PolarPoint → ℝ} {T R σ : ℝ} {Φ : ℝ → ℝ → ℝ}
    (hR : 0 < R) (hT : T ≠ 0)
    (hd : ContDiff ℝ ∞ d) (hc₀ : ContDiff ℝ ∞ c₀)
    (hdperiod : ∀ r, Function.Periodic (fun θ => d (r, θ)) T)
    (hc₀period : ∀ r, Function.Periodic (fun θ => c₀ (r, θ)) T)
    (hΦinit : ∀ θ, Φ θ 0 = θ)
    (hΦcont : ∀ θ, ContinuousOn (Φ θ) (Icc (0 : ℝ) R))
    (hΦflow : ∀ θ r, r ∈ Ioo (0 : ℝ) R →
      HasDerivAt (Φ θ) (rootPhysicalSpeed d c₀ σ (r, Φ θ r)) r)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) R) :
    let f : ℝ → ℝ := fun θ => Φ θ x
    let g : ℝ → ℝ := Function.invFun f
    ContDiff ℝ ∞ f ∧ (∀ θ, 0 < deriv f θ) ∧
      (∀ θ, f (θ + T) = f θ + T) ∧ Function.Bijective f ∧
      ContDiff ℝ ∞ g ∧ (∀ θ, 0 < deriv g θ) ∧
      (∀ θ, f (g θ) = θ ∧ g (f θ) = θ) ∧
      (∀ θ, g (θ + T) = g θ + T) := by
  obtain ⟨Θ, _, _, hs, hpos, hp, he⟩ :=
    n04b_exists_rootFlow_identification hR hT hd hc₀ hdperiod hc₀period
      hΦinit hΦcont hΦflow
  let p : ℝ × ℝ := (x, σ * x ^ (3 / 2 : ℝ))
  let F : (ℝ × ℝ) × ℝ → ℝ := fun z => Θ z.1 1 z.2
  have hmap : (fun θ => Φ θ x) = (fun θ => F (p, θ)) :=
    funext (he x hx)
  have hFs : ContDiff ℝ ∞ (fun θ => Φ θ x) := by
    rw [hmap]
    exact hs.comp (contDiff_const.prodMk contDiff_id)
  have hFpos : ∀ θ, 0 < deriv (fun η => Φ η x) θ := by
    intro θ
    rw [hmap]
    exact hpos p θ
  have hFperiod : ∀ θ, Φ (θ + T) x = Φ θ x + T := by
    intro θ
    rw [he x hx (θ + T), he x hx θ]
    exact hp p θ
  have hFp : ∀ z : (ℝ × ℝ) × ℝ,
      0 < deriv (fun θ => F (z.1, θ)) z.2 :=
    fun z => hpos z.1 z.2
  have hbij : Function.Bijective (fun θ => Φ θ x) :=
    ⟨(strictMono_of_deriv_pos hFpos).injective,
      surjective_of_continuous_periodic_lift hT hFs.continuous hFperiod⟩
  have hGs : ContDiff ℝ ∞ (Function.invFun (fun θ => Φ θ x)) := by
    rw [hmap]
    exact (contDiff_parameterizedCircleInverse hT hs hFp hp).comp
      (contDiff_const.prodMk contDiff_id)
  refine ⟨hFs, hFpos, hFperiod, hbij, hGs, ?_, ?_, ?_⟩
  · intro θ
    change 0 < deriv (Function.invFun (fun η => Φ η x)) θ
    rw [hmap]
    exact parameterizedCircleInverse_deriv_pos hT hs hFp hp p θ
  · intro θ
    exact ⟨Function.rightInverse_invFun hbij.2 θ,
      Function.leftInverse_invFun hbij.1 θ⟩
  · intro θ
    change Function.invFun (fun η => Φ η x) (θ + T) =
      Function.invFun (fun η => Φ η x) θ + T
    rw [hmap]
    exact parameterizedCircleInverse_period_add hT hs hFp hp p θ

/-- The original stored flow is jointly smooth at all positive interior
radial points. No radial smoothness at the square-root endpoint is claimed. -/
theorem n04b_rootStoredFlow_contDiffOn
    {d c₀ : PolarPoint → ℝ} {T R σ : ℝ} {Φ : ℝ → ℝ → ℝ}
    (hR : 0 < R) (hT : T ≠ 0)
    (hd : ContDiff ℝ ∞ d) (hc₀ : ContDiff ℝ ∞ c₀)
    (hdperiod : ∀ r, Function.Periodic (fun θ => d (r, θ)) T)
    (hc₀period : ∀ r, Function.Periodic (fun θ => c₀ (r, θ)) T)
    (hΦinit : ∀ θ, Φ θ 0 = θ)
    (hΦcont : ∀ θ, ContinuousOn (Φ θ) (Icc (0 : ℝ) R))
    (hΦflow : ∀ θ r, r ∈ Ioo (0 : ℝ) R →
      HasDerivAt (Φ θ) (rootPhysicalSpeed d c₀ σ (r, Φ θ r)) r) :
    ContDiffOn ℝ ∞ (fun p : PolarPoint => Φ p.2 p.1)
      (Ioo (0 : ℝ) R ×ˢ univ) := by
  obtain ⟨Θ, _, _, hs, _, _, he⟩ :=
    n04b_exists_rootFlow_identification hR hT hd hc₀ hdperiod hc₀period
      hΦinit hΦcont hΦflow
  let G : ℝ × ℝ × ℝ → ℝ := fun q => Θ (q.1, q.2.1) 1 q.2.2
  have hG : ContDiff ℝ ∞ G :=
    hs.comp ((contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd)
  have hc : ContDiffOn ℝ ∞ (rootCharacteristicCoordinate G σ)
      (Ioo (0 : ℝ) R ×ˢ univ) :=
    fun p hp => (contDiffAt_rootCharacteristicCoordinate hG hp.1.1).contDiffWithinAt
  apply hc.congr
  intro p hp
  exact he p.1 (Ioo_subset_Icc_self hp.1) p.2

/-- Odd drift and even square-root factor identify the two stored
characteristic families by reflection. This uses their actual ODEs. -/
theorem n04b_rootStoredFlow_reflect
    {d c₀ : PolarPoint → ℝ} {Φplus Φminus : ℝ → ℝ → ℝ} {R σ : ℝ}
    (hR : 0 < R) (hd : ContDiff ℝ ∞ d) (hc₀ : ContDiff ℝ ∞ c₀)
    (hdodd : ∀ r θ, d (r, -θ) = -d (r, θ))
    (hceven : ∀ r θ, c₀ (r, -θ) = c₀ (r, θ))
    (hplus_init : ∀ θ, Φplus θ 0 = θ)
    (hminus_init : ∀ θ, Φminus θ 0 = θ)
    (hplus_cont : ∀ θ, ContinuousOn (Φplus θ) (Icc (0 : ℝ) R))
    (hminus_cont : ∀ θ, ContinuousOn (Φminus θ) (Icc (0 : ℝ) R))
    (hplus_flow : ∀ θ r, r ∈ Ioo (0 : ℝ) R →
      HasDerivAt (Φplus θ) (rootPhysicalSpeed d c₀ σ (r, Φplus θ r)) r)
    (hminus_flow : ∀ θ r, r ∈ Ioo (0 : ℝ) R →
      HasDerivAt (Φminus θ) (rootPhysicalSpeed d c₀ (-σ) (r, Φminus θ r)) r)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) R) (θ : ℝ) :
    Φminus (-θ) x = -Φplus θ x := by
  apply n04b_rootPhysicalFlow_unique hR hd hc₀
    (hminus_cont (-θ)) (hminus_flow (-θ)) (hplus_cont θ).neg _ _ hx
  · intro r hr
    apply (hplus_flow θ r hr).neg.congr_deriv
    simp only [rootPhysicalSpeed, Pi.neg_apply, hdodd, hceven]
    ring
  · simp only [Pi.neg_apply, hminus_init, hplus_init]

end ContinuousFlexibility.Analysis
