import ContinuousFlexibility.Analysis.RootRescaledStoredFlow
import ContinuousFlexibility.Analysis.RootLocalizedCharacteristicSpeed
import ContinuousFlexibility.Analysis.N01ActualRootGeometry

/-!
# The same controlled root flow identifies the actual N03 trajectories

The frozen N03 germ at one root point is pulled back along the actual
stored trajectory, using its closed-endpoint continuity. This gives a
positive comparison radius for each state and initial angle. It is only
an identification radius: the previously chosen common δ and controlled
family Θ are unchanged. Both roots use the same positive sqrt(δ) scale.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

private theorem minusCharacteristicSpeed_eventuallyEq
    {A B : SymmetricCoefficients} {p : PolarPoint}
    (ha : A.a =ᶠ[𝓝 p] B.a) (hb : A.b =ᶠ[𝓝 p] B.b)
    (hc : A.c =ᶠ[𝓝 p] B.c) :
    minusCharacteristicSpeed A =ᶠ[𝓝 p] minusCharacteristicSpeed B := by
  filter_upwards [ha, hb, hc] with q hqa hqb hqc
  simp only [minusCharacteristicSpeed, hqa, hqb, hqc]

/-- A true local root equation for each actual stored trajectory. No
angular regularity or uniformity of the N03 germ is assumed. -/
theorem n03_exists_local_rootTrajectory_equation
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss base₃ : ℕ} {ε ε₃ : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hL : N03Properties D T S C E L base₃ ε₃)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base₃ ε₃)
    (hs : stateSector S z.1) (m : ℕ) (rightEnd : Bool)
    {g : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hstrip : RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) (n01ComponentRoot C m rightEnd)
      (n01ComponentRootOrientation rightEnd) R) (ι : ℝ) :
    let r := n01ComponentRoot C m rightEnd
    let σ := n01ComponentRootOrientation rightEnd
    let f : ℝ → ℝ := fun t => L.minusFlow z m (r + σ * t) ι
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R / 4 ∧
      ContinuousOn f (Icc (0 : ℝ) ρ) ∧
      ∀ t ∈ Ioo (0 : ℝ) ρ,
        HasDerivAt f
          (rootPhysicalSpeed (localizedRootDrift D S C r σ hR z)
            (localizedRootSpeed D S C g r σ hR z) (-σ) (t, f t)) t := by
  let r := n01ComponentRoot C m rightEnd
  let σ := n01ComponentRootOrientation rightEnd
  let f : ℝ → ℝ := fun t => L.minusFlow z m (r + σ * t) ι
  let w := C.right m - C.left m
  have horder := (hN.2.2.2.1).1 m
  have hw : 0 < w := sub_pos.mpr horder.2.1
  have hstored := hL.2.2.2.2.1 z hz hs m ι
  have hmap : MapsTo (fun t : ℝ => r + σ * t)
      (Icc (0 : ℝ) w) (Icc (C.left m) (C.right m)) := by
    intro t ht
    have htw : t ≤ C.right m - C.left m := ht.2
    cases rightEnd <;>
      simp only [r, σ, n01ComponentRoot, n01ComponentRootOrientation,
        Bool.false_eq_true, ite_false, ite_true, one_mul, neg_one_mul] <;>
      constructor <;> linarith [ht.1, htw]
  have hlinear : Continuous (fun t : ℝ => r + σ * t) :=
    continuous_const.add (continuous_const.mul continuous_id)
  have hf : ContinuousOn f (Icc (0 : ℝ) w) :=
    hstored.2.1.comp hlinear.continuousOn hmap
  have hroot := n01_component_root_data hN m rightEnd
  have hpoint : (r, L.minusFlow z m r ι) ∈ annularOpen D :=
    ⟨hroot.1, mem_univ _⟩
  have hbc := hL.2.2.1 z hz hs (r, L.minusFlow z m r ι) hpoint hroot.2.1
  have hspeed : minusCharacteristicSpeed (L.coefficients z) =ᶠ[𝓝 (r, L.minusFlow z m r ι)]
      minusCharacteristicSpeed (originalCoefficients D S C z) :=
    minusCharacteristicSpeed_eventuallyEq (Eventually.of_forall (hL.1 z hz hs)) hbc.1 hbc.2
  have hcurve : ContinuousWithinAt (fun t : ℝ => (r + σ * t, f t))
      (Icc (0 : ℝ) w) 0 :=
    hlinear.continuousWithinAt.prodMk (hf 0 ⟨le_rfl, hw.le⟩)
  have htendsto : Tendsto (fun t : ℝ => (r + σ * t, f t))
      (𝓝[Icc (0 : ℝ) w] 0) (𝓝 (r, L.minusFlow z m r ι)) := by
    simpa only [f, mul_zero, add_zero] using hcurve.tendsto
  have hagree := hspeed.comp_tendsto htendsto
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.mem_nhdsWithin_iff.mp hagree
  let ρ := min (R / 4) (min (w / 2) (ε₀ / 2))
  have hρ : 0 < ρ := lt_min (div_pos hR (by norm_num))
    (lt_min (half_pos hw) (half_pos hε₀))
  have hρR : ρ ≤ R / 4 := min_le_left _ _
  have hρw : ρ ≤ w := ((min_le_right _ _).trans (min_le_left _ _)).trans
    (half_le_self hw.le)
  have hρε : ρ < ε₀ := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt
    (half_lt_self hε₀)
  refine ⟨ρ, hρ, hρR, hf.mono (Icc_subset_Icc_right hρw), ?_⟩
  intro t ht
  have htW : t ∈ Ioo (0 : ℝ) w := ⟨ht.1, ht.2.trans_le hρw⟩
  have htphysical : r + σ * t ∈ Ioo (C.left m) (C.right m) := by
    have htw : t < C.right m - C.left m := htW.2
    cases rightEnd <;>
      simp only [r, σ, n01ComponentRoot, n01ComponentRootOrientation,
        Bool.false_eq_true, ite_false, ite_true, one_mul, neg_one_mul] <;>
      constructor <;> linarith [htW.1, htw]
  have heq : minusCharacteristicSpeed (L.coefficients z) (r + σ * t, f t) =
      minusCharacteristicSpeed (originalCoefficients D S C z) (r + σ * t, f t) := by
    apply hball
    refine ⟨?_, Ioo_subset_Icc_self htW⟩
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1] using
      ht.2.trans hρε
  have hraw := rootPhysicalSpeed_localization_eq_oriented_polarMinus
    (contDiff_stateProfile_of_n01 hS hT hN z.1)
    (contDiff_stateHeight_of_n01 hS hT hN z) hR hstrip
    (p := (t, f t)) ⟨ht.1.le, ht.2.le.trans hρR⟩
  have hraw' : rootPhysicalSpeed (localizedRootDrift D S C r σ hR z)
      (localizedRootSpeed D S C g r σ hR z) (-σ) (t, f t) =
      σ * minusCharacteristicSpeed (originalCoefficients D S C z) (r + σ * t, f t) :=
    hraw
  have hlin : HasDerivAt (fun s : ℝ => r + σ * s) σ t := by
    simpa only [mul_one] using ((hasDerivAt_id t).const_mul σ).const_add r
  have hd := (hstored.2.2.1 (r + σ * t) htphysical).comp t hlin
  have he : (fun u => L.minusFlow z m u ι) ∘ (fun s : ℝ => r + σ * s) = f := by
    funext s
    exact Function.comp_apply
  rw [he] at hd
  change HasDerivAt f
    (minusCharacteristicSpeed (L.coefficients z) (r + σ * t, f t) * σ) t at hd
  apply hd.congr_deriv
  rw [hraw', heq]
  ring

/-- Both endpoint trajectories are identified with the same previously
controlled family on a genuine one-sided germ. The right endpoint starts
at the stored right return angle; no uncontrolled flow is chosen here. -/
theorem n03_controlledRootFlow_eq_storedFlow_germ
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {E : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss base₃ : ℕ} {ε ε₃ : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hL : N03Properties D T S C E L base₃ ε₃)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base₃ ε₃)
    (hs : stateSector S z.1) (m : ℕ) (rightEnd : Bool)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hstrip : RootCoefficientStripConditions D.w g (stateProfile D S C z.1)
      (stateHeight D S C z) (n01ComponentRoot C m rightEnd)
      (n01ComponentRootOrientation rightEnd) R)
    {Θ : (ℝ × ℝ) → ℝ → ℝ → ℝ}
    (hΘ : N04FlowEquations
      (rootRescaledField
        (localizedRootDrift D S C (n01ComponentRoot C m rightEnd)
          (n01ComponentRootOrientation rightEnd) hR z)
        (localizedRootSpeed D S C g (n01ComponentRoot C m rightEnd)
          (n01ComponentRootOrientation rightEnd) hR z) δ) Θ) (ι : ℝ) :
    let r := n01ComponentRoot C m rightEnd
    let σ := n01ComponentRootOrientation rightEnd
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ x ∈ Icc (0 : ℝ) η,
      Θ (x, ((-σ) * Real.sqrt δ) * x ^ (3 / 2 : ℝ)) 1
          (L.minusFlow z m r ι) = L.minusFlow z m (r + σ * (δ * x)) ι := by
  let r := n01ComponentRoot C m rightEnd
  let σ := n01ComponentRootOrientation rightEnd
  let f : ℝ → ℝ := fun t => L.minusFlow z m (r + σ * t) ι
  obtain ⟨ρ, hρ, _, hf, hdf⟩ :=
    n03_exists_local_rootTrajectory_equation hS hT hN hL hz hs m rightEnd hR hstrip ι
  let κ := min ρ δ
  let η := κ / δ
  have hκ : 0 < κ := lt_min hρ hδ
  have hη : 0 < η := div_pos hκ hδ
  have hscale : δ * η = κ := by
    dsimp only [η]
    field_simp [hδ.ne']
  have hηone : η ≤ 1 := by
    apply (div_le_iff₀ hδ).mpr
    simpa only [one_mul] using (min_le_right ρ δ)
  have hsmall : Icc (0 : ℝ) (δ * η) ⊆ Icc (0 : ℝ) ρ := by
    rw [hscale]
    exact Icc_subset_Icc_right (min_le_left _ _)
  have hcont : ContinuousOn f (Icc (0 : ℝ) (δ * η)) := hf.mono hsmall
  have hode : ∀ t ∈ Ioo (0 : ℝ) (δ * η),
      HasDerivAt f (rootPhysicalSpeed (localizedRootDrift D S C r σ hR z)
        (localizedRootSpeed D S C g r σ hR z) (-σ) (t, f t)) t := by
    intro t ht
    apply hdf t
    refine ⟨ht.1, ht.2.trans_le ?_⟩
    rw [hscale]
    exact min_le_left _ _
  have hregular := contDiff_localizedRootFields_of_n01 hS hT hN hg hR hstrip
  have hperiod := periodic_localizedRootFields hS C g r σ hR z
  refine ⟨η, hη, hηone, ?_⟩
  intro x hx
  exact rootRescaledFlow_eq_storedTrajectory hη hδ Real.pi_ne_zero hregular.1 hregular.2
    hperiod.1 hperiod.2 hΘ (by simp only [f, mul_zero, add_zero]) hcont hode hx

end ContinuousFlexibility.Analysis
