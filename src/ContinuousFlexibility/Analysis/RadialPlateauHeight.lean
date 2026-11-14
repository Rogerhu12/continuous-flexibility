module

public import ContinuousFlexibility.Analysis.MaterialPlateauJets
public import ContinuousFlexibility.Analysis.MaterialPlateauGeometry
public import ContinuousFlexibility.Statements.Nonlinear

/-!
# Realizing the radial plateau as an actual physical height

The explicit scalar cutoff is supported strictly inside the annulus.
Its physical field therefore belongs to every height model, agrees with
the reference primitive as a germ throughout the complete open component,
and has the actual weighted-jet bounds supplied by the material calculation.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

def radialPlateauHeight (h : ℝ → ℝ) (l r δ : ℝ) : PolarPoint → ℝ :=
  fun p => radialPlateauProduct h l r δ p.1

theorem radialPlateauHeight_compactRadialSupport {D : ReferenceData}
    (h : ℝ → ℝ) {l r δ : ℝ} (hδ : 0 < δ)
    (hcore : Icc (l - δ) (r + δ) ⊆ Ioo D.a D.b) :
    HasCompactRadialSupport D (radialPlateauHeight h l r δ) := by
  refine ⟨Icc (l - δ) (r + δ), isCompact_Icc, hcore, ?_⟩
  intro t ht θ
  have hout : t ∉ Ioo (l - δ) (r + δ) :=
    fun ht' => ht ⟨ht'.1.le, ht'.2.le⟩
  simp only [radialPlateauHeight, radialPlateauProduct, radialPlateauCutoff_zero hδ hout,
    zero_mul]

theorem radialPlateauHeight_member {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) (γ : ℝ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {l r δ : ℝ} (hδ : 0 < δ)
    (hcore : Icc (l - δ) (r + δ) ⊆ Ioo D.a D.b) :
    HeightMember D T γ (radialPlateauHeight h l r δ) := by
  have hsupp := radialPlateauHeight_compactRadialSupport h hδ hcore
  have hF : ContDiffOn ℝ ∞ (radialPlateauHeight h l r δ) (annularOpen D) :=
    ((radialPlateauProduct_contDiff hh l r δ).comp contDiff_fst).contDiffOn.congr
      (fun _ _ => rfl)
  apply heightMember_of_compactRadialSupport (f := radialPlateauHeight h l r δ) hT
    hF
    (fun _ _ => rfl)
  · intro p
    simp only [radialPlateauHeight, Prod.fst_add, add_zero]
  · intro p hp
    have hnot : p.1 ∉ Icc (l - δ) (r + δ) :=
      fun hr => hp ⟨hcore hr, mem_univ _⟩
    have hout : p.1 ∉ Ioo (l - δ) (r + δ) :=
      fun hr => hnot ⟨hr.1.le, hr.2.le⟩
    simp only [radialPlateauHeight, radialPlateauProduct, radialPlateauCutoff_zero hδ hout,
      zero_mul]
  · exact hsupp

theorem radialPlateauHeight_eq_primitive_germ (h : ℝ → ℝ)
    {l r δ t : ℝ} (hδ : 0 < δ) (ht : t ∈ Ioo l r) (θ : ℝ) :
    radialPlateauHeight h l r δ =ᶠ[𝓝 (t, θ)] Radial.radialHeightField h := by
  have hn : ∀ᶠ p : PolarPoint in 𝓝 (t, θ), p.1 ∈ Ioo l r :=
    continuousAt_fst.eventually (isOpen_Ioo.mem_nhds ht)
  filter_upwards [hn] with p hp
  simp only [radialPlateauHeight, radialPlateauProduct,
    radialPlateauCutoff_one hδ ⟨hp.1.le, hp.2.le⟩, one_mul, Radial.radialHeightField]

theorem exists_referencePlateau_heightPair {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hD : RadialProfileGeometry D)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {l r : ℝ} (hl : D.a < l) (hr : r < D.b) :
    ∃ η : HeightPair S, η.2 = 0 ∧
      heightPairField S η = radialPlateauHeight (referenceRadialPrimitive D)
        l r (endpointPlateauWidth D l r) ∧
      ∀ t ∈ Ioo l r, ∀ θ : ℝ,
        heightPairField S η =ᶠ[𝓝 (t, θ)] Radial.radialHeightField (referenceRadialPrimitive D) := by
  have hmember := radialPlateauHeight_member hT (3 / 4 : ℝ)
    (referenceRadialPrimitive_contDiff hD) (endpointPlateauWidth_pos hl hr)
    (endpointPlateau_support_subset hl hr)
  obtain ⟨u, hu⟩ := (hS.1 (3 / 4 : ℝ)).2.2.2.2.1 _ hmember
  refine ⟨(u, 0), rfl, ?_, ?_⟩
  · funext p
    simp only [heightPairField, zero_mul, add_zero, hu]
  · intro t ht θ
    have heq : heightPairField S (u, 0) = radialPlateauHeight (referenceRadialPrimitive D)
        l r (endpointPlateauWidth D l r) := by
      funext p
      simp only [heightPairField, zero_mul, add_zero, hu]
    rw [heq]
    exact radialPlateauHeight_eq_primitive_germ _ (endpointPlateauWidth_pos hl hr) ht θ

theorem weightedPhysicalJet_radialPlateauHeight_zero_angle
    (T : MaterialData) (γ : ℝ) (h : ℝ → ℝ) (l r δ : ℝ) (a c : ℕ) (p : PolarPoint) :
    weightedPhysicalJet T γ a 0 c (radialPlateauHeight h l r δ) p =
      T.M (T.radius p.1) ^ c * iteratedDeriv a (materialPlateauPullback T γ h l r δ) p.1 := by
  simp only [weightedPhysicalJet, mixedDerivative, materialPullback, radialPlateauHeight,
    iteratedDeriv_zero]
  have heq : (fun x : ℝ =>
      T.H (T.radius x) ^ (-γ) * radialPlateauProduct h l r δ (T.radius x)) =
      materialPlateauPullback T γ h l r δ := rfl
  rw [heq]

theorem weightedPhysicalJet_radialPlateauHeight_positive_angle
    (T : MaterialData) (γ : ℝ) (h : ℝ → ℝ) (l r δ : ℝ)
    (a b c : ℕ) (hb : 0 < b) (p : PolarPoint) :
    weightedPhysicalJet T γ a b c (radialPlateauHeight h l r δ) p = 0 := by
  have hangle (x : ℝ) : iteratedDeriv b
      (fun θ => materialPullback T γ (radialPlateauHeight h l r δ) (x, θ)) p.2 = 0 := by
    change iteratedDeriv b (fun _ : ℝ =>
      T.H (T.radius x) ^ (-γ) * radialPlateauProduct h l r δ (T.radius x)) p.2 = 0
    simp [iteratedDeriv_const, hb.ne']
  simp only [weightedPhysicalJet, mixedDerivative, hangle]
  simp [iteratedDeriv_const]

/-- The scalar material estimates are estimates for the exact weighted
physical jets in the definition of the supplied height norm. -/
theorem referencePlateau_weightedPhysicalJet_bound {D : ReferenceData} {T : MaterialData}
    (hD : RadialProfileGeometry D) (hT : IsMaterialData D T) (γ : ℝ) (a : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (b c : ℕ) (l r δ : ℝ), 0 < δ → δ ≤ 1 → ∀ p : PolarPoint,
      |weightedPhysicalJet T γ a b c
        (radialPlateauHeight (referenceRadialPrimitive D) l r δ) p| ≤
          K * δ⁻¹ ^ a * T.H (T.radius p.1) ^ (-γ) * T.M (T.radius p.1) ^ c := by
  obtain ⟨K, hK, hb⟩ := referencePlateau_materialJet_bound hD hT γ a
  obtain ⟨_, hpos, _, _, _, _, _, hinside, _⟩ := hT
  refine ⟨K, hK, fun b c l r δ hδ hδ1 p => ?_⟩
  have hM : 0 ≤ T.M (T.radius p.1) := zero_le_one.trans (hpos _ (hinside p.1).1).2.2.2
  have hH : 0 ≤ T.H (T.radius p.1) ^ (-γ) :=
    Real.rpow_nonneg (hpos _ (hinside p.1).1).2.1.le _
  by_cases hb0 : b = 0
  · subst b
    rw [weightedPhysicalJet_radialPlateauHeight_zero_angle, abs_mul,
      abs_of_nonneg (pow_nonneg hM c)]
    exact (mul_le_mul_of_nonneg_left (hb l r δ hδ hδ1 p.1) (pow_nonneg hM c)).trans_eq
      (by ring)
  · rw [weightedPhysicalJet_radialPlateauHeight_positive_angle T γ _ l r δ a b c
      (Nat.pos_of_ne_zero hb0) p, abs_zero]
    positivity

end ContinuousFlexibility.Statements
