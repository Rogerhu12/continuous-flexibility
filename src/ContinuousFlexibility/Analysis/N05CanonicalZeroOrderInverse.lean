module

public import ContinuousFlexibility.Analysis.N05CanonicalWeightedInverseL2
public import ContinuousFlexibility.Analysis.N05CanonicalOutputReflection

/-!
# The actual inverse in the zero-order canonical volume space

The weighted L² output already belongs to the true sequence space and is
even. Inserting its single zero jet therefore gives the literal target
volume level, with material loss four and the same three physical scalars.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

def n05CanonicalZeroJetSequence (S : PhysicalSpacesData) (K : CanonicalData S)
    (w : CanonicalL2Sequence S K) : CanonicalVolumeJets S K 0 :=
  ⟨fun m => PiLp.single 2 (0 : Fin 1) (w m), (lp.memℓp w).mono' (fun m => by
    simp only [PiLp.norm_single, le_refl])⟩

theorem n05CanonicalZeroJetSequence_apply (S : PhysicalSpacesData) (K : CanonicalData S)
    (w : CanonicalL2Sequence S K) (m : ℕ) (j : Fin 1) :
    n05CanonicalZeroJetSequence S K w m j = w m := by
  have hj : j = 0 := Fin.eq_zero j
  subst j
  exact PiLp.single_eq_same (β := fun _ : Fin 1 => CanonicalL2 S K m) 2 0 (w m)

theorem n05CanonicalZeroJetSequence_bound (S : PhysicalSpacesData) (K : CanonicalData S)
    (w : CanonicalL2Sequence S K) : ‖n05CanonicalZeroJetSequence S K w‖ ≤ ‖w‖ := by
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro m
  change ‖(PiLp.single 2 (0 : Fin 1) (w m) :
    PiLp 2 (fun _ : Fin 1 => CanonicalL2 S K m))‖ ≤ ‖w m‖
  simp only [PiLp.norm_single, le_refl]

theorem n05CanonicalZeroJetSequence_mem_graph (S : PhysicalSpacesData)
    (K : CanonicalData S) (w : CanonicalL2Sequence S K)
    (hw : ∀ m, n05CanonicalReflection S K m (w m) = w m) :
    n05CanonicalZeroJetSequence S K w ∈ canonicalVolumeGraph S K 0 := by
  refine ⟨?_, ?_⟩
  · intro m
    simpa only [n05CanonicalZeroJetSequence_apply] using
      (n05CanonicalReflection_fixed_iff S K m (w m)).mp (hw m)
  · intro m j
    have hj : j = 0 := Fin.eq_zero j
    subst j
    intro φ hφ
    simp only [n05CanonicalZeroJetSequence_apply, Fin.val_zero, pow_zero, one_mul,
      mixedDerivative, iteratedDeriv_zero, Prod.eta]

theorem n05_canonicalUnknownScalars_le_three_norm (S : PhysicalSpacesData)
    (K : CanonicalData S) (u : CanonicalUnknown S K) :
    canonicalUnknownScalars S K u ≤ 3 * ‖u‖ := by
  have ha : |u.2.1| ≤ ‖u‖ := by
    simpa only [Real.norm_eq_abs] using (norm_fst_le u.2).trans (norm_snd_le u)
  have hb : |u.2.2.1| ≤ ‖u‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_fst_le u.2.2).trans ((norm_snd_le u.2).trans (norm_snd_le u))
  have hc : |u.2.2.2| ≤ ‖u‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_snd_le u.2.2).trans ((norm_snd_le u.2).trans (norm_snd_le u))
  unfold canonicalUnknownScalars
  linarith only [ha, hb, hc]

/-- The fixed global inverse has an actual zero-order target volume
representative, with loss four and its original endpoint scalars. -/
theorem n05CanonicalGlobalInverse_zero_level_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hD : IsRadialReference D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {β ρ γ δ M0 M1 : ℝ} (hminus : 0 < β - ρ) (hplus : 0 < β + ρ)
    (hγ : |γ - β| ≤ δ) (hmargin : δ < ρ) {G : RadialSource → RadialUnknown}
    (hGminus : ReferenceInverseProperties D (β - ρ) M0 M1 G)
    (hGplus : ReferenceInverseProperties D (β + ρ) M0 M1 G) (t : ℝ) (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ v : (n05CanonicalVolumeModel T S K).level γ t s,
      ∃ W : (n05CanonicalVolumeModel T S K).level γ (t - 4) 0,
        (n05CanonicalVolumeModel T S K).forget γ (t - 4) 0 W =
          (fun m => (n05CanonicalGlobalInverse D S C K G
            ((n05CanonicalVolumeModel T S K).forget γ t s v)).1 m) ∧
        ‖W‖ + canonicalUnknownScalars S K (n05CanonicalGlobalInverse D S C K G
          ((n05CanonicalVolumeModel T S K).forget γ t s v)) ≤ B * ‖v‖ := by
  have hgap : β - ρ < γ := by
    have hh := (abs_le.mp hγ).1
    linarith only [hh, hmargin]
  have hV := n05CanonicalVolumeModel_actual hD.1 hT S K
  obtain ⟨Bw, hBw, hweighted⟩ := n05CanonicalGlobalInverse_weighted_l2_bound
    hD hT hS h hcoordinates hminus hplus hγ hmargin hGminus hGplus t
  obtain ⟨Bu, hBu, hglobal⟩ := n05CanonicalGlobalInverse_norm_bound
    hD hT hS h hcoordinates hminus hGminus hV hgap t s
  refine ⟨Bw + 3 * Bu, by positivity, fun v => ?_⟩
  obtain ⟨w, hw, hn⟩ := hweighted s v
  have hreflection (m : ℕ) : n05CanonicalReflection S K m (w m) = w m := by
    rw [hw m, map_smul, n05CanonicalGlobalInverse_reflection
      hD hT hS h hcoordinates hV hminus hgap hGminus t s v m]
  have hW : n05CanonicalZeroJetSequence S K w ∈
      (n05CanonicalVolumeModel T S K).level γ (t - 4) 0 := by
    change n05CanonicalZeroJetSequence S K w ∈ n05CanonicalClosedSubmodule S K 0
    rw [← SetLike.mem_coe, n05CanonicalClosedSubmodule_carrier]
    exact n05CanonicalZeroJetSequence_mem_graph S K w hreflection
  let W : (n05CanonicalVolumeModel T S K).level γ (t - 4) 0 :=
    ⟨n05CanonicalZeroJetSequence S K w, hW⟩
  have hWnorm : ‖W‖ ≤ Bw * ‖v‖ := (n05CanonicalZeroJetSequence_bound S K w).trans hn
  refine ⟨W, ?_, ?_⟩
  · funext m
    rw [n05CanonicalVolumeModel_forget]
    change n05CanonicalSampleWeight T S K γ (t - 4) m •
      n05CanonicalZeroJetSequence S K w m 0 = _
    rw [n05CanonicalZeroJetSequence_apply, hw m, smul_smul,
      mul_inv_cancel₀ (n05CanonicalSampleWeight_pos hT hD.1.choose_spec.2.1
        S K γ (t - 4) m).ne', one_smul]
  · calc
      _ ≤ Bw * ‖v‖ + 3 * (Bu * ‖v‖) := add_le_add hWnorm
        ((n05_canonicalUnknownScalars_le_three_norm S K _).trans
          (mul_le_mul_of_nonneg_left (hglobal v) (by norm_num)))
      _ = (Bw + 3 * Bu) * ‖v‖ := by ring

end ContinuousFlexibility.Statements
