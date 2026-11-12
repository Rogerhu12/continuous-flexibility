import ContinuousFlexibility.Analysis.N05CanonicalWeightedNormalJets
import ContinuousFlexibility.Analysis.N05CanonicalJetAssembly

/-!
# Every normal Sobolev order of the same inverse with material loss four

Weighted angular columns of the fixed radial derivative assemble into the
actual volume graph. Its forgotten zero column retains the original weak
radial test identity, with one more angular derivative on the source.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped BigOperators

theorem n05CanonicalGlobalInverse_all_normal_level_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hD : IsRadialReference D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {β ρ γ δ M0 M1 MN : ℝ} (hminus : 0 < β - ρ) (hplus : 0 < β + ρ)
    (hγ : |γ - β| ≤ δ) (hmargin : δ < ρ) {G : RadialSource → RadialUnknown}
    (hGminus : ReferenceInverseProperties D (β - ρ) M0 M1 G)
    (hGplus : ReferenceInverseProperties D (β + ρ) M0 M1 G)
    (hNminus : FirstNormalInverseEstimate D (β - ρ) M0 MN G)
    (hNplus : FirstNormalInverseEstimate D (β + ρ) M0 MN G) (t : ℝ) (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ v : (n05CanonicalVolumeModel T S K).level γ t (s + 1),
      ∃ W : (n05CanonicalVolumeModel T S K).level γ (t - 4) s,
        (n05CanonicalVolumeModel T S K).forget γ (t - 4) s W =
          (fun m => n05CanonicalRadialJetSequence S K
            (n05CanonicalGlobalInverse D S C K G
              ((n05CanonicalVolumeModel T S K).forget γ t (s + 1) v)).1 m) ∧
        (∀ m, n05WeakCanonicalRadialDerivative S K m
          ((n05CanonicalGlobalInverse D S C K G
            ((n05CanonicalVolumeModel T S K).forget γ t (s + 1) v)).1 m)
          ((n05CanonicalVolumeModel T S K).forget γ (t - 4) s W m)) ∧
        ‖W‖ ≤ B * ‖v‖ := by
  classical
  have hgap : β - ρ < γ := by
    have hh := (abs_le.mp hγ).1
    linarith only [hh, hmargin]
  have hV := n05CanonicalVolumeModel_actual hD.1 hT S K
  obtain ⟨Bw, hBw, hweighted⟩ := n05CanonicalGlobalInverse_weighted_normalJet_bound
    hD hT hS h hcoordinates hminus hplus hγ hmargin hGminus hGplus hNminus hNplus t s
  obtain ⟨_, _, hjets⟩ := n05CanonicalGlobalInverse_normalJets_bound
    hD hT hS h hcoordinates hminus hGminus hNminus hV hgap t s
  refine ⟨((s + 1 : ℕ) : ℝ) * Bw, by positivity, fun v => ?_⟩
  choose w hw hn using (fun j : Fin (s + 1) => hweighted v j)
  have hzero (m : ℕ) : w 0 m = (n05CanonicalSampleWeight T S K γ (t - 4) m)⁻¹ •
      n05CanonicalRadialJetSequence S K (n05CanonicalGlobalInverse D S C K G
        ((n05CanonicalVolumeModel T S K).forget γ t (s + 1) v)).1 m := by
    simpa only [Fin.val_zero, n05CanonicalAngularJetSequence_zero] using hw 0 m
  have hreflection (m : ℕ) : n05CanonicalReflection S K m (w 0 m) = w 0 m := by
    rw [hzero, map_smul, (hjets v).2.1 m]
  have hweak (m : ℕ) (j : Fin (s + 1)) :
      WeakCanonicalAngularDerivative S K m (w 0 m) (w j m) j.val := by
    rw [hzero, hw j m]
    exact n05WeakCanonicalAngularDerivative_smul (((hjets v).2.2 j).1 m)
      (n05CanonicalSampleWeight T S K γ (t - 4) m)⁻¹
  have hW : n05CanonicalJetAssembly S K s w ∈
      (n05CanonicalVolumeModel T S K).level γ (t - 4) s := by
    change n05CanonicalJetAssembly S K s w ∈ n05CanonicalClosedSubmodule S K s
    rw [← SetLike.mem_coe, n05CanonicalClosedSubmodule_carrier]
    exact n05CanonicalJetAssembly_mem_graph S K s w hreflection hweak
  let W : (n05CanonicalVolumeModel T S K).level γ (t - 4) s :=
    ⟨n05CanonicalJetAssembly S K s w, hW⟩
  have hforget : (n05CanonicalVolumeModel T S K).forget γ (t - 4) s W =
      (fun m => n05CanonicalRadialJetSequence S K (n05CanonicalGlobalInverse D S C K G
        ((n05CanonicalVolumeModel T S K).forget γ t (s + 1) v)).1 m) := by
    funext m
    rw [n05CanonicalVolumeModel_forget]
    change n05CanonicalSampleWeight T S K γ (t - 4) m •
      n05CanonicalJetAssembly S K s w m 0 = _
    rw [n05CanonicalJetAssembly_apply, hzero, smul_smul,
      mul_inv_cancel₀ (n05CanonicalSampleWeight_pos hT hD.1.choose_spec.2.1
        S K γ (t - 4) m).ne', one_smul]
  refine ⟨W, hforget, ?_, ?_⟩
  · intro m
    rw [hforget]
    exact (hjets v).1 m
  · change ‖n05CanonicalJetAssembly S K s w‖ ≤ _
    calc
      _ ≤ ∑ j : Fin (s + 1), ‖w j‖ := n05CanonicalJetAssembly_bound S K s w
      _ ≤ ∑ _j : Fin (s + 1), Bw * ‖v‖ := Finset.sum_le_sum (fun j _ => hn j)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

end ContinuousFlexibility.Statements
