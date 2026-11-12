import ContinuousFlexibility.Analysis.N05CanonicalWeightedInverseJets
import ContinuousFlexibility.Analysis.N05CanonicalJetAssembly
import ContinuousFlexibility.Analysis.N05CanonicalZeroOrderInverse

/-!
# All angular orders of the same inverse with material loss four

The actual weighted jet columns assemble into the frozen volume graph.
Its zero column is the original global inverse, its higher columns are
its genuine weak derivatives, and its original three scalars satisfy the
same source-level bound. The underlying inverse is never reselected.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped BigOperators

theorem n05CanonicalGlobalInverse_all_level_bound
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
      ∃ W : (n05CanonicalVolumeModel T S K).level γ (t - 4) s,
        (n05CanonicalVolumeModel T S K).forget γ (t - 4) s W =
          (fun m => (n05CanonicalGlobalInverse D S C K G
            ((n05CanonicalVolumeModel T S K).forget γ t s v)).1 m) ∧
        ‖W‖ + canonicalUnknownScalars S K (n05CanonicalGlobalInverse D S C K G
          ((n05CanonicalVolumeModel T S K).forget γ t s v)) ≤ B * ‖v‖ := by
  classical
  have hgap : β - ρ < γ := by
    have hh := (abs_le.mp hγ).1
    linarith only [hh, hmargin]
  have hV := n05CanonicalVolumeModel_actual hD.1 hT S K
  obtain ⟨Bw, hBw, hweighted⟩ := n05CanonicalGlobalInverse_weighted_jet_bound
    hD hT hS h hcoordinates hminus hplus hγ hmargin hGminus hGplus t s
  obtain ⟨_, _, hjets⟩ := n05CanonicalGlobalInverse_angularJets_bound
    hD hT hS h hcoordinates hminus hGminus hV hgap t s
  obtain ⟨Bu, hBu, hglobal⟩ := n05CanonicalGlobalInverse_norm_bound
    hD hT hS h hcoordinates hminus hGminus hV hgap t s
  refine ⟨((s + 1 : ℕ) : ℝ) * Bw + 3 * Bu, by positivity, fun v => ?_⟩
  choose w hw hn using (fun j : Fin (s + 1) => hweighted v j)
  have hzero (m : ℕ) : w 0 m = (n05CanonicalSampleWeight T S K γ (t - 4) m)⁻¹ •
      (n05CanonicalGlobalInverse D S C K G
        ((n05CanonicalVolumeModel T S K).forget γ t s v)).1 m := by
    simpa only [Fin.val_zero, n05CanonicalAngularJetSequence_zero] using hw 0 m
  have hreflection (m : ℕ) : n05CanonicalReflection S K m (w 0 m) = w 0 m := by
    rw [hzero, map_smul, n05CanonicalGlobalInverse_reflection
      hD hT hS h hcoordinates hV hminus hgap hGminus t s v m]
  have hweak (m : ℕ) (j : Fin (s + 1)) :
      WeakCanonicalAngularDerivative S K m (w 0 m) (w j m) j.val := by
    rw [hzero, hw j m]
    exact n05WeakCanonicalAngularDerivative_smul ((hjets v j).1 m)
      (n05CanonicalSampleWeight T S K γ (t - 4) m)⁻¹
  have hW : n05CanonicalJetAssembly S K s w ∈
      (n05CanonicalVolumeModel T S K).level γ (t - 4) s := by
    change n05CanonicalJetAssembly S K s w ∈ n05CanonicalClosedSubmodule S K s
    rw [← SetLike.mem_coe, n05CanonicalClosedSubmodule_carrier]
    exact n05CanonicalJetAssembly_mem_graph S K s w hreflection hweak
  let W : (n05CanonicalVolumeModel T S K).level γ (t - 4) s :=
    ⟨n05CanonicalJetAssembly S K s w, hW⟩
  have hsum : (∑ j : Fin (s + 1), ‖w j‖) ≤ ((s + 1 : ℕ) : ℝ) * Bw * ‖v‖ := by
    calc
      _ ≤ ∑ _j : Fin (s + 1), Bw * ‖v‖ := Finset.sum_le_sum (fun j _ => hn j)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
  have hWnorm : ‖W‖ ≤ ((s + 1 : ℕ) : ℝ) * Bw * ‖v‖ := by
    change ‖n05CanonicalJetAssembly S K s w‖ ≤ _
    exact (n05CanonicalJetAssembly_bound S K s w).trans hsum
  refine ⟨W, ?_, ?_⟩
  · funext m
    rw [n05CanonicalVolumeModel_forget]
    change n05CanonicalSampleWeight T S K γ (t - 4) m •
      n05CanonicalJetAssembly S K s w m 0 = _
    rw [n05CanonicalJetAssembly_apply, hzero, smul_smul,
      mul_inv_cancel₀ (n05CanonicalSampleWeight_pos hT hD.1.choose_spec.2.1
        S K γ (t - 4) m).ne', one_smul]
  · calc
      _ ≤ ((s + 1 : ℕ) : ℝ) * Bw * ‖v‖ + 3 * (Bu * ‖v‖) := add_le_add hWnorm
        ((n05_canonicalUnknownScalars_le_three_norm S K _).trans
          (mul_le_mul_of_nonneg_left (hglobal v) (by norm_num)))
      _ = (((s + 1 : ℕ) : ℝ) * Bw + 3 * Bu) * ‖v‖ := by ring

end ContinuousFlexibility.Statements
