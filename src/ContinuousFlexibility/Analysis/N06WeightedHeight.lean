module

public import ContinuousFlexibility.Analysis.N06MaterialAbsorption

/-!
# The weighted height map supplied by N05 is continuous and linear

The existential output in N05 is unique because the chosen volume model's
forgetful map is injective. On the fixed source level it represents the height
component of the already selected graph inverse. Consequently its linearity
follows from that inverse, without asserting linearity of `globalInverse` on
arbitrary canonical sequences.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {b : ℕ} {B : CanonicalDomainData S K V b}

/-- The height projection of the fixed graph inverse, retaining its actual lp target. -/
def n06InverseHeightLp (B : CanonicalDomainData S K V b) :
    V.level (3 / 4 : ℝ) 0 b →L[ℝ] CanonicalL2Sequence S K :=
  (ContinuousLinearMap.fst ℝ (CanonicalL2Sequence S K) (ℝ × ℝ × ℝ)).comp
    ((ContinuousLinearMap.fst ℝ (CanonicalUnknown S K)
      (V.level (3 / 4 : ℝ) 0 b)).comp (B.graph.subtypeL.comp B.inverse))

theorem n06InverseHeightLp_apply (F : V.level (3 / 4 : ℝ) 0 b) :
    n06InverseHeightLp B F = (B.inverse F).val.1.1 := by
  simp only [n06InverseHeightLp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', Submodule.subtypeL_apply]

/-- The actual canonical height component of the fixed graph inverse. -/
def n06InverseCanonicalHeight (B : CanonicalDomainData S K V b) :
    V.level (3 / 4 : ℝ) 0 b →ₗ[ℝ] CanonicalSequence S K :=
  (LinearMap.pi (fun m => lp.evalₗ (𝕜 := ℝ)
    (fun n => CanonicalL2 S K n) 2 m)).comp (n06InverseHeightLp B).toLinearMap

theorem n06InverseCanonicalHeight_apply (F : V.level (3 / 4 : ℝ) 0 b) (m : ℕ) :
    n06InverseCanonicalHeight B F m = (B.inverse F).val.1.1 m := by
  change (n06InverseHeightLp B F) m = _
  rw [n06InverseHeightLp_apply]

/-- N05's weighted output can be selected as a continuous linear map on precisely
the fixed source space, representing the same graph inverse and global inverse. -/
theorem n06N05_exists_weightedHeight
    (hN05 : N05Properties D T S C K V b B) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∃ H : V.level (3 / 4 : ℝ) 0 b →L[ℝ]
          V.level (3 / 4 : ℝ) (-B.lossMaterial) b,
        ‖H‖ ≤ C₀ ∧
        (∀ F, V.forget (3 / 4 : ℝ) (-B.lossMaterial) b (H F) =
          (fun m => (B.globalInverse (V.forget (3 / 4 : ℝ) 0 b F)).1 m)) ∧
        (∀ F, V.forget (3 / 4 : ℝ) (-B.lossMaterial) b (H F) =
          n06InverseCanonicalHeight B F) ∧
        (∀ F m, (B.inverse F).val.1.1 m =
          (T.M (T.sample (K.cell m)) ^ B.lossMaterial *
            T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ)) • (H F).val m 0) := by
  have hV : IsVolumeModel T S K V := hN05.2.1
  obtain ⟨C₀, hC₀, houtput⟩ := n06N05_sameInverse_output_bound hN05 b
  obtain ⟨_, _, _, _, _, _, _, _, _, hsame, _⟩ := hN05
  choose W hW hWnorm using houtput
  have hWgraph (F : V.level (3 / 4 : ℝ) 0 b) :
      V.forget (3 / 4 : ℝ) (-B.lossMaterial) b (W F) =
        n06InverseCanonicalHeight B F := by
    rw [hW F]
    funext m
    rw [n06InverseCanonicalHeight_apply, hsame F]
  let H₀ : V.level (3 / 4 : ℝ) 0 b →ₗ[ℝ]
      V.level (3 / 4 : ℝ) (-B.lossMaterial) b :=
    { toFun := W
      map_add' := by
        intro F G
        apply hV.2.2.1 (3 / 4 : ℝ) (-B.lossMaterial) b
        simp only [map_add, hWgraph]
      map_smul' := by
        intro c F
        apply hV.2.2.1 (3 / 4 : ℝ) (-B.lossMaterial) b
        simp only [map_smul, hWgraph, RingHom.id_apply] }
  have hHnorm : ∀ F, ‖H₀ F‖ ≤ C₀ * ‖F‖ := hWnorm
  let H := H₀.mkContinuous C₀ hHnorm
  refine ⟨C₀, hC₀, H, H₀.mkContinuous_norm_le hC₀.le hHnorm, ?_, ?_, ?_⟩
  · exact hW
  · exact hWgraph
  · intro F m
    rw [← n06InverseCanonicalHeight_apply]
    rw [← hWgraph F]
    rw [hV.2.2.2]
    simp only [neg_neg]
    rfl

/-- The weighted height lift has no choice ambiguity once the graph inverse is fixed. -/
theorem n06WeightedHeight_unique (hV : IsVolumeModel T S K V)
    {H₁ H₂ : V.level (3 / 4 : ℝ) 0 b →L[ℝ]
      V.level (3 / 4 : ℝ) (-B.lossMaterial) b}
    (h₁ : ∀ F, V.forget (3 / 4 : ℝ) (-B.lossMaterial) b (H₁ F) =
      n06InverseCanonicalHeight B F)
    (h₂ : ∀ F, V.forget (3 / 4 : ℝ) (-B.lossMaterial) b (H₂ F) =
      n06InverseCanonicalHeight B F) : H₁ = H₂ := by
  apply ContinuousLinearMap.ext
  intro F
  apply hV.2.2.1 (3 / 4 : ℝ) (-B.lossMaterial) b
  rw [h₁ F, h₂ F]

end ContinuousFlexibility.Statements
