import ContinuousFlexibility.Analysis.N07aVolumeCell
import ContinuousFlexibility.Analysis.N07aWeakNormalEquation

/-!
# The four actual weak jets already supplied by N05

Only two angular derivatives of the field and one angular derivative of
its first normal derivative are used. They belong to the original volume
graph and describe the same reference inverse by its coherence clause.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {V : VolumeModelData S K}

local instance n07aFiniteJetsLevelGroup (γ t : ℝ) (s : ℕ) :
    NormedAddCommGroup (V.level γ t s) := Submodule.normedAddCommGroup _

local instance n07aFiniteJetsLevelSpace (γ t : ℝ) (s : ℕ) :
    NormedSpace ℝ (V.level γ t s) := Submodule.normedSpace _

def n07aVolumeAngularJet {γ t : ℝ} {s : ℕ} (W : V.level γ t s)
    (m : ℕ) (j : Fin (s + 1)) : CanonicalL2 S K m :=
  n07aVolumeWeight T K γ t m • W.val m j

theorem n07aVolumeAngularJet_weak (hV : IsVolumeModel T S K V)
    {γ t : ℝ} {s : ℕ} (W : V.level γ t s) (m : ℕ) (j : Fin (s + 1)) :
    N07aWeakCanonicalMixedDerivative S K m (V.forget γ t s W m)
      (n07aVolumeAngularJet (T := T) W m j) 0 j.val := by
  have hW : W.val ∈ canonicalVolumeGraph S K s := by
    rw [← hV.1 γ t s]
    exact W.property
  have hj := (n07a_weakCanonicalMixed_zero_radial_iff _ _ j.val).mpr (hW.2 m j)
  rw [n07aVolume_forget_apply hV]
  exact hj.smul (n07aVolumeWeight T K γ t m)

variable {b : ℕ} {B : CanonicalDomainData S K V b}

local instance n07aFiniteJetsUnknownGroup : NormedAddCommGroup (CanonicalUnknown S K) :=
  inferInstance

local instance n07aFiniteJetsUnknownSpace : NormedSpace ℝ (CanonicalUnknown S K) :=
  inferInstance

local instance n07aFiniteJetsGraphGroup : NormedAddCommGroup B.Space :=
  Submodule.normedAddCommGroup _

local instance n07aFiniteJetsGraphSpace : NormedSpace ℝ B.Space :=
  Submodule.normedSpace _

private theorem n07a_finite_reference_angular
    (h05 : N05Properties D T S C K V b B) (s : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ F : V.level (3 / 4 : ℝ) 0 s,
      ∃ W : V.level (3 / 4 : ℝ) (0 - B.lossMaterial) s,
        V.forget (3 / 4 : ℝ) (0 - B.lossMaterial) s W =
          (fun m => (B.globalInverse (V.forget (3 / 4 : ℝ) 0 s F)).1 m) ∧
        ‖W‖ + canonicalUnknownScalars S K
          (B.globalInverse (V.forget (3 / 4 : ℝ) 0 s F)) ≤ A * ‖F‖ :=
  h05.2.2.2.2.2.2.2.2.2.2.2.2.1 0 s

private theorem n07a_finite_reference_normal
    (h05 : N05Properties D T S C K V b B) (s : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ F : V.level (3 / 4 : ℝ) 0 (s + 1),
      ∃ W : V.level (3 / 4 : ℝ) (0 - B.lossMaterial) s,
        (∀ m φ, CanonicalTest S K m φ →
          (∫ p, V.forget (3 / 4 : ℝ) (0 - B.lossMaterial) s W m p * φ p
            ∂canonicalMeasure S K m) =
          -(∫ p, (B.globalInverse (V.forget (3 / 4 : ℝ) 0 (s + 1) F)).1 m p *
            mixedDerivative 1 0 φ p ∂canonicalMeasure S K m)) ∧ ‖W‖ ≤ A * ‖F‖ :=
  h05.2.2.2.2.2.2.2.2.2.2.2.2.2 0 s

theorem n07a_referenceInverse_finiteJets
    (h05 : N05Properties D T S C K V b B)
    (F : V.level (3 / 4 : ℝ) 0 b) (m : ℕ) :
    ∃ ur uθ urθ uθθ : CanonicalL2 S K m,
      N07aWeakCanonicalMixedDerivative S K m ((B.inverse F).val.1.1 m) ur 1 0 ∧
      N07aWeakCanonicalMixedDerivative S K m ((B.inverse F).val.1.1 m) uθ 0 1 ∧
      N07aWeakCanonicalMixedDerivative S K m ur urθ 0 1 ∧
      N07aWeakCanonicalMixedDerivative S K m uθ uθθ 0 1 := by
  cases b with
  | zero => have := h05.1; omega
  | succ n =>
    have hn : 1 ≤ n := by have := h05.1; omega
    have hcoh := h05.2.2.2.2.2.2.2.2.2.1 F
    have hA := (n07a_finite_reference_angular h05 (n + 1)).choose_spec.2
    let W : V.level (3 / 4 : ℝ) (0 - B.lossMaterial) (n + 1) := (hA F).choose
    have hW : V.forget (3 / 4 : ℝ) (0 - B.lossMaterial) (n + 1) W =
        fun k => (B.globalInverse (V.forget (3 / 4 : ℝ) 0 (n + 1) F)).1 k := (hA F).choose_spec.1
    have hA₁ := (n07a_finite_reference_normal h05 n).choose_spec.2
    let Wr : V.level (3 / 4 : ℝ) (0 - B.lossMaterial) n := (hA₁ F).choose
    have hWr := (hA₁ F).choose_spec.1
    let ur := V.forget (3 / 4 : ℝ) (0 - B.lossMaterial) n Wr m
    let uθ := n07aVolumeAngularJet (T := T) W m ⟨1, by omega⟩
    let uθθ := n07aVolumeAngularJet (T := T) W m ⟨2, by omega⟩
    let urθ := n07aVolumeAngularJet (T := T) Wr m ⟨1, by omega⟩
    have hu : V.forget (3 / 4 : ℝ) (0 - B.lossMaterial) (n + 1) W m =
        (B.inverse F).val.1.1 m := by
      exact (congrFun hW m).trans (congrArg (fun x : CanonicalUnknown S K => x.1 m) hcoh).symm
    have hr : N07aWeakCanonicalMixedDerivative S K m ((B.inverse F).val.1.1 m) ur 1 0 := by
      intro φ hφ
      have he := congrArg (fun x : CanonicalUnknown S K => x.1 m) hcoh.symm
      have hp := congrArg (fun v : CanonicalL2 S K m =>
        -(∫ p, v p * mixedDerivative 1 0 φ p ∂canonicalMeasure S K m)) he
      simpa only [Nat.add_zero, pow_one, neg_one_mul] using (hWr m φ hφ).trans hp
    have hθ : N07aWeakCanonicalMixedDerivative S K m ((B.inverse F).val.1.1 m) uθ 0 1 := by
      have h := n07aVolumeAngularJet_weak h05.2.1 W m ⟨1, by omega⟩
      rwa [hu] at h
    have hθθ : N07aWeakCanonicalMixedDerivative S K m ((B.inverse F).val.1.1 m) uθθ 0 2 := by
      have h := n07aVolumeAngularJet_weak h05.2.1 W m ⟨2, by omega⟩
      rwa [hu] at h
    exact ⟨ur, uθ, urθ, uθθ, hr, hθ,
      n07aVolumeAngularJet_weak h05.2.1 Wr m ⟨1, by omega⟩, hθ.suffix hθθ⟩

end ContinuousFlexibility.Analysis
