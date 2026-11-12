import ContinuousFlexibility.Radial.ConnectedReferenceBorder
import ContinuousFlexibility.Radial.SelectedNaturalTailTransport
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Actual retained tails of one connected selected reference

An open tail mapping into the corresponding central exterior also places
its entrance in the target core, provided the old entrance is valid.
This follows from interval order, without evaluating the profile identity
at the excluded entrance. Smoothness then supplies the missing value and
first derivative there.

The last theorem keeps the single selected object in the R08 witness.
Validity and retention of the chosen entrance are explicit inputs. In
particular, no unconditional validity of the entry at the initial chain
index is inferred from a frequency band that might be empty.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

/-- Open-tail containment gives the necessary weak bound at its entrance;
the central cut lies strictly inside the target core. -/
theorem radialRadiusScale_entry_mem_core_of_tail_map {D E : ReferenceData}
    {κ entry cut : ℝ} (hκ : 0 < κ) (right : Bool)
    (hentry : entry ∈ radialCore D) (hcut : cut ∈ radialCore E)
    (hend : (if right then E.b else E.a) = κ * (if right then D.b else D.a))
    (hmap : ∀ r ∈ radialTailInterval D right entry,
      κ * r ∈ radialTailInterval E right cut) :
    κ * entry ∈ radialCore E := by
  have hsub : radialTailInterval E right (κ * entry) ⊆
      radialTailInterval E right cut := by
    rw [← radialTailInterval_radius_image (entry := entry) hκ right hend]
    rintro _ ⟨r, hr, rfl⟩
    exact hmap r hr
  cases right
  · change E.a = κ * D.a at hend
    change Ioo E.a (κ * entry) ⊆ Ioo E.a cut at hsub
    have hleft : E.a < κ * entry := by
      rw [hend]
      exact mul_lt_mul_of_pos_left hentry.1 hκ
    have hbound := (Ioo_subset_Ioo_iff hleft).mp hsub
    exact ⟨hleft, hbound.2.trans_lt hcut.2⟩
  · change E.b = κ * D.b at hend
    change Ioo (κ * entry) E.b ⊆ Ioo cut E.b at hsub
    have hright : κ * entry < E.b := by
      rw [hend]
      exact mul_lt_mul_of_pos_left hentry.2 hκ
    have hbound := (Ioo_subset_Ioo_iff hright).mp hsub
    exact ⟨hcut.1.trans_le hbound.1, hright⟩

private theorem connected_eq_at_closure {I : Set ℝ} {r : ℝ}
    {f g : ℝ → ℝ} (hr : r ∈ closure I)
    (hf : ContinuousAt f r) (hg : ContinuousAt g r) (heq : EqOn f g I) :
    f r = g r := by
  haveI : (𝓝[I] r).NeBot := mem_closure_iff_clusterPt.mp hr
  have hfg : f =ᶠ[𝓝[I] r] g := heq.eventuallyEq_of_mem self_mem_nhdsWithin
  exact tendsto_nhds_unique_of_eventuallyEq
    hf.continuousWithinAt hg.continuousWithinAt hfg

/-- Equality on the open tail determines both entrance jets of functions
smooth at that entrance. This includes either endpoint orientation. -/
theorem radialTail_eq_jet_at_entry {D : ReferenceData} {entry : ℝ}
    (right : Bool) (hentry : entry ∈ radialCore D) {f g : ℝ → ℝ}
    (hf : ContDiffAt ℝ ∞ f entry) (hg : ContDiffAt ℝ ∞ g entry)
    (heq : EqOn f g (radialTailInterval D right entry)) :
    f entry = g entry ∧ deriv f entry = deriv g entry := by
  have hopen : IsOpen (radialTailInterval D right entry) := by
    cases right <;> exact isOpen_Ioo
  have hclosure : entry ∈ closure (radialTailInterval D right entry) := by
    cases right
    · change entry ∈ closure (Ioo D.a entry)
      rw [closure_Ioo hentry.1.ne]
      exact ⟨hentry.1.le, le_rfl⟩
    · change entry ∈ closure (Ioo entry D.b)
      rw [closure_Ioo hentry.2.ne]
      exact ⟨le_rfl, hentry.2.le⟩
  have hd : EqOn (deriv f) (deriv g) (radialTailInterval D right entry) := by
    intro r hr
    exact (heq.eventuallyEq_of_mem (hopen.mem_nhds hr)).deriv_eq
  have hfd : ContinuousAt (deriv f) entry :=
    (hf.derivWithin (m := 0) (by simp)).continuousAt
  have hgd : ContinuousAt (deriv g) entry :=
    (hg.derivWithin (m := 0) (by simp)).continuousAt
  exact ⟨connected_eq_at_closure hclosure hf.continuousAt hg.continuousAt heq,
    connected_eq_at_closure hclosure hfd hgd hd⟩

/-- A radius identity only assumed inside the open tail has the expected
value and first derivative at its excluded entrance. -/
theorem radialTail_radius_entrance_jet {D : ReferenceData}
    {κ α entry : ℝ} (hκ : 0 < κ) (right : Bool)
    (hentry : entry ∈ radialCore D) {f g : ℝ → ℝ}
    (hf : ContDiffAt ℝ ∞ f (κ * entry)) (hg : ContDiffAt ℝ ∞ g entry)
    (heq : ∀ r ∈ radialTailInterval D right entry, f (κ * r) = α * g r) :
    f (κ * entry) = α * g entry ∧
      deriv f (κ * entry) = α / κ * deriv g entry := by
  have hfs : ContDiffAt ℝ ∞ (fun r : ℝ => f (κ * r)) entry :=
    hf.comp entry (contDiffAt_const.mul contDiffAt_id)
  have hgs : ContDiffAt ℝ ∞ (fun r : ℝ => α * g r) entry := contDiffAt_const.mul hg
  have hj := radialTail_eq_jet_at_entry right hentry hfs hgs heq
  have hd : κ * deriv f (κ * entry) = α * deriv g entry := by
    simpa only [deriv_comp_mul_left, deriv_const_mul_field, smul_eq_mul] using hj.2
  refine ⟨hj.1, ?_⟩
  calc
    deriv f (κ * entry) = κ⁻¹ * (κ * deriv f (κ * entry)) := by
      rw [← mul_assoc, inv_mul_cancel₀ hκ.ne', one_mul]
    _ = κ⁻¹ * (α * deriv g entry) := by rw [hd]
    _ = α / κ * deriv g entry := by
      simp only [div_eq_mul_inv]
      ring

/-- The frozen selected-tail predicate gives a genuine entrance and
outgoing natural solution for a frequency actually lying in the band. -/
theorem selected_band_entry_natural {S : SelectedTailData} (hS : IsSelectedTail S)
    (right : Bool) (n j : ℕ) (hj : 2 ≤ j) (heven : Even j)
    (hband : radialFrequencyBand S.chain S.Cstar n j) :
    S.entry right n ∈ radialCore (S.family S.sigma) ∧
      RadialNaturalTail (S.family S.sigma) right j
        (S.entry right n) (S.outgoing right j) := by
  have h := hS.2.2.2.2.2 right n j hj heven hband
  rcases h with ⟨_, hentry, _, _, _, _, _, _, _, _, _, hnatural, _⟩
  exact ⟨hentry, hnatural⟩

/-- One actual R08 witness works for every valid entrance retained in its
tail. The source of smoothness and all transported profiles is this same
connected geometry, without adding a new realization hypothesis. -/
theorem ConnectedReferenceGeometry.selected_natural_tail_transport_retained
    (Γ : ConnectedReferenceGeometry) (hΓ : Γ.Realizes) (right : Bool) :
    let S : SelectedTailData := Γ.selected
    let D : ReferenceData := S.family S.sigma
    let E : ReferenceData := Γ.reference
    ∃ κ β α : ℝ, 0 < κ ∧ 0 < β ∧ α ≠ 0 ∧
      (if right then E.b else E.a) = κ * (if right then D.b else D.a) ∧
      (∀ r ∈ radialTailInterval D right (S.entry right S.chain.index),
        κ * r ∈ radialTailInterval E right
          (if right then Γ.centralRight else Γ.centralLeft)) ∧
      ∀ entry : ℝ, entry ∈ radialCore D →
        (if right then S.entry right S.chain.index ≤ entry
          else entry ≤ S.entry right S.chain.index) →
        κ * entry ∈ radialCore E ∧
        E.w (κ * entry) = (β * κ) * D.w entry ∧
        deriv E.w (κ * entry) = β * deriv D.w entry ∧
        (ContDiffAt ℝ ∞ (S.outgoing right 2) entry →
          E.phi (κ * entry) = α * S.outgoing right 2 entry ∧
          deriv E.phi (κ * entry) = α / κ * deriv (S.outgoing right 2) entry) ∧
        ∀ (j : ℕ) (u : ℝ → ℝ) (γ : ℝ), γ ≠ 0 →
          RadialNaturalTail D right j entry u →
          RadialNaturalTail E right j (κ * entry) (radialRadiusScale κ γ u) := by
  let S : SelectedTailData := Γ.selected
  let D : ReferenceData := S.family S.sigma
  let E : ReferenceData := Γ.reference
  rcases hΓ with ⟨hS, hacc, _, _, hpatch, _, htails, _, _, _⟩
  have hgeomE : RadialProfileGeometry E := hacc.choose_spec.1
  have hwE : ContDiff ℝ ∞ E.w := hgeomE.2.2.1.1
  have hphiE : ContDiff ℝ ∞ E.phi := hgeomE.2.2.2.1.1
  have hreal := (hS.2.2.2.1 S.sigma hS.2.2.1).1
  rcases hreal with ⟨_, _, _, _, _, _, _, _, _, hbounds⟩
  have hwD : ContDiff ℝ ∞ D.w := hbounds.1.2.2.1.1
  have hlh : Γ.centralLeft < Γ.centralRight :=
    hpatch.2.1.trans (central_turning_radii_pos_ordered.2.trans hpatch.2.2.1)
  have hcut : (if right then Γ.centralRight else Γ.centralLeft) ∈ radialCore E := by
    cases right
    · exact ⟨hpatch.1, hlh.trans hpatch.2.2.2.1⟩
    · exact ⟨hpatch.1.trans hlh, hpatch.2.2.2.1⟩
  obtain ⟨κ, β, α, hκ, hβ, hα, hend0, htail, _⟩ := htails right
  have hend : (if right then E.b else E.a) = κ * (if right then D.b else D.a) := by
    cases right <;> exact hend0
  refine ⟨κ, β, α, hκ, hβ, hα, hend, (fun r hr => (htail r hr).1), ?_⟩
  intro entry hentry hretained
  have hsub : radialTailInterval D right entry ⊆
      radialTailInterval D right (S.entry right S.chain.index) := by
    cases right
    · change entry ≤ S.entry false S.chain.index at hretained
      intro r hr
      exact ⟨hr.1, hr.2.trans_le hretained⟩
    · change S.entry true S.chain.index ≤ entry at hretained
      intro r hr
      exact ⟨hretained.trans_lt hr.1, hr.2⟩
  have hmap : ∀ r ∈ radialTailInterval D right entry,
      κ * r ∈ radialTailInterval E right
        (if right then Γ.centralRight else Γ.centralLeft) :=
    fun r hr => (htail r (hsub hr)).1
  have hw : ∀ r ∈ radialTailInterval D right entry,
      E.w (κ * r) = (β * κ) * D.w r :=
    fun r hr => (htail r (hsub hr)).2.1
  have hphi : ∀ r ∈ radialTailInterval D right entry,
      E.phi (κ * r) = α * S.outgoing right 2 r :=
    fun r hr => (htail r (hsub hr)).2.2
  have hmem := radialRadiusScale_entry_mem_core_of_tail_map
    hκ right hentry hcut hend hmap
  have hwjet := radialTail_radius_entrance_jet hκ right hentry
    hwE.contDiffAt hwD.contDiffAt hw
  have hβκ : (β * κ) / κ = β := by field_simp [hκ.ne']
  refine ⟨hmem, hwjet.1, ?_, ?_, ?_⟩
  · simpa only [hβκ] using hwjet.2
  · intro hu
    exact radialTail_radius_entrance_jet hκ right hentry hphiE.contDiffAt hu hphi
  · intro j u γ hγ hu
    exact radialNaturalTail_reference_scaled hκ hβ hγ right hentry hmem hend hw hu

/-- The original interface forgets only the explicit exterior containment
of the same radius dilation. -/
theorem ConnectedReferenceGeometry.selected_natural_tail_transport
    (Γ : ConnectedReferenceGeometry) (hΓ : Γ.Realizes) (right : Bool) :
    let S : SelectedTailData := Γ.selected
    let D : ReferenceData := S.family S.sigma
    let E : ReferenceData := Γ.reference
    ∃ κ β α : ℝ, 0 < κ ∧ 0 < β ∧ α ≠ 0 ∧
      (if right then E.b else E.a) = κ * (if right then D.b else D.a) ∧
      ∀ entry : ℝ, entry ∈ radialCore D →
        (if right then S.entry right S.chain.index ≤ entry
          else entry ≤ S.entry right S.chain.index) →
        κ * entry ∈ radialCore E ∧
        E.w (κ * entry) = (β * κ) * D.w entry ∧
        deriv E.w (κ * entry) = β * deriv D.w entry ∧
        (ContDiffAt ℝ ∞ (S.outgoing right 2) entry →
          E.phi (κ * entry) = α * S.outgoing right 2 entry ∧
          deriv E.phi (κ * entry) = α / κ * deriv (S.outgoing right 2) entry) ∧
        ∀ (j : ℕ) (u : ℝ → ℝ) (γ : ℝ), γ ≠ 0 →
          RadialNaturalTail D right j entry u →
          RadialNaturalTail E right j (κ * entry) (radialRadiusScale κ γ u) := by
  obtain ⟨κ, β, α, hκ, hβ, hα, hend, _, htransport⟩ :=
    Γ.selected_natural_tail_transport_retained hΓ right
  exact ⟨κ, β, α, hκ, hβ, hα, hend, htransport⟩

end ContinuousFlexibility.Radial
