import Thermodynamics.SecondLaw

/-!
# Thermodynamic Temperature

This file states
* the axiom that reversible `cycle`s do exists, i.e. `UsualEngineCycle.exists_reversible`
and defines
* thermodynamic temperature of `Reservoir`s, i.e. `Reservoir.temp`
-/

noncomputable section

namespace Thermodynamics

/-!
### `reversible` `UsualEngineCycle`s
-/

namespace UsualEngineCycle

section
variable {𝓗 𝓒 : Reservoir} (𝓒_lt_𝓗 : 𝓒 < 𝓗)

/-- There exists a reversible `UsualEngineCycle` between any `𝓒 < 𝓗`. -/
axiom exists_reversible : ∃ H : UsualEngineCycle 𝓒_lt_𝓗, H.reversible

variable {Q : ℝ} (hQ : 0 < Q)
/-- There exists reversible `UsualEngineCycle 𝓒_lt_𝓗` that absorbs a certain heat `Q > 0`. -/
lemma exists_rvsbl_abs : ∃ H : UsualEngineCycle 𝓒_lt_𝓗, H.reversible ∧ H.Qabs = Q := by
  let ⟨H',hH'⟩ := exists_reversible 𝓒_lt_𝓗
  let c : ℝ>0 := ⟨Q / H'.Qabs, div_pos hQ H'.do_abs⟩
  exists c • H'
  constructor
  . exact Cycle.reversible_smul_nonneg (le_of_lt c.property) hH'
  . calc
      _ = Q / H'.Qabs * H'.Qabs := Cycle.Qabs_smul_pos c.property
      _ = Q := div_mul_cancel _ (ne_of_gt H'.do_abs)

end

section
variable {𝓗 𝓒 : Reservoir}
/-- Efficiency of reversible `UsualEngineCycle 𝓒_lt_𝓗` -/
def rvsblEff (𝓒_lt_𝓗 : 𝓒 < 𝓗) := (Classical.choose (exists_reversible 𝓒_lt_𝓗)).eff
lemma rvsblEff_universal {𝓒_lt_𝓗 : 𝓒 < 𝓗} {H : UsualEngineCycle 𝓒_lt_𝓗} (hH : H.reversible) :
  H.eff = rvsblEff 𝓒_lt_𝓗 := by
  refine (UsualEngineCycle.rev_iff_eff ?_).mp hH
  exact Classical.choose_spec (exists_reversible 𝓒_lt_𝓗)
end

end UsualEngineCycle

/-!
## Thermodynamic temperature
---------------------------------------------------------------------------------------------------/

/-!
### Construction of thermodynamic temperature
-/

namespace Reservoir

section
variable {𝓗 𝓒 : Reservoir} (𝓒_lt_𝓗 : 𝓒 < 𝓗)

/-- `temp`erature `corr`elation function -/
def tempCorr := 1 - UsualEngineCycle.rvsblEff 𝓒_lt_𝓗
lemma tempCorr_pos    : 0 < tempCorr 𝓒_lt_𝓗 := by
  unfold tempCorr; field_simp; exact UsualEngineCycle.eff_lt_one
lemma tempCorr_lt_one : tempCorr 𝓒_lt_𝓗 < 1 := by
  unfold tempCorr; field_simp; exact Cycle.eff_pos

lemma tempCorr_eq_rvsbl_Qratio {𝓒_lt_𝓗 : 𝓒 < 𝓗} {H : UsualEngineCycle 𝓒_lt_𝓗}
  (hH : H.reversible) : tempCorr 𝓒_lt_𝓗 = H.Qrel / H.Qabs := by
  unfold tempCorr
  calc
    _ = 1 - H.eff := by rw [UsualEngineCycle.rvsblEff_universal hH]
    _ = H.Qrel / H.Qabs := by rw [H.eff_from_Qabs_Qrel]; ring

end

section
variable {𝓐 𝓑 𝓒 : Reservoir} (𝓒_lt_𝓑 : 𝓒 < 𝓑) (𝓑_lt_𝓐 : 𝓑 < 𝓐)
/-- `trans`itivity of `tempCorr` -/
theorem tempCorr_trans :
  tempCorr (𝓒_lt_𝓑.trans 𝓑_lt_𝓐) = (tempCorr 𝓒_lt_𝓑) * (tempCorr 𝓑_lt_𝓐) := by
  let ⟨H𝓐𝓑,hH𝓐𝓑_rvsbl⟩ := UsualEngineCycle.exists_reversible 𝓑_lt_𝓐
  let ⟨H𝓑𝓒,hH𝓑𝓒_rvsbl,hQ⟩ := UsualEngineCycle.exists_rvsbl_abs 𝓒_lt_𝓑 H𝓐𝓑.do_rel
  let 𝓒_lt_𝓐 := 𝓒_lt_𝓑.trans 𝓑_lt_𝓐
  let H𝓐𝓒' := H𝓐𝓑.toCycle + H𝓑𝓒.toCycle
  -- H𝓑𝓒
  have H𝓑𝓒_no_𝓐 : H𝓑𝓒.𝓠 𝓐 = 0 := by
    suffices 𝓐 ∉ H𝓑𝓒.𝓠.support from Finsupp.not_mem_support_iff.mp this
    simp [H𝓑𝓒.two_rsv.1]
    have := ne_of_gt 𝓑_lt_𝓐; have := ne_of_gt 𝓒_lt_𝓐; tauto
  have H𝓐𝓒'_𝓐_eq_H𝓐𝓑 := calc H𝓐𝓒'.𝓠 𝓐
    _ = H𝓐𝓑.𝓠 𝓐 + H𝓑𝓒.𝓠 𝓐 := rfl
    _ = H𝓐𝓑.𝓠 𝓐            := by simp [H𝓑𝓒_no_𝓐]
  have H𝓐𝓒'_do_abs_𝓐 : H𝓐𝓒'.𝓠 𝓐 > 0 := by
    simp [H𝓐𝓒'_𝓐_eq_H𝓐𝓑, H𝓐𝓑.do_abs_rsv]
  -- H𝓐𝓑
  have H𝓐𝓑_no_𝓒 : H𝓐𝓑.𝓠 𝓒 = 0 := by
    suffices 𝓒 ∉ H𝓐𝓑.𝓠.support from Finsupp.not_mem_support_iff.mp this
    simp [H𝓐𝓑.two_rsv.1]
    have := ne_of_lt 𝓒_lt_𝓐; have := ne_of_lt 𝓒_lt_𝓑; tauto
  have H𝓐𝓒'_𝓒_eq_H𝓑𝓒 := calc H𝓐𝓒'.𝓠 𝓒
    _ = H𝓐𝓑.𝓠 𝓒 + H𝓑𝓒.𝓠 𝓒 := rfl
    _ =            H𝓑𝓒.𝓠 𝓒 := by simp [H𝓐𝓑_no_𝓒]
  have H𝓐𝓒'_do_rel_𝓒 : H𝓐𝓒'.𝓠 𝓒 < 0 := by
    simp [H𝓐𝓒'_𝓒_eq_H𝓑𝓒, H𝓑𝓒.do_rel_rsv]
  -- H𝓐𝓒
  let H𝓐𝓒 : UsualEngineCycle 𝓒_lt_𝓐 := {
    H𝓐𝓒' with
    two_rsv := by
      constructor
      . show (H𝓐𝓑.𝓠 + H𝓑𝓒.𝓠).support = {𝓐,𝓒}
        apply Finsupp.support_add_exact
        . simp
          exact ⟨ne_of_gt H𝓐𝓒'_do_abs_𝓐, ne_of_lt H𝓐𝓒'_do_rel_𝓒⟩
        . rw [H𝓐𝓑.two_rsv.1, H𝓑𝓒.two_rsv.1]
          simp [ne_of_lt 𝓑_lt_𝓐, ne_of_gt 𝓒_lt_𝓑]
          calc H𝓐𝓑.𝓠 𝓑 + H𝓑𝓒.𝓠 𝓑
            _ = -H𝓐𝓑.Qrel + H𝓑𝓒.Qabs := by simp [H𝓐𝓑.Qrel_one_rsv, H𝓑𝓒.Qabs_one_rsv]
            _ = 0 := by field_simp [hQ]
      . exact ne_of_gt 𝓒_lt_𝓐
    do_abs_rsv := H𝓐𝓒'_do_abs_𝓐
    do_rel_rsv := H𝓐𝓒'_do_rel_𝓒
    do_work := calc H𝓐𝓒'.𝓦
      _ = H𝓐𝓑.𝓦 + H𝓑𝓒.𝓦 := by simp
      _ > 0 := by have := H𝓐𝓑.do_work; have := H𝓑𝓒.do_work; positivity
  }
  have hH𝓐𝓒_rvsbl : H𝓐𝓒.reversible := Cycle.reversible_add hH𝓐𝓑_rvsbl hH𝓑𝓒_rvsbl
  rw [tempCorr_eq_rvsbl_Qratio hH𝓐𝓑_rvsbl]
  rw [tempCorr_eq_rvsbl_Qratio hH𝓑𝓒_rvsbl]
  rw [tempCorr_eq_rvsbl_Qratio hH𝓐𝓒_rvsbl]
  rw [hQ]
  rw [H𝓐𝓒.Qabs_one_rsv, H𝓐𝓒.Qrel_one_rsv]
  rw [H𝓐𝓒'_𝓐_eq_H𝓐𝓑, H𝓐𝓒'_𝓒_eq_H𝓑𝓒]
  rw [H𝓐𝓑.Qabs_one_rsv, H𝓑𝓒.Qrel_one_rsv]
  have := H𝓐𝓑.do_rel; have := H𝓐𝓑.do_abs_rsv; field_simp; ring
end

/-- `ref`erence `sys`tem -/
@[reducible] def refSys := waterTriplePoint
/-- reference temperature of `ref_sys` -/
@[reducible] def refTemp : ℝ>0 := ⟨273.16, by norm_num⟩
/-- thermodynamic `temp`erature of `Reservoir`s -/
def temp (𝓣 : Reservoir) : ℝ>0 :=
  if        heq : 𝓣 = ⟦refSys⟧ then
    refTemp
  else   if hlt : 𝓣 < ⟦refSys⟧ then
    ⟨(tempCorr hlt) * refTemp.val, mul_pos (tempCorr_pos hlt) refTemp.property⟩
  else have hgt : 𝓣 > ⟦refSys⟧ := Ne.lt_of_le' heq (le_of_not_gt hlt)
    ⟨refTemp.val / (tempCorr hgt), div_pos refTemp.property (tempCorr_pos hgt)⟩
lemma temp_StrictMono : StrictMono temp := by
  intro 𝓒 𝓗 𝓒_lt_𝓗; unfold temp; simp
  by_cases h𝓗_le_ref : 𝓗 ≤ ⟦refSys⟧
  . have h𝓒_lt_ref : 𝓒 < ⟦refSys⟧ := 𝓒_lt_𝓗.trans_le h𝓗_le_ref
    by_cases h𝓗_eq_ref : 𝓗 = ⟦refSys⟧
    . simp [h𝓒_lt_ref, ne_of_lt, h𝓗_eq_ref]
      apply Subtype.coe_lt_coe.mp
      field_simp [tempCorr_lt_one]
    . have h𝓗_lt_ref : 𝓗 < ⟦refSys⟧ := lt_of_le_of_ne h𝓗_le_ref h𝓗_eq_ref
      simp [h𝓒_lt_ref, ne_of_lt, h𝓗_lt_ref]
      apply Subtype.coe_lt_coe.mp
      field_simp
      rw [tempCorr_trans 𝓒_lt_𝓗 h𝓗_lt_ref]
      field_simp [tempCorr_pos, tempCorr_lt_one]
  . have h𝓗_gt_ref : 𝓗 > ⟦refSys⟧ := not_le.mp h𝓗_le_ref
    simp [h𝓗_gt_ref, ne_of_gt, not_lt_of_gt]
    if h𝓒_eq_ref : 𝓒 = ⟦refSys⟧ then
      simp [h𝓒_eq_ref]
      apply Subtype.coe_lt_coe.mp
      rw [lt_div_iff (tempCorr_pos h𝓗_gt_ref)]
      field_simp [tempCorr_lt_one]
    else if h𝓒_lt_ref :  𝓒 < ⟦refSys⟧ then
      simp [h𝓒_lt_ref, ne_of_lt]
      apply Subtype.coe_lt_coe.mp
      rw [lt_div_iff (tempCorr_pos h𝓗_gt_ref)]
      ring_nf; cancel_denoms
      rw [←tempCorr_trans h𝓒_lt_ref h𝓗_gt_ref]
      exact tempCorr_lt_one _
    else
      have h𝓒_gt_ref : 𝓒 > ⟦refSys⟧ := lt_of_le_of_ne (le_of_not_lt h𝓒_lt_ref) (ne_comm.mp h𝓒_eq_ref)
      simp [h𝓒_gt_ref, ne_of_gt, not_lt_of_gt]
      apply Subtype.coe_lt_coe.mp
      rw [div_lt_div_iff (tempCorr_pos h𝓒_gt_ref) (tempCorr_pos h𝓗_gt_ref)]
      field_simp
      rw [tempCorr_trans h𝓒_gt_ref 𝓒_lt_𝓗]
      field_simp [tempCorr_pos, tempCorr_lt_one]

end Reservoir

/-!
### Applications of thermodynamic temperature
-/

namespace UsualEngineCycle
open Reservoir
variable {𝓗 𝓒 : Reservoir} (𝓒_lt_𝓗 : 𝓒 < 𝓗)

lemma rvsblEff_from_temp : rvsblEff 𝓒_lt_𝓗 = 1 - 𝓒.temp / 𝓗.temp := by
  suffices tempCorr 𝓒_lt_𝓗 = 𝓒.temp / 𝓗.temp from by unfold tempCorr at this; linarith
  unfold temp; simp
  by_cases h𝓗_le_ref : 𝓗 ≤ ⟦refSys⟧
  . have h𝓒_lt_ref : 𝓒 < ⟦refSys⟧ := 𝓒_lt_𝓗.trans_le h𝓗_le_ref
    by_cases h𝓗_eq_ref : 𝓗 = ⟦refSys⟧
    . simp [h𝓒_lt_ref, ne_of_lt, h𝓗_eq_ref]
      unfold tempCorr; ring
    . have h𝓗_lt_ref : 𝓗 < ⟦refSys⟧ := lt_of_le_of_ne h𝓗_le_ref h𝓗_eq_ref
      simp [h𝓒_lt_ref, ne_of_lt, h𝓗_lt_ref]
      rw [tempCorr_trans 𝓒_lt_𝓗 h𝓗_lt_ref]
      ring_nf
      have := tempCorr_pos h𝓗_lt_ref
      field_simp
  . have h𝓗_gt_ref : 𝓗 > ⟦refSys⟧ := not_le.mp h𝓗_le_ref
    simp [h𝓗_gt_ref, ne_of_gt, not_lt_of_gt]
    if h𝓒_eq_ref : 𝓒 = ⟦refSys⟧ then
      simp [h𝓒_eq_ref]
      ring_nf; field_simp
    else if h𝓒_lt_ref :  𝓒 < ⟦refSys⟧ then
      simp [h𝓒_lt_ref, ne_of_lt]
      ring_nf; field_simp
      exact tempCorr_trans h𝓒_lt_ref h𝓗_gt_ref
    else
      have h𝓒_gt_ref : 𝓒 > ⟦refSys⟧ := lt_of_le_of_ne (le_of_not_lt h𝓒_lt_ref) (ne_comm.mp h𝓒_eq_ref)
      simp [h𝓒_gt_ref, ne_of_gt, not_lt_of_gt]
      ring_nf; field_simp
      rw [tempCorr_trans h𝓒_gt_ref 𝓒_lt_𝓗]
      have := tempCorr_pos h𝓒_gt_ref
      field_simp; ring

end UsualEngineCycle

end Thermodynamics
