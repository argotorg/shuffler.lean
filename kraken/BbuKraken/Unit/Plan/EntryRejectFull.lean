module

public import BbuKraken.Unit.Plan.EntryRejectThm
import all BbuKraken.Unit.Plan.EntryRejectThm
public import BbuKraken.Unit.Plan.EntryResult
import all BbuKraken.Unit.Plan.EntryResult

@[expose] public section

open Std.WP Lean.Order
open scoped Program.WP

namespace Bbu.Unit.EntryValidU
open Bbu.Sep

theorem plan_reject_full [Host] [FunDecls] (g : EG) (F : MProp 64) :
    Sep.Body planAsm (fun s => Pre g F s ∧ ¬ Sizes g) (Post g F) := by
  intro s ra
  refine ⟨fun t ⟨ht, hp, hns⟩ => ?_⟩
  have hbad : EntryU.BadArgs g.r.p.m g.r.p.n g.allowed g.strategy :=
    Classical.byContradiction fun hb => hns hb
  obtain ⟨hok, hdi, hsi, hdx, hcx, h8, h9, ha, hcp, hc, htrace,
    xs, v, hlen, hmem⟩ := hp
  let lo := xs.take 8241
  let hi := xs.drop 8241
  have hlo : lo.length = 8241 := by simp only [lo, List.length_take, hlen, entryD]; decide
  have hhi : hi.length = 11 := by simp only [hi, List.length_drop, hlen, entryD]
  have hsplit : lo ++ hi = xs := List.take_append_drop 8241 xs
  let R := Arr (rsp s - 8#64 - BitVec.ofNat 64 (8 * entryD)) lo ∗
    Wd (rsp s + 16#64) g.r.p.drp ∗ Wd (rsp s + 24#64) g.sawPtr ∗
    Wd (rsp s + 32#64) g.r.dataPtr ∗ Wd (rsp s + 40#64) g.r.opsPtr ∗
    Wd (rsp s + 48#64) g.r.sourcesPtr ∗ Buffers g ∗ F
  have frame (words : List Word) (hw : words.length = 11) (w : Word) :
      Stk (rsp s) (lo ++ words) w ∗ (View (rsp s) g ∗ F) =
        Stk (rsp s) words w ∗ EntryU.Args s g.allowed g.strategy R := by
    rw [Stk.split]
    have he : lo.length + words.length = entryD := by rw [hlo, hw]
    rw [he]
    unfold View Args EntryU.Args R
    ac_rfl
  have hreject : EntryU.RejectPre g.allowed g.strategy R s := by
    refine ⟨?_, hi, v, hhi, ?_⟩
    · rw [hdi, hsi]
      exact hbad
    · rw [← frame hi hhi v, hsplit]
      exact hmem
  exact Program.wp_mono (fun _ h => h) (fun u ⟨hret, hr, hag⟩ => by
      obtain ⟨hax, words, w, hw, hm⟩ := hr
      refine ⟨hret, ?_, hag⟩
      refine ⟨g, hok, ?_, lo ++ words, w, ?_, ?_⟩
      · change ResultWord g g (rax u.data) at ⊢
        rw [hax]
        apply result_rejected
        intro us
        unfold model
        apply EntryU.reject_bounds
        exact hbad
      · simp only [List.length_append, hlo, hw]
      · rw [frame words hw w]
        exact hm)
    (((EntryU.plan_rejects_bad_args g.allowed g.strategy R) s ra).1 t ⟨ht, hreject⟩)

end Bbu.Unit.EntryValidU
