From iris.program_logic Require Export weakestpre hoare.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.

Section examples.
 Context `{heapG Σ}.

 Definition local_state (f : expr) `{Closed [] f} : expr :=
  (let: "l" := Alloc #0 in f;; !"l")%E.

 Lemma wp_local_state f `{Closed [] f} : ∀ P Φ,
  {{ heap_ctx ★ {{ P }} f {{ Φ }} ★ P }} local_state f {{v, v = #0 ★ ∃ w, Φ w}}.
 Proof.
  iIntros (P Φ) "!# (#Hctx & Hf & HP)". unfold local_state.
  wp_alloc l as "Hl". wp_let. wp_bind f.
  iApply wp_wand_l. iSplitL "Hl"; last by iApply "Hf".
  iIntros (w) "HΦ". wp_seq. wp_load; iSplit; first done. iExists _; done.
 Qed.

 Definition local_state_lifted (f : expr) `{Closed [] f} : expr :=
  (let: "l" := Alloc #0 in λ: <>, f;; !"l")%E.

 Lemma wp_local_state_lifted f `{Closed [] f} : ∀ P Φ,
  heap_ctx ★ {{ P }} f {{ Φ }} ⊢
  {{ True }} (local_state_lifted f)
   {{v, {{P}} (of_val v) #() {{u, u = #0 ★ ∃ w, Φ w}} }}.
 Proof.
  iIntros (P Φ) "[#Hctx #Hf]!# _". unfold local_state_lifted.
  wp_alloc l as "Hl".
  iMod (inv_alloc (nroot .@ "local_state_lifted") _ (l ↦ #0)%I with "[Hl]")
   as "#Hinv"; first by iNext.
  wp_let. iIntros "!# HP". wp_seq. wp_bind f.
  iApply wp_wand_l. iSplitR; last by iApply "Hf".
  iIntros (w) "HΦ". wp_seq.
  iInv (nroot .@ "local_state_lifted") as "Hl" "Hcl".
  wp_load. iMod ("Hcl" with "[Hl]") as "_"; first by iNext.
  iModIntro. iSplit; first done. iExists _; done.
 Qed.

End examples.